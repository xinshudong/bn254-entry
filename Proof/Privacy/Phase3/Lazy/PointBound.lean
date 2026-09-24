/-
**Phase 3, P4b — `pointPart_bound`: (a) the law of `E*` off the fold hit, (b) the output's
independence from it, and the collision masses.** See `FailPoint.lean` for the statement's shape.
-/

import Proof.Privacy.Phase3.Lazy.FailPoint

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (laneCount)
open scoped ENNReal

noncomputable section

section Point

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (input : AffineInput) (target : Point) (bits : BitInput)
  (mac : InputMac) (tape : Tape)

/-- The per-slot collision masses of a designated input `E`, given the lanes. -/
def restObs (label : Block)
    (result : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record × Set FixedIndex) : ℝ≥0∞ :=
  ∑ slot : Slot, (slotInput stage bits label slot +
    expectO (blockLaw table input target bits result.1) (slotOutput stage bits label slot))

/-- **Summed over a fresh shift of `E`, the collision masses are at most twice the designated
entries**, whatever the law of the lanes. -/
theorem restObs_sum_le (μ : PMF (Option (((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)) × LState × Record × Set FixedIndex))) (base : Block) :
    ∑' a, expectO μ (restObs stage table input target bits (base ^^^ a)) ≤
      2 * slotCharge stage bits := by
  rw [← expectO_tsum]
  refine (expectO_mono μ fun result => ?_).trans (expectO_const_le μ _)
  unfold restObs
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable, slotCharge, Finset.mul_sum]
  refine Finset.sum_le_sum fun slot _ => ?_
  rw [ENNReal.tsum_add, slotInput_sum, ← expectO_tsum]
  have outputs : expectO (blockLaw table input target bits result.1)
      (fun blocks => ∑' a, slotOutput stage bits (base ^^^ a) slot blocks) ≤
        ((stage.fixed (slotIndex bits slot)).used : ℝ≥0∞) := by
    refine (expectO_mono _ fun blocks => (slotOutput_sum stage bits slot base blocks).le).trans ?_
    exact expectO_const_le _ _
  rw [two_mul]
  exact add_le_add le_rfl outputs

/-- **(b) After the fold, off a mask hit.** The masks are consumed from the tape, their value is
the tape's, the rest of the run reads neither the labels nor the fold answers, and the only
record entries are `E*`: the failure is at most the collision masses of `E*` under a law of the
lanes that does not depend on the labels. -/
theorem masks_rest_le (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (oracle : LState) (touched : Set FixedIndex) (hot : Fin (2 ^ chunkWidth chunkZero) → Block)
    (state : LState) (touched' : Set FixedIndex)
    (noHit : ¬ ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin pointElementCountX × Fin 3,
      MaskHitSite bits .pointX site ∧
        (stage.fixed (maskIndex .pointX chunkZero site.1.val site.2.1 site.2.2)).knownInput
          (hot site.1).toFin)
    (maskState : ∀ (switch : Fin (2 ^ chunkWidth chunkZero)) (element : Fin pointElementCountX)
      (block : Fin 3), state.fixed (maskIndex .pointX chunkZero switch.val element block) =
        stage.fixed (maskIndex .pointX chunkZero switch.val element block))
    (maskTouched : ∀ (switch : Fin (2 ^ chunkWidth chunkZero)) (element : Fin pointElementCountX)
      (block : Fin 3), maskIndex .pointX chunkZero switch.val element block ∉ touched')
    (agree : AgreeOn PointRestIndex state oracle)
    (touchAgree : TouchAgree PointRestIndex touched' touched) :
    expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
        (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero) hot
          (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
        state (fun _ => none) touched')
        (fun r => failObs stage table input target bits r.1 r.2.2.1) ≤
      expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (pointRest table bits mac pads (maskValues bits tape pointElementCountX .pointX chunkZero
            (chunkWidth chunkZero) (chunkOf (Pipeline.coordBits bits .x) chunkZero)))
          oracle (fun _ => none) touched)
        (restObs stage table input target bits (hot (designatedSwitch bits))) := by
  set alpha := chunkOf (Pipeline.coordBits bits .x) chunkZero
  have countLe : pointElementCountX ≤ laneCount .pointX := le_refl _
  have ready := masks_detRun_ne_none bits tape .pointX chunkZero pointElementCountX countLe hot
    alpha state (fun _ => none) touched'
    (fun switch _ element block _ => maskTouched switch element block)
    (fun switch active element block notDesignated known => noHit
      ⟨(switch, element, block), ⟨active, notDesignated⟩, by
        rw [← maskState switch element block]
        exact known⟩)
  obtain ⟨result, success⟩ := Option.ne_none_iff_exists'.mp ready
  rw [detRun_bind_spec bits tape _ _ _ _ _ result success]
  cases result with
  | none =>
      simp only [continueT, expectO_pure_none]
      exact zero_le
  | some r =>
      simp only [continueT]
      have value : r.1 = maskValues bits tape pointElementCountX .pointX chunkZero
          (chunkWidth chunkZero) alpha :=
        (detRun_value bits tape _ _ _ _ r success).trans
          (masks_value bits tape .pointX chunkZero pointElementCountX countLe hot alpha)
      obtain ⟨frame, encSame, hashSame⟩ := detRun_frame bits tape (IndexAt .pointX chunkZero)
        (evalMasksM_allQ .pointX chunkZero _ _ hot alpha) _ _ _ r success
      have labelled : AllQ (fun request => ∀ index input, request = .fixedForward index input →
          IsDesignated bits index → input = hot (designatedSwitch bits))
          (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero) hot
            alpha) :=
        (evalMasksM_maskQuery pointElementCountX .pointX chunkZero _ hot alpha).mono
          fun request query => by
            obtain ⟨switch, element, block, rfl⟩ := query
            intro index input same designated
            simp only [PublicQuery.fixedForward.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            rw [designated_switch bits switch element block designated]
      have recordBound := detRun_record bits tape (hot (designatedSwitch bits)) labelled _ _ _ r
        success
      have outside : ∀ index, PointRestIndex index → ¬ IndexAt .pointX chunkZero index := by
        intro index inside atZero
        rcases inside with ⟨c, at'⟩ | ⟨c, at'⟩
        · exact chunk_succ_ne_zero c (indexAt_unique at' atZero).2
        · exact absurd (indexAt_unique at' atZero).1 (by decide)
      have agreeRest : AgreeOn PointRestIndex r.2.1 oracle :=
        ⟨fun index inside => ((frame index (outside index inside)).1).trans (agree.1 index inside),
          encSame.trans agree.2.1, hashSame.trans agree.2.2⟩
      have touchRest : TouchAgree PointRestIndex r.2.2.2 touched := fun index inside =>
        ((frame index (outside index inside)).2).trans (touchAgree index inside)
      rw [value]
      have law := runRefillT_value_frame bits (fun cell => PMF.pure (tape cell)) PointRestIndex
        (pointRest_plain bits table bits mac pads (maskValues bits tape pointElementCountX .pointX
          chunkZero (chunkWidth chunkZero) alpha)) r.2.1 oracle r.2.2.1 (fun _ => none) r.2.2.2
        touched agreeRest touchRest
      have recordSame : ∀ q, some q ∈ (runRefillT bits (fun cell => PMF.pure (tape cell))
          (pointRest table bits mac pads (maskValues bits tape pointElementCountX .pointX chunkZero
            (chunkWidth chunkZero) alpha)) r.2.1 r.2.2.1 r.2.2.2).support → q.2.2.1 = r.2.2.1 :=
        fun q member => (runRefillT_support_frame bits (fun cell => PMF.pure (tape cell))
          PointRestIndex (pointRest_plain bits table bits mac pads _) _ _ _ q member).2
      rw [expectO_frame_value _ _ law r.2.2.1 recordSame
        (fun lanes record => failObs stage table input target bits lanes record)]
      refine expectO_mono _ fun q => failObs_le stage table input target bits q.1 r.2.2.1
        (hot (designatedSwitch bits)) fun slot => ?_
      rcases recordBound (slotIndex bits slot) with same | same
      · exact Or.inl same
      · exact Or.inr same

/-- The chunk-0 labels of `pointX` at material `m`. -/
abbrev pointHot (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (material : Block) : Fin (2 ^ chunkWidth chunkZero) → Block :=
  chunkHot bits table.pointXHot (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) material

/-- The whitened level-1 label of chunk 0 of `pointX`. -/
abbrev pointLabel (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) : Block :=
  chunkLabel table.pointXHot (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)

/-- The `pointX` part of the run, the fold unfolded. -/
theorem pointPart_run (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (oracle : LState) (record : Record) (touched : Set FixedIndex) :
    runRefillT bits (fun cell => PMF.pure (tape cell)) (pointPart table bits mac pads) oracle
        record touched =
      (forwardAnswer (foldIndex .pointX bits false) (pointLabel table mac pads) oracle).bind
        fun first => (forwardAnswer (foldIndex .pointX bits true) (pointLabel table mac pads)
          first.2).bind fun second =>
            runRefillT bits (fun cell => PMF.pure (tape cell))
              (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero)
                (pointHot table bits mac pads (first.1 ^^^ second.1))
                (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
              second.2 record
              (touch (.fixedForward (foldIndex .pointX bits true) (pointLabel table mac pads))
                (touch (.fixedForward (foldIndex .pointX bits false)
                  (pointLabel table mac pads)) touched)) := by
  rw [pointPart_split]
  exact runRefillT_evalFold_two bits _ .pointX chunkZero _ _ _ _ oracle record touched

open Classical in
/-- **`pointPart_bound`.** -/
theorem pointPart_bound (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (oracle : LState) (touched : Set FixedIndex)
    (sameState : ∀ index, IndexAt .pointX chunkZero index → oracle.fixed index = stage.fixed index)
    (untouched : ∀ index, IndexAt .pointX chunkZero index → index ∉ touched) :
    expectO (runRefillT bits (fun cell => PMF.pure (tape cell)) (pointPart table bits mac pads)
        oracle (fun _ => none) touched)
        (fun r => failObs stage table input target bits r.1 r.2.2.1) ≤
      (if (stage.fixed (foldIndex .pointX bits true)).knownInput
          (pointLabel table mac pads).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .pointX bits true)) *
          (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits) := by
  by_cases foldHit : (stage.fixed (foldIndex .pointX bits true)).knownInput
      (pointLabel table mac pads).toFin
  · rw [if_pos foldHit]
    exact le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _ _ _ _ _) le_self_add
  rw [if_neg foldHit, zero_add, pointPart_run, expectO_bind]
  set i0 := foldIndex .pointX bits false
  set i1 := foldIndex .pointX bits true
  set W := pointLabel table mac pads
  set μ := runRefillT bits (fun cell => PMF.pure (tape cell))
    (pointRest table bits mac pads (maskValues bits tape pointElementCountX .pointX chunkZero
      (chunkWidth chunkZero) (chunkOf (Pipeline.coordBits bits .x) chunkZero)))
    oracle (fun _ => none) touched
  set bound : Block → ℝ≥0∞ := fun material =>
    maskHit stage bits .pointX pointElementCountX (pointHot table bits mac pads material) +
      expectO μ (restObs stage table input target bits
        (pointHot table bits mac pads material (designatedSwitch bits)))
  set κ := freshCharge (stage.fixed i1)
  set K := maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits
  have i0ne : i0 ≠ i1 := foldIndex_ne .pointX bits
  -- per pair of fold answers
  have perPair : ∀ first ∈ (forwardAnswer i0 W oracle).support,
      ∀ second ∈ (forwardAnswer i1 W first.2).support,
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero)
            (pointHot table bits mac pads (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
          second.2 (fun _ => none)
          (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage table input target bits r.1 r.2.2.1) ≤
        bound (first.1 ^^^ second.1) := by
    intro first firstMember second secondMember
    by_cases hit : ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin pointElementCountX × Fin 3,
        MaskHitSite bits .pointX site ∧
          (stage.fixed (maskIndex .pointX chunkZero site.1.val site.2.1 site.2.2)).knownInput
            (pointHot table bits mac pads (first.1 ^^^ second.1) site.1).toFin
    · refine le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _ _ _ _ _) ?_
      refine le_trans (le_of_eq ?_) le_self_add
      unfold maskHit
      rw [if_pos hit]
    · refine le_trans ?_ le_add_self
      have atMask : ∀ (switch : Fin (2 ^ chunkWidth chunkZero)) (element : Fin pointElementCountX)
          (block : Fin 3), second.2.fixed (maskIndex .pointX chunkZero switch.val element block) =
            stage.fixed (maskIndex .pointX chunkZero switch.val element block) := by
        intro switch element block
        rw [forwardAnswer_frame i1 W first.2 second secondMember _
            (foldIndex_ne_mask .pointX .pointX bits true _ _ _),
          forwardAnswer_frame i0 W oracle first firstMember _
            (foldIndex_ne_mask .pointX .pointX bits false _ _ _)]
        exact sameState _ (scaleIndexOf_indexAt _ _ _ _ _)
      have notFold : ∀ index, PointRestIndex index → index ≠ i0 ∧ index ≠ i1 := by
        intro index inside
        have away : ¬ IndexAt .pointX chunkZero index := by
          intro atZero
          rcases inside with ⟨c, at'⟩ | ⟨c, at'⟩
          · exact chunk_succ_ne_zero c (indexAt_unique at' atZero).2
          · exact absurd (indexAt_unique at' atZero).1 (by decide)
        exact ⟨fun same => away (same ▸ foldIndex_indexAt _ _ _),
          fun same => away (same ▸ foldIndex_indexAt _ _ _)⟩
      have encHash₁ := forwardAnswer_encHash i0 W oracle first firstMember
      have encHash₂ := forwardAnswer_encHash i1 W first.2 second secondMember
      refine masks_rest_le stage table input target bits mac tape pads oracle touched _ second.2 _
        hit atMask ?_ ⟨fun index inside => ?_, encHash₂.1.trans encHash₁.1,
          encHash₂.2.trans encHash₁.2⟩ ?_
      · intro switch element block member
        simp only [touch, Set.mem_ofPred_eq, touchedIndex, Option.some.injEq] at member
        rcases member with (member | same) | same
        · exact untouched _ (scaleIndexOf_indexAt _ _ _ _ _) member
        · exact foldIndex_ne_mask .pointX .pointX bits false _ _ _ same
        · exact foldIndex_ne_mask .pointX .pointX bits true _ _ _ same
      · obtain ⟨ne0, ne1⟩ := notFold index inside
        rw [forwardAnswer_frame i1 W first.2 second secondMember _ (Ne.symm ne1),
          forwardAnswer_frame i0 W oracle first firstMember _ (Ne.symm ne0)]
      · intro index inside
        obtain ⟨ne0, ne1⟩ := notFold index inside
        simp only [touch, Set.mem_ofPred_eq, touchedIndex, Option.some.injEq]
        constructor
        · rintro ((member | same) | same)
          · exact member
          · exact (ne0 same.symm).elim
          · exact (ne1 same.symm).elim
        · exact fun member => Or.inl (Or.inl member)
  -- the sum over the second answer: it is fresh
  have perFirst : ∀ first ∈ (forwardAnswer i0 W oracle).support,
      ∑' second, (forwardAnswer i1 W first.2) second *
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero)
            (pointHot table bits mac pads (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
          second.2 (fun _ => none)
          (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage table input target bits r.1 r.2.2.1) ≤ κ * K := by
    intro first firstMember
    have atSecond : first.2.fixed i1 = stage.fixed i1 := by
      rw [forwardAnswer_frame i0 W oracle first firstMember i1 i0ne]
      exact sameState _ (foldIndex_indexAt _ _ _)
    calc (∑' second, (forwardAnswer i1 W first.2) second *
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
            (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero)
              (pointHot table bits mac pads (first.1 ^^^ second.1))
              (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
            second.2 (fun _ => none)
            (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
            (fun r => failObs stage table input target bits r.1 r.2.2.1))
        ≤ ∑' second, (forwardAnswer i1 W first.2) second * bound (first.1 ^^^ second.1) := by
          refine ENNReal.tsum_le_tsum fun second => ?_
          by_cases zero : (forwardAnswer i1 W first.2) second = 0
          · rw [zero, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (perPair first firstMember second
              ((PMF.mem_support_iff _ _).mpr zero)) zero_le
      _ ≤ freshCharge (first.2.fixed i1) * ∑' a, bound (first.1 ^^^ a) :=
          forwardAnswer_sum_le i1 W first.2 (by rw [atSecond]; exact foldHit)
            fun a => bound (first.1 ^^^ a)
      _ ≤ κ * K := by
          rw [atSecond]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [ENNReal.tsum_add]
          refine add_le_add (maskHit_sum_le stage bits .pointX pointElementCountX _ _ _) ?_
          have shift : ∀ a, pointHot table bits mac pads (first.1 ^^^ a) (designatedSwitch bits) =
              (pointHot table bits mac pads 0 (designatedSwitch bits) ^^^ first.1) ^^^ a := by
            intro a
            exact (foldLabels_linear _ _ _ (first.1 ^^^ a) _).trans (BitVec.xor_assoc _ _ _).symm
          simp only [shift]
          exact restObs_sum_le stage table input target bits μ _
  calc (∑' first, (forwardAnswer i0 W oracle) first *
        expectO ((forwardAnswer i1 W first.2).bind fun second =>
          runRefillT bits (fun cell => PMF.pure (tape cell))
            (Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero)
              (pointHot table bits mac pads (first.1 ^^^ second.1))
              (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= pointRest table bits mac pads)
            second.2 (fun _ => none)
            (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) touched)))
          (fun r => failObs stage table input target bits r.1 r.2.2.1))
      ≤ ∑' first, (forwardAnswer i0 W oracle) first * (κ * K) := by
        refine ENNReal.tsum_le_tsum fun first => ?_
        by_cases zero : (forwardAnswer i0 W oracle) first = 0
        · rw [zero, zero_mul, zero_mul]
        · rw [expectO_bind]
          exact mul_le_mul_of_nonneg_left (perFirst first ((PMF.mem_support_iff _ _).mpr zero))
            zero_le
    _ = κ * K := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Point

end

end Kriterion.ArgoMAC.Phase3.Lazy
