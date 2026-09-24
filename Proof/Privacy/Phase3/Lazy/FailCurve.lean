/-
**Phase 3, P4b — the `curveX` part of the per-prefix failure bound, and the failure mass as an
expectation over the refill run.**

* `failMass_le_runs` — the installation-failure mass of `I^U` is at most the tape average of the
  expected `failObs` of the refill run (a failed installation is a slot collision with stage 1,
  `run_fail_collides`).
* `opening_bound` — from the stage-1 oracle, the honest evaluation fails with mass at most
  `1[W_c ∈ dom σ₁(i₁ᶜ)] + (1/(2^128 − n(i₁ᶜ))) · (curveX chunk-0 mask entries)` plus the expected
  `pointPart_bound` over the law of the pads. `W_c` is the raw bit-0 label: off its fold hit,
  the `curveX` chunk-0 labels are fresh; off a mask hit, the `curveX` chunk-0 masks are the tape's,
  so the rest of system A, the hash and the pads have a law that reads neither the fold answers
  nor the chunk-0 labels.
-/

import Proof.Privacy.Phase3.Lazy.PointBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (laneCount simulatedRows)
open scoped ENNReal

noncomputable section

theorem expectO_value_eq {α : Type} (μ ν : PMF (Option (α × LState × Record × Set FixedIndex)))
    (law : μ.map (Option.map Prod.fst) = ν.map (Option.map Prod.fst)) (f : α → ℝ≥0∞) :
    expectO μ (fun r => f r.1) = expectO ν (fun r => f r.1) := by
  have first := expectO_map μ Prod.fst f
  have second := expectO_map ν Prod.fst f
  rw [law] at first
  exact first.symm.trans second

section Curve

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (input : AffineInput) (target : Point) (bits : BitInput)
  (mac : InputMac) (tape : Tape)

/-! ### The failure mass is an expectation over the run -/

/-- **On the run's support, a failed installation is a slot collision with stage 1.** -/
theorem run_fail_collides (draw : Cell → PMF Block)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some ran ∈ (runRefill bits draw (openingQueriesM table bits mac) stage
      (fun _ => none) ∅).support)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block)
    (fails : programAll (programRequests bits ran.2.2 blocks) ran.2.1 = none) :
    ∃ slot, SlotCollides stage bits ran.2.2 blocks slot := by
  have present : ∀ request ∈ programRequests bits ran.2.2 blocks, request.2.1 ≠ none := by
    intro request requestMember
    simp only [programRequests, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and] at requestMember
    obtain ⟨digit, collector, block, rfl⟩ := requestMember
    exact runRefill_records bits draw _ ⟨digit, collector, block, rfl⟩
      (openingQueriesM_queriesAt table bits mac digit collector block) stage _ ∅ _ member ran rfl
  obtain ⟨request, requestMember, collides⟩ := programAll_fail _ _ present
    (programRequests_nodup bits ran.2.2 blocks) fails
  simp only [programRequests, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at requestMember
  obtain ⟨digit, collector, block, rfl⟩ := requestMember
  obtain ⟨recorded, same, hit⟩ := collides
  refine ⟨(digit, collector, block), recorded, same, ?_⟩
  rw [runRefill_frame bits draw _ ⟨digit, collector, block, rfl⟩
    (openingQueriesM_forwardOnly table bits mac) stage _ ∅ _ member ran rfl] at hit
  exact hit

open Classical in
/-- The installation continuation after the run fails at most `failObs`. -/
theorem install_le_failObs
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (collide : ∀ blocks, programAll (programRequests bits ran.2.2 blocks) ran.2.1 = none →
      ∃ slot, SlotCollides stage bits ran.2.2 blocks slot) :
    ((simulatedRows input target).bind fun targets => match targets with
      | none => PMF.pure none
      | some targets =>
        (preimages idealSamplers (collectorTargets bits
            (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
              (Pipeline.digitValues ran.1.1 ran.1.2) bits.toAffine) targets)).bind
          fun blocks => match blocks with
          | none => PMF.pure none
          | some blocks => PMF.pure (some (programRequests bits ran.2.2 blocks, ran.2.1))
      ).toOuterMeasure {inputs | FailsInstall inputs} ≤
      failObs stage table input target bits ran.1 ran.2.2 := by
  unfold failObs blockLaw
  rw [PMF.toOuterMeasure_bind_apply, expectO_bind]
  refine ENNReal.tsum_le_tsum fun targets => mul_le_mul_of_nonneg_left ?_ zero_le
  cases targets with
  | none =>
      rw [PMF.toOuterMeasure_pure_apply, if_neg (by rintro ⟨_, _, same, _⟩; cases same)]
      exact zero_le
  | some targets =>
      dsimp only
      rw [PMF.toOuterMeasure_bind_apply]
      unfold expectO
      refine ENNReal.tsum_le_tsum fun blocks => mul_le_mul_of_nonneg_left ?_ zero_le
      cases blocks with
      | none =>
          rw [PMF.toOuterMeasure_pure_apply, if_neg (by rintro ⟨_, _, same, _⟩; cases same)]
          exact zero_le
      | some blocks =>
          rw [PMF.toOuterMeasure_pure_apply]
          split
          · rename_i fails
            obtain ⟨requests, final, same, failed⟩ := fails
            simp only [Option.some.injEq, Prod.mk.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            simp only [Option.elim]
            rw [if_pos (collide blocks failed)]
          · exact zero_le

/-- A bind's mass on a set that its `none` branch avoids is at most an expectation bounding each
successful branch. -/
theorem bind_toOuterMeasure_le {X Y : Type} (μ : PMF (Option X)) (cont : Option X → PMF (Option Y))
    (S : Set (Option Y)) (f : X → ℝ≥0∞) (noneCont : (cont none).toOuterMeasure S = 0)
    (someCont : ∀ x, some x ∈ μ.support → (cont (some x)).toOuterMeasure S ≤ f x) :
    (μ.bind cont).toOuterMeasure S ≤ expectO μ f := by
  rw [PMF.toOuterMeasure_bind_apply]
  unfold expectO
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases zero : μ o = 0
  · rw [zero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  cases o with
  | none =>
      rw [noneCont]
      exact zero_le
  | some x => exact someCont x ((PMF.mem_support_iff _ _).mpr zero)

/-- **The failure mass is at most the tape average of the run's expected `failObs`.** -/
theorem failMass_le_runs (labels : LamportSignature) :
    failMass table input labels target stage ≤
      ∑' tape, uniformMaskTape tape *
        expectO (runRefillT (Lamport.restore input labels).input (fun cell => PMF.pure (tape cell))
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac)
          stage (fun _ => none) ∅) (fun r => failObs stage table input target
            (Lamport.restore input labels).input r.1 r.2.2.1) := by
  set bits := (Lamport.restore input labels).input
  set mac := (Lamport.restore input labels).inputMac
  unfold failMass installInputs
  dsimp only
  refine (bind_toOuterMeasure_le _ _ _
    (fun ran => failObs stage table input target bits ran.1 ran.2.2) ?_ ?_).trans ?_
  · rw [PMF.toOuterMeasure_pure_apply, if_neg (by rintro ⟨_, _, same, _⟩; cases same)]
  · intro ran member
    obtain ⟨tape, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact install_le_failObs stage table input target bits ran
      (run_fail_collides stage table bits mac _ ran member)
  · unfold refillRun
    rw [expectO_bind]
    refine le_of_eq (tsum_congr fun tape => ?_)
    rw [runRefill_eq_runRefillT, expectO_map]
    rfl

/-! ### The `curveX` chunk 0 -/

/-- The raw level-1 label of chunk 0 of `curveX`. -/
abbrev curveLabel : Block := chunkLabel table.curveXHot (Pipeline.macLabels mac .x)

/-- The chunk-0 labels of `curveX` at material `m`. -/
abbrev curveHot (material : Block) : Fin (2 ^ chunkWidth chunkZero) → Block :=
  chunkHot bits table.curveXHot (Pipeline.macLabels mac .x) material

/-- The `curveX` chunk-0 mask values on the tape. -/
abbrev curveMasks : Fin (2 ^ chunkWidth chunkZero) → Fin curveElementCountX → BaseField :=
  maskValues bits tape curveElementCountX .curveX chunkZero (chunkWidth chunkZero)
    (chunkOf (Pipeline.coordBits bits .x) chunkZero)

open Classical in
/-- The `pointPart` bound as a function of the pads. -/
def pointBound (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) : ℝ≥0∞ :=
  (if (stage.fixed (foldIndex .pointX bits true)).knownInput
      (pointLabel table mac pads).toFin then 1 else 0) +
    freshCharge (stage.fixed (foldIndex .pointX bits true)) *
      (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)

/-- A detRun without designated queries leaves the record as it is. -/
theorem detRun_record_plain {α : Type} {c : FreeQuery Programs.Spec α}
    (plain : AllQ (fun request => ∀ index input, request = .fixedForward index input →
      ¬ IsDesignated bits index) c) (oracle : LState) (record : Record)
    (touched : Set FixedIndex) (result : α × LState × Record × Set FixedIndex)
    (success : detRun bits tape c oracle record touched = some (some result)) :
    result.2.2.1 = record := by
  funext index
  have labelled : ∀ label : Block, AllQ (fun request => ∀ index input,
      request = .fixedForward index input → IsDesignated bits index → input = label) c :=
    fun label => plain.mono fun request never index input same designated =>
      (never index input same designated).elim
  rcases detRun_record bits tape 0 (labelled 0) oracle record touched result success index with
    same | zero
  · exact same
  rcases detRun_record bits tape 1 (labelled 1) oracle record touched result success index with
    same | one
  · exact same
  rw [zero] at one
  exact absurd (Option.some.inj one) (by decide)

open Classical in
/-- **`opening_bound`.** -/
theorem opening_bound :
    expectO (runRefillT bits (fun cell => PMF.pure (tape cell)) (openingQueriesM table bits mac)
        stage (fun _ => none) ∅) (fun r => failObs stage table input target bits r.1 r.2.2.1) ≤
      (if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table mac).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) *
          maskCharge stage bits .curveX curveElementCountX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits mac (curveMasks bits tape)) stage (fun _ => none) ∅)
          (fun q => pointBound stage table bits mac q.1) := by
  set draw : Cell → PMF Block := fun cell => PMF.pure (tape cell)
  set i0 := foldIndex .curveX bits false
  set i1 := foldIndex .curveX bits true
  set W := curveLabel table mac
  set X := expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) stage
    (fun _ => none) ∅) (fun q => pointBound stage table bits mac q.1)
  set κ := freshCharge (stage.fixed i1)
  set G : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) × LState ×
      Record × Set FixedIndex → ℝ≥0∞ := fun r => failObs stage table input target bits r.1 r.2.2.1
  have runEq : runRefillT bits draw (openingQueriesM table bits mac) stage (fun _ => none) ∅ =
      (forwardAnswer i0 W stage).bind fun first => (forwardAnswer i1 W first.2).bind fun second =>
        runRefillT bits draw (Programs.evalMasksM curveElementCountX .curveX chunkZero
            (chunkWidth chunkZero) (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 (fun _ => none) (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅)) := by
    rw [openingQueriesM_split]
    exact runRefillT_evalFold_two bits draw .curveX chunkZero _ _ _ _ stage _ ∅
  by_cases foldHit : (stage.fixed i1).knownInput W.toFin
  · rw [if_pos foldHit]
    refine le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _ _ _ _ _) ?_
    rw [add_assoc]
    exact le_self_add
  rw [if_neg foldHit, zero_add, runEq, expectO_bind]
  have i0ne : i0 ≠ i1 := foldIndex_ne .curveX bits
  have notCurveZero : ∀ index, IndexAt .pointX chunkZero index → ¬ IndexAt .curveX chunkZero index :=
    fun index atPoint atCurve => absurd (indexAt_unique atPoint atCurve).1 (by decide)
  have perPair : ∀ first ∈ (forwardAnswer i0 W stage).support,
      ∀ second ∈ (forwardAnswer i1 W first.2).support,
        expectO (runRefillT bits draw (Programs.evalMasksM curveElementCountX .curveX chunkZero
            (chunkWidth chunkZero) (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 (fun _ => none) (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))) G ≤
        maskHit stage bits .curveX curveElementCountX (curveHot table bits mac (first.1 ^^^ second.1))
          + X := by
    intro first firstMember second secondMember
    set hot := curveHot table bits mac (first.1 ^^^ second.1)
    have stateAt : ∀ index, index ≠ i0 → index ≠ i1 → second.2.fixed index = stage.fixed index :=
      fun index ne0 ne1 => by
        rw [forwardAnswer_frame i1 W first.2 second secondMember _ (Ne.symm ne1),
          forwardAnswer_frame i0 W stage first firstMember _ (Ne.symm ne0)]
    have encHash₁ := forwardAnswer_encHash i0 W stage first firstMember
    have encHash₂ := forwardAnswer_encHash i1 W first.2 second secondMember
    have touchedAt : ∀ index, index ∈ touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅) →
        index = i0 ∨ index = i1 := by
      intro index member
      simp only [touch, Set.mem_ofPred_eq, touchedIndex, Option.some.injEq,
        Set.mem_empty_iff_false, false_or] at member
      rcases member with same | same
      · exact Or.inl same.symm
      · exact Or.inr same.symm
    by_cases hit : ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin curveElementCountX × Fin 3,
        MaskHitSite bits .curveX site ∧
          (stage.fixed (maskIndex .curveX chunkZero site.1.val site.2.1 site.2.2)).knownInput
            (hot site.1).toFin
    · refine le_trans (expectO_le_one _ fun r => failObs_le_one _ _ _ _ _ _ _) ?_
      refine le_trans (le_of_eq ?_) le_self_add
      unfold maskHit
      rw [if_pos hit]
    refine le_trans ?_ le_add_self
    have countLe : curveElementCountX ≤ laneCount .curveX := le_refl _
    have ready := masks_detRun_ne_none bits tape .curveX chunkZero curveElementCountX countLe hot
      (chunkOf (Pipeline.coordBits bits .x) chunkZero) second.2 (fun _ => none)
      (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))
      (fun switch _ element block _ member => by
        rcases touchedAt _ member with same | same
        · exact foldIndex_ne_mask .curveX .curveX bits false _ _ _ same.symm
        · exact foldIndex_ne_mask .curveX .curveX bits true _ _ _ same.symm)
      (fun switch active element block notDesignated known => hit
        ⟨(switch, element, block), ⟨active, notDesignated⟩, by
          rw [← stateAt _ (foldIndex_ne_mask .curveX .curveX bits false _ _ _).symm
            (foldIndex_ne_mask .curveX .curveX bits true _ _ _).symm]
          exact known⟩)
    obtain ⟨result, success⟩ := Option.ne_none_iff_exists'.mp ready
    rw [detRun_bind_spec bits tape _ _ _ _ _ result success]
    cases result with
    | none =>
        simp only [continueT, expectO_pure_none]
        exact zero_le
    | some r =>
        simp only [continueT]
        have value : r.1 = curveMasks bits tape :=
          (detRun_value bits tape _ _ _ _ r success).trans
            (masks_value bits tape .curveX chunkZero curveElementCountX countLe hot _)
        obtain ⟨frame, encSame, hashSame⟩ := detRun_frame bits tape (IndexAt .curveX chunkZero)
          (evalMasksM_allQ .curveX chunkZero _ _ hot _) _ _ _ r success
        have recordNone : r.2.2.1 = fun _ => none := detRun_record_plain bits tape
          ((evalMasksM_allQ .curveX chunkZero curveElementCountX _ hot _).mono fun request inside =>
            by
              intro index input same designated
              subst same
              exact absurd (indexAt_unique (designated_indexAt designated) inside).1 (by decide))
          _ _ _ r success
        rw [value, expectO_runBind]
        have outside : ∀ index, CurveRestIndex index → ¬ IndexAt .curveX chunkZero index := by
          intro index inside atZero
          rcases inside with ⟨c, at'⟩ | ⟨c, at'⟩
          · exact chunk_succ_ne_zero c (indexAt_unique at' atZero).2
          · exact absurd (indexAt_unique at' atZero).1 (by decide)
        have foldNe : ∀ index, ¬ IndexAt .curveX chunkZero index → index ≠ i0 ∧ index ≠ i1 :=
          fun index away => ⟨fun same => away (same ▸ foldIndex_indexAt _ _ _),
            fun same => away (same ▸ foldIndex_indexAt _ _ _)⟩
        calc expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) r.2.1
              r.2.2.1 r.2.2.2) (fun q => expectO (runRefillT bits draw (pointPart table bits mac q.1)
                q.2.1 q.2.2.1 q.2.2.2) G)
            ≤ expectO (runRefillT bits draw (curveRest table bits mac (curveMasks bits tape)) r.2.1
                r.2.2.1 r.2.2.2) (fun q => pointBound stage table bits mac q.1) := by
              refine expectO_mono_support _ fun q member => ?_
              obtain ⟨qframe, qrecord⟩ := runRefillT_support_frame bits draw CurveRestIndex
                (curveRest_plain bits table bits mac _) _ _ _ q member
              rw [qrecord, recordNone]
              refine pointPart_bound stage table input target bits mac tape q.1 q.2.1 q.2.2.2
                (fun index atPoint => ?_) (fun index atPoint inQ => ?_)
              · have notRest : ¬ CurveRestIndex index := by
                  rintro (⟨c, at'⟩ | ⟨c, at'⟩)
                  · exact absurd (indexAt_unique atPoint at').1 (by decide)
                  · exact absurd (indexAt_unique atPoint at').1 (by decide)
                obtain ⟨ne0, ne1⟩ := foldNe index (notCurveZero index atPoint)
                rw [(qframe index notRest).1, (frame index (notCurveZero index atPoint)).1,
                  stateAt index ne0 ne1]
              · have notRest : ¬ CurveRestIndex index := by
                  rintro (⟨c, at'⟩ | ⟨c, at'⟩)
                  · exact absurd (indexAt_unique atPoint at').1 (by decide)
                  · exact absurd (indexAt_unique atPoint at').1 (by decide)
                have inR := ((qframe index notRest).2).mp inQ
                have inT := ((frame index (notCurveZero index atPoint)).2).mp inR
                obtain ⟨ne0, ne1⟩ := foldNe index (notCurveZero index atPoint)
                rcases touchedAt index inT with same | same
                · exact ne0 same
                · exact ne1 same
          _ = X := by
              refine expectO_value_eq _ _ ?_ (fun pads => pointBound stage table bits mac pads)
              refine runRefillT_value_frame bits draw CurveRestIndex
                (curveRest_plain bits table bits mac _) _ _ _ _ _ _
                ⟨fun index inside => ?_, encSame.trans (encHash₂.1.trans encHash₁.1),
                  hashSame.trans (encHash₂.2.trans encHash₁.2)⟩ fun index inside => ?_
              · obtain ⟨ne0, ne1⟩ := foldNe index (outside index inside)
                rw [(frame index (outside index inside)).1, stateAt index ne0 ne1]
              · obtain ⟨ne0, ne1⟩ := foldNe index (outside index inside)
                rw [(frame index (outside index inside)).2]
                constructor
                · intro member
                  rcases touchedAt index member with same | same
                  · exact (ne0 same).elim
                  · exact (ne1 same).elim
                · intro member
                  exact member.elim
  have perFirst : ∀ first ∈ (forwardAnswer i0 W stage).support,
      ∑' second, (forwardAnswer i1 W first.2) second *
        expectO (runRefillT bits draw (Programs.evalMasksM curveElementCountX .curveX chunkZero
            (chunkWidth chunkZero) (curveHot table bits mac (first.1 ^^^ second.1))
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
              curveRest table bits mac masks >>= pointPart table bits mac)
          second.2 (fun _ => none) (touch (.fixedForward i1 W) (touch (.fixedForward i0 W) ∅))) G ≤
        κ * maskCharge stage bits .curveX curveElementCountX + X := by
    intro first firstMember
    have atSecond : first.2.fixed i1 = stage.fixed i1 :=
      forwardAnswer_frame i0 W stage first firstMember i1 i0ne
    calc _ ≤ ∑' second, (forwardAnswer i1 W first.2) second *
            (maskHit stage bits .curveX curveElementCountX
              (curveHot table bits mac (first.1 ^^^ second.1)) + X) := by
          refine ENNReal.tsum_le_tsum fun second => ?_
          by_cases zero : (forwardAnswer i1 W first.2) second = 0
          · rw [zero, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (perPair first firstMember second
              ((PMF.mem_support_iff _ _).mpr zero)) zero_le
      _ = ∑' second, (forwardAnswer i1 W first.2) second *
            maskHit stage bits .curveX curveElementCountX
              (curveHot table bits mac (first.1 ^^^ second.1)) + X := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ κ * maskCharge stage bits .curveX curveElementCountX + X := by
          refine add_le_add ?_ le_rfl
          refine (forwardAnswer_sum_le i1 W first.2 (by rw [atSecond]; exact foldHit)
            fun a => maskHit stage bits .curveX curveElementCountX
              (curveHot table bits mac (first.1 ^^^ a))).trans ?_
          rw [atSecond]
          exact mul_le_mul_of_nonneg_left (maskHit_sum_le stage bits .curveX curveElementCountX
            _ _ _) zero_le
  calc _ ≤ ∑' first, (forwardAnswer i0 W stage) first *
          (κ * maskCharge stage bits .curveX curveElementCountX + X) := by
        refine ENNReal.tsum_le_tsum fun first => ?_
        by_cases zero : (forwardAnswer i0 W stage) first = 0
        · rw [zero, zero_mul, zero_mul]
        · rw [expectO_bind]
          exact mul_le_mul_of_nonneg_left (perFirst first ((PMF.mem_support_iff _ _).mpr zero))
            zero_le
    _ = κ * maskCharge stage bits .curveX curveElementCountX + X := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Curve

end

end Kriterion.ArgoMAC.Phase3.Lazy
