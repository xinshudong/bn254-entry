/-
**Phase 3, P1m — (B1) the fixed-key part off the curve: the designed run, described.**

Off the curve the designed shadow runs the pads at `k₁` and system A through the fill runner with
nothing planted. With nothing planted the fill runner never flags, and system A and the pads are
never intercepted, so it is P4's refill runner (`runFillFlag_eq_runRefill`), and the refill run's
description applies (`off_described`):

* every stored fixed pair is a question of system A at its canonical input (`off_fixed_input`),
  at a mask site `tape ⊕ input` (`off_site_output`), and no other index is touched
  (`off_curveLane`);
* every fold index of system A holds exactly its fold pair (`off_fold_final`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedKey

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source IsDesignated interceptAnswer)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt FixedAt IndexAt
  runRefill cellOf consumeCell refillAnswer queriesAlong queriesAlong_bind queriesAlong_pure
  evalLaneM_allQ uniformMaskTape consumedIndex foldLabels)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### With nothing planted, the fill runner is the refill runner -/

section Bridge

/-- **The fill runner with nothing planted is the refill runner**, on intercept-free programs. -/
theorem runFillFlag_eq_runRefill (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (computation : FreeQuery Programs.Spec α)
    (free : AllQ (fun r => interceptAnswer bits r = none) computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      runFillFlag LazyOracle.empty draw computation oracle touched =
        (runRefill bits draw computation oracle record touched).map
          (Option.map fun o => (o.1, o.2.1)) := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runFillFlag, runRefill, PMF.pure_map, Option.map_some]
  | query request next ih =>
    intro oracle record touched
    have intercept : interceptAnswer bits request = none := AllQ.head free
    simp only [runFillFlag, runRefill, intercept]
    cases consume : consumeCell touched oracle request with
    | some cell =>
      simp only [PMF.map_bind]
      refine congrArg _ (funext fun limb => ?_)
      rw [if_neg (not_fullTouch_empty _ _)]
      cases LazyOracle.program request (refillAnswer request limb) oracle with
      | none => simp only [PMF.pure_map, Option.map_none]
      | some updated => exact ih _ (AllQ.tail free _) updated record _
    | none =>
      simp only [PMF.map_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [if_neg (not_fullTouch_empty _ _)]
      exact ih _ (AllQ.tail free _) _ record _

end Bridge

/-! ### The designed off-curve program -/

section Program

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

theorem designedOffM_eq (first : Block) :
    designedOffM table bits mac first = Programs.padsM ⟨first, 0⟩ >>= fun _ =>
      curveXM table bits mac >>= fun _ => curveYM table bits mac >>= fun _ => pure () := rfl

theorem mem_off (ans : (request : Request) → request.Answer) (first : Block) (q : Request)
    (member : q ∈ queriesAlong ans (designedOffM table bits mac first)) :
    q ∈ queriesAlong ans (Programs.padsM ⟨first, 0⟩) ∨
      q ∈ queriesAlong ans (curveXM table bits mac) ∨
        q ∈ queriesAlong ans (curveYM table bits mac) := by
  rw [designedOffM_eq] at member
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append] at member
  exact member

theorem curveX_mem_off (ans : (request : Request) → request.Answer) (first : Block) (q : Request)
    (member : q ∈ queriesAlong ans (curveXM table bits mac)) :
    q ∈ queriesAlong ans (designedOffM table bits mac first) := by
  rw [designedOffM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append]
  exact Or.inr (Or.inl member)

theorem curveY_mem_off (ans : (request : Request) → request.Answer) (first : Block) (q : Request)
    (member : q ∈ queriesAlong ans (curveYM table bits mac)) :
    q ∈ queriesAlong ans (designedOffM table bits mac first) := by
  rw [designedOffM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, List.mem_append]
  exact Or.inr (Or.inr member)

theorem designedOffM_free (first : Block) :
    AllQ (fun r => interceptAnswer bits r = none) (designedOffM table bits mac first) := by
  rw [designedOffM_eq]
  refine ((padsM_allQ _).mono fun _ inside => intercept_none_of_encAt inside).bind fun _ => ?_
  refine ((evalLaneM_allQ _ _ _ _ _ _).mono fun r inside =>
    curve_notIntercepted bits .curveX (Or.inl rfl) r inside).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _ _).mono fun r inside =>
    curve_notIntercepted bits .curveY (Or.inr rfl) r inside).bind fun _ => .pure _

theorem designedOff_fresh (first : Block) : Fresh bits ∅ (designedOffM table bits mac first) := by
  have padsNone : AllQ (fun r => consumedIndex bits r = none) (Programs.padsM ⟨first, 0⟩) :=
    (padsM_allQ _).mono fun _ inside => consumedIndex_none_of_encAt inside
  rw [designedOffM_eq]
  refine Fresh.bind (S := ∅) (Fresh.of_none padsNone _)
    (padsNone.mono fun _ none => inIdx_of_none none) fun _ => ?_
  refine Fresh.bind (S := laneSet .curveX)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i _ outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  · rcases outside with outside | outside <;> exact outside
  refine Fresh.bind (S := laneSet .curveY)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i inside outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => .pure _ _
  rcases outside with (outside | outside) | outside
  · exact outside
  · exact outside
  · exact laneSet_ne (by decide) inside outside

variable [GroupCertificate] in
/-- **Every fixed-key question off the curve is a question of system A at its canonical input.** -/
theorem off_fixed_input (ans : (request : Request) → request.Answer) (first : Block)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) (tmac : InputMac)
    (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (designedOffM table bits mac first)) :
    x = inputOf table bits mac pads ans tmac i ∧
      ((∃ c, IndexAt .curveX c i) ∨ ∃ c, IndexAt .curveY c i) := by
  rcases mem_off table bits mac ans first _ member with a | b | c
  · exact absurd (mem_queriesAlong_allQ ans (padsM_allQ _) _ a) not_encAt_fixed
  · exact ⟨laneQuery_inputOf table bits mac pads ans tmac .curveX _ _ i x b,
      Or.inl (mem_queriesAlong_allQ ans (evalLaneM_allQ _ _ _ _ _ _) _ b)⟩
  · exact ⟨laneQuery_inputOf table bits mac pads ans tmac .curveY _ _ i x c,
      Or.inr (mem_queriesAlong_allQ ans (evalLaneM_allQ _ _ _ _ _ _) _ c)⟩

end Program

/-! ### The designed off-curve run -/

section Run

variable [FieldCertificate] [GroupCertificate]

/-- The designed off-curve run of a source, a key `k₁` and a tape. (A `def`: the unifier must never
compare it with the unfolded runner.) -/
def offRun (source : Stage1Source) (input : AffineInput) (first : Block) (tape : Tape) :
    PMF (Option (Unit × LState × Record)) :=
  runRefill (restoredBits source input) (fun cell => PMF.pure (tape cell))
    (designedOffM source.publicValue (restoredBits source input) (restoredMac source input) first)
    LazyOracle.empty (fun _ => none) ∅

theorem off_described (source : Stage1Source) (input : AffineInput) (first : Block) (tape : Tape)
    (o : Unit × LState × Record) (member : some o ∈ (offRun source input first tape).support) :
    Described (restoredBits source input) tape
      (designedOffM source.publicValue (restoredBits source input) (restoredMac source input) first)
      LazyOracle.empty (fun _ => none) o := by
  unfold offRun at member
  exact runRefill_describe (restoredBits source input) tape _
    (designedOffM_forwardOnly _ _ _ first) ∅ (designedOff_fresh _ _ _ first) LazyOracle.empty
    (fun _ => none) ∅ (fun _ _ => ⟨fun h => h, rfl⟩) o member

variable (source : Stage1Source) (input : AffineInput) (first : Block) (tape : Tape)
  (o : Unit × LState × Record) (member : some o ∈ (offRun source input first tape).support)

include member

/-- **Every stored pair off the curve is a system-A pair at its canonical input.** -/
theorem off_final_input (i : FixedIndex) (x y : Fin (2 ^ 128))
    (found : lk (o.2.1.fixed i) x = some y) :
    BitVec.ofFin x = inputOf source.publicValue (restoredBits source input)
        (restoredMac source input) (fun _ _ => (0, 0))
        (refillAns (restoredBits source input) o.2.1) (restoredMac source input) i ∧
      ((∃ c, IndexAt .curveX c i) ∨ ∃ c, IndexAt .curveY c i) := by
  rcases (off_described source input first tape o member).fixed i x y found with old | ⟨onPath, _, _⟩
  · rw [lk_empty_fixed] at old
    cases old
  · exact off_fixed_input _ _ _ _ first _ _ i _ onPath

/-- **At a mask site the stored output is `tape ⊕ input`.** -/
theorem off_site_output (i : FixedIndex) {cell : Cell} (cellEq : cellOf i = some cell)
    (x y : Fin (2 ^ 128)) (found : lk (o.2.1.fixed i) x = some y) :
    BitVec.ofFin y = tape cell ^^^ BitVec.ofFin x := by
  rcases (off_described source input first tape o member).fixed i x y found with old | ⟨_, _, tapeOut⟩
  · rw [lk_empty_fixed] at old
    cases old
  · exact tapeOut cell cellEq

/-- **Every fold index of system A holds exactly its fold pair.** -/
theorem off_fold_final (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY) (c : Fin chunkCount)
    (half : Bool) :
    let W := laneW (laneJoins source.publicValue lane)
      (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c
    let index := foldIdx lane c (chunkValue (laneWord (restoredBits source input) lane) c).toNat half
    (o.2.1.fixed index).used = 1 ∧
      lk (o.2.1.fixed index) W.toFin =
        some (fwdAns (refillAns (restoredBits source input) o.2.1) index W).toFin := by
  intro W index
  have onA : .fixedForward index W ∈ queriesAlong (refillAns (restoredBits source input) o.2.1)
      (designedOffM source.publicValue (restoredBits source input) (restoredMac source input)
        first) := by
    rcases curve with rfl | rfl
    · exact curveX_mem_off _ _ _ _ first _ (fold_mem_lane _ _ .curveX _ _ _ _ c half)
    · exact curveY_mem_off _ _ _ _ first _ (fold_mem_lane _ _ .curveY _ _ _ _ c half)
  have stored := (off_described source input first tape o member).stored _ onA
    (intercept_none_of_hot lane c _ half W)
  have lk1 := stored_fixed_lk stored
  have fwdEq : fwdAns (refillAns (restoredBits source input) o.2.1) index W =
      answerOf o.2.1 (.fixedForward index W) :=
    refillAns_plain (intercept_none_of_hot lane c _ half W)
  refine ⟨?_, by rw [fwdEq]; exact lk1⟩
  have small := used_le_one _ (inputOf source.publicValue (restoredBits source input)
      (restoredMac source input) (fun _ _ => (0, 0)) (refillAns (restoredBits source input) o.2.1)
      (restoredMac source input) index).toFin
    fun x y found => by
      rw [← (off_final_input source input first tape o member index x y found).1,
        BitVec.toFin_ofFin]
  have positive : (o.2.1.fixed index).used ≠ 0 := by
    intro zero
    have known : (o.2.1.fixed index).knownInput W.toFin :=
      (knownInput_iff _ _).mpr (by rw [lk1]; exact Option.some_ne_none _)
    unfold SparsePermutation.knownInput at known
    omega
  omega

end Run

/-! ### Off the curve, with a potential -/

section Whole

variable [FieldCertificate] [GroupCertificate]

/-- **Off the curve, with a potential that may read the tape.** -/
theorem off_whole_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (potential : Tape → LState → ℝ≥0∞)
    (step : ∀ (tape : Tape) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (state : LState), ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential tape answer.2 ≤
          potential tape state)
    (siteSame : ∀ (tape : Tape) (state updated : LState) (index : FixedIndex)
      (input' output : Block), cellOf index ≠ none →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential tape updated = potential tape state)
    (c : ℝ≥0∞) (initial : ∀ tape, potential tape LazyOracle.empty ≤ c)
    (final : ∀ (first : Block) (tape : Tape) (o : Unit × LState × Record),
      some o ∈ (offRun source input first tape).support →
        ind (event (pointsOf o.2.1)) ≤ potential tape o.2.1) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ c := by
  refine le_trans (off_event_le scalar source input event (fun _ _ => c) fun first tape => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe, PMF.tsum_coe,
      one_mul, one_mul]))
  rw [runFillFlag_eq_runRefill (restoredBits source input) _ _
    (designedOffM_free _ _ _ first) LazyOracle.empty (fun _ => none) ∅, tsum_map_mul]
  refine le_trans (tsum_mul_le_of_support _ _ (optWeight (potential tape)) fun o member => ?_) ?_
  · rcases o with _ | o
    · exact zero_le
    · exact final first tape o (by unfold offRun; exact member)
  · exact le_trans (runRefill_potential_sites _ _ ForwardOnly (potential tape) (siteSame tape)
      (step tape) _ (designedOffM_forwardOnly _ _ _ first) _ _ _) (initial tape)

/-- **A deterministic event off the curve.** -/
theorem off_const_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Q : Prop)
    (reduce : ∀ (first : Block) (tape : Tape) (o : Unit × LState × Record),
      some o ∈ (offRun source input first tape).support → event (pointsOf o.2.1) → Q) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ ind Q :=
  off_whole_le scalar source input event (fun _ _ => ind Q)
    (fun _ request state _ => le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    (fun _ _ _ _ _ _ _ _ => rfl) (ind Q) (fun _ => le_rfl)
    fun first tape o member => ind_mono (reduce first tape o member)

/-- **A single fixed output off the curve** at an index without a mask site: `≤ 1/2^128`. -/
theorem offSingle_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (i : FixedIndex) (noCell : cellOf i = none) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedOut i y) ≤ delta := by
  refine off_whole_le scalar source input (fun p => p.fixedOut i y)
    (fun _ s => singleF y.toFin (s.fixed i))
    (fun _ request state forward => fixed_lift_step i _ (singleF_step _) request forward state)
    (fun _ state updated index input' output isCell success =>
      fixed_siteSame i _ noCell state updated index input' output isCell success) delta
    (fun _ => le_of_eq ?_) fun first tape o member => ?_
  · show singleF y.toFin (SparsePermutation.empty _) = delta
    have zero : (SparsePermutation.empty (2 ^ 128)).used = 0 := rfl
    unfold singleF
    rw [if_pos zero]
  · exact singleF_bound _ _ (used_le_one _ (inputOf source.publicValue (restoredBits source input)
      (restoredMac source input) (fun _ _ => (0, 0)) (refillAns (restoredBits source input) o.2.1)
      (restoredMac source input) i).toFin fun x y' found => by
        rw [← (off_final_input source input first tape o member i x y' found).1,
          BitVec.toFin_ofFin])

/-- **An index outside system A is never touched off the curve.** -/
theorem offNone_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (i : FixedIndex) (outside : ¬ ((∃ c, IndexAt .curveX c i) ∨ ∃ c, IndexAt .curveY c i))
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop)
    (touches : ∀ state : LState, event (pointsOf state) → ∃ x y, lk (state.fixed i) x = some y) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ 0 :=
  le_trans (off_const_le scalar source input event False fun first tape o member hit => by
    obtain ⟨x, y, found⟩ := touches o.2.1 hit
    exact outside (off_final_input source input first tape o member i x y found).2)
    (le_of_eq (ind_neg id))

/-- **At a mask index of system A off the curve, the canonical input hits any tape-dependent
target with mass `≤ 1/2^128`.** -/
theorem offCurveScale_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX)
    (b : Fin 3) (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (z : Tape → Block)
    (reduce : ∀ (first : Block) (tape : Tape) (o : Unit × LState × Record),
      some o ∈ (offRun source input first tape).support → event (pointsOf o.2.1) →
        (lane = .curveX ∨ lane = .curveY) ∧
          inputOf source.publicValue (restoredBits source input) (restoredMac source input)
            (fun _ _ => (0, 0)) (refillAns (restoredBits source input) o.2.1)
            (restoredMac source input) (.scale lane c s e b) = z tape) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind (event (outcomePoints o)) ≤ delta := by
  set value := (chunkValue (laneWord (restoredBits source input) lane) c).toNat with valueDef
  set fixedPart : Block := foldLabels value
    (labelAt (chunkLabels (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c))
    (joinAt (hotSlice (laneJoins source.publicValue lane) c)) 0 ⟨s.val, by
      have := s.isLt; unfold chunkBits at this; exact this⟩ with fixedDef
  refine off_whole_le scalar source input event
    (fun tape => chunkFoldPot lane c value (z tape ^^^ fixedPart))
    (fun tape => chunkFoldPot_step lane c value _)
    (fun tape => chunkFoldPot_siteSame lane c value _) delta
    (fun tape => le_of_eq (chunkFoldPot_empty lane c value _))
    fun first tape o member => ?_
  by_cases hit : event (pointsOf o.2.1)
  · obtain ⟨curve, same⟩ := reduce first tape o member hit
    obtain ⟨used0, lk0⟩ := off_fold_final source input first tape o member lane curve c false
    obtain ⟨used1, lk1⟩ := off_fold_final source input first tape o member lane curve c true
    refine le_trans (ind_mono fun _ => ?_) (foldF_bound _ _ _ used0 used1 _ _ _ _ lk0 lk1)
    rw [inputOf_scale] at same
    rw [BitVec.ofFin_toFin, BitVec.ofFin_toFin]
    exact (xor_eq_iff _ _ _).mp same
  · rw [ind_neg hit]
    exact zero_le

end Whole


end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
