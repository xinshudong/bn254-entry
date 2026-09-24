/-
**Phase 3, P1m — (B1) the fixed-key conjunct off the curve.**

Off the curve only system A is asked (`off_final_input`): a curve fold input is the source's own
label (`offHotCurveIn_le`, uniform over the key: `hotCurve_key_le`), a curve mask input hits a
point through the fold potential (`offCurveScale_le`), an output is a fresh lazy image or
`tape ⊕ input` (`offSingle_le`, `offCurveScale_le`), and every other index is untouched
(`offNone_le`):

* `designed_fixed_off` — off the curve, `Pr[x ∈ fixedIn_i] + Pr[y ∈ fixedOut_i] ≤ 4/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape IndexAt cellOf uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

section Conjunct

variable [FieldCertificate] [GroupCertificate]

/-- **The input mass at a curve fold index off the curve** is the indicator of the source's own
fold input. -/
theorem offHotCurveIn_le (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool)
    (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤
      ind (laneW (laneJoins source.publicValue lane)
        (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c = x) :=
  off_const_le scalar source input (fun p => p.fixedIn (.hot lane c f e h) x)
    (laneW (laneJoins source.publicValue lane)
      (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c = x)
    fun first tape o member hit => by
      obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp hit
      have same := (off_final_input source input first tape o member _ _ _ found).1
      rw [BitVec.ofFin_toFin] at same
      exact same.symm

theorem lane_cases (lane : Lane) :
    (lane = .curveX ∨ lane = .curveY) ∨ (lane = .pointX ∨ lane = .pointY) := by
  cases lane <;> simp

/-- **The input half off the curve**: `≤ 2/2^128`. -/
theorem designed_fixedIn_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (x : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [keyedPoints_measure_eq, offCurve]
  have touchesIn : ∀ (j : FixedIndex) (state : LState), (pointsOf state).fixedIn j x →
      ∃ x' y', lk (state.fixed j) x' = some y' := fun j state hit => by
    obtain ⟨y', found⟩ := Option.ne_none_iff_exists'.mp hit
    exact ⟨_, y', found⟩
  cases i with
  | hot lane c f e h =>
    rcases lane_cases lane with curve | point
    · exact le_trans (ENNReal.tsum_le_tsum fun key => mul_le_mul' le_rfl
        (offHotCurveIn_le scalar (joinSource pub key) input lane c f e h x))
        (le_trans (hotCurve_key_le pub input lane curve c x) delta_le_two)
    · have outside : ¬ ((∃ c', IndexAt .curveX c' (.hot lane c f e h)) ∨
          ∃ c', IndexAt .curveY c' (.hot lane c f e h)) := by
        rintro (⟨_, hl, _⟩ | ⟨_, hl, _⟩) <;> rcases point with rfl | rfl <;> cases hl
      exact tsum_le_of_support' _ _ _ fun key _ => le_trans
        (offNone_le scalar (joinSource pub key) input _ outside
          (fun p => p.fixedIn (.hot lane c f e h) x) (touchesIn _)) zero_le
  | scale lane c s e b =>
    exact tsum_le_of_support' _ _ _ fun key _ => le_trans
      (offCurveScale_le scalar (joinSource pub key) input lane c s e b
        (fun p => p.fixedIn (.scale lane c s e b) x) (fun _ => x)
        fun first tape o member hit => by
          obtain ⟨y', found⟩ := Option.ne_none_iff_exists'.mp hit
          obtain ⟨same, lanes⟩ := off_final_input (joinSource pub key) input first tape o member
            _ _ _ found
          rw [BitVec.ofFin_toFin] at same
          refine ⟨?_, same.symm⟩
          rcases lanes with ⟨_, hl, _⟩ | ⟨_, hl, _⟩
          · exact Or.inl hl
          · exact Or.inr hl) delta_le_two
  | gadget d κ pos =>
    have outside : ¬ ((∃ c', IndexAt .curveX c' (.gadget d κ pos)) ∨
        ∃ c', IndexAt .curveY c' (.gadget d κ pos)) := by
      rintro (⟨_, hl⟩ | ⟨_, hl⟩) <;> exact hl
    exact tsum_le_of_support' _ _ _ fun key _ => le_trans
      (offNone_le scalar (joinSource pub key) input _ outside
        (fun p => p.fixedIn (.gadget d κ pos) x) (touchesIn _)) zero_le

/-- **The output half off the curve**: `≤ 1/2^128 ≤ 2/2^128`. -/
theorem designed_fixedOut_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
      2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_
  rw [offCurve]
  refine le_trans ?_ delta_le_two
  cases i with
  | hot lane c f e h => exact offSingle_le scalar source input _ (hot_noCell lane c f e h) y
  | gadget d κ pos => exact offSingle_le scalar source input _ (gadget_noCell d κ pos) y
  | scale lane c s e b =>
    cases cellEq : cellOf (.scale lane c s e b) with
    | none => exact offSingle_le scalar source input _ cellEq y
    | some cell =>
      exact offCurveScale_le scalar source input lane c s e b
        (fun p => p.fixedOut (.scale lane c s e b) y) (fun tape => y ^^^ tape cell)
        fun first tape o member hit => by
          obtain ⟨x, found⟩ := hit
          obtain ⟨inputEq, lanes⟩ := off_final_input source input first tape o member _ x _ found
          have outEq := off_site_output source input first tape o member _ cellEq x _ found
          rw [BitVec.ofFin_toFin] at outEq
          refine ⟨?_, ?_⟩
          · rcases lanes with ⟨_, hl, _⟩ | ⟨_, hl, _⟩
            · exact Or.inl hl
            · exact Or.inr hl
          · rw [← inputEq, outEq, BitVec.xor_comm (tape cell), BitVec.xor_assoc, BitVec.xor_self,
              BitVec.xor_zero]

/-- **The fixed-key conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`, off the
curve.** -/
theorem designed_fixed_off (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (offCurve : Scheme.scheme.function scalar input = none) (i : FixedIndex) (x y : Block) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedIn i x} +
      (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.fixedOut i y} ≤
        4 / 2 ^ 128 := by
  rw [← two_inv_add_two_inv]
  exact add_le_add (designed_fixedIn_off scalar pub input offCurve i x)
    (designed_fixedOut_off scalar pub input offCurve i y)

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
