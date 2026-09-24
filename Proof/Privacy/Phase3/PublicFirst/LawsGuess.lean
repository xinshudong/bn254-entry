/-
**Phase 3, P1o — the coincidence guess, real.**

`coincidenceGuess : CoincidenceGuess (ENNReal.ofReal coincidenceError)`: at every fixed input and
against every weight on the stage-1 view `(P, enc)`, the reach meets a hidden garbler entry with
mass at most `2^16/2^128`.

* **Cover** (`LawsGuessReach.coincide_events`): a coincidence is one of `4064` label events —
  per lane and chunk a level-1 coincidence (event 1, system B off the curve) and four level-2 ones
  (event 2, no level-1 coincidence), per gadget position and bit a coincidence off the curve
  (event 3), per gadget position a collision on the curve (event 4).
* **Each event** has conditional mass `≤ 2/2^128` given the view (`LawsGuessFamily`: the
  `k₂`-family, the `Δ`-family, the transposition family).
* **Total**: `4064 · 2/2^128 = 8128/2^128 ≤ 2^16/2^128` (a factor `≈ 2^3` of room).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsGuessFamily
import Proof.Privacy.Phase3.PublicFirst.LiftGuess

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open scoped ENNReal

noncomputable section

namespace Guess

/-- The coincidence events: event 1 per (lane, chunk), event 2 per (lane, chunk, switch), event 3
per (coordinate, position, bit), event 4 per (coordinate, position). -/
abbrev EventIndex :=
  (Lane × Fin chunkCount) ⊕ (Lane × Fin chunkCount × Fin 4) ⊕
    (Coord × Fin PlanB.coordinateBits × Bool) ⊕ (Coord × Fin PlanB.coordinateBits)

theorem card_eventIndex : Fintype.card EventIndex = 4064 := by
  simp only [EventIndex, Fintype.card_sum, Fintype.card_prod, card_lane, card_coord, Fintype.card_fin,
    Fintype.card_bool]
  rfl

section Events

variable [FieldCertificate] [GroupCertificate]

/-- The event of an index. -/
def eventOf (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) :
    EventIndex → Coins × Oracle → Prop
  | .inl (lane, c) => fun tape => Hit1 parameter scalar tape input lane c
  | .inr (.inl (lane, c, j)) => fun tape => Hit2 parameter scalar tape input lane c j
  | .inr (.inr (.inl (κ, position, bit))) => fun tape => GadgetOff tape input κ position bit
  | .inr (.inr (.inr (κ, position))) => fun tape => GadgetOn tape κ position

open Classical in
/-- **Each event's guess bound.** -/
theorem event_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (i : EventIndex)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if eventOf parameter scalar input i tape then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) * ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
  rcases i with ⟨lane, c⟩ | ⟨lane, c, j⟩ | ⟨κ, position, bit⟩ | ⟨κ, position⟩
  · exact hit1_bound parameter scalar input lane c weight
  · exact hit2_bound parameter scalar input lane c j weight
  · exact gadgetOff_bound parameter scalar input κ position bit weight
  · exact gadgetOn_bound parameter scalar input κ position weight

/-- **The cover**: a coincidence is one of the events. -/
theorem coincide_cover (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    ∃ i, eventOf parameter scalar input i tape := by
  rcases coincide_events parameter scalar tape input hit with
    ⟨lane, c, one⟩ | ⟨lane, c, j, two⟩ | ⟨κ, position, bit, three⟩ | ⟨κ, position, four⟩
  · exact ⟨.inl (lane, c), one⟩
  · exact ⟨.inr (.inl (lane, c, j)), two⟩
  · exact ⟨.inr (.inr (.inl (κ, position, bit))), three⟩
  · exact ⟨.inr (.inr (.inr (κ, position))), four⟩

open Classical in
theorem coincideWeight_le (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    coincideWeight parameter scalar tape input ≤
      ∑ i : EventIndex, if eventOf parameter scalar input i tape then 1 else 0 := by
  unfold coincideWeight
  split
  · rename_i hit
    obtain ⟨i, holds⟩ := coincide_cover parameter scalar tape input hit
    calc (1 : ℝ≥0∞) = if eventOf parameter scalar input i tape then 1 else 0 := by rw [if_pos holds]
      _ ≤ ∑ j : EventIndex, if eventOf parameter scalar input j tape then 1 else 0 :=
        Finset.single_le_sum (f := fun j => if eventOf parameter scalar input j tape then (1 : ℝ≥0∞) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ i)
  · exact zero_le

theorem viewOf_eq_stageOneView (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    viewOf parameter scalar tape = stageOneView parameter scalar tape := rfl

theorem coincidenceError_eq : ENNReal.ofReal coincidenceError = (2 ^ 16 / 2 ^ 128 : ℝ≥0∞) := by
  unfold coincidenceError
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem guess_count_le : (4064 : ℝ≥0∞) * (2 / 2 ^ 128) ≤ 2 ^ 16 / 2 ^ 128 := by
  rw [← mul_div_assoc]
  exact ENNReal.div_le_div_right (by norm_num) _

open Classical in
/-- **The per-input coincidence guess, at a fixed input.** -/
theorem coincidence_guess_at (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape *
        (weight (viewOf parameter scalar tape) * coincideWeight parameter scalar tape input)
      ≤ ENNReal.ofReal coincidenceError *
          ∑' tape, swappedChallengeTape tape * weight (viewOf parameter scalar tape) := by
  simp only [viewOf_eq_stageOneView]
  calc ∑' tape, swappedChallengeTape tape *
        (weight (stageOneView parameter scalar tape) * coincideWeight parameter scalar tape input)
      ≤ ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
          ∑ i : EventIndex, if eventOf parameter scalar input i tape then 1 else 0) :=
        ENNReal.tsum_le_tsum fun tape =>
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (coincideWeight_le parameter scalar tape input))
    _ = ∑ i : EventIndex, ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
          if eventOf parameter scalar input i tape then 1 else 0) := by
        simp_rw [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : EventIndex, (2 / 2 ^ 128 : ℝ≥0∞) *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
        Finset.sum_le_sum fun i _ => event_bound parameter scalar input i weight
    _ = ((4064 : ℝ≥0∞) * (2 / 2 ^ 128)) *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
        rw [Finset.sum_const, Finset.card_univ, card_eventIndex, nsmul_eq_mul, mul_assoc]
        norm_num
    _ ≤ ENNReal.ofReal coincidenceError *
          ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) := by
        rw [coincidenceError_eq]
        exact mul_le_mul' guess_count_le le_rfl

end Events

end Guess

/-- **`CoincidenceGuess` at the allowance `2^16/2^128`, real.** -/
theorem coincidenceGuess : CoincidenceGuess (ENNReal.ofReal coincidenceError) := by
  intro field group parameter scalar input
  exact @Guess.coincidence_guess_at field group parameter scalar input

/-- **`CoincidenceBound`, real.** -/
theorem coincidenceBound : CoincidenceBound coincidenceError :=
  coincidenceBound_of_guess coincidenceGuess

/-- **The Glue's `publicFirst`, from the two laws and P1k's bounds** (the coincidence guess is
discharged). -/
theorem planB_publicFirst_of_laws_bounds (laws : DesignedLaws) (bounds : DesignedBounds) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError :=
  planB_publicFirst_of_guess laws bounds coincidenceGuess

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
