/-
**Phase 3, P1f — `StageOneGuess`, from the bridge-key guess.**

A stage-1 touch of the garbler's non-EncPRF entries is an input or output hit at one fixed-key
index (`stageOne_touch`), each at most `2^-128` given the stage-1 view (`inputHit_le`,
`outputHit_le`), or a hash query at the bridge key `t`. So `StageOneGuess (3/2^128 + 1/(p−1))`
follows from one statement about `t` alone, `StageOneBridgeGuess`: given the stage-1 view, `t`
hits a given key with conditional mass at most `1/p` (`stageOneGuess_of_bridge`).
-/

import Proof.Privacy.Phase3.Hidden.StageOneFixed

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- **The stage-1 bridge-key guess**: given the stage-1 view, the bridge key `t` equals a given key
with conditional mass at most `1/p`. -/
def StageOneBridgeGuess : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (key : BaseField),
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ tape.1.bridgeKey = key} ≤
      (baseFieldModulus : ℝ≥0∞)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view}

theorem two_block_le_charge : 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ ENNReal.ofReal hiddenCharge := by
  have real : (2 : ℝ) / 2 ^ 128 ≤ hiddenCharge := by
    unfold hiddenCharge baseFieldModulus
    norm_num
  calc 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ = ENNReal.ofReal (2 / 2 ^ 128) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal hiddenCharge := ENNReal.ofReal_le_ofReal real

theorem field_le_charge : (baseFieldModulus : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal hiddenCharge := by
  have real : 1 / (baseFieldModulus : ℝ) ≤ hiddenCharge := by
    unfold hiddenCharge baseFieldModulus
    norm_num
  calc (baseFieldModulus : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (baseFieldModulus : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by unfold baseFieldModulus; positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_natCast, one_div]
    _ ≤ ENNReal.ofReal hiddenCharge := ENNReal.ofReal_le_ofReal real

/-- **`StageOneGuess` at `L1`'s constant, from the bridge-key guess.** -/
theorem stageOneGuess_of_bridge (bridge : StageOneBridgeGuess) :
    StageOneGuess (ENNReal.ofReal hiddenCharge) := by
  intro field group fixedFintype encFintype fixedEq encEq parameter scalar view entry
  let μ := swappedChallengeTape
  let V := {tape : Coins × Oracle | stageOneView parameter scalar tape = view}
  have twoHits : ∀ (index : FixedIndex) (x y : Block),
      μ.toOuterMeasure {tape | tape ∈ V ∧ (InputHit scalar index x tape ∨ OutputHit scalar index y tape)} ≤
        ENNReal.ofReal hiddenCharge * μ.toOuterMeasure V := by
    intro index x y
    refine le_trans (outer_and_or_le μ V {tape | InputHit scalar index x tape}
      {tape | OutputHit scalar index y tape}) ?_
    refine le_trans (add_le_add (inputHit_le parameter scalar view index x)
      (outputHit_le parameter scalar view index y)) ?_
    rw [← add_mul, ← two_mul]
    exact mul_le_mul' two_block_le_charge le_rfl
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (InputHit scalar index x tape ∨ OutputHit scalar index answer tape)})
        fun tape member =>
          ⟨member.1, stageOne_touch scalar tape ⟨.fixedForward index x, answer⟩ member.2⟩) ?_
      exact twoHits index x answer
  | fixedInverse index y =>
      refine le_trans (outer_mono_event μ
        (T := {tape | tape ∈ V ∧ (InputHit scalar index answer tape ∨ OutputHit scalar index y tape)})
        fun tape member =>
          ⟨member.1, (stageOne_touch scalar tape ⟨.fixedInverse index y, answer⟩ member.2).symm⟩)
        (twoHits index answer y)
  | encForward index x =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageOne_touch scalar tape ⟨.encForward index x, answer⟩ member.2).elim) ?_
      simp
  | encInverse index y =>
      refine le_trans (outer_mono_event μ (T := ∅) fun tape member =>
        (stageOne_touch scalar tape ⟨.encInverse index y, answer⟩ member.2).elim) ?_
      simp
  | hash key =>
      refine le_trans (outer_mono_event μ
        (T := {tape | stageOneView parameter scalar tape = view ∧ tape.1.bridgeKey = key})
        fun tape member => ⟨member.1,
          (stageOne_touch scalar tape ⟨.hash key, answer⟩ member.2).symm⟩) ?_
      exact le_trans (bridge parameter scalar view key) (mul_le_mul' field_le_charge le_rfl)

end

end Kriterion.ArgoMAC.Security.Phase3
