/-
**`SamplerCutoff`**: the abstract ideal game with the machine's bounded samplers is within
`2^-128` of the one with `idealSamplers`.

Every bounded sampler is abort-close to its exact law (`source_close`, `tail_close`,
`lambda_close`, `preimage_close`); abort-closeness composes along the two kernels of
`planBAbstractSimulator` (`stage2_close`) and the game's abort-or-value binds (`game_close`),
aborts count as `false` on both sides (`advantage_le`), and the total extra abort mass is below
`2^-128` (`cutoffMass_le`).
-/

import Proof.Simulator.CutoffSource
import Proof.Simulator.CutoffTail

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Abort-closeness along the game -/

/-- An `OptionT` bind: the extra abort masses add. -/
theorem AbortClose.optionT_bind {α β : Type} {ε ε' : ENNReal} {first second : OptionT PMF α}
    {next next' : α → OptionT PMF β} (close : AbortClose ε first.run second.run)
    (step : ∀ a, AbortClose ε' (next a).run (next' a).run) :
    AbortClose (ε + ε') (first >>= next).run (second >>= next').run :=
  AbortClose.bind_opt close (fun result => match result with
      | some a => (next a).run
      | none => PMF.pure none)
    (fun result => match result with
      | some a => (next' a).run
      | none => PMF.pure none) rfl rfl step

section Game

variable [FieldCertificate] [GroupCertificate] [DecidableEq PlanB.FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The opening** with bounded samplers is abort-close to the opening with exact ones. -/
theorem opening_close {εt εl εp : ENNReal} (bounded ideal : Samplers)
    (tail : AbortClose εt bounded.tail ideal.tail) (lift : AbortClose εl bounded.lift ideal.lift)
    (preimage : ∀ value, AbortClose εp (bounded.preimage value) (ideal.preimage value))
    (table : PlanB.Public) (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    AbortClose (εt + (εl + ((digitCount * 3 : Nat) * εp + 0)))
      (opening bounded table input labels target oracle)
      (opening ideal table input labels target oracle) := by
  unfold opening
  refine AbortClose.bind_common _ _ _ fun ran => ?_
  refine AbortClose.bind_opt tail _ _ rfl rfl fun tailValue => ?_
  refine AbortClose.bind_opt lift _ _ rfl rfl fun liftValue => ?_
  refine AbortClose.bind_opt ?_ _ _ rfl rfl fun blocks => AbortClose.refl _
  unfold preimages
  exact (AbortClose.optionProduct _ _ _ fun index => preimage _).map_opt _ rfl

/-- **Stage 2** with bounded samplers is abort-close to stage 2 with exact ones. -/
theorem stage2_close {εt εl εp : ENNReal} (bounded ideal : Samplers)
    (tail : AbortClose εt bounded.tail ideal.tail) (lift : AbortClose εl bounded.lift ideal.lift)
    (preimage : ∀ value, AbortClose εp (bounded.preimage value) (ideal.preimage value))
    (source : Stage1Source) (input : AffineInput) (output : Option Point)
    (oracle : LazyOracle.State PlanB.FixedIndex EncPRF.PermutationIndex) :
    AbortClose (εt + (εl + ((digitCount * 3 : Nat) * εp + 0)))
      ((planBAbstractSimulator bounded).stage2 source input output oracle)
      ((planBAbstractSimulator ideal).stage2 source input output oracle) := by
  cases output with
  | none => exact (AbortClose.refl _).mono zero_le
  | some target =>
      exact (opening_close bounded ideal tail lift preimage _ _ _ _ _).map_opt _ rfl

/-- **The game**: bounded samplers against exact ones. -/
theorem game_close {εs εt εl εp : ENNReal} (bounded ideal : Samplers)
    (source : AbortClose εs bounded.source ideal.source)
    (tail : AbortClose εt bounded.tail ideal.tail) (lift : AbortClose εl bounded.lift ideal.lift)
    (preimage : ∀ value, AbortClose εp (bounded.preimage value) (ideal.preimage value))
    (finite : εs + (εt + (εl + ((digitCount * 3 : Nat) * εp + 0))) ≠ ⊤)
    (adversary : PlanBAdversary Unit) (parameter : Nat) (scalar : NonZeroScalar) :
    Assumptions.advantage (planBIdealGame ideal adversary parameter scalar ())
      (planBIdealGame bounded adversary parameter scalar ()) ≤
        (εs + (εt + (εl + ((digitCount * 3 : Nat) * εp + 0)))).toReal := by
  unfold planBIdealGame abstractIdealGame
  refine advantage_le ?_ finite
  have total : εs + (εt + (εl + ((digitCount * 3 : Nat) * εp + 0))) =
      εs + (0 + ((εt + (εl + ((digitCount * 3 : Nat) * εp + 0))) + (0 + 0))) := by
    simp only [zero_add, add_zero]
  rw [total]
  refine AbortClose.optionT_bind ((source.map_opt _ rfl)) fun first => ?_
  rcases first with ⟨circuit, state, oracle⟩
  refine AbortClose.optionT_bind (AbortClose.refl _) fun second => ?_
  rcases second with ⟨selected, chosen⟩
  refine AbortClose.optionT_bind (stage2_close bounded ideal tail lift preimage _ _ _ _)
    fun third => ?_
  rcases third with ⟨labels, updated⟩
  refine AbortClose.optionT_bind (AbortClose.refl _) fun fourth => ?_
  rcases fourth with ⟨decision, final⟩
  exact AbortClose.refl _

end Game

end

end Kriterion.ArgoMAC.PlanB.SimMachine
