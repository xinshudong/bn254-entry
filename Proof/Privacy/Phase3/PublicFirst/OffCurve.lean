/-
**Phase 3, P1g — `ShadowObligation` is FALSE: the off-curve system-A masks.**

`G1U` (`hiddenDeletedHybrid`) runs on `G0U`'s tape, on which **every** garbler scale mask of
**every** lane — system A's curve lanes included — is swapped to uniform `F_p`
(`GameSwap.garblerKeys`, `MaskSwap.swappedTape_garblerMasks`), and it installs the garbler's
entries that the evaluator's reach asks (`visibleEntries`). The reach is `Programs.onCurveM`
**whatever the input** (`reachTranscript` does not check curve membership), so at an
**off-curve** input the inactive system-A scale entries are installed with their swapped values:
an adversary that evaluates system A itself reads a uniform `F_p` mask.

`HW` (`publicFirstHybrid`) at an off-curve input makes **no** oracle call
(`openedSimulator`'s stage 2 on `none`, `hw_offCurve_stage2`): the adversary's own system-A
queries are fresh lazy answers, and its mask is `sampleFp` of three uniform blocks — Rule S's
biased law.

The distinguisher "is the mask below `R = 2^384 mod p`?" separates the two laws
(`offCurve_counterShape`): the advantage is exactly `R(p−R)/(p·2^384) ≈ 2^-134.04`, far above
the `G1U → HW` allowance at `q₁ = 0`, `stageOneHitError 0 + exceptionalError = 182/(r−1) ≈
2^-246.09` (`offCurve_counterShape_exceeds`). So no middle game below both `G1U` and `HW` has flag
mass within the allowance (`FlagMono` and `Below` bound the advantage by the flag mass,
`coreUntilBad_of_overlap`): `ShadowObligation` and the Glue's `publicFirst` at the constant
`4q₁/2^128 + 182/(r−1)` are false.

**The honest constant moves**: `G1U → HW` must also carry the swap of the visible system-A masks
off the curve, at most `1905·δ₃` (`127` chunks, `3` inactive switches, `3 + 2` curve elements;
the adversary sees no other swapped mask it can locate), which `maskSwapError = N·δ₃` dominates.
-/

import Proof.Privacy.Phase3.GameSwap

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (stageOneHitError exceptionalError)
open scoped ENNReal

noncomputable section

/-! ### 1. Counting -/

/-- **The numbers below `M·p + R` whose residue is below `R ≤ p`**: `(M + 1)·R` of them. -/
theorem card_filter_mod_lt (p M R : ℕ) (hp : 0 < p) (hR : R ≤ p) :
    ((Finset.range (M * p + R)).filter fun n => n % p < R).card = (M + 1) * R := by
  have target : (Finset.range (M + 1) ×ˢ Finset.range R).card = (M + 1) * R := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  rw [← target]
  refine Finset.card_nbij' (fun n => (n / p, n % p)) (fun kj => kj.1 * p + kj.2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    refine ⟨?_, hn.2⟩
    rw [Nat.div_lt_iff_lt_mul hp]
    calc n < M * p + R := hn.1
      _ ≤ M * p + p := by omega
      _ = (M + 1) * p := by ring
  · intro kj hkj
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hkj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    have hlt : kj.2 < p := lt_of_lt_of_le hkj.2 hR
    have low : kj.1 * p ≤ M * p := Nat.mul_le_mul_right _ (by omega)
    refine ⟨by omega, ?_⟩
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    exact hkj.2
  · intro n _
    exact Nat.div_add_mod' n p
  · intro kj hkj
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hkj
    have hlt : kj.2 < p := lt_of_lt_of_le hkj.2 hR
    refine Prod.ext ?_ ?_
    · show (kj.1 * p + kj.2) / p = kj.1
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hlt, zero_add]
    · show (kj.1 * p + kj.2) % p = kj.2
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- The three limbs of a block triple read back. -/
theorem natToBlocks_blocksToNat (blocks : Block × Block × Block) :
    natToBlocks (blocksToNat blocks.1 blocks.2.1 blocks.2.2) = blocks := by
  obtain ⟨a, b, c⟩ := blocks
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [natToBlocks, blocksToNat]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat] <;> omega

theorem blocksToNat_lt (blocks : Block × Block × Block) :
    blocksToNat blocks.1 blocks.2.1 blocks.2.2 < 2 ^ 384 := by
  obtain ⟨a, b, c⟩ := blocks
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [blocksToNat]
  omega

/-- The probability of an event under a uniform law, as a count. -/
theorem uniform_map_true {α : Type} [Fintype α] [Nonempty α] (f : α → Bool) :
    ((PMF.uniformOfFintype α).map f) true
      = ((Finset.univ.filter fun a => f a = true).card : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  have flip : ∀ a, (if true = f a then (Fintype.card α : ℝ≥0∞)⁻¹ else 0)
      = if f a = true then (Fintype.card α : ℝ≥0∞)⁻¹ else 0 := by
    intro a
    by_cases hit : f a = true <;> simp [hit]
  simp only [flip]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-! ### 2. The two laws of one mask -/

/-- `R = 2^384 mod p`. -/
abbrev residue : ℕ := reductionResidue

/-- `M = ⌊2^384 / p⌋`. -/
abbrev quotient : ℕ := 2 ^ 384 / baseFieldModulus

theorem quotient_mul_add : quotient * baseFieldModulus + residue = 2 ^ 384 := by
  unfold quotient residue reductionResidue
  exact Nat.div_add_mod' _ _

theorem residue_lt : residue < baseFieldModulus := by
  unfold residue reductionResidue
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))

/-- **The distinguisher**: is the mask below `R`? -/
def lowMask (value : BaseField) : Bool := decide (value.val < residue)

/-- `G1U`'s law of an off-curve system-A mask: uniform on `F_p`. -/
def swappedMaskLaw : PMF BaseField := PMF.uniformOfFintype BaseField

/-- `HW`'s law of the same mask: `sampleFp` of three fresh uniform blocks. -/
def lazyMaskLaw : PMF BaseField :=
  (PMF.uniformOfFintype (Block × Block × Block)).map fun blocks =>
    sampleFp blocks.1 blocks.2.1 blocks.2.2

theorem card_low_field :
    (Finset.univ.filter fun value : BaseField => lowMask value = true).card = residue := by
  have target : (Finset.range residue).card = residue := Finset.card_range _
  rw [← target]
  refine Finset.card_nbij' (fun value : BaseField => value.val) (fun n => (n : BaseField))
    ?_ ?_ ?_ ?_
  · intro value hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, lowMask,
      decide_eq_true_eq] at hv
    simpa using hv
  · intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, lowMask,
      decide_eq_true_eq]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hn residue_lt)]
    exact hn
  · intro value _
    exact ZMod.natCast_zmod_val value
  · intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    show ((n : BaseField)).val = n
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hn residue_lt)]

set_option linter.constructorNameAsVariable false in
theorem card_low_blocks :
    (Finset.univ.filter fun blocks : Block × Block × Block =>
        lowMask (sampleFp blocks.1 blocks.2.1 blocks.2.2) = true).card
      = (quotient + 1) * residue := by
  have hp : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [← card_filter_mod_lt baseFieldModulus quotient residue hp residue_lt.le, quotient_mul_add]
  refine Finset.card_nbij' (fun blocks => blocksToNat blocks.1 blocks.2.1 blocks.2.2)
    natToBlocks ?_ ?_ ?_ ?_
  · intro blocks hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, lowMask,
      decide_eq_true_eq, sampleFp, ZMod.val_natCast] at hb
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨blocksToNat_lt blocks, hb⟩
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, lowMask,
      decide_eq_true_eq]
    rw [sampleFp_natToBlocks n hn.1, ZMod.val_natCast]
    exact hn.2
  · intro blocks _
    exact natToBlocks_blocksToNat blocks
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    exact blocksToNat_natToBlocks n hn.1

/-- **`G1U`'s side**: the swapped mask is low with mass `R/p`. -/
theorem swapped_low : (swappedMaskLaw.map lowMask) true
    = (residue : ℝ≥0∞) / baseFieldModulus := by
  rw [swappedMaskLaw, uniform_map_true, card_low_field, ZMod.card]

/-- **`HW`'s side**: the lazy mask is low with mass `R(M+1)/2^384`. -/
theorem lazy_low : (lazyMaskLaw.map lowMask) true
    = ((quotient + 1) * residue : ℕ) / 2 ^ 384 := by
  rw [lazyMaskLaw, PMF.map_comp, uniform_map_true]
  simp only [Function.comp_def]
  rw [card_low_blocks, card_blockTriple]
  push_cast
  rfl

/-! ### 3. The advantage, and the allowance -/

/-- **The off-curve counter-shape**: the two mask laws are at advantage exactly
`R(p−R)/(p·2^384)` against the low-mask test. -/
theorem offCurve_counterShape :
    Assumptions.advantage (swappedMaskLaw.map lowMask) (lazyMaskLaw.map lowMask)
      = (residue : ℝ) * (baseFieldModulus - residue) / (baseFieldModulus * 2 ^ 384) := by
  unfold Assumptions.advantage
  rw [swapped_low, lazy_low]
  have hp : (0 : ℝ) < baseFieldModulus := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
  have split : ((quotient : ℝ) * baseFieldModulus + residue) = 2 ^ 384 := by
    exact_mod_cast quotient_mul_add
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  push_cast
  have below : (residue : ℝ) < baseFieldModulus := by exact_mod_cast residue_lt
  have positive : (0 : ℝ) < (quotient : ℝ) * baseFieldModulus + residue := by
    rw [split]; positivity
  rw [← split]
  set p : ℝ := (baseFieldModulus : ℝ)
  set R : ℝ := (residue : ℝ)
  set M : ℝ := (quotient : ℝ)
  have rNonneg : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  rw [div_sub_div _ _ hp.ne' positive.ne', abs_div, abs_of_pos (mul_pos hp positive)]
  congr 1
  have expand : R * (M * p + R) - p * ((M + 1) * R) = -(R * (p - R)) := by ring
  rw [expand, abs_neg, abs_of_nonneg (mul_nonneg rNonneg (by linarith))]

/-- `182·p·2^384 < R·(p−R)·(r−1)`, in `ℕ`. -/
theorem allowance_lt_nat :
    182 * baseFieldModulus * 2 ^ 384
      < residue * (baseFieldModulus - residue) * (scalarFieldModulus - 1) := by
  rw [residue, reductionResidue_eq]
  unfold baseFieldModulus scalarFieldModulus
  decide

/-- **The counter-shape exceeds `G1U → HW`'s allowance at `q₁ = 0`**:
`R(p−R)/(p·2^384) ≈ 2^-134.04 > 182/(r−1) ≈ 2^-246.09`. -/
theorem offCurve_counterShape_exceeds :
    stageOneHitError 0 + exceptionalError
      < Assumptions.advantage (swappedMaskLaw.map lowMask) (lazyMaskLaw.map lowMask) := by
  rw [offCurve_counterShape]
  unfold stageOneHitError exceptionalError
  simp only [Nat.cast_zero, mul_zero, zero_div, zero_add]
  have hp : (0 : ℝ) < baseFieldModulus := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
  have hr : (1 : ℝ) < scalarFieldModulus := by
    unfold scalarFieldModulus; norm_num
  have below : residue ≤ baseFieldModulus := residue_lt.le
  have rOne : 1 ≤ scalarFieldModulus := by unfold scalarFieldModulus; norm_num
  have natBound := allowance_lt_nat
  have realBound : (182 : ℝ) * baseFieldModulus * 2 ^ 384
      < residue * ((baseFieldModulus : ℝ) - residue) * ((scalarFieldModulus : ℝ) - 1) := by
    have cast := (Nat.cast_lt (α := ℝ)).mpr natBound
    push_cast [Nat.cast_sub below, Nat.cast_sub rOne] at cast
    exact cast
  rw [div_lt_div_iff₀ (by linarith) (mul_pos hp (by positivity))]
  nlinarith [realBound]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
