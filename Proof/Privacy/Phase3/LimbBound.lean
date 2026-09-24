/-
**Phase 3, P1 — the output-limb bound `max_v Pr[o_b = v] ≤ 7/M` of note §2.3 is FALSE.**

**Where it is consumed.** P3's `Glue.abortError` (`Budget.lean`) charges
`q₁ · (3 / (2^128 − q₁) + 7 / preimageFloor)`; the `7 / preimageFloor` term is the note's limb bound,
used for the *output* freshness of `LazyOracle.permutationProgram` in the `H → I^U` hop: the programmed
output `o_b ⊕ E*` must avoid the stage-1 range at its index, charged as `n_i · max_v Pr[o_b = v]`.

**It is false for the middle limb.** The simulator's preimage of `y*` is P3's `idealPreimage y*`:
`n = y*.val + p·m` with `m` uniform below `M(y*) = preimageCount y* + 1`, limbs `n mod 2^128`,
`⌊n/2^128⌋ mod 2^128`, `⌊n/2^256⌋`. For `y* = 0` the middle limb is `0` for the fifteen values
`m = j · d` (`j < 15`), `d = 122790619433043459006028388082740403832` — the first convergent
denominator of `p / 2^256` with `‖d · p / 2^256‖ < 2^-128` — so

```
Pr[o_1 = 0 | y* = 0]  ≥  15 / M(0)  >  7 / preimageFloor          (limbOne_counterexample)
```

(numerically `15` is also the maximum: two hits in one window differ by some `d'` with
`‖d' p / 2^256‖ < 2^-128`, so `d' ≥ d` and at most `⌊(M − 1)/d⌋ + 1 = 15` hits fit; the other two
limbs are at most `⌈M / 2^128⌉ = 6` and `⌈2^256 / p⌉ = 6`. The upper bound `15` is **not** proved in
Lean: it needs the best-approximation property of the continued fraction of `p / 2^256`.)

**It is not needed.** The output collision `o_b ⊕ E* ∈ ran_i` is `E* ∈ ran_i ⊕ o_b`. In `I^U` the
preimage is drawn from `y*` alone, and `y*` is a function of the target rows and of masks the
simulator draws independently of the labels, so `o_b` is independent of `E*` given the view; the
collision is then at most `n_i · max_e Pr[E* = e | view]`, the **same** `ε = 1/(2^128 − q₁)` as the
input check (`Freshness.perQuery_hit_le`). The abort term becomes `2 · q₁ / (2^128 − q₁)`, with no limb
term at all. (Alternatively keep a limb term with `15` in place of `7`, which needs the unproved
upper bound above.)
-/

import Proof.Privacy.Phase3.Basic
import Proof.Privacy.Phase3.Glue.Budget

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 400

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (idealPreimage preimageCount preimageFloor limbs)
open scoped ENNReal

noncomputable section

/-- The first convergent denominator of `p / 2^256` whose multiple of `p` is within `2^128` of a
multiple of `2^256`. -/
def limbPeriod : ℕ := 122790619433043459006028388082740403832

/-- `M(0) = preimageCount 0 + 1`, evaluated. -/
theorem preimageCount_zero : preimageCount (0 : BaseField) + 1
    = 1800144782160100251025577826785925726523 := by
  rw [preimageCount, ZMod.val_zero, baseFieldModulus]
  decide

/-- `preimageFloor`, evaluated: one less than `M(0)`. -/
theorem preimageFloor_eq : preimageFloor = 1800144782160100251025577826785925726522 := by
  rw [preimageFloor, baseFieldModulus]
  decide

/-- The fifteen multiples of `limbPeriod` are preimage indices of `0`. -/
theorem hit_lt (j : Fin 15) : j.val * limbPeriod < preimageCount (0 : BaseField) + 1 := by
  rw [preimageCount_zero, limbPeriod]
  have := j.isLt
  omega

/-- … and each has middle limb `0`. -/
theorem hit_middle (j : Fin 15) :
    (limbs ((0 : BaseField).val + baseFieldModulus * (j.val * limbPeriod))).2.1 = 0 := by
  rw [ZMod.val_zero, Nat.zero_add, limbs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show _ = 0
  revert j
  decide

/-- The middle limb of P3's preimage sampler. -/
def middleLimb (value : BaseField) : PMF Block := (idealPreimage value).map fun triple => triple.2.1

/-- **At `y* = 0` the middle limb is `0` with probability at least `15 / M(0)`.** -/
theorem middleLimb_zero_ge :
    (15 : ℝ≥0∞) * ((preimageCount (0 : BaseField) + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ middleLimb 0 0 := by
  classical
  rw [middleLimb, idealPreimage, PMF.map_comp, uniform_map_apply, Fintype.card_fin]
  refine mul_le_mul_left ?_ _
  let embed : Fin 15 → {m : Fin (preimageCount (0 : BaseField) + 1) //
      ((fun triple : Block × Block × Block => triple.2.1) ∘ fun m : Fin (preimageCount 0 + 1) =>
        limbs ((0 : BaseField).val + baseFieldModulus * m.val)) m = 0} :=
    fun j => ⟨⟨j.val * limbPeriod, hit_lt j⟩, hit_middle j⟩
  have injective : Function.Injective embed := by
    intro first second same
    have values := congrArg (fun m => m.1.val) same
    simp only [embed] at values
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by rw [limbPeriod]; norm_num) values)
  have := Fintype.card_le_of_injective embed injective
  rw [Fintype.card_fin] at this
  exact_mod_cast this

/-- **The note's limb bound is false.** P3's `idealPreimage 0` puts mass strictly above
`7 / preimageFloor` on middle limb `0`. -/
theorem limbOne_counterexample : (7 : ℝ≥0∞) / preimageFloor < middleLimb 0 0 := by
  refine lt_of_lt_of_le ?_ middleLimb_zero_ge
  rw [preimageCount_zero, preimageFloor_eq]
  rw [ENNReal.div_eq_inv_mul, mul_comm (((1800144782160100251025577826785925726522 : ℕ) : ℝ≥0∞)⁻¹)]
  have left : (7 : ℝ≥0∞) * ((1800144782160100251025577826785925726522 : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (7 / 1800144782160100251025577826785925726522) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.div_eq_inv_mul, mul_comm]
    norm_num
  have right : (15 : ℝ≥0∞) * ((1800144782160100251025577826785925726523 : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (15 / 1800144782160100251025577826785925726523) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.div_eq_inv_mul, mul_comm]
    norm_num
  rw [left, right, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end

end Kriterion.ArgoMAC.Security.Phase3
