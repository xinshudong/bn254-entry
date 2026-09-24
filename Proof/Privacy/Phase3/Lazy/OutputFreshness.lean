/-
**Phase 3, P4 — output freshness of a programmed Davies–Meyer block.**

P3's `Glue.OutputFreshness` (`Glue/Budget.lean`): a programmed output `limb xor label`, with the
limb drawn independently of the label and the label's point masses at most `ε`, lands in a fixed
set of `n` blocks with mass at most `n·ε`.

* `xor_apply_le` — the whole fact is a point-mass bound: `Pr[limb xor label = y] ≤ ε` for every
  `y`, because `label ↦ y xor label` is a bijection of `Block`, so the limb law is only reindexed;
* `outputFreshness : Glue.OutputFreshness` — P3's statement, verbatim;
* `conditional_xor_apply_le` / `conditionalOutputFreshness` — the same without independence: for
  any joint law of `(label, limb)` in which the label's point masses **given the limb** are at
  most `ε` (`joint (label, limb) ≤ ε · Pr[limb]`), the collision mass is still `≤ n·ε`. This is
  the form to use if the limb law is not literally independent of the label (the product form is
  the special case `joint = label ⊗ limb`, `product_conditional_bound`).
-/

import Proof.Privacy.Phase3.Glue.Budget

namespace Kriterion.ArgoMAC.Phase3.Lazy

open Cryptography
open scoped ENNReal

noncomputable section

/-- XOR by a fixed block, as a bijection of `Block`. -/
def xorEquiv (mask : Block) : Block ≃ Block where
  toFun value := value ^^^ mask
  invFun value := value ^^^ mask
  left_inv value := by simp [BitVec.xor_assoc]
  right_inv value := by simp [BitVec.xor_assoc]

/-- One point of an XOR-shifted law is one point of the law. -/
theorem map_xor_apply (law : PMF Block) (mask target : Block) :
    (law.map fun value => value ^^^ mask) target = law (target ^^^ mask) := by
  have image : (fun value : Block => value ^^^ mask) = xorEquiv mask := rfl
  rw [image, PMF.map_apply]
  rw [tsum_eq_single (target ^^^ mask)]
  · simp [xorEquiv, BitVec.xor_assoc]
  · intro other miss
    refine if_neg fun same => miss ?_
    rw [same]
    simp [xorEquiv, BitVec.xor_assoc]

/-- Reindexing a sum of a law by `label ↦ target xor label` does not change it. -/
theorem tsum_xor (law : PMF Block) (target : Block) :
    (∑' label : Block, law (target ^^^ label)) = 1 := by
  have reindex := (Equiv.tsum_eq (xorEquiv target) (fun value : Block => law value))
  have shape : (fun label : Block => law (target ^^^ label)) =
      fun label => law ((xorEquiv target) label) := by
    funext label
    simp [xorEquiv, BitVec.xor_comm]
  rw [shape, reindex, law.tsum_coe]

/-- **The point-mass bound.** A limb XOR an independent label whose point masses are at most `ε`
has point masses at most `ε`. -/
theorem xor_apply_le (labelLaw limbLaw : PMF Block) (ε : ℝ≥0∞)
    (bound : ∀ label, labelLaw label ≤ ε) (target : Block) :
    (labelLaw.bind fun label => limbLaw.map fun limb => limb ^^^ label) target ≤ ε := by
  rw [PMF.bind_apply]
  simp only [map_xor_apply]
  calc (∑' label, labelLaw label * limbLaw (target ^^^ label))
      ≤ ∑' label, ε * limbLaw (target ^^^ label) :=
        ENNReal.tsum_le_tsum fun label => mul_le_mul_left (bound label) _
    _ = ε * ∑' label, limbLaw (target ^^^ label) := ENNReal.tsum_mul_left
    _ = ε := by rw [tsum_xor, mul_one]

/-- A finite set of targets, each of mass at most `ε`, has mass at most `n·ε`. -/
theorem toOuterMeasure_finset_le {A : Type} (law : PMF A) (targets : Finset A) (ε : ℝ≥0∞)
    (bound : ∀ target, law target ≤ ε) :
    law.toOuterMeasure (targets : Set A) ≤ (targets.card : ℝ≥0∞) * ε := by
  classical
  rw [PMF.toOuterMeasure_apply_finset]
  calc (∑ target ∈ targets, law target) ≤ ∑ _target ∈ targets, ε :=
        Finset.sum_le_sum fun target _ => bound target
    _ = (targets.card : ℝ≥0∞) * ε := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **`Glue.OutputFreshness`** (P3's statement, verbatim): the programmed output `limb xor label`,
with the limb independent of the label and the label's point masses at most `ε`, lands in a
stage-1 range of `n` blocks with mass at most `n·ε`. -/
theorem outputFreshness : Kriterion.ArgoMAC.Phase3.Glue.OutputFreshness := by
  intro labelLaw limbLaw range ε bound
  exact toOuterMeasure_finset_le _ range ε (xor_apply_le labelLaw limbLaw ε bound)

/-! ### Without independence: the conditional form -/

/-- `limb xor (target xor limb) = target`. -/
theorem xor_cancel (target limb : Block) : limb ^^^ (target ^^^ limb) = target := by
  rw [BitVec.xor_comm limb, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **The point-mass bound, conditionally.** If, jointly, the label's point masses given the limb
are at most `ε` (`joint (label, limb) ≤ ε · Pr[limb]`), then `limb xor label` has point masses at
most `ε`. -/
theorem conditional_xor_apply_le (joint : PMF (Block × Block)) (ε : ℝ≥0∞)
    (bound : ∀ label limb, joint (label, limb) ≤ ε * (joint.map Prod.snd) limb)
    (target : Block) :
    (joint.map fun pair => pair.2 ^^^ pair.1) target ≤ ε := by
  classical
  have fibre : (joint.map fun pair => pair.2 ^^^ pair.1) target =
      ∑' limb : Block, joint (target ^^^ limb, limb) := by
    rw [PMF.map_apply, ENNReal.tsum_prod', ENNReal.tsum_comm]
    refine tsum_congr fun limb => ?_
    rw [tsum_eq_single (target ^^^ limb)]
    · rw [if_pos (xor_cancel target limb).symm]
    · intro label miss
      refine if_neg fun same => miss ?_
      rw [same, BitVec.xor_comm limb label, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [fibre]
  calc (∑' limb, joint (target ^^^ limb, limb))
      ≤ ∑' limb, ε * (joint.map Prod.snd) limb :=
        ENNReal.tsum_le_tsum fun limb => bound _ _
    _ = ε * ∑' limb, (joint.map Prod.snd) limb := ENNReal.tsum_mul_left
    _ = ε := by rw [PMF.tsum_coe, mul_one]

/-- **Output freshness, conditionally**: the collision mass with a fixed range of `n` blocks is at
most `n·ε` whenever the label's conditional point masses given the limb are at most `ε`. -/
theorem conditionalOutputFreshness (joint : PMF (Block × Block)) (range : Finset Block)
    (ε : ℝ≥0∞) (bound : ∀ label limb, joint (label, limb) ≤ ε * (joint.map Prod.snd) limb) :
    (joint.map fun pair => pair.2 ^^^ pair.1).toOuterMeasure (range : Set Block) ≤
      (range.card : ℝ≥0∞) * ε :=
  toOuterMeasure_finset_le _ range ε (conditional_xor_apply_le joint ε bound)

/-- The product law of an independent pair meets the conditional hypothesis, so
`conditionalOutputFreshness` contains `outputFreshness`. -/
theorem product_conditional_bound (labelLaw limbLaw : PMF Block) (ε : ℝ≥0∞)
    (bound : ∀ label, labelLaw label ≤ ε) (label limb : Block) :
    (labelLaw.bind fun label => limbLaw.map fun limb => (label, limb)) (label, limb) ≤
      ε * ((labelLaw.bind fun label => limbLaw.map fun limb => (label, limb)).map Prod.snd)
        limb := by
  classical
  have marginal : ((labelLaw.bind fun label => limbLaw.map fun limb => (label, limb)).map
      Prod.snd) = limbLaw := by
    rw [PMF.map_bind]
    have inner : ∀ label : Block,
        (limbLaw.map fun limb => (label, limb)).map Prod.snd = limbLaw :=
      fun label => (PMF.map_comp _ _ _).trans (PMF.map_id limbLaw)
    simp only [inner]
    exact PMF.bind_const _ _
  rw [marginal, PMF.bind_apply, tsum_eq_single label]
  · rw [PMF.map_apply, tsum_eq_single limb]
    · rw [if_pos rfl]
      exact mul_le_mul_left (bound label) _
    · intro other miss
      exact if_neg fun same => miss (congrArg Prod.snd same).symm
  · intro other miss
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun value => ?_)
    exact if_neg fun same => miss (congrArg Prod.fst same).symm

/-! ### Independence is load-bearing (counter-shape)

`outputFreshness` bounds the collision by the label's **marginal** point masses only because the
limb is independent of the label. If the limb is a function of the label -- for instance a
cached lazy answer read at an input correlated with the label -- the marginal bound says nothing:
with `limb = label` and a uniform label (point masses `2^-128`), `limb xor label = 0` always. -/

/-- **Counter-shape.** A joint law whose label marginal has point masses `≤ 2^-128` but whose
`limb xor label` hits the one-block range `{0}` with mass `1 > 1 · 2^-128`. -/
theorem outputFreshness_needs_independence :
    ∃ (joint : PMF (Block × Block)) (ε : ℝ≥0∞), (∀ label, (joint.map Prod.fst) label ≤ ε) ∧
      ¬ ((joint.map fun pair => pair.2 ^^^ pair.1).toOuterMeasure ((({0} : Finset Block)) : Set Block) ≤
        ((({0} : Finset Block)).card : ℝ≥0∞) * ε) := by
  classical
  refine ⟨(PMF.uniformOfFintype Block).map fun label => (label, label), (2 ^ 128 : ℝ≥0∞)⁻¹, ?_, ?_⟩
  · intro label
    rw [PMF.map_comp]
    have identity : (Prod.fst ∘ fun label : Block => (label, label)) = id := rfl
    have card : Fintype.card Block = 2 ^ 128 :=
      (Fintype.card_congr (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ :
        Block ≃ Fin (2 ^ 128))).trans (Fintype.card_fin _)
    rw [identity, PMF.map_id, PMF.uniformOfFintype_apply, card, Nat.cast_pow, Nat.cast_ofNat]
  · rw [PMF.map_comp]
    have zero : ((fun pair : Block × Block => pair.2 ^^^ pair.1) ∘ fun label : Block =>
        (label, label)) = fun _ => 0 := by
      funext label
      simp
    have constant : (PMF.uniformOfFintype Block).map (fun _ => (0 : Block)) = PMF.pure 0 :=
      PMF.map_const _ _
    rw [zero, constant, Finset.coe_singleton, PMF.toOuterMeasure_pure_apply,
      if_pos (Set.mem_singleton _), Finset.card_singleton, Nat.cast_one, one_mul]
    exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))

end

end Kriterion.ArgoMAC.Phase3.Lazy
