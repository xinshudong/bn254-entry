/-
**Phase 3, P1h — generic: the swap kernel is a product over any split of its sites.**

For a predicate `p` on the mask sites, the site permutations split into those off `p` and those
on `p` (`splitPerms`), the masks likewise (`splitMasks`), and `maskMap` respects the split. Then
(`swapKernel_split`)

```
(swapKernel point).map (splitPerms p) = productPMF (swapKernel point_{¬p}) (swapKernel point_p),
```

the two halves are independent swap kernels at the restricted points. It rests on two facts about
fibre laws: they move along equivalences (`fibreLaw_map_equiv'`) and the fibre law of a product map
is the product of the fibre laws (`fibreLaw_prod`).
-/

import Proof.Privacy.Phase3.MaskSwap

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ### Fibre laws -/

/-- **A fibre law moves along equivalences.** -/
theorem fibreLaw_map_equiv' {A A' B B' : Type} [Fintype A] [Fintype A'] [DecidableEq B] [DecidableEq B']
    (g : A → B) (g' : A' → B') (onto : Function.Surjective g) (onto' : Function.Surjective g')
    (eA : A ≃ A') (eB : B ≃ B') (compat : ∀ a, g' (eA a) = eB (g a)) (b : B) :
    (fibreLaw g onto b).map eA = fibreLaw g' onto' (eB b) := by
  classical
  have cards : Fintype.card {y : A // g y = b} = Fintype.card {y : A' // g' y = eB b} :=
    Fintype.card_congr
      { toFun := fun y => ⟨eA y.1, by rw [compat, y.2]⟩
        invFun := fun y => ⟨eA.symm y.1, by
          apply eB.injective
          rw [← compat, Equiv.apply_symm_apply]
          exact y.2⟩
        left_inv := fun y => Subtype.ext (eA.symm_apply_apply y.1)
        right_inv := fun y => Subtype.ext (eA.apply_symm_apply y.1) }
  refine PMF.ext fun x => ?_
  rw [PMF.map_apply, tsum_eq_single (eA.symm x)]
  · rw [if_pos (eA.apply_symm_apply x).symm, fibreLaw_apply, fibreLaw_apply, cards]
    have iff : g (eA.symm x) = b ↔ g' x = eB b := by
      constructor
      · intro h
        rw [← Equiv.apply_symm_apply eA x, compat, h]
      · intro h
        apply eB.injective
        rw [← compat, Equiv.apply_symm_apply]
        exact h
    by_cases h : g' x = eB b
    · rw [if_pos (iff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (iff.mp h')), if_neg h]
  · intro other miss
    rw [if_neg (fun same => miss (by rw [same, Equiv.symm_apply_apply]))]

/-- **The fibre law of a product map is the product of the fibre laws.** -/
theorem fibreLaw_prod {A₁ A₂ B₁ B₂ : Type} [Fintype A₁] [Fintype A₂] [DecidableEq B₁] [DecidableEq B₂]
    (g₁ : A₁ → B₁) (g₂ : A₂ → B₂) (onto₁ : Function.Surjective g₁) (onto₂ : Function.Surjective g₂)
    (onto : Function.Surjective (Prod.map g₁ g₂)) (b₁ : B₁) (b₂ : B₂) :
    fibreLaw (Prod.map g₁ g₂) onto (b₁, b₂) = productPMF (fibreLaw g₁ onto₁ b₁) (fibreLaw g₂ onto₂ b₂) := by
  classical
  have cards : Fintype.card {y : A₁ × A₂ // Prod.map g₁ g₂ y = (b₁, b₂)} =
      Fintype.card {y : A₁ // g₁ y = b₁} * Fintype.card {y : A₂ // g₂ y = b₂} := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr
      { toFun := fun y => (⟨y.1.1, (Prod.mk.inj y.2).1⟩, ⟨y.1.2, (Prod.mk.inj y.2).2⟩)
        invFun := fun y => ⟨(y.1.1, y.2.1), by rw [Prod.map_apply, y.1.2, y.2.2]⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  refine PMF.ext fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  rw [productPMF_apply, fibreLaw_apply, fibreLaw_apply, fibreLaw_apply, cards]
  simp only [Prod.map_apply, Prod.mk.injEq]
  by_cases h₁ : g₁ x₁ = b₁ <;> by_cases h₂ : g₂ x₂ = b₂ <;>
    simp only [h₁, h₂, and_self, and_false, false_and, if_true, if_false, mul_zero, zero_mul]
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Independent binds. -/
theorem productPMF_bind {A₁ A₂ B₁ B₂ : Type} (μ₁ : PMF B₁) (μ₂ : PMF B₂) (κ₁ : B₁ → PMF A₁)
    (κ₂ : B₂ → PMF A₂) :
    (productPMF μ₁ μ₂).bind (fun b => productPMF (κ₁ b.1) (κ₂ b.2)) =
      productPMF (μ₁.bind κ₁) (μ₂.bind κ₂) := by
  unfold productPMF
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.map_bind]
  refine congrArg (PMF.bind μ₁) (funext fun b₁ => ?_)
  rw [PMF.bind_comm]

/-! ### Splitting the sites -/

section Split

variable {M : Type} [Fintype M] [DecidableEq M] (p : M → Prop) [DecidablePred p]

/-- The sites off `p` and on `p`. -/
abbrev SiteOff := {m : M // ¬ p m}
abbrev SiteOn := {m : M // p m}

/-- The points restricted to a set of sites. -/
def restrictPoint (q : M → Prop) (point : M × Fin 3 → Block) : {m : M // q m} × Fin 3 → Block :=
  fun site => point (site.1.1, site.2)

/-- **The site permutations, split.** -/
def splitPerms : SitePerms M ≃ SitePerms (SiteOff p) × SitePerms (SiteOn p) where
  toFun f := (fun site => f (site.1.1, site.2), fun site => f (site.1.1, site.2))
  invFun g := fun site => if h : p site.1 then g.2 (⟨site.1, h⟩, site.2) else g.1 (⟨site.1, h⟩, site.2)
  left_inv f := funext fun site => by by_cases h : p site.1 <;> simp [h]
  right_inv g := by
    refine Prod.ext (funext fun site => ?_) (funext fun site => ?_)
    · simp [site.1.2]
    · simp [site.1.2]

/-- **The masks, split.** -/
def splitMasks : (M → BaseField) ≃ (SiteOff p → BaseField) × (SiteOn p → BaseField) where
  toFun f := (fun m => f m.1, fun m => f m.1)
  invFun g := fun m => if h : p m then g.2 ⟨m, h⟩ else g.1 ⟨m, h⟩
  left_inv f := funext fun m => by by_cases h : p m <;> simp [h]
  right_inv g := by
    refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
    · simp [m.2]
    · simp [m.2]

/-- `maskMap` respects the split. -/
theorem maskMap_split (point : M × Fin 3 → Block) (f : SitePerms M) :
    splitMasks p (maskMap point f) =
      Prod.map (maskMap (restrictPoint (fun m => ¬ p m) point)) (maskMap (restrictPoint p point))
        (splitPerms p f) := rfl

/-- **The swap kernel is a product over the split.** -/
theorem swapKernel_split (point : M × Fin 3 → Block) :
    (swapKernel point).map (splitPerms p) =
      productPMF (swapKernel (restrictPoint (fun m => ¬ p m) point)) (swapKernel (restrictPoint p point)) := by
  classical
  have onto : Function.Surjective (Prod.map (maskMap (restrictPoint (fun m => ¬ p m) point))
      (maskMap (restrictPoint p point))) :=
    fun b => ⟨((maskMap_surjective _ b.1).choose, (maskMap_surjective _ b.2).choose),
      Prod.ext (maskMap_surjective _ b.1).choose_spec (maskMap_surjective _ b.2).choose_spec⟩
  unfold swapKernel
  rw [PMF.map_bind]
  have each : ∀ m : M → BaseField,
      (fibreLaw (maskMap point) (maskMap_surjective point) m).map (splitPerms p) =
        productPMF (fibreLaw (maskMap (restrictPoint (fun m => ¬ p m) point)) (maskMap_surjective _)
          (splitMasks p m).1)
          (fibreLaw (maskMap (restrictPoint p point)) (maskMap_surjective _) (splitMasks p m).2) := by
    intro m
    rw [fibreLaw_map_equiv' (maskMap point) _ (maskMap_surjective point) onto (splitPerms p) (splitMasks p)
      (fun f => (maskMap_split p point f).symm) m]
    exact fibreLaw_prod _ _ _ _ onto _ _
  simp only [each]
  have uniform : (PMF.uniformOfFintype (M → BaseField)).map (splitMasks p) =
      productPMF (PMF.uniformOfFintype (SiteOff p → BaseField))
        (PMF.uniformOfFintype (SiteOn p → BaseField)) := by
    rw [uniformOfFintype_map_equiv, uniformOfFintype_productPMF]
  rw [← productPMF_bind, ← uniform, PMF.bind_map]
  rfl

end Split

end

end Kriterion.ArgoMAC.Security.Phase3
