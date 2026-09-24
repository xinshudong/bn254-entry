/-
**Phase 3, P1r — `LawOn`, step (E), part 5: the limb laws, site by site.**

Both sides of `LawOn` draw the view's limbs as uniform `sampleFp`-preimages of masks: the garbler's
fibre-uniform tape (`fibreLaw masksOf`), the private side's preimages of its collector targets
(`Glue.preimages idealSamplers`). Here both are the same product of per-site laws
(`limbWeight μ bd = ∏ n, idealPreimage (μ n) (bd n)`):

* `idealPreimage_eq`: P3's `idealPreimage y` **is** the fibre law of `sampleFp` at `y`
  (`preimageEquiv`: the preimages below `2^384` are `y.val + p·m`, `m ≤ preimageCount y`);
* `fibre_limbs`: the fibre-uniform limbs of a mask family are the product of the per-site laws;
* `preimages_limbs`: the independent preimages of `819/3` targets are the product of the per-site
  laws (`optionProduct_tsum`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPartial

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (idealPreimage preimageCount limbs limbAt preimages idealSamplers
  optionProduct)
open scoped ENNReal

noncomputable section

/-! ### 1. One site -/

/-- `sampleFp` of a triple. -/
def sampleTriple (tr : Block × Block × Block) : BaseField := sampleFp tr.1 tr.2.1 tr.2.2

theorem preimage_bound (y : BaseField) (m : Nat) (small : m < preimageCount y + 1) :
    y.val + baseFieldModulus * m < 2 ^ 384 := by
  have ySmall : y.val < baseFieldModulus := ZMod.val_lt y
  have pSmall : baseFieldModulus < 2 ^ 254 := baseFieldModulus_lt
  have pPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
  have mLe : m ≤ (2 ^ 384 - 1 - y.val) / baseFieldModulus := by
    unfold preimageCount at small
    omega
  have step : baseFieldModulus * m ≤ 2 ^ 384 - 1 - y.val :=
    le_trans (Nat.mul_le_mul_left _ mLe) (Nat.mul_div_le _ _)
  have big : (2 : Nat) ^ 254 < 2 ^ 384 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  omega

theorem cast_preimage (y : BaseField) (m : Nat) :
    ((y.val + baseFieldModulus * m : Nat) : BaseField) = y := by
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- **The preimages of a residue**: `y.val + p·m`, `m ≤ preimageCount y`. -/
def preimageEquiv (y : BaseField) :
    Fin (preimageCount y + 1) ≃ {tr : Block × Block × Block // sampleTriple tr = y} where
  toFun m := ⟨natToBlocks (y.val + baseFieldModulus * m.val), by
    unfold sampleTriple
    rw [sampleFp_natToBlocks _ (preimage_bound y m.val m.isLt), cast_preimage]⟩
  invFun tr := ⟨blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus, by
    have pPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
    have lt := blocksToNat_lt tr.1
    have residue : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 % baseFieldModulus = y.val := by
      have hit : ((blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 : Nat) : BaseField) = y := tr.2
      have values := congrArg ZMod.val hit
      rwa [ZMod.val_natCast] at values
    have split := Nat.mod_add_div (blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2) baseFieldModulus
    have bound : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus * baseFieldModulus ≤
        2 ^ 384 - 1 - y.val := by
      rw [Nat.mul_comm]
      omega
    have le := (Nat.le_div_iff_mul_le pPos).mpr bound
    unfold preimageCount
    omega⟩
  left_inv m := by
    have pPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
    apply Fin.ext
    show blocksToNat (natToBlocks _).1 (natToBlocks _).2.1 (natToBlocks _).2.2 / baseFieldModulus = m.val
    rw [blocksToNat_natToBlocks _ (preimage_bound y m.val m.isLt), Nat.add_mul_div_left _ _ pPos,
      Nat.div_eq_of_lt (ZMod.val_lt y), zero_add]
  right_inv tr := by
    apply Subtype.ext
    have residue : blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 % baseFieldModulus = y.val := by
      have hit : ((blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 : Nat) : BaseField) = y := tr.2
      have values := congrArg ZMod.val hit
      rwa [ZMod.val_natCast] at values
    show natToBlocks (y.val + baseFieldModulus * (blocksToNat tr.1.1 tr.1.2.1 tr.1.2.2 / baseFieldModulus)) =
      tr.1
    rw [← residue, Nat.mod_add_div]
    exact natToBlocks_blocksToNat tr.1

instance (y : BaseField) : Nonempty {tr : Block × Block × Block // sampleTriple tr = y} :=
  ⟨preimageEquiv y 0⟩

/-- **P3's ideal preimage is the fibre law of `sampleFp`.** -/
theorem idealPreimage_eq (y : BaseField) :
    idealPreimage y = (PMF.uniformOfFintype {tr : Block × Block × Block // sampleTriple tr = y}).map
      Subtype.val := by
  have factor : (fun m : Fin (preimageCount y + 1) => limbs (y.val + baseFieldModulus * m.val)) =
      Subtype.val ∘ preimageEquiv y := rfl
  unfold idealPreimage
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

theorem idealPreimage_apply (y : BaseField) (tr : Block × Block × Block) :
    idealPreimage y tr = if sampleTriple tr = y then
      ((Fintype.card {tr : Block × Block × Block // sampleTriple tr = y} : ℝ≥0∞))⁻¹ else 0 := by
  classical
  rw [idealPreimage_eq, PMF.map_apply]
  split_ifs with hit
  · rw [tsum_eq_single ⟨tr, hit⟩]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply]
    · intro other miss
      have : tr ≠ other.1 := fun same => miss (Subtype.ext same.symm)
      simp [this]
  · refine ENNReal.tsum_eq_zero.mpr fun other => ?_
    have : tr ≠ other.1 := fun same => hit (same ▸ other.2)
    simp [this]

/-! ### 2. Many sites -/

section Sites

variable {N : Type} [Fintype N] [DecidableEq N]

/-- **The product of the per-site laws.** -/
def limbWeight (μ : N → BaseField) (bd : N → Block × Block × Block) : ℝ≥0∞ :=
  ∏ n, idealPreimage (μ n) (bd n)

/-- The cells of a triple family. -/
def cellsOf (bd : N → Block × Block × Block) : N × Fin 3 → Block := fun p => limbAt p.2 (bd p.1)

/-- The triples of a cell family. -/
def triplesOf (t : N × Fin 3 → Block) : N → Block × Block × Block := fun n => (t (n, 0), t (n, 1), t (n, 2))

/-- Cells are triples. -/
def tripleEquiv : (N × Fin 3 → Block) ≃ (N → Block × Block × Block) where
  toFun := triplesOf
  invFun := cellsOf
  left_inv t := by
    funext p
    obtain ⟨n, ⟨j, hj⟩⟩ := p
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  right_inv bd := rfl

theorem masksOf_eq (t : N × Fin 3 → Block) (n : N) : masksOf t n = sampleTriple (triplesOf t n) := rfl

/-- The fibre of a mask family is the product of the per-site fibres. -/
def fibreEquiv (μ : N → BaseField) :
    {t : N × Fin 3 → Block // masksOf t = μ} ≃ ((n : N) → {tr : Block × Block × Block // sampleTriple tr = μ n}) where
  toFun t n := ⟨triplesOf t.1 n, congrFun t.2 n⟩
  invFun f := ⟨cellsOf fun n => (f n).1, funext fun n => (f n).2⟩
  left_inv t := Subtype.ext (tripleEquiv.left_inv t.1)
  right_inv f := rfl

theorem fibreLaw_apply_prod (μ : N → BaseField) (t : N × Fin 3 → Block) :
    fibreLaw masksOf masksOf_onto μ t = limbWeight μ (triplesOf t) := by
  classical
  rw [fibreLaw_apply, limbWeight]
  simp only [idealPreimage_apply]
  rw [Finset.prod_ite_zero]
  have cards : Fintype.card {t : N × Fin 3 → Block // masksOf t = μ} =
      ∏ n, Fintype.card {tr : Block × Block × Block // sampleTriple tr = μ n} := by
    rw [Fintype.card_congr (fibreEquiv μ), Fintype.card_pi]
  have same : (masksOf t = μ) ↔ ∀ n ∈ Finset.univ, sampleTriple (triplesOf t n) = μ n :=
    ⟨fun h n _ => congrFun h n, fun h => funext fun n => h n (Finset.mem_univ n)⟩
  by_cases hit : masksOf t = μ
  · rw [if_pos hit, if_pos (same.mp hit), cards, Nat.cast_prod]
    refine ENNReal.prod_inv_distrib fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _)
  · rw [if_neg hit, if_neg (fun h => hit (same.mpr h))]

/-- **The fibre-uniform limbs are the product of the per-site laws.** -/
theorem fibre_limbs (μ : N → BaseField) (G : (N × Fin 3 → Block) → ℝ≥0∞) :
    ∑' t, fibreLaw masksOf masksOf_onto μ t * G t =
      ∑' bd : N → Block × Block × Block, limbWeight μ bd * G (cellsOf bd) := by
  rw [← (tripleEquiv (N := N)).symm.tsum_eq]
  refine tsum_congr fun bd => ?_
  rw [fibreLaw_apply_prod]
  rfl

end Sites

/-! ### 3. The preimages -/

theorem optionProduct_tsum {α : Type} : ∀ (n : Nat) (μ : Fin n → PMF α) (H : (Fin n → α) → ℝ≥0∞),
    ∑' o, optionProduct n (fun i => (μ i).map some) o * Option.elim o 0 H =
      ∑' f : Fin n → α, (∏ i, μ i (f i)) * H f
  | 0, μ, H => by
      show ∑' o, (PMF.pure (some Fin.elim0)) o * Option.elim o 0 H = _
      rw [tsum_pure_mul]
      rw [tsum_fintype, Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Option.elim]
      congr 1
  | n + 1, μ, H => by
      show ∑' o, ((μ 0).map some).bind (fun head => match head with
        | none => PMF.pure none
        | some head => (optionProduct n fun index => (μ index.succ).map some).map
            (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)) o * Option.elim o 0 H = _
      rw [tsum_bind_mul, tsum_map_mul]
      have inner : ∀ h : α, ∑' o, ((optionProduct n fun index => (μ index.succ).map some).map
          (Option.map fun tail => Fin.cons (α := fun _ => α) h tail)) o * Option.elim o 0 H =
          ∑' f : Fin n → α, (∏ i, μ i.succ (f i)) * H (Fin.cons h f) := by
        intro h
        rw [tsum_map_mul]
        have elim : ∀ o : Option (Fin n → α), Option.elim (Option.map (fun tail =>
            Fin.cons (α := fun _ => α) h tail) o) 0 H = Option.elim o 0 (fun f => H (Fin.cons h f)) := by
          rintro (_ | f) <;> rfl
        simp only [elim]
        exact optionProduct_tsum n (fun i => μ i.succ) (fun f => H (Fin.cons h f))
      simp only [inner]
      rw [← (Fin.consEquiv (fun _ => α)).tsum_eq]
      refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun (a : α) (f : Fin n → α) =>
        (∏ i, μ i (Fin.cons (α := fun _ => α) a f i)) * H (Fin.cons (α := fun _ => α) a f))).symm
      simp only [← ENNReal.tsum_mul_left]
      refine tsum_congr fun h => tsum_congr fun f => ?_
      show μ 0 h * ((∏ i, μ i.succ (f i)) * H (Fin.cons h f)) =
        (∏ i, μ i (Fin.cons (α := fun _ => α) h f i)) * H (Fin.cons h f)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring

/-- The (digit, collector) slots. -/
abbrev DSite := Fin digitCount × Fin 3

/-- **The preimages of the collector targets are the product of the per-site laws.** -/
theorem preimages_limbs (τ : DSite → BaseField) (G : (DSite → Block × Block × Block) → ℝ≥0∞) :
    ∑' b, preimages idealSamplers τ b * Option.elim b 0 G =
      ∑' bd : DSite → Block × Block × Block, limbWeight τ bd * G bd := by
  unfold preimages
  rw [tsum_map_mul]
  have elim : ∀ o : Option (Fin (digitCount * 3) → Block × Block × Block),
      Option.elim (Option.map (fun blocks site => blocks (finProdFinEquiv site)) o) 0 G =
        Option.elim o 0 (fun blocks => G fun site => blocks (finProdFinEquiv site)) := by
    rintro (_ | f) <;> rfl
  simp only [elim]
  have ideal : ∀ index : Fin (digitCount * 3), idealSamplers.preimage (τ (finProdFinEquiv.symm index)) =
      (idealPreimage (τ (finProdFinEquiv.symm index))).map some := fun _ => rfl
  simp only [ideal]
  rw [optionProduct_tsum]
  rw [← (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Block × Block × Block))).tsum_eq]
  refine tsum_congr fun bd => ?_
  have back : (fun site => (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Block × Block × Block)) bd)
      (finProdFinEquiv site)) = bd := by
    funext site
    simp [Equiv.arrowCongr_apply]
  rw [back, limbWeight]
  congr 1

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
