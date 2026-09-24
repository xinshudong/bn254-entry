/-
**Phase 3, P1s — `LawOn`, step (E), part 14: the private side's sums.**

* `tsum_mul_ite_zero`, `tsum_pmf_const`: an `ite`-indicator and a constant out of an average;
* `tsum_uniform_fst`, `tsum_uniform_pi_fst`: the marginal of a uniform pair (family of pairs);
* **`coins_marginal`**: a function of the offsets and the `ρ`s, averaged over uniform coins, is the
  average over uniform clamped offsets and independent uniform `ρ`s;
* `rowsAt_eq`, `desT`, `desT_eq`: the private side's designated masks at the coins are the core's
  `desK` at the coins' offsets and `ρ`s; **`coins_bd`**: the coins average of the designated limbs;
* **`reorder_core`**: the (abstract) reordering of the private side's nine averages into the core's.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnESim

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source collectorElement)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

/-! ### 1. Sums -/

section Sums

theorem tsum_mul_ite_zero {α : Type} (μ : α → ℝ≥0∞) (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    ∑' a, μ a * (if c then 0 else f a) = if c then 0 else ∑' a, μ a * f a := by
  by_cases h : c
  · simp [h]
  · simp [h]

theorem swapT {α β : Type} (μ : α → ℝ≥0∞) (ν : β → ℝ≥0∞) (f : α → β → ℝ≥0∞) :
    ∑' a, μ a * ∑' b, ν b * f a b = ∑' b, ν b * ∑' a, μ a * f a b := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

theorem tsum_pmf_const {α : Type} (μ : PMF α) (c : ℝ≥0∞) : ∑' a, μ a * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem tsum_uniform_fst {A B C : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C]
    [Nonempty C] (e : A ≃ B × C) (g : B → ℝ≥0∞) :
    ∑' a, PMF.uniformOfFintype A a * g (e a).1 = ∑' b, PMF.uniformOfFintype B b * g b := by
  rw [tsum_equiv_uniform e, tsum_uniform_prod]
  refine tsum_congr fun b => congrArg _ ?_
  simp only [Equiv.apply_symm_apply]
  exact tsum_const_uniform _

theorem tsum_uniform_pi_fst {ι A B C : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] (e : A ≃ B × C) (g : (ι → B) → ℝ≥0∞) :
    ∑' R, PMF.uniformOfFintype (ι → A) R * g (fun i => (e (R i)).1) =
      ∑' ρ, PMF.uniformOfFintype (ι → B) ρ * g ρ :=
  tsum_uniform_fst ((Equiv.piCongrRight fun _ => e).trans
    (Equiv.arrowProdEquivProdArrow ι (fun _ => B) (fun _ => C))) g

open Classical in
/-- **The reordering of the private side's averages into the core's** (abstractly): the offsets
`q` outermost, the indicator out, then `e, h`, and the split limbs `bv, bd` innermost. -/
theorem reorder_core {C Kk V Bv Q R Bd E H X : Type} (p : Q → Prop)
    (uC : C → ℝ≥0∞) (uK : Kk → ℝ≥0∞) (uV : V → ℝ≥0∞) (lwv : V → Bv → ℝ≥0∞) (uQ : Q → ℝ≥0∞)
    (uR : R → ℝ≥0∞) (lwd : Q → R → C → V → Bd → ℝ≥0∞) (uE : E → ℝ≥0∞) (uH : H → ℝ≥0∞)
    (uX : X → ℝ≥0∞) (f : C → Kk → E → H → X → Bv → Bd → ℝ≥0∞)
    (G : Q → E → H → C → V → R → Kk → X → ℝ≥0∞)
    (split : ∀ q e h c v r k x,
      ∑' bv, lwv v bv * ∑' bd, lwd q r c v bd * f c k e h x bv bd = G q e h c v r k x) :
    ∑' c, uC c * ∑' k, uK k * ∑' v, uV v * ∑' bv, lwv v bv * ∑' q, uQ q * ∑' r, uR r *
        ∑' bd, lwd q r c v bd * (if p q then 0 else
          ∑' e, uE e * ∑' h, uH h * ∑' x, uX x * f c k e h x bv bd) =
      ∑' q, uQ q * if p q then 0 else ∑' e, uE e * ∑' h, uH h * ∑' c, uC c * ∑' v, uV v *
        ∑' r, uR r * ∑' k, uK k * ∑' x, uX x * G q e h c v r k x := by
  simp only [← split]
  simp only [swapT (ν := uQ)]
  refine tsum_congr fun q => congrArg _ ?_
  by_cases hq : p q
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    simp only [swapT (ν := uH)]
    simp only [swapT (ν := uE)]
    simp only [swapT (ν := uX)]
    simp only [swapT (ν := uK)]
    simp only [swapT (ν := uR)]

end Sums

/-! ### 2. The coins' offsets and `ρ`s -/

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-- **A function of the offsets and the `ρ`s, averaged over uniform coins.** -/
theorem coins_marginal (g : ClampedOffsets → (Fin digitCount → NonZeroBase) → ℝ≥0∞) :
    ∑' coins, PMF.uniformOfFintype Coins coins *
        g ⟨coins.offsets, coins.offsetsClamped⟩ (fun d => (coins.pointRandomness.get d).rho) =
      ∑' K, PMF.uniformOfFintype ClampedOffsets K *
        ∑' ρ, PMF.uniformOfFintype (Fin digitCount → NonZeroBase) ρ * g K ρ := by
  rw [tsum_equiv_uniform coinsSplit, tsum_uniform_prod (α := ClampedOffsets) (β := CoinsRest)]
  refine tsum_congr fun K => congrArg _ ?_
  rw [tsum_uniform_prod (α := Fin outputMacCount → RowRandomness)]
  have perR : ∀ (R : Fin outputMacCount → RowRandomness)
      (b : (Fin outputMacCount → Exception.Entry) × BaseField × NonZeroBase × BaseField × BaseField ×
        (Coord → Fin coordinateBitCount → Block) × (Coord → Block)),
      g ⟨(coinsSplit.symm (K, R, b)).offsets, (coinsSplit.symm (K, R, b)).offsetsClamped⟩
          (fun d => ((coinsSplit.symm (K, R, b)).pointRandomness.get d).rho) =
        g K (fun d => (rowRandEquiv (R d)).1) := by
    intro R b
    exact congrArg (g K) (funext fun d => congrArg RowRandomness.rho (Vector.get_ofFn R d))
  simp only [perR]
  simp only [tsum_const_uniform]
  exact tsum_uniform_pi_fst rowRandEquiv (g K)

omit [GroupCertificate] in
theorem rowsAt_eq (coins : Coins) (K : ClampedOffsets) (hK : K.1 = coins.offsets) (d : Fin digitCount) :
    rowsAt scalar coins d = rowsK scalar K (fun d => (coins.pointRandomness.get d).rho) d := by
  unfold rowsAt rowsK
  rw [rowsGet, hK]

/-- **The private side's designated masks**: F4's collector solve at the coins' true rows. -/
def desT (coins : Coins) (cells : PublicCells) (vis : VisibleCells (offShape input)) : DSite → BaseField :=
  fun dc => simDesignated (offShape input) (rowTarget (rowsAt scalar coins dc.1) input) (cells.1 dc.1).1
    (cells.1 dc.1).2 (vis.1 dc.1) (.inl (collectorElement dc.2))

theorem desT_eq (coins : Coins) (cells : PublicCells) (vis : VisibleCells (offShape input)) :
    desT scalar input coins cells vis =
      desK scalar input ⟨coins.offsets, coins.offsetsClamped⟩ (fun d => (coins.pointRandomness.get d).rho)
        cells vis := by
  funext dc
  unfold desT desK
  rw [rowsAt_eq scalar coins ⟨coins.offsets, coins.offsetsClamped⟩ rfl]

open Classical in
/-- **The coins' average of the designated limbs** is the average over offsets and `ρ`s. -/
theorem coins_bd (cells : PublicCells) (vis : VisibleCells (offShape input))
    (Z : (DSite → Block × Block × Block) → ℝ≥0∞) :
    ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' bd, limbWeight (desT scalar input coins cells vis) bd *
          (if Exact0 scalar input coins.offsets then 0 else Z bd) =
      ∑' K, PMF.uniformOfFintype ClampedOffsets K *
        ∑' ρ, PMF.uniformOfFintype (Fin digitCount → NonZeroBase) ρ *
          ∑' bd, limbWeight (desK scalar input K ρ cells vis) bd *
            (if Exact0 scalar input K.1 then 0 else Z bd) := by
  rw [← coins_marginal (fun K ρ => ∑' bd, limbWeight (desK scalar input K ρ cells vis) bd *
    (if Exact0 scalar input K.1 then 0 else Z bd))]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [desT_eq]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
