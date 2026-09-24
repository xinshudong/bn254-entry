/-
**Phase 3, P1 — shared probability lemmas.**

The phase-3 route (`B-output-aware-simulator.md`) needs four generic facts about
finite uniform laws, which this module proves once:

* `etvDist_bind_left_le_const` — a *shared* first draw followed by two kernels that are pointwise
  `ε`-close gives two laws that are `ε`-close (VCV-io proves the `ℝ`-valued form; its `ℝ≥0∞` step is
  `private`, so it is re-proved here);
* `uniform_eq_bind_fibreLaw` — the uniform law on `A` disintegrates along any surjection `g` as
  "draw `g a` from its pushforward, then draw `a` uniformly on that fibre";
* `uniform_map_of_fibre_equiv` — a map whose fibres are pairwise equinumerous pushes the uniform law
  to the uniform law (no fibre is ever counted);
* `etvDist_pi_map_uniform_le` and `sampleFp_etvDist_le` — the per-draw reduction bias of Rule S's
  three-block sampler, `δ₃ = (2 ^ 384 mod p) / 2 ^ 384`, and its `n`-fold product.

**Why these are local proofs.** The last two restate, generically and in the `Phase3`
namespace, the arguments of two modules of the earlier hybrid chain, which targeted a superseded
profile and have been removed from this repository.
-/

import Proof.Privacy.PGS.DaviesMeyerUniform
import Construction.PGS.Sampler

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 400

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv uniformOfFintype_map_fst card_block)
open scoped ENNReal

noncomputable section

/-! ### Data processing, in `PMF.map` spelling -/

/-- `PMF.etvDist_map_le` is stated with `<$>`; this is the same fact for `PMF.map`. -/
theorem etvDist_map_le' {A B : Type} (f : A → B) (p q : PMF A) :
    (p.map f).etvDist (q.map f) ≤ p.etvDist q :=
  PMF.etvDist_map_le f p q

/-! ### A shared first draw -/

/-- **A shared first draw.** Two kernels behind one common law differ by at most the
`p`-average of their pointwise distances. (VCV-io's `pmf_etvDist_bind_left_le`, which is
`private`.) -/
theorem etvDist_bind_left_le {α β : Type} (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, (f a).etvDist (g a) * p a := by
  have hrhs :
      (∑' a, (f a).etvDist (g a) * p a) =
        (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_right_comm]
  rw [PMF.etvDist, hrhs]
  refine ENNReal.div_le_div_right ?_ 2
  calc ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
      ≤ ∑' y, ∑' x, ENNReal.absDiff (p x * (f x) y) (p x * (g x) y) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff ((f x) y) ((g x) y) * p x :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun x => by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            ENNReal.absDiff_mul_right_le ((f x) y) ((g x) y) (p x)
    _ = ∑' x, ∑' y, ENNReal.absDiff ((f x) y) ((g x) y) * p x := ENNReal.tsum_comm
    _ = ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x := by
        simp_rw [ENNReal.tsum_mul_right]

/-- **A shared first draw, uniform bound.** If the two kernels are pointwise `bound`-close, so are
the two laws. This is the step that lets a per-point-set bound (`MaskSwap.swapKernel_etvDist_le`)
cover the whole tape, whatever the law of the points. -/
theorem etvDist_bind_left_le_const {α β : Type} (p : PMF α) (f g : α → PMF β) (bound : ℝ≥0∞)
    (each : ∀ a, (f a).etvDist (g a) ≤ bound) :
    (p.bind f).etvDist (p.bind g) ≤ bound := by
  refine le_trans (etvDist_bind_left_le p f g) ?_
  calc ∑' a, (f a).etvDist (g a) * p a ≤ ∑' a, bound * p a :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_left (each a) _
    _ = bound * ∑' a, p a := ENNReal.tsum_mul_left
    _ = bound := by rw [p.tsum_coe, mul_one]

/-! ### Pushforwards of a uniform law, counted -/

/-- The pushforward mass of one point is its fibre's share. -/
theorem uniform_map_apply {A B : Type} [Fintype A] [Nonempty A] [DecidableEq B]
    (g : A → B) (point : B) :
    ((PMF.uniformOfFintype A).map g) point
      = (Fintype.card {x : A // g x = point} : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [eq_comm]

/-- **Equinumerous fibres push uniform to uniform.** If every two fibres of `g` are in bijection
(`shift`), then `g` pushes the uniform law on `A` to the uniform law on `B`. No fibre is counted:
the common cardinality cancels against `#A = #B · #fibre`. -/
theorem uniform_map_of_fibre_equiv {A B : Type} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] [DecidableEq B] (g : A → B)
    (shift : ∀ first second : B, {x : A // g x = first} ≃ {x : A // g x = second}) :
    (PMF.uniformOfFintype A).map g = PMF.uniformOfFintype B := by
  classical
  obtain ⟨base⟩ := (inferInstance : Nonempty B)
  have fibreCard : ∀ point : B,
      Fintype.card {x : A // g x = point} = Fintype.card {x : A // g x = base} :=
    fun point => Fintype.card_congr (shift point base)
  have total : Fintype.card A = Fintype.card B * Fintype.card {x : A // g x = base} := by
    calc Fintype.card A = Fintype.card (Σ point : B, {x : A // g x = point}) :=
          Fintype.card_congr (Equiv.sigmaFiberEquiv g).symm
      _ = ∑ point : B, Fintype.card {x : A // g x = point} := Fintype.card_sigma
      _ = ∑ _point : B, Fintype.card {x : A // g x = base} :=
          Finset.sum_congr rfl fun point _ => fibreCard point
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have fibrePos : 0 < Fintype.card {x : A // g x = base} := by
    rcases Nat.eq_zero_or_pos (Fintype.card {x : A // g x = base}) with zero | pos
    · have : Fintype.card A = 0 := by rw [total, zero, mul_zero]
      exact absurd this Fintype.card_ne_zero
    · exact pos
  refine PMF.ext fun point => ?_
  rw [uniform_map_apply, PMF.uniformOfFintype_apply, fibreCard point, total, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card B : ℝ≥0∞)⁻¹), ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr fibrePos.ne') (ENNReal.natCast_ne_top _),
    one_mul]

/-! ### The fibre disintegration -/

section Fibre

variable {A B : Type} [Fintype A] [DecidableEq B] (g : A → B) (onto : Function.Surjective g)

/-- The uniform law on the fibre of `g` over `point`, read as a law on `A`. -/
def fibreLaw (point : B) : PMF A :=
  haveI : Nonempty {x : A // g x = point} :=
    ⟨⟨Classical.choose (onto point), Classical.choose_spec (onto point)⟩⟩
  (PMF.uniformOfFintype {x : A // g x = point}).map Subtype.val

theorem fibreLaw_apply (point : B) (x : A) :
    fibreLaw g onto point x
      = if g x = point then (Fintype.card {y : A // g y = point} : ℝ≥0∞)⁻¹ else 0 := by
  classical
  unfold fibreLaw
  rw [PMF.map_apply]
  split_ifs with hit
  · rw [tsum_eq_single ⟨x, hit⟩]
    · simp [PMF.uniformOfFintype_apply]
    · intro other miss
      have : x ≠ other.1 := fun same => miss (Subtype.ext same.symm)
      simp [this]
  · refine ENNReal.tsum_eq_zero.mpr fun other => ?_
    have : x ≠ other.1 := fun same => hit (same ▸ other.2)
    simp [this]

/-- Every point the fibre law can draw lies in the fibre. -/
theorem fibreLaw_map (point : B) : (fibreLaw g onto point).map g = PMF.pure point := by
  classical
  unfold fibreLaw
  rw [PMF.map_comp]
  have constant : (g ∘ Subtype.val : {x : A // g x = point} → B) = fun _ => point := by
    funext x; exact x.2
  rw [constant]
  exact PMF.map_const _ point

/-- **The fibre disintegration of the uniform law.** Drawing `a` uniformly is drawing `g a` from its
pushforward and then `a` uniformly on the fibre over it. -/
theorem uniform_eq_bind_fibreLaw [Nonempty A] :
    PMF.uniformOfFintype A = ((PMF.uniformOfFintype A).map g).bind (fibreLaw g onto) := by
  classical
  refine PMF.ext fun x => ?_
  rw [PMF.bind_apply, tsum_eq_single (g x)]
  · rw [fibreLaw_apply, if_pos rfl, uniform_map_apply, PMF.uniformOfFintype_apply, mul_comm,
      ← mul_assoc]
    have fibrePos : 0 < Fintype.card {y : A // g y = g x} :=
      Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr fibrePos.ne') (ENNReal.natCast_ne_top _),
      one_mul]
  · intro other miss
    rw [fibreLaw_apply, if_neg (fun same => miss same.symm), mul_zero]

end Fibre

/-! ### The one-sided form of total variation -/

/-- **Total variation is one-sided.** Only the outcomes the first law undershoots contribute. -/
theorem etvDist_eq_tsum_tsub {A : Type} (first second : PMF A) :
    first.etvDist second = ∑' value, (second value - first value) := by
  have minLe : (∑' value, (first value ⊓ second value)) ≤ 1 :=
    le_of_le_of_eq (ENNReal.tsum_le_tsum fun value => inf_le_left) first.tsum_coe
  have left : (∑' value, (first value - second value))
      + (∑' value, (first value ⊓ second value)) = 1 := by
    rw [← ENNReal.tsum_add, ← first.tsum_coe]
    exact tsum_congr fun value => tsub_add_min
  have right : (∑' value, (second value - first value))
      + (∑' value, (first value ⊓ second value)) = 1 := by
    rw [← ENNReal.tsum_add, ← second.tsum_coe]
    refine tsum_congr fun value => ?_
    rw [inf_comm]
    exact tsub_add_min
  have equal : (∑' value, (first value - second value))
      = ∑' value, (second value - first value) :=
    (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top minLe)).mp
      (left.trans right.symm)
  rw [PMF.etvDist]
  simp only [ENNReal.absDiff]
  rw [ENNReal.tsum_add, equal,
    show (∑' value, (second value - first value)) + ∑' value, (second value - first value)
      = 2 * ∑' value, (second value - first value) from by ring, mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-! ### Independent pairs and `n` independent copies -/

/-- Two independent draws. -/
def productPMF {A C : Type} (first : PMF A) (second : PMF C) : PMF (A × C) :=
  first.bind fun value => second.map (Prod.mk value)

@[simp] theorem productPMF_apply {A C : Type} (first : PMF A) (second : PMF C) (point : A × C) :
    productPMF first second point = first point.1 * second point.2 := by
  classical
  obtain ⟨left, right⟩ := point
  rw [productPMF, PMF.bind_apply]
  have inner : ∀ value : A,
      (second.map (Prod.mk value)) (left, right) = if value = left then second right else 0 := by
    intro value
    rw [PMF.map_apply]
    by_cases hit : value = left
    · subst hit
      rw [if_pos rfl, tsum_eq_single right]
      · simp
      · intro other miss
        simp [Prod.ext_iff, Ne.symm miss]
    · rw [if_neg hit, ENNReal.tsum_eq_zero]
      intro other
      exact if_neg fun same => hit (congrArg Prod.fst same).symm
  simp only [inner]
  rw [tsum_eq_single left]
  · simp
  · intro other miss
    simp [miss]

theorem productPMF_swap {A C : Type} (first : PMF A) (second : PMF C) :
    (productPMF first second).map Prod.swap = productPMF second first := by
  refine PMF.ext fun point => ?_
  obtain ⟨right, left⟩ := point
  rw [PMF.map_apply, tsum_eq_single (left, right)]
  · simp [mul_comm]
  · intro other miss
    refine if_neg fun same => miss ?_
    obtain ⟨a, c⟩ := other
    cases same
    rfl

/-- A uniform law on a product is the independent pair of uniform laws. -/
theorem uniformOfFintype_productPMF {A C : Type} [Fintype A] [Nonempty A] [Fintype C]
    [Nonempty C] :
    PMF.uniformOfFintype (A × C)
      = productPMF (PMF.uniformOfFintype A) (PMF.uniformOfFintype C) := by
  refine PMF.ext fun point => ?_
  rw [productPMF_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]

theorem etvDist_productPMF_left_le {A C : Type} (first second : PMF A) (common : PMF C) :
    (productPMF first common).etvDist (productPMF second common) ≤ first.etvDist second :=
  PMF.etvDist_bind_right_le _ first second

theorem etvDist_productPMF_right_le {A C : Type} (common : PMF A) (first second : PMF C) :
    (productPMF common first).etvDist (productPMF common second) ≤ first.etvDist second := by
  rw [← productPMF_swap first common, ← productPMF_swap second common]
  exact le_trans (etvDist_map_le' Prod.swap _ _) (etvDist_productPMF_left_le first second common)

theorem etvDist_productPMF_le {A C : Type} (firstLeft secondLeft : PMF A)
    (firstRight secondRight : PMF C) :
    (productPMF firstLeft firstRight).etvDist (productPMF secondLeft secondRight)
      ≤ firstLeft.etvDist secondLeft + firstRight.etvDist secondRight :=
  le_trans (PMF.etvDist_triangle _ (productPMF secondLeft firstRight) _)
    (add_le_add (etvDist_productPMF_left_le firstLeft secondLeft firstRight)
      (etvDist_productPMF_right_le secondLeft firstRight secondRight))

theorem productPMF_map {A B C D : Type} (first : PMF A) (second : PMF C) (left : A → B)
    (right : C → D) :
    (productPMF first second).map (Prod.map left right)
      = productPMF (first.map left) (second.map right) := by
  rw [productPMF, productPMF, PMF.map_bind, PMF.bind_map]
  refine congrArg (PMF.bind first) (funext fun value => ?_)
  show PMF.map (Prod.map left right) (PMF.map (Prod.mk value) second)
    = PMF.map (Prod.mk (left value)) (PMF.map right second)
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- One more coordinate, at the front. -/
def consEquiv (A : Type) (n : Nat) : (A × (Fin n → A)) ≃ (Fin (n + 1) → A) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun family := (family 0, Fin.tail family)
  left_inv pair := by
    obtain ⟨head, tail⟩ := pair
    simp [Fin.tail_cons]
  right_inv family := by simp [Fin.cons_self_tail]

theorem cons_comp {A B : Type} (g : A → B) (n : Nat) (head : A) (tail : Fin n → A) :
    (fun index : Fin (n + 1) => g ((Fin.cons head tail : Fin (n + 1) → A) index))
      = (Fin.cons (g head) (fun index => g (tail index)) : Fin (n + 1) → B) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · simp
  · intro place
    simp

/-- `n` independent copies of one law. -/
def powerPMF {A : Type} (law : PMF A) : (n : Nat) → PMF (Fin n → A)
  | 0 => PMF.pure fun index => index.elim0
  | n + 1 => (productPMF law (powerPMF law n)).map (consEquiv A n)

theorem powerPMF_uniform {A : Type} [Fintype A] [Nonempty A] :
    ∀ n : Nat, powerPMF (PMF.uniformOfFintype A) n = PMF.uniformOfFintype (Fin n → A)
  | 0 => by
      refine PMF.ext fun family => ?_
      have unique : family = fun index : Fin 0 => index.elim0 := funext fun index => index.elim0
      rw [powerPMF, PMF.pure_apply, if_pos unique, PMF.uniformOfFintype_apply]
      simp
  | n + 1 => by
      rw [powerPMF, powerPMF_uniform n, ← uniformOfFintype_productPMF]
      exact uniformOfFintype_map_equiv (consEquiv A n)

theorem powerPMF_map {A B : Type} (law : PMF A) (g : A → B) :
    ∀ n : Nat, (powerPMF law n).map (fun family index => g (family index))
      = powerPMF (law.map g) n
  | 0 => by
      rw [powerPMF, powerPMF, PMF.pure_map]
      exact congrArg PMF.pure (funext fun index => index.elim0)
  | n + 1 => by
      rw [powerPMF, powerPMF, PMF.map_comp, ← powerPMF_map law g n, ← productPMF_map,
        PMF.map_comp]
      refine congrArg (PMF.map · (productPMF law (powerPMF law n))) (funext fun pair => ?_)
      obtain ⟨head, tail⟩ := pair
      exact cons_comp g n head tail

theorem etvDist_powerPMF_le {A : Type} (first second : PMF A) :
    ∀ n : Nat, (powerPMF first n).etvDist (powerPMF second n) ≤ (n : ℝ≥0∞) * first.etvDist second
  | 0 => by
      rw [powerPMF, powerPMF]
      simp
  | n + 1 => by
      rw [powerPMF, powerPMF]
      have step : ((productPMF first (powerPMF first n)).map (consEquiv A n)).etvDist
          ((productPMF second (powerPMF second n)).map (consEquiv A n))
          ≤ first.etvDist second + (powerPMF first n).etvDist (powerPMF second n) :=
        le_trans (etvDist_map_le' (consEquiv A n) _ _)
          (etvDist_productPMF_le first second (powerPMF first n) (powerPMF second n))
      refine le_trans step ?_
      refine le_trans (add_le_add (le_refl (first.etvDist second))
        (etvDist_powerPMF_le first second n)) (le_of_eq ?_)
      push_cast
      ring

theorem etvDist_power_uniform_le {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (g : A → B) (n : Nat) (bound : ℝ≥0∞)
    (perDraw : ((PMF.uniformOfFintype A).map g).etvDist (PMF.uniformOfFintype B) ≤ bound) :
    ((PMF.uniformOfFintype (Fin n → A)).map (fun family index => g (family index))).etvDist
        (PMF.uniformOfFintype (Fin n → B))
      ≤ (n : ℝ≥0∞) * bound := by
  rw [← powerPMF_uniform (A := A) n, ← powerPMF_uniform (A := B) n, powerPMF_map]
  exact le_trans
    (etvDist_powerPMF_le ((PMF.uniformOfFintype A).map g) (PMF.uniformOfFintype B) n)
    (mul_le_mul_right perDraw _)

/-- **A per-draw bias, paid once per index**, for any finite index type. -/
theorem etvDist_pi_map_uniform_le {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A]
    [Nonempty A] [Fintype B] [Nonempty B] (g : A → B) (bound : ℝ≥0∞)
    (perDraw : ((PMF.uniformOfFintype A).map g).etvDist (PMF.uniformOfFintype B) ≤ bound) :
    ((PMF.uniformOfFintype (I → A)).map (fun family index => g (family index))).etvDist
        (PMF.uniformOfFintype (I → B))
      ≤ (Fintype.card I : ℝ≥0∞) * bound := by
  classical
  set places := Fintype.equivFin I with placesDef
  set reindexLeft : (Fin (Fintype.card I) → A) ≃ (I → A) :=
    Equiv.arrowCongr places.symm (Equiv.refl A) with leftDef
  set reindexRight : (Fin (Fintype.card I) → B) ≃ (I → B) :=
    Equiv.arrowCongr places.symm (Equiv.refl B) with rightDef
  have left : (PMF.uniformOfFintype (Fin (Fintype.card I) → A)).map reindexLeft
      = PMF.uniformOfFintype (I → A) := uniformOfFintype_map_equiv reindexLeft
  have right : (PMF.uniformOfFintype (Fin (Fintype.card I) → B)).map reindexRight
      = PMF.uniformOfFintype (I → B) := uniformOfFintype_map_equiv reindexRight
  rw [← left, ← right, PMF.map_comp]
  have commute : (fun family : I → A => fun index => g (family index)) ∘ reindexLeft
      = reindexRight ∘ (fun family : Fin (Fintype.card I) → A => fun place => g (family place)) :=
    rfl
  rw [commute, ← PMF.map_comp]
  exact le_trans (etvDist_map_le' reindexRight _ _)
    (etvDist_power_uniform_le g (Fintype.card I) bound perDraw)

/-! ### The reduction bias of one Rule S draw -/

/-- **The reduction bias.** A map onto `ZMod p` from a domain of size `p * q + r` whose every fibre
has at least `q` points pushes the uniform law to within `r / (p * q + r)` of uniform. -/
theorem etvDist_reduction_le {A : Type} [Fintype A] [Nonempty A] (p q r : Nat) [NeZero p]
    (g : A → ZMod p) (cardA : Fintype.card A = p * q + r)
    (fibres : ∀ residue : ZMod p, q ≤ Fintype.card {x : A // g x = residue}) :
    ((PMF.uniformOfFintype A).map g).etvDist (PMF.uniformOfFintype (ZMod p))
      ≤ (r : ℝ≥0∞) / (p * q + r : Nat) := by
  classical
  have cardMod : Fintype.card (ZMod p) = p := ZMod.card p
  have sizePos : 0 < Fintype.card A := Fintype.card_pos
  have sizeNe : (Fintype.card A : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr sizePos.ne'
  have sizeTop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have modNe : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have modTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have lower : ∀ residue : ZMod p,
      (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹
        ≤ ((PMF.uniformOfFintype A).map g) residue := by
    intro residue
    rw [uniform_map_apply]
    exact mul_le_mul_left (Nat.cast_le.mpr (fibres residue)) _
  have termwise : ∀ residue : ZMod p,
      (PMF.uniformOfFintype (ZMod p)) residue - ((PMF.uniformOfFintype A).map g) residue
        ≤ (p : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
    intro residue
    rw [PMF.uniformOfFintype_apply, cardMod]
    exact tsub_le_tsub_left (lower residue) _
  rw [etvDist_eq_tsum_tsub]
  calc (∑' residue : ZMod p, ((PMF.uniformOfFintype (ZMod p)) residue
          - ((PMF.uniformOfFintype A).map g) residue))
      ≤ ∑' _residue : ZMod p,
          ((p : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum termwise
    _ = (p : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹ - (q : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, cardMod, nsmul_eq_mul]
    _ = (r : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_sub (fun _ _ => modTop), ENNReal.mul_inv_cancel modNe modTop,
          ← mul_assoc]
        refine (ENNReal.sub_eq_of_eq_add
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top modTop (ENNReal.natCast_ne_top q))
            (ENNReal.inv_ne_top.mpr sizeNe)) ?_)
        rw [← add_mul]
        have total : ((r : ℝ≥0∞) + (p : ℝ≥0∞) * (q : ℝ≥0∞)) = (Fintype.card A : ℝ≥0∞) := by
          rw [cardA]
          push_cast
          ring
        rw [total, ENNReal.mul_inv_cancel sizeNe sizeTop]
    _ = (r : ℝ≥0∞) / (p * q + r : Nat) := by
        rw [ENNReal.div_eq_inv_mul, mul_comm, cardA]

/-- The three-limb decomposition of a natural number below `2 ^ 384`. -/
def natToBlocks (value : Nat) : Block × Block × Block :=
  (BitVec.ofNat 128 value, BitVec.ofNat 128 (value / 2 ^ 128),
    BitVec.ofNat 128 (value / 2 ^ 256))

theorem blocksToNat_natToBlocks (value : Nat) (small : value < 2 ^ 384) :
    blocksToNat (natToBlocks value).1 (natToBlocks value).2.1 (natToBlocks value).2.2
      = value := by
  simp only [blocksToNat, natToBlocks, BitVec.toNat_ofNat]
  omega

theorem sampleFp_natToBlocks (value : Nat) (small : value < 2 ^ 384) :
    sampleFp (natToBlocks value).1 (natToBlocks value).2.1 (natToBlocks value).2.2
      = (value : BaseField) := by
  rw [sampleFp, blocksToNat_natToBlocks value small]

/-- Three blocks carry `2 ^ 384` values. -/
theorem card_blockTriple : Fintype.card (Block × Block × Block) = 2 ^ 384 := by
  rw [Fintype.card_prod, Fintype.card_prod, card_block, ← pow_add, ← pow_add]

/-- **Every residue has at least `⌊2 ^ 384 / p⌋` preimages under Rule S's sampler.** The witnesses
are `v, v + p, v + 2p, …`, decomposed into three limbs. -/
theorem sampleFp_fibre_card (residue : BaseField) :
    2 ^ 384 / baseFieldModulus
      ≤ Fintype.card {blocks : Block × Block × Block //
        sampleFp blocks.1 blocks.2.1 blocks.2.2 = residue} := by
  classical
  have modPos : 0 < baseFieldModulus := Nat.pos_of_ne_zero (NeZero.ne baseFieldModulus)
  have residueSmall : residue.val < baseFieldModulus := ZMod.val_lt residue
  have bound : ∀ k : Fin (2 ^ 384 / baseFieldModulus),
      residue.val + k.val * baseFieldModulus < 2 ^ 384 := by
    intro k
    have step : residue.val + k.val * baseFieldModulus
        < (k.val + 1) * baseFieldModulus := by
      rw [Nat.succ_mul]
      omega
    have grow : (k.val + 1) * baseFieldModulus
        ≤ (2 ^ 384 / baseFieldModulus) * baseFieldModulus :=
      Nat.mul_le_mul_right _ k.isLt
    have final : (2 ^ 384 / baseFieldModulus) * baseFieldModulus ≤ 2 ^ 384 :=
      Nat.div_mul_le_self _ _
    omega
  have embedValue : ∀ k : Fin (2 ^ 384 / baseFieldModulus),
      sampleFp (natToBlocks (residue.val + k.val * baseFieldModulus)).1
          (natToBlocks (residue.val + k.val * baseFieldModulus)).2.1
          (natToBlocks (residue.val + k.val * baseFieldModulus)).2.2
        = residue := by
    intro k
    rw [sampleFp_natToBlocks _ (bound k)]
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero]
    exact ZMod.natCast_zmod_val residue
  let embed : Fin (2 ^ 384 / baseFieldModulus) → {blocks : Block × Block × Block //
      sampleFp blocks.1 blocks.2.1 blocks.2.2 = residue} := fun k =>
    ⟨natToBlocks (residue.val + k.val * baseFieldModulus), embedValue k⟩
  have injective : Function.Injective embed := by
    intro first second same
    have valueEq : residue.val + first.val * baseFieldModulus
        = residue.val + second.val * baseFieldModulus := by
      have recovered := congrArg
        (fun point : {blocks : Block × Block × Block //
            sampleFp blocks.1 blocks.2.1 blocks.2.2 = residue} =>
          blocksToNat point.1.1 point.1.2.1 point.1.2.2) same
      simpa only [embed, blocksToNat_natToBlocks _ (bound first),
        blocksToNat_natToBlocks _ (bound second)] using recovered
    refine Fin.ext (Nat.eq_of_mul_eq_mul_right modPos ?_)
    omega
  simpa using Fintype.card_le_of_injective embed injective

/-- `2 ^ 384 mod p`: the residue of Rule S's three-block sample space. -/
def reductionResidue : Nat := 2 ^ 384 % baseFieldModulus

/-- The residue, evaluated once. -/
theorem reductionResidue_eq :
    reductionResidue =
      19955747995551142847684105936715069082057687757382501343901258828998203168490 := by
  rw [reductionResidue, baseFieldModulus]
  rfl

/-- **`δ₃`, the per-draw bias of Rule S's three-block sampler**: `(2 ^ 384 mod p) / 2 ^ 384`. -/
def delta3 : ℝ≥0∞ := (reductionResidue : ℝ≥0∞) / 2 ^ 384

/-- **Rule S, one draw.** `PlanB.sampleFp` of three uniform blocks is within `δ₃` of uniform. -/
theorem sampleFp_etvDist_le :
    ((PMF.uniformOfFintype (Block × Block × Block)).map
        (fun blocks => sampleFp blocks.1 blocks.2.1 blocks.2.2)).etvDist
        (PMF.uniformOfFintype BaseField)
      ≤ delta3 := by
  have split : baseFieldModulus * (2 ^ 384 / baseFieldModulus) + 2 ^ 384 % baseFieldModulus
      = 2 ^ 384 := Nat.div_add_mod _ _
  have cards : Fintype.card (Block × Block × Block)
      = baseFieldModulus * (2 ^ 384 / baseFieldModulus) + 2 ^ 384 % baseFieldModulus := by
    rw [card_blockTriple, split]
  have bound := etvDist_reduction_le (A := Block × Block × Block) baseFieldModulus
    (2 ^ 384 / baseFieldModulus) (2 ^ 384 % baseFieldModulus)
    (fun blocks => sampleFp blocks.1 blocks.2.1 blocks.2.2) cards sampleFp_fibre_card
  rw [split] at bound
  refine le_trans bound (le_of_eq ?_)
  rw [delta3, reductionResidue, Nat.cast_pow, Nat.cast_ofNat]

end

end Kriterion.ArgoMAC.Security.Phase3
