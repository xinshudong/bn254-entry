/-
**Phase 3, P4 — fresh uniform limbs against the lazy oracle: `1/2^128` per stage-1 entry.**

The intermediate run (`runRefill` with a fresh uniform block per consumed cell) against `I`'s run
(`Glue.runIntercept`), for an arbitrary query computation:

* `consume_step_etvDist_le` — **one consumed query.** At a fresh input, programming
  `input ↦ limb xor input` with a uniform `limb` (abort if the output is used) against the lazy
  forward query (uniform on the unused outputs) differ by exactly the used fraction
  `used / 2^128`: both are the same map of "uniform on all outputs, `none` on a used one" and
  "uniform on the unused outputs" (`restrict_etvDist_le`), and the programmed state is the lazy
  state of the same output (`LazyOracle.permutationProgram` extends by the output's position, the
  lazy draw by the rank of the same unused output).
* `runRefill_uniform_etvDist_le` — **the whole run**: the distance is at most
  `potential touched oracle / 2^128`, where the potential counts the entries at the mask-site
  indices not yet touched in stage 2. A consumed query pays its index's entries and removes that
  index from the potential (`potential_consume`); any other query only removes indices
  (`potential_touch_le`, with `query_frame`: a lazy query changes only the index it touches).

At the start of stage 2 nothing is touched, so the run costs `(Σ_cells used) / 2^128`: one
`1/2^128` per stage-1 entry at a mask-site index (the answer exclusion of the lazy oracle).
-/

import Proof.Privacy.Phase3.Lazy.EagerLazy
import Proof.Privacy.Phase3.Lazy.OutputFreshness

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex siteIndex_injective
  etvDist_bind_left_le etvDist_eq_tsum_tsub uniform_map_apply)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Two generic distance facts -/

/-- A shared first draw whose two continuations are `c`-close on its support. -/
theorem etvDist_bind_le_of_support {α β : Type} (p : PMF α) (f g : α → PMF β) (c : ℝ≥0∞)
    (close : ∀ a ∈ p.support, (f a).etvDist (g a) ≤ c) :
    (p.bind f).etvDist (p.bind g) ≤ c := by
  refine le_trans (etvDist_bind_left_le p f g) ?_
  calc (∑' a, (f a).etvDist (g a) * p a) ≤ ∑' a, c * p a := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases zero : p a = 0
        · rw [zero, mul_zero, mul_zero]
        · exact mul_le_mul_left (close a ((PMF.mem_support_iff _ _).mpr zero)) _
    _ = c := by rw [ENNReal.tsum_mul_left, p.tsum_coe, mul_one]

/-- **Uniform with abort against uniform on the allowed values.** A map that sends every
disallowed point to `none`, applied to the uniform law and to the uniform law on the allowed
points, gives laws within the disallowed fraction. -/
theorem restrict_etvDist_le {X β : Type} [Fintype X] [Nonempty X] (allowed : X → Prop)
    [DecidablePred allowed] [Nonempty {x // allowed x}] (g : X → Option β)
    (blocked : ∀ x, ¬ allowed x → g x = none) :
    ((PMF.uniformOfFintype X).map g).etvDist
        ((PMF.uniformOfFintype {x // allowed x}).map (g ∘ Subtype.val)) ≤
      (Fintype.card {x // ¬ allowed x} : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) := by
  classical
  let cut : X → Option X := fun x => if allowed x then some x else none
  have factor : g = (fun value : Option X => value.bind g) ∘ cut := by
    funext x
    by_cases hx : allowed x
    · simp [cut, hx]
    · simp [cut, hx, blocked x hx]
  have factorRestricted : g ∘ (Subtype.val : {x // allowed x} → X) =
      (fun value : Option X => value.bind g) ∘ (cut ∘ (Subtype.val : {x // allowed x} → X)) := by
    rw [← Function.comp_assoc, ← factor]
  have left : (PMF.uniformOfFintype X).map g =
      ((PMF.uniformOfFintype X).map cut).map (fun value : Option X => value.bind g) := by
    rw [PMF.map_comp, ← factor]
  have right : (PMF.uniformOfFintype {x // allowed x}).map (g ∘ Subtype.val) =
      ((PMF.uniformOfFintype {x // allowed x}).map (cut ∘ Subtype.val)).map
        (fun value : Option X => value.bind g) := by
    rw [PMF.map_comp, ← factorRestricted]
  rw [left, right]
  refine le_trans (PMF.etvDist_map_le _ _ _) ?_
  rw [PMF.etvDist_comm, etvDist_eq_tsum_tsub, ENNReal.tsum_eq_add_tsum_ite none]
  have restrictedNone : ((PMF.uniformOfFintype {x // allowed x}).map (cut ∘ Subtype.val)) none
      = 0 := by
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => if_neg ?_
    simp [cut, x.2]
  have noneMass : ((PMF.uniformOfFintype X).map cut) none =
      (Fintype.card {x // ¬ allowed x} : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) := by
    rw [uniform_map_apply, div_eq_mul_inv]
    congr 2
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by by_cases hx : allowed x <;>
      simp [cut, hx])
  have someMass : ∀ x : X, ((PMF.uniformOfFintype X).map cut) (some x) ≤
      ((PMF.uniformOfFintype {x // allowed x}).map (cut ∘ Subtype.val)) (some x) := by
    intro x
    rw [uniform_map_apply, uniform_map_apply]
    by_cases hx : allowed x
    · have left : Fintype.card {y : X // cut y = some x} = 1 := by
        rw [Fintype.card_eq_one_iff]
        refine ⟨⟨x, by simp [cut, hx]⟩, fun y => Subtype.ext ?_⟩
        have hy := y.2
        by_cases hy' : allowed y.1
        · simp only [cut, hy', if_true, Option.some.injEq] at hy
          exact hy
        · simp [cut, hy'] at hy
      have right : Fintype.card {y : {x // allowed x} // (cut ∘ Subtype.val) y = some x} = 1 := by
        rw [Fintype.card_eq_one_iff]
        refine ⟨⟨⟨x, hx⟩, by simp [cut, hx]⟩, fun y => Subtype.ext (Subtype.ext ?_)⟩
        have hy := y.2
        simp only [Function.comp_apply, cut, y.1.2, if_true, Option.some.injEq] at hy
        exact hy
      rw [left, right, Nat.cast_one, one_mul, one_mul]
      exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Fintype.card_subtype_le _))
    · have left : Fintype.card {y : X // cut y = some x} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        refine ⟨fun y => ?_⟩
        have hy := y.2
        by_cases hy' : allowed y.1
        · simp only [cut, hy', if_true, Option.some.injEq] at hy
          exact hx (hy ▸ hy')
        · simp [cut, hy'] at hy
      rw [left, Nat.cast_zero, zero_mul]
      exact zero_le
  rw [noneMass, restrictedNone, tsub_zero]
  refine le_trans (add_le_add le_rfl (le_of_eq (ENNReal.tsum_eq_zero.mpr fun value => ?_)))
    (le_of_eq (add_zero _))
  split_ifs with isNone
  · rfl
  · obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp isNone
    exact tsub_eq_zero_of_le (someMass x)

/-! ### The frame of a lazy query -/

/-- A lazy query changes the fixed-key state only at the index it touches. -/
theorem query_frame (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) (index : FixedIndex)
    (other : touchedIndex request ≠ some index) : answer.2.fixed index = oracle.fixed index := by
  cases request with
  | fixedForward touched input =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have different : index ≠ touched := fun same => other (by rw [same]; rfl)
      exact Function.update_of_ne different _ _
  | fixedInverse touched output =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have different : index ≠ touched := fun same => other (by rw [same]; rfl)
      exact Function.update_of_ne different _ _
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | hash _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl

/-! ### The potential: entries at the untouched mask-site indices -/

open Classical in
/-- The entries at the mask-site indices that stage 2 has not touched yet. -/
def potential (touched : Set FixedIndex) (oracle : LState) : ℝ≥0∞ :=
  ∑ cell : Cell, if siteIndex cell ∈ touched then 0 else
    (((oracle.fixed (siteIndex cell)).used : ℕ) : ℝ≥0∞)

/-- A query that changes the state only at the index it touches does not raise the potential. -/
theorem potential_touch_le (request : Request) (touched : Set FixedIndex)
    (oracle updated : LState)
    (frame : ∀ index, touchedIndex request ≠ some index → updated.fixed index = oracle.fixed index) :
    potential (touch request touched) updated ≤ potential touched oracle := by
  classical
  unfold potential
  refine Finset.sum_le_sum fun cell _ => ?_
  by_cases inTouch : siteIndex cell ∈ touch request touched
  · rw [if_pos inTouch]
    exact zero_le
  · have notTouched : siteIndex cell ∉ touched := fun member => inTouch (Or.inl member)
    have notNow : touchedIndex request ≠ some (siteIndex cell) := fun same => inTouch (Or.inr same)
    rw [if_neg inTouch, if_neg notTouched, frame _ notNow]

/-- **A consumed index pays its entries once.** -/
theorem potential_consume (touched : Set FixedIndex) (oracle updated : LState) (cell : Cell)
    (index : FixedIndex) (input : Block) (notTouched : index ∉ touched)
    (site : siteIndex cell = index)
    (frame : ∀ other, other ≠ index → updated.fixed other = oracle.fixed other) :
    potential touched oracle =
      (((oracle.fixed index).used : ℕ) : ℝ≥0∞) +
        potential (touch (.fixedForward index input) touched) updated := by
  classical
  unfold potential
  have termwise : ∀ other : Cell,
      (if siteIndex other ∈ touched then (0 : ℝ≥0∞) else
          (((oracle.fixed (siteIndex other)).used : ℕ) : ℝ≥0∞)) =
        (if siteIndex other ∈ touch (.fixedForward index input) touched then (0 : ℝ≥0∞) else
          (((updated.fixed (siteIndex other)).used : ℕ) : ℝ≥0∞)) +
        (if other = cell then (((oracle.fixed index).used : ℕ) : ℝ≥0∞) else 0) := by
    intro other
    by_cases same : other = cell
    · subst same
      have inTouch : siteIndex other ∈ touch (.fixedForward index input) touched :=
        Or.inr (by rw [site]; rfl)
      rw [if_pos inTouch, if_pos rfl, zero_add, site, if_neg notTouched]
    · have indexNe : siteIndex other ≠ index := fun equal =>
        same (siteIndex_injective (equal.trans site.symm))
      have touchIff : siteIndex other ∈ touch (.fixedForward index input) touched ↔
          siteIndex other ∈ touched := by
        constructor
        · rintro (member | equal)
          · exact member
          · exact absurd (Option.some.inj equal).symm indexNe
        · exact fun member => Or.inl member
      rw [if_neg same, add_zero]
      by_cases hother : siteIndex other ∈ touched
      · rw [if_pos hother, if_pos (touchIff.mpr hother)]
      · rw [if_neg hother, if_neg (fun m => hother (touchIff.mp m)), frame _ indexNe]
  rw [Finset.sum_congr rfl fun other _ => termwise other, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ cell, if_pos (Finset.mem_univ _), add_comm]

/-! ### One consumed query -/

/-- `Block ≃ Fin (2^128)`. -/
def blockFinEquiv : Block ≃ Fin (2 ^ 128) where
  toFun block := block.toFin
  invFun value := BitVec.ofFin value
  left_inv _ := rfl
  right_inv _ := rfl

/-- The known outputs of a sparse permutation are exactly `used` many. -/
theorem card_knownOutput {size : ℕ} (state : SparsePermutation size) :
    Fintype.card {output : Fin size // state.knownOutput output} = state.used := by
  have shift : {output : Fin size // state.knownOutput output} ≃ {position : Fin size //
      position < state.used} :=
    Equiv.subtypeEquiv state.output.symm fun _ => Iff.rfl
  rw [Fintype.card_congr shift, Fintype.card_fin_lt_of_le state.within]

/-- **One consumed query, on one sparse permutation.** At a fresh input, the programmed uniform
limb against the lazy forward draw: within `used / 2^128`. -/
theorem program_forward_etvDist_le {S : Type} (state : SparsePermutation (2 ^ 128))
    (input : Block) (fresh : ¬ state.knownInput input.toFin) (place : SparsePermutation (2 ^ 128) → S) :
    ((PMF.uniformOfFintype Block).map fun limb =>
        (LazyOracle.permutationProgram state input.toFin (limb ^^^ input).toFin).map
          fun next => (limb ^^^ input, place next)).etvDist
      (((state.forward input.toFin).distribution.map
          fun answer => (BitVec.ofFin answer.1, place answer.2)).map some) ≤
      ((state.used : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  classical
  have unknown : ¬ (state.input.symm input.toFin).val < state.used := fresh
  have room : state.used < 2 ^ 128 := by
    have := (state.input.symm input.toFin).isLt; omega
  let answerOf : Fin (2 ^ 128) → Option (Block × S) := fun output =>
    if state.knownOutput output then none
    else some (BitVec.ofFin output,
      place (state.extend room (state.input.symm input.toFin) (state.output.symm output)))
  have : Nonempty {output : Fin (2 ^ 128) // ¬ state.knownOutput output} :=
    ⟨state.unusedOutputEquiv ⟨0, by omega⟩⟩
  have programmed : ((PMF.uniformOfFintype Block).map fun limb =>
        (LazyOracle.permutationProgram state input.toFin (limb ^^^ input).toFin).map
          fun next => (limb ^^^ input, place next)) =
      (PMF.uniformOfFintype (Fin (2 ^ 128))).map answerOf := by
    have equiv : (PMF.uniformOfFintype Block).map ((xorEquiv input).trans blockFinEquiv) =
        PMF.uniformOfFintype (Fin (2 ^ 128)) := uniform_equiv _
    rw [← equiv, PMF.map_comp]
    congr 1
    funext limb
    show _ = answerOf (limb ^^^ input).toFin
    simp only [LazyOracle.permutationProgram, answerOf]
    by_cases used : state.knownOutput (limb ^^^ input).toFin
    · rw [if_pos used, dif_neg (fun both => both.2 used)]
      rfl
    · rw [if_neg used, dif_pos ⟨fresh, used⟩]
      rfl
  have lazy : ((state.forward input.toFin).distribution.map
          fun answer => (BitVec.ofFin answer.1, place answer.2)).map some =
      (PMF.uniformOfFintype {output : Fin (2 ^ 128) // ¬ state.knownOutput output}).map
        (answerOf ∘ Subtype.val) := by
    rw [← state.unusedOutput_uniform room, PMF.map_comp]
    unfold SparsePermutation.forward
    simp only [dif_neg unknown, Draw.distribution, PMF.map_comp]
    congr 1
    funext rank
    simp only [Function.comp_apply, answerOf, SparsePermutation.unusedOutputEquiv,
      Equiv.coe_fn_mk]
    rw [if_neg (by simp [SparsePermutation.knownOutput, SparsePermutation.suffix]),
      Equiv.symm_apply_apply]
  rw [programmed, lazy]
  refine le_trans (restrict_etvDist_le (fun output => ¬ state.knownOutput output) answerOf
    fun output blocked => by simp only [answerOf, if_pos (not_not.mp blocked)]) (le_of_eq ?_)
  have cardUsed : Fintype.card {output : Fin (2 ^ 128) // ¬ ¬ state.knownOutput output} =
      state.used := by
    rw [← card_knownOutput state]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_not)
  rw [cardUsed, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-- **One consumed query** of the lazy oracle: the programmed uniform limb against the lazy
forward query, within `used / 2^128`. -/
theorem consume_step_etvDist_le (oracle : LState) (index : FixedIndex) (input : Block)
    (fresh : ¬ (oracle.fixed index).knownInput input.toFin) :
    ((PMF.uniformOfFintype Block).map fun limb =>
        (LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle).map
          fun updated => (limb ^^^ input, updated)).etvDist
      ((LazyOracle.query (.fixedForward index input) oracle).map some) ≤
      (((oracle.fixed index).used : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  have bound := program_forward_etvDist_le (oracle.fixed index) input fresh
    (fun next => { oracle with fixed := Function.update oracle.fixed index next })
  have programSide : ((PMF.uniformOfFintype Block).map fun limb =>
        (LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle).map
          fun updated => (limb ^^^ input, updated)) =
      ((PMF.uniformOfFintype Block).map fun limb =>
        (LazyOracle.permutationProgram (oracle.fixed index) input.toFin (limb ^^^ input).toFin).map
          fun next => (limb ^^^ input,
            ({ oracle with fixed := Function.update oracle.fixed index next } : LState))) := by
    congr 1
    funext limb
    simp only [LazyOracle.program, Option.map_map]
    rfl
  rw [programSide]
  exact bound

end

end Kriterion.ArgoMAC.Phase3.Lazy
