/-
**Phase 3, P1g — the flagged refill without intercepts, and its uniform reading.**

`runFillFlag planted draw` is P4's refill runner without the designated intercepts, stopped
(`none`) at the first touch of `planted` (and at a failed program): the first forward question at
an untouched mask-site index programs `input ↦ limb xor input` with `limb` drawn from `draw`; every
other question is lazy. It is the off-curve private run of the middle game `M'`
(`PublicFirst/MiddleOff.lean`), where the limbs come from P4's `uniformMaskTape` (uniform masks, as
`G1U`'s swapped system-A entries).

* `uniform_bind_runFillFlag` — a uniform tape is a fresh uniform limb at each consumed cell (P4's
  `uniform_bind_runRefill`, for this runner);
* `runFillFlag_uniform_eq` — **with fresh uniform limbs, on a state whose untouched mask-site
  indices are empty, the runner is the flagged lazy run** `runLazyQFlag` (a program at an empty
  index never fails, and its answer is a uniform block, as a fresh lazy answer).
-/

import Proof.Privacy.Phase3.PublicFirst.Private
import Proof.Privacy.Phase3.Lazy.EagerLazy

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape consumeCell refillAnswer touch touchedIndex
  subset_touch consumeCell_spec uniform_update_eq uniform_pair_bind)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The flagged refill runner without intercepts.** -/
def runFillFlag (planted : LState) (draw : Cell → PMF Block) {α : Type} :
    FreeQuery Programs.Spec α → LState → Set FixedIndex → PMF (Option (α × LState))
  | .pure value, oracle, _ => PMF.pure (some (value, oracle))
  | .query request next, oracle, touched =>
      match consumeCell touched oracle request with
      | some cell => (draw cell).bind fun limb =>
          if FullTouch planted request (refillAnswer request limb) then PMF.pure none else
          match LazyOracle.program request (refillAnswer request limb) oracle with
          | none => PMF.pure none
          | some updated =>
              runFillFlag planted draw (next (refillAnswer request limb)) updated
                (touch request touched)
      | none => (LazyOracle.query request oracle).bind fun answer =>
          if FullTouch planted request answer.1 then PMF.pure none else
          runFillFlag planted draw (next answer.1) answer.2 (touch request touched)

/-- The run reads the tape only at untouched indices. -/
theorem runFillFlag_tape_congr (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set FixedIndex) (first second : Tape),
      (∀ cell, siteIndex cell ∉ touched → first cell = second cell) →
      runFillFlag planted (fun cell => PMF.pure (first cell)) computation oracle touched =
        runFillFlag planted (fun cell => PMF.pure (second cell)) computation oracle touched := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle touched first second agree
      have later : ∀ cell, siteIndex cell ∉ touch request touched → first cell = second cell :=
        fun cell notTouched => agree cell fun member => notTouched (subset_touch _ _ member)
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        obtain ⟨index, input, rfl, fresh, _, siteEq⟩ := consumeCell_spec consumed
        have same : first cell = second cell := agree cell (siteEq ▸ fresh)
        rw [same]
        congr 1
        funext limb
        split
        · rfl
        · split
          · rfl
          · exact ih _ _ _ _ _ later
      · congr 1
        funext answer
        split
        · rfl
        · exact ih _ _ _ _ _ later

/-- **Eager = lazy for the fill runner**: a uniform tape is a fresh uniform limb per consumed
cell. -/
theorem uniform_bind_runFillFlag (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set FixedIndex),
      (PMF.uniformOfFintype Tape).bind (fun tape =>
          runFillFlag planted (fun cell => PMF.pure (tape cell)) computation oracle touched) =
        runFillFlag planted (fun _ => PMF.uniformOfFintype Block) computation oracle touched := by
  induction computation with
  | pure value =>
      intro oracle touched
      exact PMF.bind_const _ _
  | query request next ih =>
      intro oracle touched
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        obtain ⟨index, input, rfl, fresh, _, siteEq⟩ := consumeCell_spec consumed
        simp only [PMF.pure_bind]
        conv_lhs => rw [← uniform_update_eq cell, PMF.bind_map]
        have local_read : ∀ (limb : Block) (tape : Tape),
            (if FullTouch planted (.fixedForward index input)
                (refillAnswer (.fixedForward index input) limb) then PMF.pure none else
              match LazyOracle.program (.fixedForward index input)
                  (refillAnswer (.fixedForward index input) limb) oracle with
              | none => PMF.pure none
              | some updated => runFillFlag planted
                  (fun cell' => PMF.pure (Function.update tape cell limb cell'))
                  (next (refillAnswer (.fixedForward index input) limb)) updated
                  (touch (.fixedForward index input) touched)) =
            (if FullTouch planted (.fixedForward index input)
                (refillAnswer (.fixedForward index input) limb) then PMF.pure none else
              match LazyOracle.program (.fixedForward index input)
                  (refillAnswer (.fixedForward index input) limb) oracle with
              | none => PMF.pure none
              | some updated => runFillFlag planted (fun cell' => PMF.pure (tape cell'))
                  (next (refillAnswer (.fixedForward index input) limb)) updated
                  (touch (.fixedForward index input) touched)) := by
          intro limb tape
          split
          · rfl
          · split
            · rfl
            · refine runFillFlag_tape_congr planted _ _ _ _ _ fun cell' notTouched => ?_
              have different : cell' ≠ cell := by
                rintro rfl
                exact notTouched (Or.inr (by rw [siteEq]; rfl))
              exact Function.update_of_ne different _ _
        simp only [Function.comp_def, Function.update_self]
        refine (congrArg (PMF.bind (PMF.uniformOfFintype (Block × Tape)))
          (funext fun pair => local_read pair.1 pair.2)).trans ?_
        rw [uniform_pair_bind]
        congr 1
        funext limb
        split
        · exact PMF.bind_const _ _
        · split
          · rename_i hprog
            simp only [hprog]
            exact PMF.bind_const _ _
          · rename_i updated hprog
            simp only [hprog]
            exact ih _ _ _
      · rw [PMF.bind_comm]
        congr 1
        funext answer
        split
        · exact PMF.bind_const _ _
        · exact ih _ _ _

/-! ### With fresh limbs, the fill is the lazy run -/

/-- Every mask-site index not yet touched is empty. -/
def UntouchedEmpty (oracle : LState) (touched : Set FixedIndex) : Prop :=
  ∀ cell : Cell, siteIndex cell ∉ touched → oracle.fixed (siteIndex cell) = SparsePermutation.empty _

theorem untouchedEmpty_empty : UntouchedEmpty (LazyOracle.empty : LState) ∅ := fun _ _ => rfl

/-- The one-pair permutation `input ↦ output`, built on the empty one. -/
def storedPerm (input output : Block) : SparsePermutation (2 ^ 128) :=
  (SparsePermutation.empty (2 ^ 128)).extend (Nat.two_pow_pos 128)
    ((SparsePermutation.empty (2 ^ 128)).input.symm input.toFin)
    ((SparsePermutation.empty (2 ^ 128)).output.symm output.toFin)

/-- The state after storing one pair at an empty index. -/
def storeOne (oracle : LState) (index : FixedIndex) (input output : Block) : LState :=
  { oracle with fixed := Function.update oracle.fixed index (storedPerm input output) }

/-- A program at an empty index succeeds, storing the pair. -/
theorem program_empty (oracle : LState) (index : FixedIndex) (input output : Block)
    (empty : oracle.fixed index = SparsePermutation.empty _) :
    LazyOracle.program (.fixedForward index input) output oracle
      = some (storeOne oracle index input output) := by
  simp only [LazyOracle.program, LazyOracle.permutationProgram, empty]
  rw [dif_pos ⟨fun known => by
      unfold SparsePermutation.knownInput at known
      exact absurd known (by show ¬ (_ < 0); omega),
    fun known => by
      unfold SparsePermutation.knownOutput at known
      exact absurd known (by show ¬ (_ < 0); omega)⟩]
  rfl

/-- The unknown outputs of the empty permutation are all blocks. -/
def emptyUnknownEquiv :
    {y : Fin (2 ^ 128) // ¬ (SparsePermutation.empty (2 ^ 128)).knownOutput y} ≃ Block where
  toFun y := BitVec.ofFin y.val
  invFun b := ⟨b.toFin, by
    unfold SparsePermutation.knownOutput
    show ¬ (_ < 0)
    omega⟩
  left_inv y := rfl
  right_inv b := rfl

/-- **A lazy question at an empty index is a uniform block, stored.** -/
theorem query_empty (oracle : LState) (index : FixedIndex) (input : Block)
    (empty : oracle.fixed index = SparsePermutation.empty _) :
    LazyOracle.query (.fixedForward index input) oracle =
      (PMF.uniformOfFintype Block).map fun output => (output, storeOne oracle index input output) := by
  have key : ∀ state : SparsePermutation (2 ^ 128), state = SparsePermutation.empty _ →
      (state.forward input.toFin).distribution.map (fun answer =>
        (BitVec.ofFin answer.1, ({ oracle with
          fixed := Function.update oracle.fixed index answer.2 } : LState))) =
      (PMF.uniformOfFintype Block).map fun output => (output, storeOne oracle index input output) := by
    intro state same
    subst same
    have fresh : ¬ (SparsePermutation.empty (2 ^ 128)).knownInput input.toFin := by
      show ¬ (_ < 0)
      omega
    obtain ⟨room, nonempty, law⟩ := forward_fresh_eq (SparsePermutation.empty (2 ^ 128))
      input.toFin fresh
    rw [law, PMF.map_comp, ← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
      emptyUnknownEquiv, PMF.map_comp]
    rfl
  exact key _ empty

/-- Binds agree when their continuations agree on the support. -/
theorem bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (agree : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  refine PMF.ext fun b => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases member : a ∈ p.support
  · rw [agree a member]
  · rw [(PMF.apply_eq_zero_iff p a).mpr member, zero_mul, zero_mul]

/-- The xor shift of a uniform block is uniform. -/
theorem uniform_bind_xor {β : Type} (mask : Block) (f : Block → PMF β) :
    (PMF.uniformOfFintype Block).bind (fun limb => f (limb ^^^ mask)) =
      (PMF.uniformOfFintype Block).bind f := by
  have shift : (PMF.uniformOfFintype Block).map (fun limb => limb ^^^ mask) =
      PMF.uniformOfFintype Block :=
    Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv
      (Kriterion.ArgoMAC.Phase3.Lazy.xorEquiv mask)
  calc (PMF.uniformOfFintype Block).bind (fun limb => f (limb ^^^ mask))
      = ((PMF.uniformOfFintype Block).map (fun limb => limb ^^^ mask)).bind f :=
        (PMF.bind_map _ _ _).symm
    _ = (PMF.uniformOfFintype Block).bind f := by rw [shift]

/-- **With fresh uniform limbs, the fill runner is the flagged lazy run**, on a state whose untouched
mask-site indices are empty. -/
theorem runFillFlag_uniform_eq (planted : LState) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (touched : Set FixedIndex), UntouchedEmpty oracle touched →
      runFillFlag planted (fun _ => PMF.uniformOfFintype Block) computation oracle touched =
        runLazyQFlag planted computation oracle := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle touched invariant
      simp only [runFillFlag, runLazyQFlag]
      split
      · rename_i cell consumed
        obtain ⟨index, input, rfl, notTouched, fresh, siteEq⟩ := consumeCell_spec consumed
        have empty : oracle.fixed index = SparsePermutation.empty _ := by
          rw [← siteEq]
          exact invariant cell (siteEq ▸ notTouched)
        have after : ∀ output : Block,
            UntouchedEmpty (storeOne oracle index input output)
              (touch (.fixedForward index input) touched) := by
          intro output other notTouched'
          have different : siteIndex other ≠ index := fun same =>
            notTouched' (Or.inr (by rw [same]; rfl))
          have untouched : siteIndex other ∉ touched := fun member =>
            notTouched' (Or.inl member)
          simp only [storeOne]
          rw [Function.update_of_ne different]
          exact invariant other untouched
        rw [query_empty oracle index input empty]
        refine Eq.trans ?_ (PMF.bind_map (PMF.uniformOfFintype Block)
          (fun output => (output, storeOne oracle index input output)) _).symm
        simp only [refillAnswer, program_empty oracle index input _ empty]
        refine (uniform_bind_xor input (fun output :
            (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer =>
          if FullTouch planted (.fixedForward index input) output then PMF.pure none else
          runFillFlag planted (fun _ => PMF.uniformOfFintype Block) (next output)
            (storeOne oracle index input output) (touch (.fixedForward index input) touched))).trans ?_
        congr 1
        funext output
        show (if _ then _ else _) = (if _ then _ else _)
        split
        · rfl
        · exact ih _ _ _ (after _)
      · refine bind_congr_support _ _ _ fun answer member => ?_
        split
        · rfl
        · refine ih _ _ _ fun other notTouched' => ?_
          have untouched : siteIndex other ∉ touched := fun inside =>
            notTouched' (Or.inl inside)
          have different : touchedIndex request ≠ some (siteIndex other) := fun same =>
            notTouched' (Or.inr same)
          rw [Kriterion.ArgoMAC.Phase3.Lazy.query_frame request oracle answer member _ different]
          exact invariant other untouched

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
