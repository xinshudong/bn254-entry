/-
**Phase 3, P1m — (B1) the fixed-key part: three potentials.**

A forward lazy question at a permutation index draws its answer uniformly among the unused outputs;
each potential below is not raised in expectation by any forward question (`*_step`), ignores the
mask-site and designated indices (so the refill run's consumed programs and the designated
installation leave it unchanged), and bounds the corresponding indicator at a state with the right
number of pairs:

* `singlePot i y` — the mass with which `y` becomes the (only) output at `i`: `1/2^128` before the
  first pair, the indicator after, `0` beyond;
* `foldPot i₀ i₁ z` — the mass with which the two (only) outputs at `i₀ ≠ i₁` xor to `z`:
  `1/2^128` until both are drawn, the indicator after, `0` beyond one pair at either;
* `padPot j w t` — the mass with which the EncPRF permutation `j` maps `w` to `t`: `1/(2^128 − 1)`
  while `w` is unasked and at most one other input is, the indicator after (at most two pairs), `0`
  beyond.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedStruct

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source IsDesignated interceptAnswer)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ runRefill consumeCell
  refillAnswer consumeCell_spec cellOf card_unusedOutput)
open scoped ENNReal

noncomputable section

/-! ### One fresh forward answer -/

section Perm

/-- `1/2^128`. -/
abbrev delta : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹

theorem delta_le_epsOne : delta ≤ epsOne :=
  ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.sub_le _ _)

/-- A fresh answer at a permutation with `n` pairs hits a point with mass `≤ 1/(2^128 − n)`. -/
theorem fresh_hit_le (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)] (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤
      ((2 ^ 128 - S.used : ℕ) : ℝ≥0∞)⁻¹ :=
  unknown_single_le S y

theorem fresh_hit_le_delta (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)]
    (zero : S.used = 0) (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤ delta := by
  refine le_trans (fresh_hit_le S y) (le_of_eq ?_)
  rw [zero, Nat.sub_zero]

theorem fresh_hit_le_eps (S : SparsePermutation (2 ^ 128)) [Nonempty (Unknown S)]
    (small : S.used ≤ 1) (y : Fin (2 ^ 128)) :
    ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out * ind (out.val = y) ≤ epsOne := by
  refine le_trans (fresh_hit_le S y) (ENNReal.inv_le_inv.mpr ?_)
  exact_mod_cast Nat.sub_le_sub_left small _

/-- **The effect of a forward question on one permutation**: a stored input changes nothing; a new
one adds one pair with a uniform unused output. -/
theorem perm_step (F : SparsePermutation (2 ^ 128) → ℝ≥0∞) (S : SparsePermutation (2 ^ 128))
    (x : Fin (2 ^ 128))
    (fresh : ∀ (_ : ¬ S.knownInput x) (room : S.used < 2 ^ 128) [Nonempty (Unknown S)],
      ∑' out : Unknown S, PMF.uniformOfFintype (Unknown S) out *
        F (S.extend room (S.input.symm x) (S.output.symm out.val)) ≤ F S) :
    ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S := by
  by_cases known : S.knownInput x
  · have pure : (S.forward x).distribution = PMF.pure (S.output (S.input.symm x), S) := by
      unfold SparsePermutation.forward
      simp only [SparsePermutation.knownInput] at known
      rw [dif_pos known]
      rfl
    rw [pure, tsum_pure_mul]
  · obtain ⟨room, nonempty, law⟩ := forward_fresh_eq S x known
    rw [law, tsum_map_mul]
    exact fresh known room

/-- A permutation with one pair knows exactly one output. -/
theorem knownOutput_one (S : SparsePermutation (2 ^ 128)) (one : S.used = 1) (b : Fin (2 ^ 128)) :
    S.knownOutput b ↔ b = S.output ⟨0, Nat.two_pow_pos 128⟩ := by
  unfold SparsePermutation.knownOutput
  rw [one]
  constructor
  · intro small
    have zero : S.output.symm b = ⟨0, Nat.two_pow_pos 128⟩ := Fin.ext (Nat.lt_one_iff.mp small)
    rw [← zero, Equiv.apply_symm_apply]
  · rintro rfl
    rw [Equiv.symm_apply_apply]
    exact Nat.zero_lt_one

theorem knownInput_extend (S : SparsePermutation (2 ^ 128)) (x y : Fin (2 ^ 128))
    (freshX : ¬ S.knownInput x) (freshY : ¬ S.knownOutput y) (room : S.used < 2 ^ 128)
    (z : Fin (2 ^ 128)) :
    (S.extend room (S.input.symm x) (S.output.symm y)).knownInput z ↔ S.knownInput z ∨ z = x := by
  rw [knownInput_iff, knownInput_iff, lookup_extend S x y freshX freshY room z]
  by_cases same : z = x
  · simp [same]
  · simp [same]

/-! #### The single-output potential -/

open Classical in
/-- **The single-output potential of one permutation.** -/
def singleF (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if S.used = 0 then delta else if S.used = 1 then ind (S.knownOutput y) else 0

theorem singleF_step (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (S.forward x).distribution answer * singleF y answer.2 ≤ singleF y S := by
  refine perm_step _ S x fun notKnown room _ => ?_
  have outputs : ∀ out : Unknown S, (S.extend room (S.input.symm x)
      (S.output.symm out.val)).knownOutput y ↔ S.knownOutput y ∨ y = out.val :=
    fun out => knownOutput_extend _ _ _ notKnown out.2 room y
  simp only [singleF, extend_used, outputs]
  have n0 : S.used + 1 ≠ 0 := by omega
  by_cases h0 : S.used = 0
  · have noneKnown : ¬ S.knownOutput y := by
      unfold SparsePermutation.knownOutput
      omega
    have n1 : S.used + 1 = 1 := by omega
    rw [if_pos h0]
    simp only [n0, n1, if_false, if_true, noneKnown, false_or]
    refine le_trans (le_of_eq (tsum_congr fun out => ?_)) (fresh_hit_le_delta S h0 y)
    congr 1
    exact congrArg ind (propext ⟨fun h => h.symm, fun h => h.symm⟩)
  · have n1 : S.used + 1 ≠ 1 := by omega
    by_cases h1 : S.used = 1
    · have n2 : S.used + 1 = 2 := by omega
      simp only [n0, n1, if_false, mul_zero, tsum_zero]
      exact zero_le
    · simp only [n0, n1, if_false, mul_zero, tsum_zero]
      exact zero_le

/-- At a state with at most one pair, the output indicator is below the potential. -/
theorem singleF_bound (y : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (small : S.used ≤ 1) :
    ind (∃ x, lk S x = some y) ≤ singleF y S := by
  by_cases hit : ∃ x, lk S x = some y
  · rw [ind_pos hit]
    have known : S.knownOutput y := (knownOutput_iff _ _).mpr hit
    have positive : S.used ≠ 0 := by
      intro zero
      unfold SparsePermutation.knownOutput at known
      omega
    have one : S.used = 1 := by omega
    unfold singleF
    rw [if_neg positive, if_pos one, ind_pos known]
  · rw [ind_neg hit]
    exact zero_le

/-! #### The fold potential -/

open Classical in
/-- **The fold potential of two permutations**: their (only) outputs xor to `z`. -/
def foldF (z : Block) (S T : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if S.used ≤ 1 ∧ T.used ≤ 1 then
    (if S.used = 1 ∧ T.used = 1 then
      ind (∃ a b, S.knownOutput a ∧ T.knownOutput b ∧ BitVec.ofFin a ^^^ BitVec.ofFin b = z)
    else delta)
  else 0

theorem foldF_step₀ (z : Block) (S T : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (S.forward x).distribution answer * foldF z answer.2 T ≤ foldF z S T := by
  refine perm_step (fun S' => foldF z S' T) S x fun notKnown room _ => ?_
  have outputs : ∀ (out : Unknown S) (a : Fin (2 ^ 128)), (S.extend room (S.input.symm x)
      (S.output.symm out.val)).knownOutput a ↔ S.knownOutput a ∨ a = out.val :=
    fun out a => knownOutput_extend _ _ _ notKnown out.2 room a
  simp only [foldF, extend_used, outputs]
  by_cases h0 : S.used = 0
  · have noneKnown : ∀ a, ¬ S.knownOutput a := fun a known => by
      unfold SparsePermutation.knownOutput at known
      omega
    simp only [h0, noneKnown, false_or, zero_add, le_refl, true_and, zero_ne_one, false_and,
      if_false]
    by_cases t1 : T.used ≤ 1
    · simp only [t1, if_true, Nat.zero_le, true_and]
      by_cases t1' : T.used = 1
      · simp only [t1', and_self, if_true]
        have single : ∀ out : Unknown S, ind (∃ a b, a = out.val ∧ T.knownOutput b ∧
            BitVec.ofFin a ^^^ BitVec.ofFin b = z) =
            ind (out.val = (z ^^^ BitVec.ofFin (T.output ⟨0, Nat.two_pow_pos 128⟩)).toFin) := by
          intro out
          congr 1
          apply propext
          constructor
          · rintro ⟨a, b, rfl, known, same⟩
            rw [knownOutput_one T t1' b] at known
            subst known
            rw [← same, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.toFin_ofFin]
          · intro same
            refine ⟨out.val, _, rfl, (knownOutput_one T t1' _).mpr rfl, ?_⟩
            rw [same, BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        simp only [single]
        exact fresh_hit_le_delta S h0 _
      · simp only [t1', and_false, if_false]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    · simp only [t1, and_false, if_false, mul_zero, tsum_zero, le_refl]
  · by_cases h1 : S.used = 1
    · have big : ¬ S.used + 1 ≤ 1 := by omega
      simp only [big, false_and, if_false, mul_zero, tsum_zero]
      exact zero_le
    · have big : ¬ S.used + 1 ≤ 1 := by omega
      simp only [big, false_and, if_false, mul_zero, tsum_zero]
      exact zero_le

theorem foldF_step₁ (z : Block) (S T : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (T.forward x).distribution answer * foldF z S answer.2 ≤ foldF z S T := by
  refine perm_step (fun T' => foldF z S T') T x fun notKnown room _ => ?_
  have outputs : ∀ (out : Unknown T) (b : Fin (2 ^ 128)), (T.extend room (T.input.symm x)
      (T.output.symm out.val)).knownOutput b ↔ T.knownOutput b ∨ b = out.val :=
    fun out b => knownOutput_extend _ _ _ notKnown out.2 room b
  simp only [foldF, extend_used, outputs]
  by_cases h0 : T.used = 0
  · have noneKnown : ∀ b, ¬ T.knownOutput b := fun b known => by
      unfold SparsePermutation.knownOutput at known
      omega
    simp only [h0, noneKnown, false_or, zero_add, le_refl, and_true, zero_ne_one, and_false,
      if_false]
    by_cases s1 : S.used ≤ 1
    · simp only [s1, if_true, Nat.zero_le, and_true]
      by_cases s1' : S.used = 1
      · simp only [s1', and_self, if_true]
        have single : ∀ out : Unknown T, ind (∃ a b, S.knownOutput a ∧ b = out.val ∧
            BitVec.ofFin a ^^^ BitVec.ofFin b = z) =
            ind (out.val = (BitVec.ofFin (S.output ⟨0, Nat.two_pow_pos 128⟩) ^^^ z).toFin) := by
          intro out
          congr 1
          apply propext
          constructor
          · rintro ⟨a, b, known, rfl, same⟩
            rw [knownOutput_one S s1' a] at known
            subst known
            rw [← same, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.toFin_ofFin]
          · intro same
            refine ⟨_, out.val, (knownOutput_one S s1' _).mpr rfl, rfl, ?_⟩
            rw [same, BitVec.ofFin_toFin, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
        simp only [single]
        exact fresh_hit_le_delta T h0 _
      · simp only [s1', false_and, if_false]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    · simp only [s1, false_and, if_false, mul_zero, tsum_zero, le_refl]
  · have big : ¬ T.used + 1 ≤ 1 := by omega
    simp only [big, and_false, if_false, mul_zero, tsum_zero]
    exact zero_le

/-- At two single-pair states, the xor indicator of their outputs is below the potential. -/
theorem foldF_bound (z : Block) (S T : SparsePermutation (2 ^ 128)) (s1 : S.used = 1)
    (t1 : T.used = 1) (x₀ x₁ a b : Fin (2 ^ 128)) (found₀ : lk S x₀ = some a)
    (found₁ : lk T x₁ = some b) :
    ind (BitVec.ofFin a ^^^ BitVec.ofFin b = z) ≤ foldF z S T := by
  unfold foldF
  rw [if_pos ⟨s1.le, t1.le⟩, if_pos ⟨s1, t1⟩]
  exact ind_mono fun same =>
    ⟨a, b, (knownOutput_iff _ _).mpr ⟨x₀, found₀⟩, (knownOutput_iff _ _).mpr ⟨x₁, found₁⟩, same⟩

/-! #### The pad potential -/

open Classical in
/-- **The pad potential of one EncPRF permutation**: `w` is mapped to `t`. -/
def padF (w t : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) : ℝ≥0∞ :=
  if S.knownInput w then (if S.used ≤ 2 then ind (lk S w = some t) else 0)
  else (if S.used ≤ 1 then epsOne else 0)

theorem padF_step (w t : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128)) (x : Fin (2 ^ 128)) :
    ∑' answer, (S.forward x).distribution answer * padF w t answer.2 ≤ padF w t S := by
  refine perm_step _ S x fun notKnown room _ => ?_
  have inputs : ∀ out : Unknown S, (S.extend room (S.input.symm x)
      (S.output.symm out.val)).knownInput w ↔ S.knownInput w ∨ w = x :=
    fun out => knownInput_extend _ _ _ notKnown out.2 room w
  have lookups : ∀ out : Unknown S, lk (S.extend room (S.input.symm x) (S.output.symm out.val)) w =
      if w = x then some out.val else lk S w :=
    fun out => lookup_extend S x out.val notKnown out.2 room w
  simp only [padF, extend_used, inputs, lookups]
  by_cases same : w = x
  · subst same
    simp only [notKnown, or_true, if_true, false_or, if_false]
    by_cases small : S.used ≤ 1
    · have small' : S.used + 1 ≤ 2 := by omega
      simp only [small', if_true, small, Option.some.injEq]
      exact fresh_hit_le_eps S small t
    · have big : ¬ S.used + 1 ≤ 2 := by omega
      simp only [big, if_false, small, mul_zero, tsum_zero, le_refl]
  · simp only [same, or_false, if_false]
    by_cases known : S.knownInput w
    · simp only [known, if_true]
      by_cases small : S.used + 1 ≤ 2
      · have small' : S.used ≤ 2 := by omega
        simp only [small, small', if_true]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      · simp only [small, if_false, mul_zero, tsum_zero]
        exact zero_le
    · simp only [known, if_false]
      by_cases zero : S.used = 0
      · have small : S.used + 1 ≤ 1 := by omega
        have small' : S.used ≤ 1 := by omega
        simp only [small, small', if_true]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      · have big : ¬ S.used + 1 ≤ 1 := by omega
        simp only [big, if_false, mul_zero, tsum_zero]
        exact zero_le

/-- With `w` stored and at most two pairs, the indicator of `w ↦ t` is the potential. -/
theorem padF_bound (w t v : Fin (2 ^ 128)) (S : SparsePermutation (2 ^ 128))
    (found : lk S w = some v) (small : S.used ≤ 2) : ind (v = t) ≤ padF w t S := by
  have known : S.knownInput w := (knownInput_iff _ _).mpr (by rw [found]; exact Option.some_ne_none _)
  unfold padF
  rw [if_pos known, if_pos small, found]
  exact ind_mono fun same => by rw [same]

end Perm

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Lifting a permutation potential to the lazy state -/

section Lift

/-- **A potential of one fixed-key permutation, not raised by its forward questions, is not raised
by any forward question.** -/
theorem fixed_lift_step (i : FixedIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (step : ∀ S x, ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * F (answer.2.fixed i) ≤ F (state.fixed i) := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      F (answer.2.fixed i) ≤ _
    rw [tsum_map_mul]
    by_cases same : i = index
    · subst same
      simp only [Function.update_self]
      exact step _ _
    · simp only [Function.update_of_ne same]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      F (answer.2.fixed i) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer * F (answer.2.fixed i) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The same for one EncPRF permutation. -/
theorem enc_lift_step (j : EncPRF.PermutationIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (step : ∀ S x, ∑' answer, (S.forward x).distribution answer * F answer.2 ≤ F S)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * F (answer.2.enc j) ≤ F (state.enc j) := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    by_cases same : j = index
    · subst same
      simp only [Function.update_self]
      exact step _ _
    · simp only [Function.update_of_ne same]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer * F (answer.2.enc j) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **A potential of two fixed-key permutations**, not raised by forward questions at either. -/
theorem fixed2_lift_step (i₀ i₁ : FixedIndex) (different : i₀ ≠ i₁)
    (F : SparsePermutation (2 ^ 128) → SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (step₀ : ∀ S T x, ∑' answer, (S.forward x).distribution answer * F answer.2 T ≤ F S T)
    (step₁ : ∀ S T x, ∑' answer, (T.forward x).distribution answer * F S answer.2 ≤ F S T)
    (request : Request) (forward : ForwardOnly request) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * F (answer.2.fixed i₀) (answer.2.fixed i₁) ≤
      F (state.fixed i₀) (state.fixed i₁) := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      F (answer.2.fixed i₀) (answer.2.fixed i₁) ≤ _
    rw [tsum_map_mul]
    by_cases zero : i₀ = index
    · subst zero
      simp only [Function.update_self, Function.update_of_ne (Ne.symm different)]
      exact step₀ _ _ _
    · by_cases one : i₁ = index
      · subst one
        simp only [Function.update_self, Function.update_of_ne zero]
        exact step₁ _ _ _
      · simp only [Function.update_of_ne zero, Function.update_of_ne one]
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      F (answer.2.fixed i₀) (answer.2.fixed i₁) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer *
        F (answer.2.fixed i₀) (answer.2.fixed i₁) ≤ _
    rw [tsum_map_mul]
    dsimp only
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Lift

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
