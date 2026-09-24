/-
**Phase 3, P1k — (B1) tools: forward-only programs, potentials along the refill run, and the two
EncPRF/hash potentials.**

* `ForwardOnly` — no inverse question; every program of `HW`'s opening and of the shadow is
  forward-only (`openingQueriesM_forwardOnly`, `shadowOnM_forwardOnly`).
* `runRefill_potential` — a potential reading only the EncPRF and hash parts, not raised in
  expectation by any lazy question of a program, is a supermartingale along P4's refill run (the
  consumed questions and the designated installation only program fixed-key indices).
* `keyPotential S` — the mass with which the (first) hash answer's first half lands in `S`:
  `|S|/2^128` while the hash table is empty, the indicator once it holds one key, `0` beyond
  (`keyPotential_step`).
* `outPotential j y` — the **exact** marginal mass with which `y` becomes an output of the EncPRF
  permutation `j`: `2/2^128` before its first pair, `1[a = y] + 1[a ≠ y]/(2^128 − 1)` after the
  first answer `a`, the indicator after the second, `0` beyond (`outPotential_step`). Using the
  marginal (not the conditional `1/(2^128 − 1)` twice) is what keeps the EncPRF per-pair mass at
  exactly `4/2^128`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsRevealBound

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape runRefill consumeCell refillAnswer
  consumeCell_spec AllQ FixedAt IndexAt EncAt evalLaneM_allQ padM_allQ whitePadsM_allQ
  card_unusedOutput)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Forward-only programs -/

section Forward

/-- A question that is not an inverse question. -/
def ForwardOnly : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => False
  | .encForward _ _ => True
  | .encInverse _ _ => False
  | .hash _ => True

theorem forwardOnly_of_fixedAt {S : FixedIndex → Prop}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : FixedAt S request) :
    ForwardOnly request := by
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact inside.elim
  | encForward _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem forwardOnly_of_encAt {request : PublicQuery FixedIndex EncPRF.PermutationIndex}
    (inside : EncAt request) : ForwardOnly request := by
  cases request with
  | fixedForward _ _ => trivial
  | fixedInverse _ _ => exact inside.elim
  | encForward _ _ => trivial
  | encInverse _ _ => exact inside.elim
  | hash _ => trivial

theorem evalLaneM_forwardOnly [FieldCertificate] (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ ForwardOnly (Programs.evalLaneM count lane joins scale bits labels) :=
  (evalLaneM_allQ count lane joins scale bits labels).mono fun _ inside =>
    forwardOnly_of_fixedAt inside

theorem padM_forwardOnly (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    AllQ ForwardOnly (Programs.padM keys coordinate index bit) :=
  (padM_allQ keys coordinate index bit).mono fun _ inside => forwardOnly_of_encAt inside

theorem hashM_forwardOnly (index : FixedIndex) (label : Block) :
    AllQ ForwardOnly (Programs.hashM index label) := by
  refine AllQ.bind ?_ fun _ => .pure _
  exact .query _ _ trivial fun _ => .pure _

theorem askHash_forwardOnly (input : BaseField) : AllQ ForwardOnly (Programs.askHash input) :=
  .query _ _ trivial fun _ => .pure _

theorem curvePrefixM_forwardOnly [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) : AllQ ForwardOnly (curvePrefixM table bits mac) :=
  (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ => askHash_forwardOnly _

theorem whitePadsM_forwardOnly (keys : WhiteningKeys) : AllQ ForwardOnly (whitePadsM keys) :=
  (whitePadsM_allQ keys).mono fun _ inside => forwardOnly_of_encAt inside

theorem truePadsM_forwardOnly (keys : WhiteningKeys) : AllQ ForwardOnly (truePadsM keys) :=
  (AllQ.vector fun _ => padM_forwardOnly _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => padM_forwardOnly _ _ _ _).bind fun _ => .pure _

theorem evalPadsM_forwardOnly (keys : WhiteningKeys) (bits : BitInput) :
    AllQ ForwardOnly (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (padM_forwardOnly _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_forwardOnly _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (padM_forwardOnly _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_forwardOnly _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ => .pure _

theorem gadgetDigestM_forwardOnly (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    AllQ ForwardOnly (Programs.gadgetDigestM output coordinate mac) :=
  (AllQ.vector fun _ => hashM_forwardOnly _ _).bind fun _ => .pure _

theorem unlockM_forwardOnly (table : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    AllQ ForwardOnly (Programs.unlockM table input mac) :=
  AllQ.vector fun _ =>
    ((gadgetDigestM_forwardOnly _ _ _).bind fun _ =>
      (gadgetDigestM_forwardOnly _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

theorem onCurveM_forwardOnly [FieldCertificate] [GroupCertificate] (table : Public)
    (bits : BitInput) (mac : InputMac) : AllQ ForwardOnly (Programs.onCurveM table bits mac) :=
  (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
      (askHash_forwardOnly _).bind fun _ =>
        (evalPadsM_forwardOnly _ _).bind fun _ =>
          (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
            (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
              (unlockM_forwardOnly _ _ _).bind fun _ => .pure _

theorem shadowOnM_forwardOnly [FieldCertificate] [GroupCertificate] (table : Public)
    (bits : BitInput) (mac : InputMac) : AllQ ForwardOnly (shadowOnM table bits mac) :=
  (curvePrefixM_forwardOnly _ _ _).bind fun _ =>
    (truePadsM_forwardOnly _).bind fun _ =>
      (onCurveM_forwardOnly _ _ _).bind fun _ => .pure _

theorem openingQueriesM_forwardOnly [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) : AllQ ForwardOnly (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq_prefix]
  exact (curvePrefixM_forwardOnly _ _ _).bind fun _ =>
    (whitePadsM_forwardOnly _).bind fun _ =>
      (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
        (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ => .pure _

end Forward

/-! ### Potentials along the refill run -/

section RefillPotential

/-- A potential of an outcome of the refill run (an abort weighs nothing). -/
def optWeight {α : Type} (potential : LState → ℝ≥0∞) : Option (α × LState × Record) → ℝ≥0∞
  | none => 0
  | some result => potential result.2.1

/-- **A supermartingale along the refill run**, for a potential reading only the EncPRF and hash
parts. -/
theorem runRefill_potential (bits : BitInput) (draw : Cell → PMF Block)
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (potential : LState → ℝ≥0∞)
    (congr : ∀ s s' : LState, s.enc = s'.enc → s.hash = s'.hash → potential s = potential s')
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      ∑' o, runRefill bits draw computation oracle record touched o * optWeight potential o ≤
        potential oracle := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runRefill]
    rw [tsum_pure_mul]
    rfl
  | query request next ih =>
    intro oracle record touched
    simp only [runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer => exact ih answer (AllQ.tail holds _) _ _ _
    | none =>
      simp only
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        obtain ⟨index, input, rfl, _⟩ := consumeCell_spec consumed
        rw [tsum_bind_mul]
        refine le_trans (ENNReal.tsum_le_tsum fun limb => mul_le_mul' le_rfl (?_ :
          _ ≤ potential oracle)) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
        split
        · rw [tsum_pure_mul]
          exact zero_le
        · rename_i updated success
          have same : potential updated = potential oracle := by
            refine congr _ _ (program_fixed_enc index input _ oracle updated success) ?_
            simp only [LazyOracle.program, Option.map_eq_some_iff] at success
            obtain ⟨next, _, rfl⟩ := success
            rfl
          rw [← same]
          exact ih _ (AllQ.tail holds _) _ _ _
      | none =>
        rw [tsum_bind_mul]
        exact le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (ih answer.1 (AllQ.tail holds _) answer.2 _ _))
          (step request oracle (AllQ.head holds))

end RefillPotential

/-! ### The hash key potential -/

section Keys

theorem tsum_le_of_support' {X : Type} (μ : PMF X) (f : X → ℝ≥0∞) (c : ℝ≥0∞)
    (bound : ∀ x ∈ μ.support, f x ≤ c) : ∑' x, μ x * f x ≤ c := by
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * c := ENNReal.tsum_le_tsum fun x => by
        by_cases member : x ∈ μ.support
        · exact mul_le_mul' le_rfl (bound x member)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr member]
          simp
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
/-- **The key potential**: the mass with which the hash answer's first half lands in `S`. -/
def keyPotential (S : Finset Block) (state : LState) : ℝ≥0∞ :=
  if state.hash = [] then (S.card : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹
  else if ∀ k k', state.hash.lookup k ≠ none → state.hash.lookup k' ≠ none → k = k' then
    (if ∃ k v, LazyOracle.lookup (.hash k) state = some v ∧ v.1 ∈ S then 1 else 0)
  else 0

theorem keyPotential_congr (S : Finset Block) (s s' : LState) (same : s.hash = s'.hash) :
    keyPotential S s = keyPotential S s' := by
  obtain ⟨f, e, h⟩ := s
  obtain ⟨f', e', h'⟩ := s'
  simp only at same
  subst same
  rfl

/-- The first half of a uniform pair lands in `S` with mass `|S|/2^128`. -/
theorem uniform_first_mass {N : ℕ} [NeZero N] (e : Fin N ≃ Block × Block) (S : Finset Block) :
    ∑' value, PMF.uniformOfFintype (Fin N) value * ind ((e value).1 ∈ S) ≤
      (S.card : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have card : N = Fintype.card (Block × Block) := by
    rw [← Fintype.card_fin N]
    exact Fintype.card_congr e
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]
  have count : ∑ value : Fin N, ind ((e value).1 ∈ S) =
      ((Finset.univ.filter fun pair : Block × Block => pair.1 ∈ S).card : ℝ≥0∞) := by
    rw [← Equiv.sum_comp e.symm (fun value => ind ((e value).1 ∈ S))]
    simp only [Equiv.apply_symm_apply]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun pair _ => ?_
    by_cases h : pair.1 ∈ S
    · rw [ind_pos h, if_pos h]
    · rw [ind_neg h, if_neg h]
  rw [count]
  have filterCard : (Finset.univ.filter fun pair : Block × Block => pair.1 ∈ S).card =
      S.card * 2 ^ 128 := by
    have : (Finset.univ.filter fun pair : Block × Block => pair.1 ∈ S) = S ×ˢ Finset.univ := by
      ext pair
      simp
    rw [this, Finset.card_product, Finset.card_univ, Kriterion.ArgoMAC.Phase3.Lazy.card_block]
  rw [filterCard, card, Fintype.card_prod, Kriterion.ArgoMAC.Phase3.Lazy.card_block,
    Nat.cast_mul, Nat.cast_mul]
  have ne : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : (2 ^ 128 : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  have top : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  generalize ((2 ^ 128 : ℕ) : ℝ≥0∞) = M at ne top ⊢
  rw [ENNReal.mul_inv (Or.inl ne) (Or.inl top)]
  refine le_of_eq ?_
  calc M⁻¹ * M⁻¹ * ((S.card : ℝ≥0∞) * M) = (S.card : ℝ≥0∞) * M⁻¹ * (M⁻¹ * M) := by ring
    _ = (S.card : ℝ≥0∞) * M⁻¹ := by rw [ENNReal.inv_mul_cancel ne top, mul_one]

open Classical in
/-- The first stored key: its value's first half lands in `S` with mass `|S|/2^128`. -/
theorem fresh_key_mass {N : ℕ} [NeZero N] (E : Fin N ≃ Block × Block) (S : Finset Block)
    (input : BaseField) :
    ∑' value : Fin N, PMF.uniformOfFintype (Fin N) value *
      (if ∃ k v, (List.lookup k [(input, value)]).map E = some v ∧ v.1 ∈ S then 1 else 0) ≤
    (S.card : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (le_of_eq (tsum_congr fun value => ?_)) (uniform_first_mass E S)
  have iff : (∃ k v, (List.lookup k [(input, value)]).map E = some v ∧ v.1 ∈ S) ↔
      (E value).1 ∈ S := by
    constructor
    · rintro ⟨k, v, found, member⟩
      by_cases same : k = input
      · subst same
        simp only [List.lookup, beq_self_eq_true, Option.map_some, Option.some.injEq] at found
        rw [← found] at member
        exact member
      · have different : (k == input) = false := by simpa [beq_iff_eq] using same
        simp [List.lookup, different] at found
    · intro member
      exact ⟨input, E value, by simp [List.lookup], member⟩
  rw [ite_eq_ind, iff]

/-- **No question raises the key potential in expectation.** -/
theorem keyPotential_step (S : Finset Block)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState) :
    ∑' answer, LazyOracle.query request state answer * keyPotential S answer.2 ≤
      keyPotential S state := by
  have frame : ∀ μ : PMF (request.Answer × LState), (∀ a ∈ μ.support, a.2.hash = state.hash) →
      ∑' a, μ a * keyPotential S a.2 ≤ keyPotential S state := fun μ h =>
    tsum_le_of_support' _ _ _ fun a member => le_of_eq (keyPotential_congr S _ _ (h a member))
  cases request with
  | fixedForward index input =>
    exact frame _ fun a member => by
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | fixedInverse index output =>
    exact frame _ fun a member => by
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encForward index input =>
    exact frame _ fun a member => by
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | encInverse index output =>
    exact frame _ fun a member => by
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rfl
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer *
      keyPotential S answer.2 ≤ _
    rw [tsum_map_mul]
    unfold HashTable.query
    cases found : state.hash.lookup input with
    | some value =>
      simp only [Draw.distribution]
      rw [tsum_pure_mul]
    | none =>
      simp only [Draw.distribution]
      rw [tsum_map_mul]
      by_cases empty : state.hash = []
      · have start : keyPotential S state = (S.card : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
          unfold keyPotential
          rw [if_pos empty]
        rw [start]
        classical
        have oneKey : ∀ value : Fin (Fintype.card (Block × Block)), ∀ k k' : BaseField,
            List.lookup k [(input, value)] ≠ none → List.lookup k' [(input, value)] ≠ none →
              k = k' := by
          intro value k k' hk hk'
          have e1 : k = input := by
            by_contra different
            have : (k == input) = false := by simpa [beq_iff_eq] using different
            simp [List.lookup, this] at hk
          have e2 : k' = input := by
            by_contra different
            have : (k' == input) = false := by simpa [beq_iff_eq] using different
            simp [List.lookup, this] at hk'
          rw [e1, e2]
        have eachEq : ∀ value : Fin (Fintype.card (Block × Block)),
            keyPotential S { state with hash := (input, value) :: state.hash } =
              (if ∃ k v, LazyOracle.lookup (.hash k)
                  ({ state with hash := [(input, value)] } : LState) = some v ∧ v.1 ∈ S
                then 1 else 0) := by
          intro value
          rw [empty]
          unfold keyPotential
          dsimp only
          rw [if_neg (List.cons_ne_nil _ _), if_pos (oneKey value)]
        simp only [eachEq]
        exact fresh_key_mass _ S input
      · obtain ⟨⟨k0, v0⟩, rest, shape⟩ := List.exists_cons_of_ne_nil empty
        have k0ne : k0 ≠ input := by
          rintro rfl
          rw [shape] at found
          simp [List.lookup] at found
        refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun value => ?_)) zero_le
        rw [mul_eq_zero]
        right
        dsimp only
        unfold keyPotential
        dsimp only
        rw [if_neg (List.cons_ne_nil _ _), if_neg]
        intro one
        apply k0ne
        refine one k0 input ?_ ?_
        · have different : (k0 == input) = false := by simpa [beq_iff_eq] using k0ne
          simp [List.lookup, different, shape]
        · simp [List.lookup]

end Keys

/-! ### The EncPRF output potential -/

section Output

/-- `1/(2^128 − 1)`. -/
abbrev epsOne : ℝ≥0∞ := ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞)⁻¹

open Classical in
/-- **The exact marginal output potential of an EncPRF index.** -/
def outPotential (j : EncPRF.PermutationIndex) (y : Fin (2 ^ 128)) (state : LState) : ℝ≥0∞ :=
  if (state.enc j).used = 0 then 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹
  else if (state.enc j).used = 1 then (if (state.enc j).knownOutput y then 1 else epsOne)
  else if (state.enc j).used = 2 then (if (state.enc j).knownOutput y then 1 else 0)
  else 0

theorem outPotential_congr (j : EncPRF.PermutationIndex) (y : Fin (2 ^ 128)) (s s' : LState)
    (same : s.enc = s'.enc) : outPotential j y s = outPotential j y s' := by
  unfold outPotential
  rw [same]

/-- The known outputs after a fresh extension. -/
theorem knownOutput_extend (state : SparsePermutation (2 ^ 128)) (x y : Fin (2 ^ 128))
    (freshX : ¬ state.knownInput x) (freshY : ¬ state.knownOutput y) (room : state.used < 2 ^ 128)
    (z : Fin (2 ^ 128)) :
    (state.extend room (state.input.symm x) (state.output.symm y)).knownOutput z ↔
      state.knownOutput z ∨ z = y := by
  rw [knownOutput_iff, knownOutput_iff]
  constructor
  · rintro ⟨w, found⟩
    rw [lookup_extend state x y freshX freshY room w] at found
    by_cases same : w = x
    · rw [if_pos same] at found
      exact Or.inr (Option.some.inj found).symm
    · rw [if_neg same] at found
      exact Or.inl ⟨w, found⟩
  · rintro (⟨w, found⟩ | rfl)
    · refine ⟨w, ?_⟩
      rw [lookup_extend state x y freshX freshY room w, if_neg]
      · exact found
      · rintro rfl
        exact freshX ((knownInput_iff _ _).mpr (by rw [found]; simp))
    · exact ⟨x, by rw [lookup_extend state x _ freshX freshY room x, if_pos rfl]⟩

/-- A uniform unknown output hits one point with mass `1/#unknown`. -/
theorem unknown_single_le (s : SparsePermutation (2 ^ 128)) [Nonempty (Unknown s)]
    (y : Fin (2 ^ 128)) :
    ∑' out : Unknown s, PMF.uniformOfFintype (Unknown s) out * ind (out.val = y) ≤
      ((2 ^ 128 - s.used : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [← card_unusedOutput s]
  refine le_trans (le_of_eq (tsum_congr fun out => ?_)) (uniform_single_le (X := Unknown s)
    (fun out => out.val = y) (fun a b ha hb => Subtype.ext (ha.trans hb.symm)))
  rw [ite_eq_ind]

/-- **The first answer's exact marginal**: `1[x = x₀] + 1[x ≠ x₀]/(2^128 − 1)` under the uniform
law on `2^128` points has mass exactly `2/2^128`. -/
theorem first_answer_le {X : Type} [Fintype X] [Nonempty X] (x₀ : X)
    (card : Fintype.card X = 2 ^ 128) (f : X → ℝ≥0∞)
    (hf : ∀ x, f x = open Classical in if x = x₀ then 1 else epsOne) :
    ∑' x, PMF.uniformOfFintype X x * f x ≤ 2 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, card]
  rw [← Finset.mul_sum]
  have total : ∑ x : X, f x = 1 + ((2 ^ 128 - 1 : ℕ) : ℝ≥0∞) * epsOne := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀), hf x₀, if_pos rfl]
    congr 1
    rw [Finset.sum_congr rfl fun x member => by
      rw [hf x, if_neg (Finset.ne_of_mem_erase member)], Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card, nsmul_eq_mul]
  rw [total, ENNReal.mul_inv_cancel (by norm_num) (ENNReal.natCast_ne_top _), one_add_one_eq_two,
    mul_comm]

open Classical in
/-- **One forward EncPRF question does not raise the output potential in expectation.** -/
theorem outPotential_step (j : EncPRF.PermutationIndex) (y : Fin (2 ^ 128))
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (forward : ForwardOnly request)
    (state : LState) :
    ∑' answer, LazyOracle.query request state answer * outPotential j y answer.2 ≤
      outPotential j y state := by
  cases request with
  | fixedInverse _ _ => exact forward.elim
  | encInverse _ _ => exact forward.elim
  | fixedForward index input =>
    change ∑' answer, (((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with fixed := Function.update state.fixed index answer.2 }))) answer *
      outPotential j y answer.2 ≤ _
    rw [tsum_map_mul]
    refine le_of_eq ?_
    simp_rw [show ∀ answer : Fin (2 ^ 128) × SparsePermutation (2 ^ 128),
        outPotential j y { state with fixed := Function.update state.fixed index answer.2 } =
          outPotential j y state from fun _ => outPotential_congr j y _ _ rfl]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | hash input =>
    change ∑' answer, ((state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (_, { state with hash := answer.2 }))) answer *
      outPotential j y answer.2 ≤ _
    rw [tsum_map_mul]
    refine le_of_eq ?_
    simp_rw [show ∀ answer : Fin (Fintype.card (Block × Block)) ×
        HashTable BN254.BaseField (Fintype.card (Block × Block)),
        outPotential j y { state with hash := answer.2 } = outPotential j y state from
          fun _ => outPotential_congr j y _ _ rfl]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | encForward index input =>
    change ∑' answer, (((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1,
        { state with enc := Function.update state.enc index answer.2 }))) answer *
      outPotential j y answer.2 ≤ _
    rw [tsum_map_mul]
    by_cases other : j ≠ index
    · refine le_of_eq ?_
      simp_rw [show ∀ answer : Fin (2 ^ 128) × SparsePermutation (2 ^ 128),
          outPotential j y { state with enc := Function.update state.enc index answer.2 } =
            outPotential j y state from fun answer => by
          unfold outPotential
          simp only [Function.update_of_ne other]]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    · simp only [not_not] at other
      subst other
      by_cases known : (state.enc j).knownInput input.toFin
      · have pure : ((state.enc j).forward input.toFin).distribution =
            PMF.pure ((state.enc j).output ((state.enc j).input.symm input.toFin), state.enc j) := by
          unfold SparsePermutation.forward
          simp only [SparsePermutation.knownInput] at known
          rw [dif_pos known]
          rfl
        rw [pure, tsum_pure_mul]
        simp only [Function.update_eq_self]
        exact le_rfl
      · obtain ⟨room, _, law⟩ := forward_fresh_eq (state.enc j) input.toFin known
        rw [law, tsum_map_mul]
        simp only [outPotential, Function.update_self, extend_used]
        have outputs : ∀ out : Unknown (state.enc j),
            ((state.enc j).extend room ((state.enc j).input.symm input.toFin)
              ((state.enc j).output.symm out.val)).knownOutput y ↔
              (state.enc j).knownOutput y ∨ y = out.val :=
          fun out => knownOutput_extend _ _ _ known out.2 room y
        simp only [outputs]
        have n0 : (state.enc j).used + 1 ≠ 0 := by omega
        by_cases h0 : (state.enc j).used = 0
        · -- first answer: exactly the marginal
          have noneKnown : ¬ (state.enc j).knownOutput y := by
            intro h
            unfold SparsePermutation.knownOutput at h
            omega
          have n1 : (state.enc j).used + 1 = 1 := by omega
          rw [if_pos h0]
          simp only [n0, n1, if_false, if_true, noneKnown, false_or,
            show (1 : ℕ) ≠ 0 from by decide]
          refine first_answer_le ⟨y, noneKnown⟩ (by rw [card_unusedOutput, h0]; rfl) _
            fun out => ?_
          by_cases h : y = out.val
          · rw [if_pos h, if_pos (Subtype.ext h.symm)]
          · rw [if_neg h, if_neg (fun same => h (congrArg Subtype.val same).symm)]
        · by_cases h1 : (state.enc j).used = 1
          · -- second answer
            have n1 : (state.enc j).used + 1 ≠ 1 := by omega
            have n2 : (state.enc j).used + 1 = 2 := by omega
            rw [if_neg h0, if_pos h1]
            simp only [n0, n1, n2, if_false, if_true, show (2 : ℕ) ≠ 0 from by decide,
              show (2 : ℕ) ≠ 1 from by decide]
            by_cases was : (state.enc j).knownOutput y
            · simp only [was, true_or, if_true]
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            · simp only [was, false_or, if_false]
              refine le_trans (le_of_eq (tsum_congr fun out => ?_))
                (le_trans (unknown_single_le _ y) (le_of_eq ?_))
              · congr 1
                by_cases h : y = out.val
                · rw [if_pos h, ind_pos h.symm]
                · rw [if_neg h, ind_neg (Ne.symm h)]
              · rw [h1]
          · -- a third pair: the potential drops to zero
            have n1 : (state.enc j).used + 1 ≠ 1 := by omega
            have n2 : (state.enc j).used + 1 ≠ 2 := by omega
            simp only [n0, n1, n2, if_false, mul_zero, tsum_zero]
            exact zero_le

end Output

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
