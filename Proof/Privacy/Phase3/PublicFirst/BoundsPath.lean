/-
**Phase 3, P1m — (B1) tools: where the pairs of a run come from.**

* `refillAns bits state` — the answers along a refill run's path: an intercepted (designated)
  question gets its interception (its own input), every other one its stored answer.
* `Fresh bits used c` — along every path of `c`, the non-designated forward fixed-key indices
  (`consumedIndex`) are pairwise distinct and avoid `used`. Closed under `bind` (with index sets),
  `FreeQuery.vector` (pairwise disjoint index sets), `ite`.
* **`runRefill_describe`** — P4's refill run of a forward-only `Fresh` program on a tape, from a
  state empty and untouched off `used`: the value is the program along `refillAns`, every
  non-intercepted question on the path is stored, and every fixed-key pair of the final state is an
  old one or the pair of a non-designated question on the path, **with output `tape ⊕ input` at a
  mask site** (a consumed question); every hash key is old or asked on the path; every new record is
  a designated question's input on the path.
* **`runLazyQ_provenance`** — the lazy runner of a forward-only program: every new fixed-key pair
  and hash key of the final state is asked on the path (read from the final state).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEncOff

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source interceptAnswer recordAfter IsDesignated)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request runRefill AllQ consumeCell
  refillAnswer consumeCell_spec touch touchedIndex cellOf cellOf_spec queriesAlong consumedIndex
  consumedIndex_designated consumedIndex_plain query_frame program_frame)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Paths along an answer function -/

section Paths

theorem mem_queriesAlong_allQ {P : Request → Prop} {α : Type}
    (answer : (request : Request) → request.Answer) {c : FreeQuery Programs.Spec α}
    (holds : AllQ P c) : ∀ r ∈ queriesAlong answer c, P r := by
  induction holds with
  | pure value => exact fun _ member => by cases member
  | query request next here _ ih =>
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact here
    · exact ih _ r member

/-- **Two answer functions agreeing along one's path give the same path and value.** -/
theorem queriesAlong_congr {α : Type} (answer other : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α)
    (agree : ∀ r ∈ queriesAlong answer c, other r = answer r) :
    queriesAlong other c = queriesAlong answer c ∧
      FreeQuery.eval other c = FreeQuery.eval answer c := by
  induction c with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next ih =>
    have head : other request = answer request := agree request List.mem_cons_self
    have rest := ih (answer request) fun r member => agree r (List.mem_cons_of_mem _ member)
    refine ⟨?_, ?_⟩
    · show request :: queriesAlong other (next (other request)) =
        request :: queriesAlong answer (next (answer request))
      rw [head, rest.1]
    · show FreeQuery.eval other (next (other request)) = FreeQuery.eval answer (next (answer request))
      rw [head, rest.2]

end Paths

/-! ### The refill run's answers -/

section Answers

/-- **The answers along a refill run's path**: the interception where there is one, else the
stored answer. -/
def refillAns (bits : BitInput) (state : LState) (request : Request) : request.Answer :=
  match interceptAnswer bits request with
  | some answer => answer
  | none => answerOf state request

theorem refillAns_intercept {bits : BitInput} {state : LState} {request : Request}
    {answer : request.Answer} (intercept : interceptAnswer bits request = some answer) :
    refillAns bits state request = answer := by
  unfold refillAns
  rw [intercept]

theorem refillAns_plain {bits : BitInput} {state : LState} {request : Request}
    (intercept : interceptAnswer bits request = none) :
    refillAns bits state request = answerOf state request := by
  unfold refillAns
  rw [intercept]

end Answers

/-! ### Fresh programs -/

section Fresh

/-- The consumed index of a request lies in `S`. -/
def InIdx (bits : BitInput) (S : Set FixedIndex) (request : Request) : Prop :=
  ∀ i, consumedIndex bits request = some i → i ∈ S

/-- **Along every path, the consumed indices are distinct and avoid `used`.** -/
inductive Fresh (bits : BitInput) {α : Type} : Set FixedIndex → FreeQuery Programs.Spec α → Prop
  | pure (used : Set FixedIndex) (value : α) : Fresh bits used (.pure value)
  | query (used : Set FixedIndex) (request : Request)
      (next : request.Answer → FreeQuery Programs.Spec α) :
      (∀ i, consumedIndex bits request = some i → i ∉ used) →
      (∀ answer, Fresh bits (used ∪ {i | consumedIndex bits request = some i}) (next answer)) →
      Fresh bits used (.query request next)

namespace Fresh

variable {bits : BitInput} {α β : Type}

theorem mono {used : Set FixedIndex} {c : FreeQuery Programs.Spec α} (fresh : Fresh bits used c) :
    ∀ {smaller : Set FixedIndex}, smaller ⊆ used → Fresh bits smaller c := by
  induction fresh with
  | pure used value => exact fun _ => .pure _ value
  | query used request next avoid _ ih =>
    intro smaller sub
    refine .query smaller request next (fun i hi inside => avoid i hi (sub inside)) fun answer => ?_
    exact ih answer (Set.union_subset_union_left _ sub)

theorem tail {used : Set FixedIndex} {request : Request}
    {next : request.Answer → FreeQuery Programs.Spec α} (fresh : Fresh bits used (.query request next))
    (answer : request.Answer) :
    Fresh bits (used ∪ {i | consumedIndex bits request = some i}) (next answer) := by
  cases fresh with
  | query _ _ _ _ rest => exact rest answer

theorem head {used : Set FixedIndex} {request : Request}
    {next : request.Answer → FreeQuery Programs.Spec α} (fresh : Fresh bits used (.query request next)) :
    ∀ i, consumedIndex bits request = some i → i ∉ used := by
  cases fresh with
  | query _ _ _ avoid _ => exact avoid

/-- **A sequence of fresh programs with disjoint index sets is fresh.** -/
theorem bind {S : Set FixedIndex} {c : FreeQuery Programs.Spec α} {used : Set FixedIndex}
    (first : Fresh bits used c) (inside : AllQ (InIdx bits S) c)
    {f : α → FreeQuery Programs.Spec β} (rest : ∀ value, Fresh bits (used ∪ S) (f value)) :
    Fresh bits used (c >>= f) := by
  induction first with
  | pure used value => exact (rest value).mono Set.subset_union_left
  | query used request next avoid _ ih =>
    refine .query used request _ avoid fun answer => ?_
    refine ih answer (AllQ.tail inside answer) fun value => (rest value).mono ?_
    intro i member
    rcases member with (member | member) | member
    · exact Or.inl member
    · exact Or.inr (AllQ.head inside i member)
    · exact Or.inr member

/-- A fresh program stays fresh against indices outside its index set. -/
theorem union_disjoint {S : Set FixedIndex} {c : FreeQuery Programs.Spec α} {used : Set FixedIndex}
    (fresh : Fresh bits used c) (inside : AllQ (InIdx bits S) c) {U : Set FixedIndex}
    (disjoint : ∀ i ∈ S, i ∉ U) : Fresh bits (used ∪ U) c := by
  induction fresh with
  | pure used value => exact .pure _ value
  | query used request next avoid _ ih =>
    refine .query _ request next (fun i hi member => ?_) fun answer => ?_
    · rcases member with member | member
      · exact avoid i hi member
      · exact disjoint i (AllQ.head inside i hi) member
    · refine (ih answer (AllQ.tail inside answer)).mono ?_
      intro i member
      rcases member with (member | member) | member
      · exact Or.inl (Or.inl member)
      · exact Or.inr member
      · exact Or.inl (Or.inr member)

/-- A program consuming nothing is fresh. -/
theorem of_none {c : FreeQuery Programs.Spec α}
    (holds : AllQ (fun request => consumedIndex bits request = none) c) :
    ∀ used, Fresh bits used c := by
  induction holds with
  | pure value => exact fun used => .pure used value
  | query request next here _ ih =>
    intro used
    refine .query used request next (fun i hi => by rw [here] at hi; cases hi) fun answer => ?_
    exact ih answer _

theorem ite {condition : Prop} [Decidable condition] {first second : FreeQuery Programs.Spec α}
    {used : Set FixedIndex} (yes : Fresh bits used first) (no : Fresh bits used second) :
    Fresh bits used (if condition then first else second) := by
  split
  · exact yes
  · exact no

/-- **A loop of fresh programs with pairwise disjoint index sets is fresh.** -/
theorem vector {count : ℕ} {program : Fin count → FreeQuery Programs.Spec α}
    (S : Fin count → Set FixedIndex) (each : ∀ index, Fresh bits ∅ (program index))
    (inside : ∀ index, AllQ (InIdx bits (S index)) (program index))
    (disjoint : ∀ index index', index ≠ index' → ∀ i ∈ S index, i ∉ S index') :
    ∀ (used : Set FixedIndex), (∀ index, ∀ i ∈ S index, i ∉ used) →
      Fresh bits used (FreeQuery.vector count program) := by
  induction count with
  | zero => exact fun used _ => .pure _ _
  | succ count ih =>
    intro used avoid
    show Fresh bits used (FreeQuery.vector count (fun index => program index.castSucc) >>=
      fun values => program (Fin.last count) >>= fun value => Pure.pure (values.push value))
    refine bind (S := {i | ∃ index : Fin count, i ∈ S index.castSucc})
      (ih (fun index => S index.castSucc) (fun index => each _) (fun index => inside _)
        (fun a b ne => disjoint _ _ (fun same => ne (Fin.castSucc_injective _ same)))
        used (fun index => avoid _))
      (AllQ.vector fun index => (inside index.castSucc).mono fun r holds i hi =>
        ⟨index, holds i hi⟩) fun values => ?_
    refine bind (S := S (Fin.last count)) ?_ (inside _) fun value => .pure _ _
    have base := union_disjoint (each (Fin.last count)) (inside _)
      (U := used ∪ {i | ∃ index : Fin count, i ∈ S index.castSucc}) fun i member outside => by
        rcases outside with outside | ⟨index, inS⟩
        · exact avoid _ i member outside
        · exact disjoint _ _ (Fin.castSucc_lt_last index).ne i inS member
    exact base.mono fun i member => Or.inr member

end Fresh

end Fresh

/-! ### One step: the pairs a lazy question or a program adds -/

section Steps

/-- **A forward lazy question adds at most its own pair.** -/
theorem query_fixed_pairs (request : Request) (forward : ForwardOnly request) (state : LState)
    (answer : request.Answer × LState) (member : answer ∈ (LazyOracle.query request state).support)
    (i : FixedIndex) (x y : Fin (2 ^ 128)) (found : lk (answer.2.fixed i) x = some y) :
    lk (state.fixed i) x = some y ∨ request = .fixedForward i (BitVec.ofFin x) := by
  cases request with
  | fixedForward index input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    by_cases same : i = index
    · subst same
      simp only [Function.update_self] at found
      rcases forward_new _ _ drawn drawnMember x (by rw [found]; exact Option.some_ne_none _)
        with old | new
      · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp old
        have later := forward_grows _ _ drawn drawnMember x y' hy'
        rw [found] at later
        cases later
        exact Or.inl hy'
      · subst new
        have stored := LazyOracle.forward_lookup _ _ drawn drawnMember
        change lk drawn.2 input.toFin = some drawn.1 at stored
        exact Or.inr (by rw [BitVec.ofFin_toFin])
    · simp only [Function.update_of_ne same] at found
      exact Or.inl found
  | fixedInverse _ _ => exact forward.elim
  | encForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encInverse _ _ => exact forward.elim
  | hash input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found

/-- **A lazy question adds at most its own hash key.** -/
theorem query_hash_pairs (request : Request) (state : LState)
    (answer : request.Answer × LState) (member : answer ∈ (LazyOracle.query request state).support)
    (k : BaseField) (v : Fin (Fintype.card (Block × Block)))
    (found : answer.2.hash.lookup k = some v) :
    state.hash.lookup k = some v ∨ request = .hash k := by
  cases request with
  | fixedForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | fixedInverse index output =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encForward index input =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | encInverse index output =>
    obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact Or.inl found
  | hash input =>
    obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    by_cases same : k = input
    · exact Or.inr (by rw [same])
    · left
      unfold HashTable.query at drawnMember
      split at drawnMember
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at drawnMember
        subst drawnMember
        exact found
      · simp only [Draw.distribution] at drawnMember
        obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp drawnMember
        have different : (k == input) = false := by simpa [beq_iff_eq] using same
        simpa [List.lookup, different] using found

/-- **A fixed-key program adds exactly its own pair.** -/
theorem program_fixed_pairs (index : FixedIndex) (input output : Block) (state updated : LState)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated)
    (i : FixedIndex) (x y : Fin (2 ^ 128)) (found : lk (updated.fixed i) x = some y) :
    lk (state.fixed i) x = some y ∨ (i = index ∧ x = input.toFin ∧ y = output.toFin) := by
  simp only [LazyOracle.program, Option.map_eq_some_iff] at success
  obtain ⟨next, programmed, rfl⟩ := success
  by_cases same : i = index
  · subst same
    simp only [Function.update_self] at found
    unfold LazyOracle.permutationProgram at programmed
    split at programmed
    · rename_i fresh
      cases programmed
      rw [lookup_extend _ _ _ fresh.1 fresh.2] at found
      split at found
      · rename_i atInput
        cases found
        exact Or.inr ⟨rfl, atInput, rfl⟩
      · exact Or.inl found
    · cases programmed
  · simp only [Function.update_of_ne same] at found
    exact Or.inl found

theorem empty_not_knownInput (z : Fin (2 ^ 128)) :
    ¬ (SparsePermutation.empty (2 ^ 128)).knownInput z := by
  show ¬ (_ < 0)
  omega

theorem empty_not_knownOutput (z : Fin (2 ^ 128)) :
    ¬ (SparsePermutation.empty (2 ^ 128)).knownOutput z := by
  show ¬ (_ < 0)
  omega

/-- The one pair of `storedPerm`. -/
theorem lk_storedPerm (input output : Block) (z : Fin (2 ^ 128)) :
    lk (storedPerm input output) z = if z = input.toFin then some output.toFin else none := by
  unfold storedPerm
  rw [lookup_extend (SparsePermutation.empty (2 ^ 128)) input.toFin output.toFin
    (empty_not_knownInput _) (empty_not_knownOutput _) (Nat.two_pow_pos 128) z, lk_empty]

/-- `storeOne` stores its pair. -/
theorem storeOne_stores (oracle : LState) (index : FixedIndex) (input output : Block) :
    StoredAs (storeOne oracle index input output) ⟨.fixedForward index input, output⟩ := by
  show (lk ((Function.update oracle.fixed index (storedPerm input output)) index)
    input.toFin).map BitVec.ofFin = some output
  rw [Function.update_self, lk_storedPerm, if_pos rfl]
  simp

theorem program_hash (index : FixedIndex) (input output : Block) (state updated : LState)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    updated.hash = state.hash := by
  simp only [LazyOracle.program, Option.map_eq_some_iff] at success
  obtain ⟨next, _, rfl⟩ := success
  rfl

end Steps

/-! ### The refill run, described -/

section Refill

/-- **What a refill run leaves.** -/
structure Described (bits : BitInput) (tape : Tape) {α : Type} (computation : FreeQuery Programs.Spec α)
    (oracle : LState) (record : Record) (outcome : α × LState × Record) : Prop where
  grows : Grows oracle outcome.2.1
  value : outcome.1 = FreeQuery.eval (refillAns bits outcome.2.1) computation
  stored : ∀ r ∈ queriesAlong (refillAns bits outcome.2.1) computation,
    interceptAnswer bits r = none → StoredAs outcome.2.1 ⟨r, answerOf outcome.2.1 r⟩
  fixed : ∀ i x y, lk (outcome.2.1.fixed i) x = some y → lk (oracle.fixed i) x = some y ∨
    (.fixedForward i (BitVec.ofFin x) ∈ queriesAlong (refillAns bits outcome.2.1) computation ∧
      ¬ IsDesignated bits i ∧
        ∀ cell, cellOf i = some cell → BitVec.ofFin y = tape cell ^^^ BitVec.ofFin x)
  hash : ∀ k v, outcome.2.1.hash.lookup k = some v → oracle.hash.lookup k = some v ∨
    .hash k ∈ queriesAlong (refillAns bits outcome.2.1) computation
  records : ∀ i, outcome.2.2 i = record i ∨ (IsDesignated bits i ∧
    ∃ x, outcome.2.2 i = some x ∧ .fixedForward i x ∈ queriesAlong (refillAns bits outcome.2.1)
      computation)

theorem interceptAnswer_none_forward {bits : BitInput} {index : FixedIndex} {input : Block}
    (intercept : interceptAnswer bits (.fixedForward index input) = none) :
    ¬ IsDesignated bits index := by
  intro designated
  rw [Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_designated bits input designated] at intercept
  cases intercept

theorem recordAfter_cases (bits : BitInput) (request : Request) (record : Record) (i : FixedIndex) :
    recordAfter bits request record i = record i ∨
      (IsDesignated bits i ∧ ∃ x, recordAfter bits request record i = some x ∧
        request = .fixedForward i x) := by
  classical
  cases request with
  | fixedForward index input =>
    simp only [recordAfter]
    split
    · rename_i designated
      by_cases same : i = index
      · subst same
        exact Or.inr ⟨designated, input, by rw [Function.update_self], rfl⟩
      · exact Or.inl (Function.update_of_ne same _ _)
    · exact Or.inl rfl
  | fixedInverse _ _ => exact Or.inl rfl
  | encForward _ _ => exact Or.inl rfl
  | encInverse _ _ => exact Or.inl rfl
  | hash _ => exact Or.inl rfl

/-- **P4's refill run of a fresh forward-only program, described.** -/
theorem runRefill_describe (bits : BitInput) (tape : Tape) {α : Type}
    (computation : FreeQuery Programs.Spec α) (forward : AllQ ForwardOnly computation) :
    ∀ (used : Set FixedIndex), Fresh bits used computation →
      ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
        (∀ i, i ∉ used → i ∉ touched ∧ oracle.fixed i = SparsePermutation.empty _) →
        ∀ outcome, some outcome ∈ (runRefill bits (fun cell => PMF.pure (tape cell)) computation
          oracle record touched).support →
          Described bits tape computation oracle record outcome := by
  induction computation with
  | pure value =>
    intro used _ oracle record touched _ outcome member
    simp only [runRefill, PMF.mem_support_pure_iff, Option.some.injEq] at member
    subst member
    exact ⟨Grows.refl _, rfl, (fun _ h => by cases h), (fun _ _ _ found => Or.inl found),
      (fun _ _ found => Or.inl found), (fun _ => Or.inl rfl)⟩
  | query request next ih =>
    intro used fresh oracle record touched empties outcome member
    have isForward : ForwardOnly request := AllQ.head forward
    simp only [runRefill] at member
    cases intercept : interceptAnswer bits request with
    | some answer =>
      rw [intercept] at member
      have d := ih answer (AllQ.tail forward answer) _ (fresh.tail answer) oracle _ touched
        (fun i outside => empties i fun inside => outside (Or.inl inside)) outcome member
      have same : refillAns bits outcome.2.1 request = answer := refillAns_intercept intercept
      have path : queriesAlong (refillAns bits outcome.2.1) (.query request next) =
          request :: queriesAlong (refillAns bits outcome.2.1) (next answer) := by
        show request :: queriesAlong _ (next (refillAns bits outcome.2.1 request)) = _
        rw [same]
      refine ⟨d.grows, ?_, ?_, ?_, ?_, ?_⟩
      · show outcome.1 = FreeQuery.eval _ (next (refillAns bits outcome.2.1 request))
        rw [same]
        exact d.value
      · intro r member' notIntercepted
        rw [path] at member'
        rcases List.mem_cons.mp member' with rfl | member'
        · rw [intercept] at notIntercepted
          cases notIntercepted
        · exact d.stored r member' notIntercepted
      · intro i x y found
        rw [path]
        rcases d.fixed i x y found with old | ⟨onPath, rest⟩
        · exact Or.inl old
        · exact Or.inr ⟨List.mem_cons_of_mem _ onPath, rest⟩
      · intro k v found
        rw [path]
        rcases d.hash k v found with old | onPath
        · exact Or.inl old
        · exact Or.inr (List.mem_cons_of_mem _ onPath)
      · intro i
        rw [path]
        rcases d.records i with same' | ⟨designated, x, recorded, onPath⟩
        · rcases recordAfter_cases bits request record i with kept | ⟨designated, x, recorded, rfl⟩
          · exact Or.inl (same'.trans kept)
          · exact Or.inr ⟨designated, x, same'.trans recorded, List.mem_cons_self⟩
        · exact Or.inr ⟨designated, x, recorded, List.mem_cons_of_mem _ onPath⟩
    | none =>
      rw [intercept] at member
      simp only at member
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        rw [consumed] at member
        obtain ⟨index, input, rfl, notTouched, fresh', siteEq⟩ := consumeCell_spec consumed
        simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at member
        obtain ⟨limb, rfl, rest⟩ := member
        have notDesignated := interceptAnswer_none_forward intercept
        have consumedEq : consumedIndex bits (.fixedForward index input) = some index :=
          consumedIndex_plain bits input notDesignated
        have notUsed : index ∉ used := fresh.head index consumedEq
        have emptyHere : oracle.fixed index = SparsePermutation.empty _ := (empties index notUsed).2
        split at rest
        · simp at rest
        rename_i updated success
        have updatedEq : updated = storeOne oracle index input
            (refillAnswer (.fixedForward index input) (tape cell)) :=
          (Option.some.inj ((program_empty oracle index input _ emptyHere).symm.trans success)).symm
        subst updatedEq
        have tailEmpties : ∀ i, i ∉ used ∪ {i | consumedIndex bits (.fixedForward index input) = some i} →
            i ∉ touch (.fixedForward index input) touched ∧
              (storeOne oracle index input (refillAnswer (.fixedForward index input) (tape cell))).fixed i =
                SparsePermutation.empty _ := by
          intro i outside
          have notUsedI : i ∉ used := fun inside => outside (Or.inl inside)
          have different : i ≠ index := fun same => outside (Or.inr (by rw [same]; exact consumedEq))
          refine ⟨?_, ?_⟩
          · rintro (inside | inside)
            · exact (empties i notUsedI).1 inside
            · exact different (Option.some.inj inside).symm
          · simp only [storeOne]
            rw [Function.update_of_ne different]
            exact (empties i notUsedI).2
        have d := ih _ (AllQ.tail forward _) _ (fresh.tail _) _ record _ tailEmpties outcome rest
        have storedHere : StoredAs outcome.2.1 ⟨.fixedForward index input,
            refillAnswer (.fixedForward index input) (tape cell)⟩ :=
          storedAs_grows d.grows (storeOne_stores oracle index input _)
        have same : refillAns bits outcome.2.1 (.fixedForward index input) =
            refillAnswer (.fixedForward index input) (tape cell) := by
          rw [refillAns_plain intercept]
          exact answerOf_of_stored storedHere
        have path : queriesAlong (refillAns bits outcome.2.1) (.query (.fixedForward index input) next) =
            .fixedForward index input :: queriesAlong (refillAns bits outcome.2.1)
              (next (refillAnswer (.fixedForward index input) (tape cell))) := by
          show _ :: queriesAlong _ (next (refillAns bits outcome.2.1 (.fixedForward index input))) = _
          rw [same]
        refine ⟨(program_state_grows index input _ oracle _ (program_empty oracle index input _
          emptyHere)).trans d.grows, ?_, ?_, ?_, ?_, ?_⟩
        · show outcome.1 = FreeQuery.eval _
            (next (refillAns bits outcome.2.1 (.fixedForward index input)))
          rw [same]
          exact d.value
        · intro r member' notIntercepted
          rw [path] at member'
          rcases List.mem_cons.mp member' with rfl | member'
          · rw [answerOf_of_stored storedHere]
            exact storedHere
          · exact d.stored r member' notIntercepted
        · intro i x y found
          rw [path]
          rcases d.fixed i x y found with old | ⟨onPath, rest⟩
          · rcases program_fixed_pairs index input _ oracle _ (program_empty oracle index input _
              emptyHere) i x y old with older | ⟨rfl, rfl, rfl⟩
            · exact Or.inl older
            · refine Or.inr ⟨by rw [BitVec.ofFin_toFin]; exact List.mem_cons_self, notDesignated,
                fun cell' found' => ?_⟩
              have sameCell : cell' = cell := by
                have := cellOf_spec found'
                rw [← siteEq] at this
                exact Kriterion.ArgoMAC.Security.Phase3.siteIndex_injective this
              subst sameCell
              simp only [refillAnswer, BitVec.ofFin_toFin]
          · exact Or.inr ⟨List.mem_cons_of_mem _ onPath, rest⟩
        · intro k v found
          rw [path]
          rcases d.hash k v found with old | onPath
          · left
            rw [← program_hash index input _ oracle _ (program_empty oracle index input _
              emptyHere)]
            exact old
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro i
          rw [path]
          rcases d.records i with same' | ⟨designated, x, recorded, onPath⟩
          · exact Or.inl same'
          · exact Or.inr ⟨designated, x, recorded, List.mem_cons_of_mem _ onPath⟩
      | none =>
        rw [consumed] at member
        simp only [PMF.mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, rest⟩ := member
        have tailEmpties : ∀ i, i ∉ used ∪ {i | consumedIndex bits request = some i} →
            i ∉ touch request touched ∧ answer.2.fixed i = SparsePermutation.empty _ := by
          intro i outside
          have notUsedI : i ∉ used := fun inside => outside (Or.inl inside)
          have different : touchedIndex request ≠ some i := by
            intro hit
            apply outside
            refine Or.inr ?_
            cases request with
            | fixedForward index input =>
              cases hit
              exact consumedIndex_plain bits input (interceptAnswer_none_forward intercept)
            | fixedInverse _ _ => exact isForward.elim
            | encForward _ _ => cases hit
            | encInverse _ _ => cases hit
            | hash _ => cases hit
          refine ⟨?_, ?_⟩
          · rintro (inside | inside)
            · exact (empties i notUsedI).1 inside
            · exact different inside
          · rw [query_frame request oracle answer answerMember i different]
            exact (empties i notUsedI).2
        have d := ih answer.1 (AllQ.tail forward _) _ (fresh.tail _) answer.2 record _ tailEmpties
          outcome rest
        have storedHere : StoredAs outcome.2.1 ⟨request, answer.1⟩ :=
          storedAs_grows d.grows (query_stores request oracle answer answerMember)
        have same : refillAns bits outcome.2.1 request = answer.1 := by
          rw [refillAns_plain intercept]
          exact answerOf_of_stored storedHere
        have path : queriesAlong (refillAns bits outcome.2.1) (.query request next) =
            request :: queriesAlong (refillAns bits outcome.2.1) (next answer.1) := by
          show request :: queriesAlong _ (next (refillAns bits outcome.2.1 request)) = _
          rw [same]
        refine ⟨(query_grows request oracle answer answerMember).trans d.grows, ?_, ?_, ?_, ?_, ?_⟩
        · show outcome.1 = FreeQuery.eval _ (next (refillAns bits outcome.2.1 request))
          rw [same]
          exact d.value
        · intro r member' notIntercepted
          rw [path] at member'
          rcases List.mem_cons.mp member' with rfl | member'
          · rw [answerOf_of_stored storedHere]
            exact storedHere
          · exact d.stored r member' notIntercepted
        · intro i x y found
          rw [path]
          rcases d.fixed i x y found with old | ⟨onPath, rest⟩
          · rcases query_fixed_pairs request isForward oracle answer answerMember i x y old
              with older | rfl
            · exact Or.inl older
            · have notDesignated := interceptAnswer_none_forward intercept
              refine Or.inr ⟨List.mem_cons_self, notDesignated, fun cell' found' => ?_⟩
              exfalso
              have consumedEq := consumedIndex_plain bits (BitVec.ofFin x) notDesignated
              have notUsed := fresh.head i consumedEq
              have emptyHere := (empties i notUsed).2
              have untouched := (empties i notUsed).1
              simp only [consumeCell] at consumed
              rw [if_neg (by
                rintro (inside | known)
                · exact untouched inside
                · rw [emptyHere] at known
                  exact absurd known (by show ¬ (_ < 0); omega)), found'] at consumed
              cases consumed
          · exact Or.inr ⟨List.mem_cons_of_mem _ onPath, rest⟩
        · intro k v found
          rw [path]
          rcases d.hash k v found with old | onPath
          · rcases query_hash_pairs request oracle answer answerMember k v old with older | rfl
            · exact Or.inl older
            · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ onPath)
        · intro i
          rw [path]
          rcases d.records i with same' | ⟨designated, x, recorded, onPath⟩
          · exact Or.inl same'
          · exact Or.inr ⟨designated, x, recorded, List.mem_cons_of_mem _ onPath⟩

end Refill

/-! ### The lazy run: provenance -/

section Lazy

/-- **Every new pair of a lazy run of a forward-only program is asked on its path.** -/
theorem runLazyQ_provenance {α : Type} (computation : FreeQuery Programs.Spec α)
    (forward : AllQ ForwardOnly computation) :
    ∀ (state : LState) (outcome : α × LState), outcome ∈ (runLazyQ computation state).support →
      (∀ i x y, lk (outcome.2.fixed i) x = some y → lk (state.fixed i) x = some y ∨
        .fixedForward i (BitVec.ofFin x) ∈ queriesAlong (answerOf outcome.2) computation) ∧
      (∀ k v, outcome.2.hash.lookup k = some v → state.hash.lookup k = some v ∨
        .hash k ∈ queriesAlong (answerOf outcome.2) computation) := by
  induction computation with
  | pure value =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact ⟨fun _ _ _ found => Or.inl found, fun _ _ found => Or.inl found⟩
  | query request next ih =>
    intro state outcome member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    obtain ⟨fixedRest, hashRest⟩ := ih answer.1 (AllQ.tail forward _) answer.2 outcome rest
    have grow := runLazyQ_grows _ answer.2 outcome rest
    have storedHere : StoredAs outcome.2 ⟨request, answer.1⟩ :=
      storedAs_grows grow (query_stores request state answer answerMember)
    have same : answerOf outcome.2 request = answer.1 := answerOf_of_stored storedHere
    have path : queriesAlong (answerOf outcome.2) (.query request next) =
        request :: queriesAlong (answerOf outcome.2) (next answer.1) := by
      show request :: queriesAlong _ (next (answerOf outcome.2 request)) = _
      rw [same]
    rw [path]
    refine ⟨fun i x y found => ?_, fun k v found => ?_⟩
    · rcases fixedRest i x y found with old | onPath
      · rcases query_fixed_pairs request (AllQ.head forward) state answer answerMember i x y old
          with older | rfl
        · exact Or.inl older
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ onPath)
    · rcases hashRest k v found with old | onPath
      · rcases query_hash_pairs request state answer answerMember k v old with older | rfl
        · exact Or.inl older
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ onPath)

end Lazy

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
