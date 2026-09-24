/-
**Phase 3, P1g — tools for the off-curve refutation: runs on stored entries, transcripts, and
installing a complete oracle's entries.**

* `freeOracle` / `run_freeOracle`: a bounded free program as an adversary program, run lazily;
* `runLazyQ_of_stored`: a program whose every question (along a complete oracle) is stored in the
  lazy state is answered deterministically, and leaves the state alone;
* `transcript_bind`, `mem_transcript_vector`, `mem_transcript_pi`: where an entry of a transcript
  comes from;
* `plantAll_stored`: installing entries of a complete oracle on a state consistent with it keeps it
  consistent, and every installed forward entry is then stored (a skipped program was already
  stored, by consistency).
-/

import Proof.Privacy.Phase3.PublicFirst.Private
import Proof.Privacy.Phase3.PublicFirst.OffCurve

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Scheme (Oracle)
open Kriterion.ArgoMAC.Phase3.Lazy (LState)
open scoped ENNReal

noncomputable section

/-! ### 1. Running a bounded free program -/

section Run

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- A bounded free query program, as an adversary's `OracleProgram`. -/
def freeOracle {α : Type} : (c : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) →
    (budget : ℕ) → FreeQuery.Bounded c budget →
      OracleProgram (publicOracleSpec FixedIndex EncIndex) α budget
  | .pure value, _, _ => .pure (PMF.pure value)
  | .query _ _, 0, bounded => absurd bounded FreeQuery.Bounded.not_zero
  | .query request next, budget + 1, bounded =>
      .query request fun answer => freeOracle (next answer) budget (bounded.next answer)

/-- **The lazy run of the adversary program is the lazy run of the free program.** -/
theorem run_freeOracle {α : Type} (c : FreeQuery (publicOracleSpec FixedIndex EncIndex) α) :
    ∀ (budget : ℕ) (bounded : FreeQuery.Bounded c budget)
      (state : LazyOracle.State FixedIndex EncIndex),
      LazyOracle.run (freeOracle c budget bounded) state = runLazyQ c state := by
  induction c with
  | pure value =>
    intro budget bounded state
    show (PMF.pure value).map (fun result => (result, state)) = PMF.pure (value, state)
    rw [PMF.pure_map]
  | query request next ih =>
    intro budget bounded state
    cases budget with
    | zero => exact absurd bounded FreeQuery.Bounded.not_zero
    | succ budget =>
      show (LazyOracle.query request state).bind (fun answer =>
          LazyOracle.run (freeOracle (next answer.1) budget (bounded.next answer.1)) answer.2) = _
      simp only [runLazyQ]
      congr 1
      funext answer
      exact ih answer.1 budget _ answer.2

/-- The lazy run of a sequence. -/
theorem runLazyQ_bind {α β : Type} (c : FreeQuery (publicOracleSpec FixedIndex EncIndex) α)
    (f : α → FreeQuery (publicOracleSpec FixedIndex EncIndex) β) :
    ∀ state, runLazyQ (c >>= f) state = (runLazyQ c state).bind fun r => runLazyQ (f r.1) r.2 := by
  induction c with
  | pure value =>
    intro state
    show runLazyQ (f value) state = (PMF.pure (value, state)).bind _
    rw [PMF.pure_bind]
  | query request next ih =>
    intro state
    show (LazyOracle.query request state).bind (fun answer =>
        runLazyQ (next answer.1 >>= f) answer.2) = _
    simp only [runLazyQ, PMF.bind_bind]
    congr 1
    funext answer
    exact ih answer.1 answer.2

end Run

/-! ### 2. Transcripts -/

section Transcript

variable (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer)

theorem transcript_bind {α β : Type} (c : FreeQuery Programs.Spec α)
    (f : α → FreeQuery Programs.Spec β) :
    transcript answer (c >>= f) =
      transcript answer c ++ transcript answer (f (FreeQuery.eval answer c)) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
    show ⟨request, answer request⟩ :: transcript answer (next (answer request) >>= f) = _
    rw [ih]
    rfl

theorem mem_transcript_left {α β : Type} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer c) : entry ∈ transcript answer (c >>= f) := by
  rw [transcript_bind]
  exact List.mem_append_left _ member

theorem mem_transcript_right {α β : Type} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (f (FreeQuery.eval answer c))) :
    entry ∈ transcript answer (c >>= f) := by
  rw [transcript_bind]
  exact List.mem_append_right _ member

theorem mem_transcript_vector {α : Type} {entry : Entry FixedIndex EncPRF.PermutationIndex} :
    ∀ (count : ℕ) (program : Fin count → FreeQuery Programs.Spec α) (index : Fin count),
      entry ∈ transcript answer (program index) →
        entry ∈ transcript answer (FreeQuery.vector count program)
  | 0, _, index, _ => index.elim0
  | count + 1, program, index, member => by
      show entry ∈ transcript answer (FreeQuery.vector count (fun index => program index.castSucc)
        >>= fun values => program (Fin.last count) >>= fun value =>
          (Pure.pure (values.push value) : FreeQuery Programs.Spec (Vector α (count + 1))))
      induction index using Fin.lastCases with
      | last => exact mem_transcript_right answer (mem_transcript_left answer member)
      | cast index =>
        exact mem_transcript_left answer
          (mem_transcript_vector count (fun index => program index.castSucc) index member)

theorem mem_transcript_pi {entry : Entry FixedIndex EncPRF.PermutationIndex} :
    ∀ (count : ℕ) {β : Fin count → Type} (program : (index : Fin count) →
      FreeQuery Programs.Spec (β index)) (index : Fin count),
      entry ∈ transcript answer (program index) →
        entry ∈ transcript answer (FreeQuery.pi count program)
  | 0, _, _, index, _ => index.elim0
  | count + 1, β, program, index, member => by
      show entry ∈ transcript answer (program 0 >>= fun head =>
        FreeQuery.pi count (fun index => program index.succ) >>= fun tail =>
          (Pure.pure (Fin.cons (α := β) head tail) :
            FreeQuery Programs.Spec ((index : Fin (count + 1)) → β index)))
      induction index using Fin.cases with
      | zero => exact mem_transcript_left answer member
      | succ index =>
        exact mem_transcript_right answer (mem_transcript_left answer
          (mem_transcript_pi count (fun index => program index.succ) index member))

theorem transcript_askFixed (index : FixedIndex) (input : Block) :
    transcript answer (Programs.askFixed index input) =
      [⟨.fixedForward index input, answer (.fixedForward index input)⟩] := rfl

/-- Every transcript entry carries the complete oracle's answer. -/
theorem transcript_answer {α : Type} (c : FreeQuery Programs.Spec α)
    {entry : Entry FixedIndex EncPRF.PermutationIndex} (member : entry ∈ transcript answer c) :
    entry.2 = answer entry.1 := by
  induction c with
  | pure value => cases member
  | query request next ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst same
      rfl
    · exact ih _ rest

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **A program whose questions are stored runs deterministically**, leaving the state alone. -/
theorem runLazyQ_of_stored {α : Type} (c : FreeQuery Programs.Spec α) (state : LState)
    (stored : ∀ entry ∈ transcript answer c,
      LazyOracle.query entry.1 state = PMF.pure (entry.2, state)) :
    runLazyQ c state = PMF.pure (FreeQuery.eval answer c, state) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
    have head := stored ⟨request, answer request⟩ List.mem_cons_self
    show (LazyOracle.query request state).bind _ = _
    rw [head, PMF.pure_bind]
    exact ih (answer request) fun entry member => stored entry (List.mem_cons_of_mem _ member)

/-- A stored forward pair is answered without sampling. -/
theorem query_fixedForward_stored (state : LState) (index : FixedIndex) (input output : Block)
    (found : lk (state.fixed index) input.toFin = some output.toFin) :
    LazyOracle.query (.fixedForward index input) state = PMF.pure (output, state) := by
  have forward := LazyOracle.lookup_forward (state.fixed index) input.toFin output.toFin found
  show ((state.fixed index).forward input.toFin).distribution.map (fun answer =>
    (BitVec.ofFin answer.1, { state with fixed := Function.update state.fixed index answer.2 })) = _
  rw [forward]
  simp only [Draw.distribution, PMF.pure_map, Function.update_eq_self, BitVec.ofFin_toFin]

end Transcript

/-! ### 3. Installing a complete oracle's entries -/

section Install

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- Every stored fixed-key pair of a state is the complete oracle's. -/
def FixedConsistent (oracle : PermutationOracle FixedIndex Block) (state : LState) : Prop :=
  ∀ (index : FixedIndex) (z y : Fin (2 ^ 128)), lk (state.fixed index) z = some y →
    oracle.permutation index (BitVec.ofFin z) = BitVec.ofFin y

theorem fixedConsistent_empty (oracle : PermutationOracle FixedIndex Block) :
    FixedConsistent oracle LazyOracle.empty := by
  intro index z y found
  rw [show (LazyOracle.empty : LState).fixed index = SparsePermutation.empty _ from rfl,
    lk_empty] at found
  cases found

/-- A consistent state stores a forward pair of the oracle as soon as it knows its input or its
output. -/
theorem stored_of_known (oracle : PermutationOracle FixedIndex Block) {state : LState}
    (consistent : FixedConsistent oracle state) (index : FixedIndex) (input : Block)
    (known : (state.fixed index).knownInput input.toFin ∨
      (state.fixed index).knownOutput (oracle.permutation index input).toFin) :
    lk (state.fixed index) input.toFin = some (oracle.permutation index input).toFin := by
  rcases known with knownIn | knownOut
  · obtain ⟨y, found⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp knownIn)
    have value := consistent index _ y found
    rw [BitVec.ofFin_toFin] at value
    rw [found, value, BitVec.toFin_ofFin]
  · obtain ⟨z, found⟩ := (knownOutput_iff _ _).mp knownOut
    have value := consistent index z _ found
    rw [BitVec.ofFin_toFin] at value
    have same : BitVec.ofFin z = input := (oracle.permutation index).injective value
    have hz : z = input.toFin := by rw [← same]
    rw [← hz]
    exact found

/-- The answer of a complete oracle, as an entry predicate. -/
def OracleEntry (tape : Oracle) (entry : Entry FixedIndex EncPRF.PermutationIndex) : Prop :=
  entry.2 = publicAnswer tape entry.1

theorem lk_update_self (state : LState) (index : FixedIndex) (next : SparsePermutation (2 ^ 128))
    (z : Fin (2 ^ 128)) :
    lk (({ state with fixed := Function.update state.fixed index next } : LState).fixed index) z
      = lk next z := by
  simp

theorem lk_update_other (state : LState) (index other : FixedIndex)
    (next : SparsePermutation (2 ^ 128)) (different : other ≠ index) (z : Fin (2 ^ 128)) :
    lk (({ state with fixed := Function.update state.fixed index next } : LState).fixed other) z
      = lk (state.fixed other) z := by
  simp [Function.update_of_ne different]

/-- **One installation step**: it keeps consistency, keeps every stored pair, and stores the entry
if it is a forward pair. -/
theorem plantEntry_consistent (tape : Oracle) {state : LState}
    (consistent : FixedConsistent tape.1 state) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (oracleEntry : OracleEntry tape entry) :
    FixedConsistent tape.1 (plantEntry state entry) ∧
      (∀ index z y, lk (state.fixed index) z = some y →
        lk ((plantEntry state entry).fixed index) z = some y) ∧
      (∀ index input, entry.1 = .fixedForward index input →
        lk ((plantEntry state entry).fixed index) input.toFin
          = some (tape.1.permutation index input).toFin) := by
  obtain ⟨request, value⟩ := entry
  unfold OracleEntry at oracleEntry
  simp only at oracleEntry
  subst oracleEntry
  cases request with
  | fixedForward index input =>
    unfold plantEntry
    simp only [LazyOracle.program]
    cases success : LazyOracle.permutationProgram (state.fixed index) input.toFin
        (publicAnswer tape (.fixedForward index input)).toFin with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      refine ⟨consistent, fun _ _ _ found => found, ?_⟩
      intro index' input' same
      simp only [PublicQuery.fixedForward.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      refine stored_of_known tape.1 consistent index input ?_
      have stale : ¬ (¬ (state.fixed index).knownInput input.toFin ∧
          ¬ (state.fixed index).knownOutput (publicAnswer tape (.fixedForward index input)).toFin) := by
        intro fresh
        have some := (permutationProgram_isSome_iff _ _ _).mpr fresh
        rw [success] at some
        cases some
      by_contra neither
      exact stale ⟨fun k => neither (Or.inl k), fun k => neither (Or.inr k)⟩
    | some next =>
      simp only [Option.map_some, Option.getD_some]
      have fresh := (permutationProgram_isSome_iff _ _ _).mp (by rw [success]; rfl)
      refine ⟨?_, ?_, ?_⟩
      · intro index' z y found
        by_cases same : index' = index
        · subst same
          rw [lk_update_self, lk_permutationProgram success] at found
          split at found
          · rename_i hz
            cases found
            subst hz
            rw [BitVec.ofFin_toFin]
            rfl
          · exact consistent _ z y found
        · rw [lk_update_other _ _ _ _ same] at found
          exact consistent _ z y found
      · intro index' z y found
        by_cases same : index' = index
        · subst same
          rw [lk_update_self, lk_permutationProgram success]
          have different : z ≠ input.toFin := by
            rintro rfl
            exact fresh.1 ((knownInput_iff _ _).mpr (by rw [found]; exact Option.some_ne_none _))
          rw [if_neg different]
          exact found
        · rw [lk_update_other _ _ _ _ same]
          exact found
      · intro index' input' same
        simp only [PublicQuery.fixedForward.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        rw [lk_update_self, lk_permutationProgram success, if_pos rfl]
        rfl
  | fixedInverse index output =>
    unfold plantEntry
    simp only [LazyOracle.program]
    cases success : LazyOracle.permutationProgram (state.fixed index)
        (publicAnswer tape (.fixedInverse index output)).toFin output.toFin with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
    | some next =>
      simp only [Option.map_some, Option.getD_some]
      have fresh := (permutationProgram_isSome_iff _ _ _).mp (by rw [success]; rfl)
      refine ⟨?_, ?_, fun _ _ same => by cases same⟩
      · intro index' z y found
        by_cases same : index' = index
        · subst same
          rw [lk_update_self, lk_permutationProgram success] at found
          split at found
          · rename_i hz
            cases found
            subst hz
            exact (tape.1.permutation index').apply_symm_apply output
          · exact consistent _ z y found
        · rw [lk_update_other _ _ _ _ same] at found
          exact consistent _ z y found
      · intro index' z y found
        by_cases same : index' = index
        · subst same
          rw [lk_update_self, lk_permutationProgram success]
          have different : z ≠ (publicAnswer tape (.fixedInverse index' output)).toFin := by
            intro hz
            rw [hz] at found
            exact fresh.1 ((knownInput_iff _ _).mpr (by rw [found]; exact Option.some_ne_none _))
          rw [if_neg different]
          exact found
        · rw [lk_update_other _ _ _ _ same]
          exact found
  | encForward index input =>
    unfold plantEntry
    simp only [LazyOracle.program]
    cases LazyOracle.permutationProgram (state.enc index) input.toFin
        (publicAnswer tape (.encForward index input)).toFin with
    | none => exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
    | some next => exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
  | encInverse index output =>
    unfold plantEntry
    simp only [LazyOracle.program]
    cases LazyOracle.permutationProgram (state.enc index)
        (publicAnswer tape (.encInverse index output)).toFin output.toFin with
    | none => exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
    | some next => exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
  | hash input =>
    unfold plantEntry
    simp only [LazyOracle.program]
    split
    · exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩
    · exact ⟨consistent, fun _ _ _ found => found, fun _ _ same => by cases same⟩

/-- **Installing a complete oracle's entries** keeps a consistent state consistent and stores every
forward entry of the list. -/
theorem plantAll_stored (tape : Oracle) :
    ∀ (entries : List (Entry FixedIndex EncPRF.PermutationIndex)) (state : LState),
      FixedConsistent tape.1 state → (∀ entry ∈ entries, OracleEntry tape entry) →
        FixedConsistent tape.1 (plantAll entries state) ∧
          ∀ index input,
            (lk (state.fixed index) input.toFin = some (tape.1.permutation index input).toFin ∨
              (⟨.fixedForward index input, tape.1.permutation index input⟩ :
                Entry FixedIndex EncPRF.PermutationIndex) ∈ entries) →
            lk ((plantAll entries state).fixed index) input.toFin
              = some (tape.1.permutation index input).toFin
  | [], state, consistent, _ => ⟨consistent, fun _ _ held => by
      rcases held with found | member
      · exact found
      · cases member⟩
  | entry :: rest, state, consistent, entries => by
      obtain ⟨nextConsistent, keeps, stores⟩ :=
        plantEntry_consistent tape consistent entry (entries entry List.mem_cons_self)
      obtain ⟨finalConsistent, finalStored⟩ := plantAll_stored tape rest (plantEntry state entry)
        nextConsistent fun other member => entries other (List.mem_cons_of_mem _ member)
      refine ⟨finalConsistent, fun index input held => finalStored index input ?_⟩
      rcases held with found | member
      · exact Or.inl (keeps index _ _ found)
      · rcases List.mem_cons.mp member with same | later
        · subst same
          exact Or.inl (stores index input rfl)
        · exact Or.inr later

end Install

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
