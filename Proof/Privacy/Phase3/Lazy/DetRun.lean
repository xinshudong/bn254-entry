/-
**Phase 3, P4b — the refill runner where it needs no randomness.**

On a fixed tape, a query that is intercepted (a designated index) or consumed (a first touch of a
mask-site index at an unknown input) is answered deterministically. `detRun` runs a program that
way; `none` means it met a query needing the lazy oracle.

* `detRun_spec` — where `detRun` succeeds, the refill run is the point mass at its result.
* `detRun_value` — the value is the program evaluated against the tape answers `tapeAnswer`
  (a designated query gets its own input, a mask-site query `tape cell xor input`), so the
  Davies–Meyer hashes it computes are the tape limbs (or `0`), **whatever the labels**.
* `detRun_ne_none` — it succeeds when every query along the tape path is intercepted or is a
  first touch at an unknown input, at pairwise distinct indices (`queriesAlong`).
* `detRun_frame`, `detRun_record` — what a successful run changes.
-/

import Proof.Privacy.Phase3.Lazy.RunFrame

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

section Det

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (tape : Tape)

/-- **The refill runner on a tape, without randomness.** The outer `none`: a query needing the
lazy oracle was met. The inner `none`: a failed program (an abort of the run). -/
def detRun {α : Type} : FreeQuery Programs.Spec α → LState → Record → Set FixedIndex →
    Option (Option (α × LState × Record × Set FixedIndex))
  | .pure value, oracle, record, touched => some (some (value, oracle, record, touched))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => detRun (next answer) oracle (recordAfter bits request record) touched
      | none => match consumeCell touched oracle request with
        | some cell =>
            match LazyOracle.program request (refillAnswer request (tape cell)) oracle with
            | none => some none
            | some updated => detRun (next (refillAnswer request (tape cell))) updated record
                (touch request touched)
        | none => none

theorem detRun_intercepted {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set FixedIndex) (answer : request.Answer)
    (intercepted : interceptAnswer bits request = some answer) :
    detRun bits tape (.query request next) oracle record touched =
      detRun bits tape (next answer) oracle (recordAfter bits request record) touched := by
  conv_lhs => unfold detRun
  rw [intercepted]

theorem detRun_consumed {α : Type} (request : Request)
    (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState) (record : Record)
    (touched : Set FixedIndex) (cell : Cell) (intercept : interceptAnswer bits request = none)
    (consume : consumeCell touched oracle request = some cell) :
    detRun bits tape (.query request next) oracle record touched =
      match LazyOracle.program request (refillAnswer request (tape cell)) oracle with
      | none => some none
      | some updated => detRun bits tape (next (refillAnswer request (tape cell))) updated record
          (touch request touched) := by
  conv_lhs => unfold detRun
  rw [intercept]
  dsimp only
  rw [consume]

/-- **Where `detRun` succeeds, the refill run on the tape is its point mass.** -/
theorem detRun_spec {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex)
      (result : Option (α × LState × Record × Set FixedIndex)),
      detRun bits tape c oracle record touched = some result →
        runRefillT bits (fun cell => PMF.pure (tape cell)) c oracle record touched =
          PMF.pure result := by
  induction c with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      rfl
  | query request next ih =>
      intro oracle record touched result success
      cases intercept : interceptAnswer bits request with
      | some answer =>
          simp only [detRun, intercept] at success
          rw [runRefillT_intercepted bits _ request next oracle record touched answer intercept]
          exact ih _ _ _ _ _ success
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              rw [runRefillT_consumed bits _ request next oracle record touched cell intercept
                consume, PMF.pure_bind]
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none =>
                  simp only [programmed, Option.some.injEq] at success
                  subst success
                  rfl
              | some updated =>
                  simp only [programmed] at success
                  exact ih _ _ _ _ _ success
          | none => simp [detRun, intercept, consume] at success

/-- The bind law of `detRun`'s spec: a successful first part hands over to the rest. -/
theorem detRun_bind_spec {α β : Type} (c : FreeQuery Programs.Spec α)
    (k : α → FreeQuery Programs.Spec β) (oracle : LState) (record : Record)
    (touched : Set FixedIndex) (result : Option (α × LState × Record × Set FixedIndex))
    (success : detRun bits tape c oracle record touched = some result) :
    runRefillT bits (fun cell => PMF.pure (tape cell)) (c >>= k) oracle record touched =
      continueT bits (fun cell => PMF.pure (tape cell)) k result := by
  rw [runRefillT_bind, detRun_spec bits tape c oracle record touched result success,
    PMF.pure_bind]

/-! ### The value -/

theorem interceptAnswer_designated {index : FixedIndex} (input : Block)
    (designated : IsDesignated bits index) :
    interceptAnswer bits (.fixedForward index input) = some input := by
  simp only [interceptAnswer]
  exact if_pos designated

theorem interceptAnswer_plain {index : FixedIndex} (input : Block)
    (notDesignated : ¬ IsDesignated bits index) :
    interceptAnswer bits (.fixedForward index input) = none := by
  simp only [interceptAnswer]
  exact if_neg notDesignated

open Classical in
/-- The tape answer of a forward fixed-key query. -/
def tapeBlock (index : FixedIndex) (input : Block) : Block :=
  if IsDesignated bits index then input else
    match cellOf index with
    | some cell => tape cell ^^^ input
    | none => 0

/-- **The tape answers**: a designated forward query gets its own input (Davies–Meyer hash `0`),
a mask-site query `tape cell xor input` (hash `tape cell`). -/
def tapeAnswer : (request : Request) → request.Answer
  | .fixedForward index input => tapeBlock bits tape index input
  | .fixedInverse _ _ => (0 : Block)
  | .encForward _ _ => (0 : Block)
  | .encInverse _ _ => (0 : Block)
  | .hash _ => ((0 : Block), (0 : Block))

theorem tapeAnswer_forward (index : FixedIndex) (input : Block) :
    tapeAnswer bits tape (.fixedForward index input) = tapeBlock bits tape index input := rfl

theorem tapeBlock_designated {index : FixedIndex} (input : Block)
    (designated : IsDesignated bits index) : tapeBlock bits tape index input = input := by
  unfold tapeBlock
  rw [if_pos designated]

theorem tapeBlock_cell {index : FixedIndex} (input : Block) {cell : Cell}
    (notDesignated : ¬ IsDesignated bits index) (found : cellOf index = some cell) :
    tapeBlock bits tape index input = tape cell ^^^ input := by
  unfold tapeBlock
  rw [if_neg notDesignated, found]

theorem interceptAnswer_tapeAnswer {request : Request} {answer : request.Answer}
    (intercepted : interceptAnswer bits request = some answer) :
    answer = tapeAnswer bits tape request := by
  cases request with
  | fixedForward index input =>
      by_cases designated : IsDesignated bits index
      · rw [interceptAnswer_designated bits input designated] at intercepted
        cases intercepted
        exact (tapeBlock_designated bits tape input designated).symm
      · rw [interceptAnswer_plain bits input designated] at intercepted
        cases intercepted
  | fixedInverse _ _ => simp [interceptAnswer] at intercepted
  | encForward _ _ => simp [interceptAnswer] at intercepted
  | encInverse _ _ => simp [interceptAnswer] at intercepted
  | hash _ => simp [interceptAnswer] at intercepted

theorem consumeCell_tapeAnswer {request : Request} {touched : Set FixedIndex} {oracle : LState}
    {cell : Cell} (intercept : interceptAnswer bits request = none)
    (consumed : consumeCell touched oracle request = some cell) :
    refillAnswer request (tape cell) = tapeAnswer bits tape request := by
  obtain ⟨index, input, rfl, _, _, found⟩ := consumeCell_spec consumed
  have notDesignated : ¬ IsDesignated bits index := by
    intro designated
    rw [interceptAnswer_designated bits input designated] at intercept
    cases intercept
  have cellEq : cellOf index = some cell := by
    rw [← found]
    exact cellOf_siteIndex cell
  exact (tapeBlock_cell bits tape input notDesignated cellEq).symm

/-- **The value of a successful `detRun` is the program against the tape answers.** -/
theorem detRun_value {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex)
      (result : α × LState × Record × Set FixedIndex),
      detRun bits tape c oracle record touched = some (some result) →
        result.1 = FreeQuery.eval (tapeAnswer bits tape) c := by
  induction c with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      rfl
  | query request next ih =>
      intro oracle record touched result success
      cases intercept : interceptAnswer bits request with
      | some answer =>
          simp only [detRun, intercept] at success
          rw [ih _ _ _ _ _ success, interceptAnswer_tapeAnswer bits tape intercept]
          rfl
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none => simp [programmed] at success
              | some updated =>
                  simp only [programmed] at success
                  rw [ih _ _ _ _ _ success, consumeCell_tapeAnswer bits tape intercept consume]
                  rfl
          | none => simp [detRun, intercept, consume] at success

/-! ### When `detRun` succeeds -/

/-- The queries along the path an answer function selects. -/
def queriesAlong {α : Type} (answer : (request : Request) → request.Answer) :
    FreeQuery Programs.Spec α → List Request
  | .pure _ => []
  | .query request next => request :: queriesAlong answer (next (answer request))

theorem queriesAlong_bind {α β : Type} (answer : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α) (f : α → FreeQuery Programs.Spec β) :
    queriesAlong answer (c >>= f) =
      queriesAlong answer c ++ queriesAlong answer (f (FreeQuery.eval answer c)) := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show request :: queriesAlong answer (next (answer request) >>= f) = _
      rw [ih]
      rfl

theorem queriesAlong_pure {α : Type} (answer : (request : Request) → request.Answer) (value : α) :
    queriesAlong answer (Pure.pure value : FreeQuery Programs.Spec α) = [] := rfl

theorem queriesAlong_vector {α : Type} (answer : (request : Request) → request.Answer) :
    ∀ (count : Nat) (program : Fin count → FreeQuery Programs.Spec α),
      queriesAlong answer (FreeQuery.vector count program) =
        (List.finRange count).flatMap fun index => queriesAlong answer (program index)
  | 0, _ => rfl
  | count + 1, program => by
      show queriesAlong answer (FreeQuery.vector count (fun index => program index.castSucc) >>=
        fun values => program (Fin.last count) >>= fun value => Pure.pure (values.push value)) = _
      rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil,
        queriesAlong_vector answer count, List.finRange_succ_last, List.flatMap_append,
        List.flatMap_map, List.flatMap_singleton]

open Classical in
/-- The index a request consumes, if it is a non-designated forward query. -/
def consumedIndex : Request → Option FixedIndex
  | .fixedForward index _ => if IsDesignated bits index then none else some index
  | _ => none

theorem consumedIndex_designated {index : FixedIndex} (input : Block)
    (designated : IsDesignated bits index) :
    consumedIndex bits (.fixedForward index input) = none := by
  simp only [consumedIndex]
  exact if_pos designated

theorem consumedIndex_plain {index : FixedIndex} (input : Block)
    (notDesignated : ¬ IsDesignated bits index) :
    consumedIndex bits (.fixedForward index input) = some index := by
  simp only [consumedIndex]
  exact if_neg notDesignated

/-- A request the tape runner answers from `(oracle, touched)`: a designated forward query, or a
first touch of a mask-site index at an unknown input. -/
def TapeReady (oracle : LState) (touched : Set FixedIndex) : Request → Prop
  | .fixedForward index input => IsDesignated bits index ∨
      (index ∉ touched ∧ ¬ (oracle.fixed index).knownInput input.toFin ∧ cellOf index ≠ none)
  | .fixedInverse _ _ => False
  | .encForward _ _ => False
  | .encInverse _ _ => False
  | .hash _ => False

/-- **`detRun` succeeds** when every query along the tape path is ready and the consumed indices
are pairwise distinct. -/
theorem detRun_ne_none {α : Type} (c : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      (∀ request ∈ queriesAlong (tapeAnswer bits tape) c, TapeReady bits oracle touched request) →
      ((queriesAlong (tapeAnswer bits tape) c).filterMap (consumedIndex bits)).Nodup →
        detRun bits tape c oracle record touched ≠ none := by
  induction c with
  | pure value => intro oracle record touched _ _; simp [detRun]
  | query request next ih =>
      intro oracle record touched ready distinct
      have here := ready request List.mem_cons_self
      have later : ∀ r ∈ queriesAlong (tapeAnswer bits tape) (next (tapeAnswer bits tape request)),
          TapeReady bits oracle touched r := fun r member =>
        ready r (List.mem_cons_of_mem _ member)
      cases request with
      | fixedForward index input =>
          by_cases designated : IsDesignated bits index
          · have intercept := interceptAnswer_designated bits input designated
            have answerEq : tapeAnswer bits tape (.fixedForward index input) = input :=
              (tapeAnswer_forward bits tape index input).trans
                (tapeBlock_designated bits tape input designated)
            rw [detRun_intercepted bits tape (.fixedForward index input) next oracle record touched
              input intercept]
            rw [answerEq] at later
            refine ih input _ _ _ later ?_
            have tailDistinct := distinct
            simp only [queriesAlong, List.filterMap_cons] at tailDistinct
            rw [consumedIndex_designated bits input designated, answerEq] at tailDistinct
            exact tailDistinct
          · obtain ⟨untouched, fresh, isCell⟩ := here.resolve_left designated
            obtain ⟨cell, cellEq⟩ := Option.ne_none_iff_exists'.mp isCell
            have intercept := interceptAnswer_plain bits input designated
            have consume : consumeCell touched oracle (.fixedForward index input) = some cell := by
              simp only [consumeCell]
              rw [if_neg (by rintro (hit | hit) <;> contradiction), cellEq]
            have answerEq : refillAnswer (.fixedForward index input) (tape cell) =
                tapeAnswer bits tape (.fixedForward index input) :=
              consumeCell_tapeAnswer bits tape intercept consume
            rw [detRun_consumed bits tape (.fixedForward index input) next oracle record touched
              cell intercept consume]
            cases programmed : LazyOracle.program (.fixedForward index input)
                (refillAnswer (.fixedForward index input) (tape cell)) oracle with
            | none => simp
            | some updated =>
                simp only
                rw [answerEq]
                have distinct' := distinct
                simp only [queriesAlong, List.filterMap_cons] at distinct'
                rw [consumedIndex_plain bits input designated] at distinct'
                simp only [List.nodup_cons] at distinct'
                refine ih _ _ _ _ (fun r member => ?_) distinct'.2
                have old := later r member
                cases r with
                | fixedForward index' input' =>
                    by_cases designated' : IsDesignated bits index'
                    · exact Or.inl designated'
                    · obtain ⟨untouched', fresh', isCell'⟩ := old.resolve_left designated'
                      have different : index' ≠ index := by
                        intro same
                        apply distinct'.1
                        refine List.mem_filterMap.mpr ⟨.fixedForward index' input', member, ?_⟩
                        rw [consumedIndex_plain bits input' designated', same]
                      refine Or.inr ⟨?_, ?_, isCell'⟩
                      · simp only [touch, Set.mem_ofPred_eq, touchedIndex, Option.some.injEq]
                        rintro (hit | hit)
                        · exact untouched' hit
                        · exact different hit.symm
                      · rw [program_frame index input _ oracle updated programmed index' different]
                        exact fresh'
                | fixedInverse _ _ => exact old.elim
                | encForward _ _ => exact old.elim
                | encInverse _ _ => exact old.elim
                | hash _ => exact old.elim
      | fixedInverse _ _ => exact here.elim
      | encForward _ _ => exact here.elim
      | encInverse _ _ => exact here.elim
      | hash _ => exact here.elim

/-- **What a successful `detRun` changes**: only indices its forward queries name (state and
touched mark); never the EncPRF or hash parts. -/
theorem detRun_frame {α : Type} (S : FixedIndex → Prop) {c : FreeQuery Programs.Spec α}
    (inside : AllQ (FixedAt S) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex)
      (result : α × LState × Record × Set FixedIndex),
      detRun bits tape c oracle record touched = some (some result) →
        (∀ index, ¬ S index → result.2.1.fixed index = oracle.fixed index ∧
          (index ∈ result.2.2.2 ↔ index ∈ touched)) ∧
        result.2.1.enc = oracle.enc ∧ result.2.1.hash = oracle.hash := by
  induction inside with
  | pure value =>
      intro oracle record touched result success
      simp only [detRun, Option.some.injEq] at success
      subst success
      exact ⟨fun _ _ => ⟨rfl, Iff.rfl⟩, rfl, rfl⟩
  | query request next here _ ih =>
      intro oracle record touched result success
      cases request with
      | fixedForward index input =>
          cases intercept : interceptAnswer bits (.fixedForward index input) with
          | some answer =>
              simp only [detRun, intercept] at success
              exact ih _ _ _ _ _ success
          | none =>
              cases consume : consumeCell touched oracle (.fixedForward index input) with
              | some cell =>
                  simp only [detRun, intercept, consume] at success
                  cases programmed : LazyOracle.program (.fixedForward index input)
                      (refillAnswer (.fixedForward index input) (tape cell)) oracle with
                  | none => simp [programmed] at success
                  | some updated =>
                      simp only [programmed] at success
                      obtain ⟨frame, encSame, hashSame⟩ := ih _ _ _ _ _ success
                      have updatedShape : updated.enc = oracle.enc ∧ updated.hash = oracle.hash := by
                        simp only [LazyOracle.program] at programmed
                        obtain ⟨next', _, rfl⟩ := Option.map_eq_some_iff.mp programmed
                        exact ⟨rfl, rfl⟩
                      refine ⟨fun other outside => ?_, encSame.trans updatedShape.1,
                        hashSame.trans updatedShape.2⟩
                      have different : other ≠ index := fun same => outside (same ▸ here)
                      obtain ⟨stateSame, touchedSame⟩ := frame other outside
                      refine ⟨stateSame.trans (program_frame index input _ oracle updated
                        programmed other different), touchedSame.trans ?_⟩
                      simp only [touch, Set.mem_ofPred_eq, touchedIndex, Option.some.injEq]
                      exact ⟨fun hit => hit.elim id fun same => (different same.symm).elim,
                        Or.inl⟩
              | none => simp [detRun, intercept, consume] at success
      | fixedInverse _ _ => exact here.elim
      | encForward _ _ => exact here.elim
      | encInverse _ _ => exact here.elim
      | hash _ => exact here.elim

/-- **The records a successful `detRun` writes**: if every designated forward query of the program
carries the input `label`, each record entry is the old one or `label`. -/
theorem detRun_record {α : Type} (label : Block) {c : FreeQuery Programs.Spec α}
    (labelled : AllQ (fun request => ∀ index input, request = .fixedForward index input →
      IsDesignated bits index → input = label) c) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex)
      (result : α × LState × Record × Set FixedIndex),
      detRun bits tape c oracle record touched = some (some result) →
        ∀ index, result.2.2.1 index = record index ∨ result.2.2.1 index = some label := by
  induction labelled with
  | pure value =>
      intro oracle record touched result success index
      simp only [detRun, Option.some.injEq] at success
      subst success
      exact Or.inl rfl
  | query request next here _ ih =>
      intro oracle record touched result success index
      cases intercept : interceptAnswer bits request with
      | some answer =>
          simp only [detRun, intercept] at success
          rcases ih _ _ _ _ _ success index with same | same
          · cases request with
            | fixedForward index' input =>
                simp only [recordAfter] at same
                split_ifs at same with designated
                · by_cases hit : index = index'
                  · subst hit
                    rw [Function.update_self] at same
                    exact Or.inr (same.trans (congrArg some (here _ _ rfl designated)))
                  · rw [Function.update_of_ne hit] at same
                    exact Or.inl same
                · exact Or.inl same
            | fixedInverse _ _ => exact Or.inl same
            | encForward _ _ => exact Or.inl same
            | encInverse _ _ => exact Or.inl same
            | hash _ => exact Or.inl same
          · exact Or.inr same
      | none =>
          cases consume : consumeCell touched oracle request with
          | some cell =>
              simp only [detRun, intercept, consume] at success
              cases programmed : LazyOracle.program request (refillAnswer request (tape cell))
                  oracle with
              | none => simp [programmed] at success
              | some updated =>
                  simp only [programmed] at success
                  exact ih _ _ _ _ _ success index
          | none => simp [detRun, intercept, consume] at success

end Det

end

end Kriterion.ArgoMAC.Phase3.Lazy
