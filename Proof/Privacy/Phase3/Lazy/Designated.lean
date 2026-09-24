/-
**Phase 3, P4 — evaluator unfolding (a): every designated index is recorded.**

Event (a) of the abort analysis: a designated request with a missing input. In `I^U` it aborts; in
`H` it is skipped. It never happens: the honest evaluation `openingQueriesM` asks, **on every
path**, a forward query at each of the 819 designated indices, because switch `j* = α₀ xor 1` is
inactive, so `evalMasksM` evaluates its `switchMaskM` at every `pointX` element and block. The
refill runner intercepts each such query and records its input (`designated_recorded`).

* `QueriesAt index c` — every path of `c` makes a forward query at `index`. It is closed under
  `bind` on either side (`bind_left`, `bind_right`) and under `FreeQuery.vector` at any iteration
  (`vector`).
* `openingQueriesM_queriesAt` — the evaluation queries every designated index.
* `runRefill_records` — a program that queries a designated index leaves it recorded, whatever the
  tape law.
-/

import Proof.Privacy.Phase3.Lazy.AbortReduction

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- Every path of the program makes a forward query at `index`. -/
inductive QueriesAt (index : FixedIndex) {α : Type} : FreeQuery Programs.Spec α → Prop
  | here (input : Block) (next : Block → FreeQuery Programs.Spec α) :
      QueriesAt index (.query (.fixedForward index input) next)
  | later (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) :
      (∀ answer, QueriesAt index (next answer)) → QueriesAt index (.query request next)

namespace QueriesAt

variable {index : FixedIndex} {α β : Type}

/-- A path through `c` then `f` contains a path through `c`. -/
theorem bind_left {c : FreeQuery Programs.Spec α} (queries : QueriesAt index c)
    (f : α → FreeQuery Programs.Spec β) : QueriesAt index (c >>= f) := by
  induction queries with
  | here input next => exact .here input _
  | later request next _ ih => exact .later request _ ih

/-- If every continuation queries, so does the sequence. -/
theorem bind_right (c : FreeQuery Programs.Spec α) {f : α → FreeQuery Programs.Spec β}
    (queries : ∀ value, QueriesAt index (f value)) : QueriesAt index (c >>= f) := by
  induction c with
  | pure value => exact queries value
  | query request next ih => exact .later request _ ih

/-- A loop queries if one iteration does. -/
theorem vector {count : Nat} (program : Fin count → FreeQuery Programs.Spec α) (iteration : Fin count)
    (queries : QueriesAt index (program iteration)) :
    QueriesAt index (FreeQuery.vector count program) := by
  induction count with
  | zero => exact iteration.elim0
  | succ count ih =>
      show QueriesAt index (FreeQuery.vector count (fun i => program i.castSucc) >>= fun values =>
        program (Fin.last count) >>= fun value => Pure.pure (values.push value))
      by_cases last : iteration = Fin.last count
      · subst last
        exact bind_right _ fun _ => bind_left queries _
      · obtain ⟨earlier, rfl⟩ := Fin.exists_castSucc_eq.mpr last
        exact bind_left (ih (fun i => program i.castSucc) earlier queries) _

end QueriesAt

/-! ### The evaluation queries every designated index -/

/-- `switchMaskM` queries every (element, block) index of its switch. -/
theorem switchMaskM_queriesAt (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) (element : Fin count) (block : Fin 3) :
    QueriesAt (scaleIndexOf lane chunk switch element block)
      (Programs.switchMaskM count lane chunk switch label) := by
  unfold Programs.switchMaskM
  refine QueriesAt.bind_left (QueriesAt.vector _ element ?_) _
  have ask : ∀ block' : Fin 3, QueriesAt (scaleIndexOf lane chunk switch element block')
      (Programs.hashM (scaleIndexOf lane chunk switch element block') label) := fun block' =>
    QueriesAt.bind_left (.here label _) _
  fin_cases block
  · exact QueriesAt.bind_left (ask 0) _
  · exact QueriesAt.bind_right _ fun _ => QueriesAt.bind_left (ask 1) _
  · exact QueriesAt.bind_right _ fun _ => QueriesAt.bind_right _ fun _ =>
      QueriesAt.bind_left (ask 2) _

/-- `evalMasksM` queries every (element, block) index of every inactive switch. -/
theorem evalMasksM_queriesAt (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha switch : Fin (2 ^ width)) (inactive : switch ≠ alpha)
    (element : Fin count) (block : Fin 3) :
    QueriesAt (scaleIndexOf lane chunk switch.val element block)
      (Programs.evalMasksM count lane chunk width hot alpha) := by
  unfold Programs.evalMasksM
  refine QueriesAt.bind_left (QueriesAt.vector _ switch ?_) _
  simp only [if_neg inactive]
  exact switchMaskM_queriesAt count lane chunk switch.val (hot switch) element block

/-- The designated switch is inactive. -/
theorem designatedSwitch_ne (bits : BitInput) : designatedSwitch bits ≠ activeSwitch bits := by
  intro same
  have values := congrArg Fin.val same
  simp only [designatedSwitch] at values
  have bit := congrArg (Nat.testBit · 0) values
  simp at bit
  omega

/-- **The honest evaluation queries every designated index, on every path.** -/
theorem openingQueriesM_queriesAt [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) (digit : Fin digitCount) (collector block : Fin 3) :
    QueriesAt (designatedIndex bits digit collector block) (openingQueriesM table bits mac) := by
  unfold openingQueriesM
  refine QueriesAt.bind_right _ fun _ => QueriesAt.bind_right _ fun _ =>
    QueriesAt.bind_right _ fun _ => QueriesAt.bind_right _ fun _ => QueriesAt.bind_left ?_ _
  unfold Programs.evalLaneM
  refine QueriesAt.bind_left (QueriesAt.vector _ chunkZero ?_) _
  unfold Programs.evalChunkM
  refine QueriesAt.bind_right _ fun hot => QueriesAt.bind_left ?_ _
  exact evalMasksM_queriesAt pointElementCountX .pointX chunkZero (chunkWidth chunkZero) hot
    (chunkOf (Pipeline.coordBits bits .x) chunkZero) (designatedSwitch bits)
    (designatedSwitch_ne bits) (xElementIndex digit (collectorElement collector)) block

/-! ### The refill runner records every designated query -/

section Record

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A recorded designated input stays recorded. -/
theorem recordAfter_keeps (bits : BitInput) (request : Request) (record : Record)
    (index : FixedIndex) (kept : record index ≠ none) :
    recordAfter bits request record index ≠ none := by
  cases request with
  | fixedForward index' input =>
      simp only [recordAfter]
      split
      · by_cases same : index = index'
        · subst same; simp
        · rw [Function.update_of_ne same]; exact kept
      · exact kept
  | fixedInverse _ _ => exact kept
  | encForward _ _ => exact kept
  | encInverse _ _ => exact kept
  | hash _ => exact kept

/-- Every path of the runner keeps a recorded index recorded. -/
theorem runRefill_keeps (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (computation : FreeQuery Programs.Spec α) (index : FixedIndex) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex), record index ≠ none →
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → value.2.2 index ≠ none := by
  induction computation with
  | pure value =>
      intro oracle record touched kept result member value same
      simp only [runRefill, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      cases same
      exact kept
  | query request next ih =>
      intro oracle record touched kept result member value same
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ (recordAfter_keeps bits request record index kept) result member value same
      · split at member
        · obtain ⟨limb, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · exact ih _ _ _ _ kept result member value same
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          exact ih _ _ _ _ kept result member value same

/-- An intercepted query is answered by the interception and recorded. -/
theorem runRefill_intercept (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) (oracle : LState)
    (record : Record) (touched : Set FixedIndex) (answer : request.Answer)
    (intercept : interceptAnswer bits request = some answer) :
    runRefill bits draw (.query request next) oracle record touched =
      runRefill bits draw (next answer) oracle (recordAfter bits request record) touched := by
  simp only [runRefill]
  split
  · rename_i answer' hit
    rw [intercept] at hit
    cases hit
    rfl
  · rename_i hit
    rw [intercept] at hit
    cases hit

/-- **A program that queries a designated index leaves it recorded**, on every path. -/
theorem runRefill_records (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (index : FixedIndex) (designated : IsDesignated bits index)
    {computation : FreeQuery Programs.Spec α} (queries : QueriesAt index computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → value.2.2 index ≠ none := by
  induction queries with
  | here input next =>
      intro oracle record touched result member value same
      have intercept : interceptAnswer bits (.fixedForward index input) = some input := by
        simp only [interceptAnswer]
        exact if_pos designated
      rw [runRefill_intercept bits draw (.fixedForward index input) next oracle record touched input
        intercept] at member
      refine runRefill_keeps bits draw _ index oracle _ touched ?_ result member value same
      simp only [recordAfter, if_pos designated, Function.update_self]
      exact Option.some_ne_none _
  | later request next _ ih =>
      intro oracle record touched result member value same
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ result member value same
      · split at member
        · obtain ⟨limb, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · exact ih _ _ _ _ result member value same
        · obtain ⟨answer, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          exact ih _ _ _ _ result member value same

/-- **(a) Every designated index is recorded** after the refill run of the honest evaluation. -/
theorem designated_recorded [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) (oracle : LState) (digit : Fin digitCount) (collector block : Fin 3)
    (result : Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
      × LState × Record))
    (member : result ∈ (refillRun bits (openingQueriesM table bits mac) oracle).support)
    (value : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (same : result = some value) :
    value.2.2 (designatedIndex bits digit collector block) ≠ none := by
  obtain ⟨tape, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  exact runRefill_records bits _ _ ⟨digit, collector, block, rfl⟩
    (openingQueriesM_queriesAt table bits mac digit collector block) oracle _ ∅ result member
    value same

end Record

end

end Kriterion.ArgoMAC.Phase3.Lazy
