/-
**Phase 3, P4 — evaluator unfolding (6): the run never touches a designated index.**

The designated programs of `I^U` fail only against entries at their own index. Those entries are
exactly the stage-1 entries, because the refill run of the honest evaluation leaves every
designated index as it found it:

* `ForwardOnly` — every query of the program is a forward query (fixed-key or EncPRF) or a hash
  query. `openingQueriesM_forwardOnly` proves this for the honest evaluation: `askFixed`, `askEnc`
  and `askHash` only, through `bind`, `vector`, the fold recursion and the branches.
* `runRefill_frame` — a forward-only program leaves a designated index unchanged on every path.
  Forward queries there are intercepted. A consumed cell is programmed, and a lazy query answered,
  at its own non-designated index.
-/

import Proof.Privacy.Phase3.Lazy.Designated

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- A request that is not an inverse query. -/
def IsForward : Request → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => False
  | .encForward _ _ => True
  | .encInverse _ _ => False
  | .hash _ => True

/-- Every query of the program is a forward (or hash) query. -/
inductive ForwardOnly {α : Type} : FreeQuery Programs.Spec α → Prop
  | pure (value : α) : ForwardOnly (.pure value)
  | query (request : Request) (next : request.Answer → FreeQuery Programs.Spec α) :
      IsForward request → (∀ answer, ForwardOnly (next answer)) → ForwardOnly (.query request next)

namespace ForwardOnly

variable {α β : Type}

theorem bind {c : FreeQuery Programs.Spec α} (first : ForwardOnly c)
    {f : α → FreeQuery Programs.Spec β} (rest : ∀ value, ForwardOnly (f value)) :
    ForwardOnly (c >>= f) := by
  induction first with
  | pure value => exact rest value
  | query request next forward _ ih => exact .query request _ forward ih

theorem pure' (value : α) : ForwardOnly (Pure.pure value : FreeQuery Programs.Spec α) := .pure value

theorem vector {count : Nat} {program : Fin count → FreeQuery Programs.Spec α}
    (each : ∀ index, ForwardOnly (program index)) :
    ForwardOnly (FreeQuery.vector count program) := by
  induction count with
  | zero => exact .pure _
  | succ count ih =>
      exact bind (ih fun index => each index.castSucc) fun _ =>
        bind (each (Fin.last count)) fun _ => pure' _

theorem ite {condition : Prop} [Decidable condition] {first second : FreeQuery Programs.Spec α}
    (yes : ForwardOnly first) (no : ForwardOnly second) :
    ForwardOnly (if condition then first else second) := by
  split
  · exact yes
  · exact no

end ForwardOnly

/-! ### The honest evaluation is forward-only -/

theorem askFixed_forwardOnly (index : FixedIndex) (input : Block) :
    ForwardOnly (Programs.askFixed index input) :=
  .query (.fixedForward index input) _ trivial fun _ => .pure _

theorem askEnc_forwardOnly (index : EncPRF.PermutationIndex) (input : Block) :
    ForwardOnly (Programs.askEnc index input) :=
  .query (.encForward index input) _ trivial fun _ => .pure _

theorem askHash_forwardOnly (input : BaseField) : ForwardOnly (Programs.askHash input) :=
  .query (.hash input) _ trivial fun _ => .pure _

theorem hashM_forwardOnly (index : FixedIndex) (label : Block) :
    ForwardOnly (Programs.hashM index label) :=
  (askFixed_forwardOnly index label).bind fun _ => .pure _

theorem foldMaskM_forwardOnly (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) : ForwardOnly (Programs.foldMaskM lane chunk step entry label) :=
  (hashM_forwardOnly _ _).bind fun _ => (hashM_forwardOnly _ _).bind fun _ => .pure _

theorem switchMaskM_forwardOnly (count : Nat) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Nat) (label : Block) :
    ForwardOnly (Programs.switchMaskM count lane chunk switch label) :=
  (ForwardOnly.vector fun _ => (hashM_forwardOnly _ _).bind fun _ =>
    (hashM_forwardOnly _ _).bind fun _ => (hashM_forwardOnly _ _).bind fun _ => .pure _).bind
      fun _ => .pure _

theorem evalStepM_forwardOnly (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (bitLabel join : Block) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    ForwardOnly (Programs.evalStepM lane chunk step bitLabel join active parent) :=
  (ForwardOnly.vector fun _ => ForwardOnly.ite (.pure _) (foldMaskM_forwardOnly _ _ _ _ _)).bind
    fun _ => .pure _

theorem evalFoldM_forwardOnly (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) :
    ∀ steps, ForwardOnly (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (evalFoldM_forwardOnly lane chunk value bitLabel join steps).bind fun _ =>
      (evalStepM_forwardOnly _ _ _ _ _ _ _).bind fun _ => .pure _

theorem evalMasksM_forwardOnly (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha : Fin (2 ^ width)) :
    ForwardOnly (Programs.evalMasksM count lane chunk width hot alpha) :=
  (ForwardOnly.vector fun _ => ForwardOnly.ite (.pure _) (switchMaskM_forwardOnly _ _ _ _ _)).bind
    fun _ => .pure _

theorem evalLaneM_forwardOnly (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    ForwardOnly (Programs.evalLaneM count lane joins scale bits labels) :=
  (ForwardOnly.vector fun _ => (evalFoldM_forwardOnly _ _ _ _ _ _).bind fun _ =>
    (evalMasksM_forwardOnly _ _ _ _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

theorem padM_forwardOnly (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    ForwardOnly (Programs.padM keys coordinate index bit) :=
  (askEnc_forwardOnly _ _).bind fun _ => .pure _

theorem whitePadsM_forwardOnly (keys : WhiteningKeys) : ForwardOnly (whitePadsM keys) :=
  (ForwardOnly.vector fun _ => padM_forwardOnly _ _ _ _).bind fun _ =>
    (ForwardOnly.vector fun _ => padM_forwardOnly _ _ _ _).bind fun _ => .pure _

/-- **The honest evaluation makes no inverse query.** -/
theorem openingQueriesM_forwardOnly [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) : ForwardOnly (openingQueriesM table bits mac) :=
  (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
      (askHash_forwardOnly _).bind fun _ =>
        (whitePadsM_forwardOnly _).bind fun _ =>
          (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
            (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ => .pure _

/-! ### A forward-only run leaves a designated index alone -/

section Frame

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- Programming a forward pair changes only its own index. -/
theorem program_frame (index : FixedIndex) (input answer : Block) (oracle updated : LState)
    (success : LazyOracle.program (.fixedForward index input) answer oracle = some updated)
    (other : FixedIndex) (different : other ≠ index) : updated.fixed other = oracle.fixed other := by
  simp only [LazyOracle.program] at success
  obtain ⟨next, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Function.update_of_ne different _ _

/-- **A forward-only program leaves every designated index as it found it**, on every path. -/
theorem runRefill_frame (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (index : FixedIndex) (designated : IsDesignated bits index)
    {computation : FreeQuery Programs.Spec α} (forward : ForwardOnly computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      ∀ result ∈ (runRefill bits draw computation oracle record touched).support,
        ∀ value, result = some value → value.2.1.fixed index = oracle.fixed index := by
  induction forward with
  | pure value =>
      intro oracle record touched result member final same
      simp only [runRefill, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      cases same
      rfl
  | query request next isForward _ ih =>
      intro oracle record touched result member final same
      simp only [runRefill] at member
      split at member
      · exact ih _ _ _ _ result member final same
      · rename_i notIntercepted
        -- a non-intercepted forward query is at a non-designated index
        have away : touchedIndex request ≠ some index := by
          intro hit
          cases request with
          | fixedForward index' input =>
              simp only [touchedIndex, Option.some.injEq] at hit
              subst hit
              simp only [interceptAnswer, if_pos designated] at notIntercepted
              exact Option.some_ne_none _ notIntercepted
          | fixedInverse _ _ => exact isForward.elim
          | encForward _ _ => simp [touchedIndex] at hit
          | encInverse _ _ => exact isForward.elim
          | hash _ => simp [touchedIndex] at hit
        split at member
        · rename_i cell consumed
          obtain ⟨index', input, rfl, _, _, _⟩ := consumeCell_spec consumed
          obtain ⟨limb, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          split at member
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at member
            subst member
            cases same
          · rename_i updated programmed
            rw [ih _ _ _ _ result member final same]
            exact program_frame index' input _ oracle updated programmed index
              fun same' => away (by rw [same']; rfl)
        · obtain ⟨answer, answerMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          rw [ih _ _ _ _ result member final same]
          exact query_frame request oracle answer answerMember index away

/-- **(6) The refill run of the honest evaluation leaves every designated index as stage 1 left
it.** -/
theorem designated_untouched [FieldCertificate] (table : Public) (bits : BitInput)
    (mac : InputMac) (oracle : LState) (index : FixedIndex) (designated : IsDesignated bits index)
    (result : Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
      × LState × Record))
    (member : result ∈ (refillRun bits (openingQueriesM table bits mac) oracle).support)
    (value : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (same : result = some value) :
    value.2.1.fixed index = oracle.fixed index := by
  obtain ⟨tape, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  exact runRefill_frame bits _ index designated (openingQueriesM_forwardOnly table bits mac)
    oracle _ ∅ result member value same

end Frame

end

end Kriterion.ArgoMAC.Phase3.Lazy
