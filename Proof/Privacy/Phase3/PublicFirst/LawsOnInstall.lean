/-
**Phase 3, P1q — `LawOn`, step (D3): the designated installation.**

After `HW`'s refill opening from the empty oracle, eager (`opening_eager`: a uniform oracle `O`
overlaid by the tape `T₀ = zeroDesig bits T`), the opening's state is its non-designated transcript
planted on the empty oracle, and its record holds the designated inputs `E*`. The designated
installation (`programAllSkip (programRequests …)`) programs `E* ↦ o_b ⊕ E*` at the 819 designated
indices. Here:

* **path independence** (`PathSame`, `pathSame_opening`): the opening's questions do not depend on
  the answers at the designated questions (they are scale-switch masks, read only by the lanes'
  values, never by a later question);
* the record holds, at each designated index, the input of the opening's unique question there
  (`recordOf_unique`, from `CellOnce`: each site index is asked at most once);
* the installation is a plant (`programAllSkip_eq`);
* **`install_state`**: the installed state has the lookups of the opening's whole transcript on the
  oracle overlaid by the **installed tape** `T₁ = installTape bits T blocks` (the designated limbs
  are the preimage blocks' limbs, the other limbs the tape's).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM whitePadsM IsDesignated
  designatedIndex interceptAnswer recordAfter programRequests limbAt)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record AllQ Request queriesAlong
  queriesAlong_bind queriesAlong_pure queriesAlong_vector FixedAt IndexAt EncAt HashAt)
open scoped ENNReal

noncomputable section

/-! ### 1. Transcripts and question paths -/

section Paths

variable {α β γ δ : Type}

theorem mem_transcript_iff (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (c : FreeQuery Programs.Spec α) (e : Entry FixedIndex EncPRF.PermutationIndex) :
    e ∈ transcript ans c ↔ e.1 ∈ queriesAlong ans c ∧ ans e.1 = e.2 := by
  induction c with
  | pure value =>
      show e ∈ ([] : List (Entry FixedIndex EncPRF.PermutationIndex)) ↔
        e.1 ∈ ([] : List Request) ∧ ans e.1 = e.2
      simp
  | query request next ih =>
      show e ∈ (⟨request, ans request⟩ :: transcript ans (next (ans request)) :
          List (Entry FixedIndex EncPRF.PermutationIndex)) ↔
        e.1 ∈ request :: queriesAlong ans (next (ans request)) ∧ ans e.1 = e.2
      rw [List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (same | ⟨member, answer⟩)
        · subst same
          exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr member, answer⟩
      · rintro ⟨same | member, answer⟩
        · left
          obtain ⟨q, a⟩ := e
          simp only at same answer
          subst same
          subst answer
          rfl
        · exact Or.inr ⟨member, answer⟩

theorem map_fst_transcript (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (c : FreeQuery Programs.Spec α) : (transcript ans c).map Sigma.fst = queriesAlong ans c := by
  induction c with
  | pure value => rfl
  | query request next ih =>
      show request :: (transcript ans (next (ans request))).map Sigma.fst =
        request :: queriesAlong ans (next (ans request))
      rw [ih]

/-- A forward question the refill run leaves to the oracle. -/
def Clear (bits : BitInput) (r : Request) : Prop := NotIntercepted bits r ∧ NoInverse r

/-- Two answer functions agreeing on every clear question. -/
def AgreeOff (bits : BitInput) (a b : (r : Request) → r.Answer) : Prop := ∀ r, Clear bits r → a r = b r

/-- **Two computations take the same question path** on any two answer functions agreeing off the
designated (and inverse) questions. -/
def PathSame (bits : BitInput) (c : FreeQuery Programs.Spec α) (c' : FreeQuery Programs.Spec β) : Prop :=
  ∀ a b, AgreeOff bits a b → queriesAlong a c = queriesAlong b c'

variable (bits : BitInput)

theorem clear_agree {c : FreeQuery Programs.Spec α} (clear : AllQ (Clear bits) c)
    (a b : (r : Request) → r.Answer) (agree : AgreeOff bits a b) :
    queriesAlong a c = queriesAlong b c ∧ FreeQuery.eval a c = FreeQuery.eval b c := by
  induction clear with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next holds _ ih =>
      have head : a request = b request := agree request holds
      obtain ⟨sameQ, sameV⟩ := ih (a request)
      refine ⟨?_, ?_⟩
      · show request :: queriesAlong a (next (a request)) = request :: queriesAlong b (next (b request))
        rw [sameQ, head]
      · show FreeQuery.eval a (next (a request)) = FreeQuery.eval b (next (b request))
        rw [sameV, head]

namespace PathSame

variable {bits}

theorem pure' (x : α) (y : β) :
    PathSame bits (Pure.pure x : FreeQuery Programs.Spec α) (Pure.pure y : FreeQuery Programs.Spec β) :=
  fun _ _ _ => rfl

theorem bind {c : FreeQuery Programs.Spec α} {c' : FreeQuery Programs.Spec β}
    {f : α → FreeQuery Programs.Spec γ} {g : β → FreeQuery Programs.Spec δ}
    (first : PathSame bits c c') (rest : ∀ x y, PathSame bits (f x) (g y)) :
    PathSame bits (c >>= f) (c' >>= g) := by
  intro a b agree
  rw [queriesAlong_bind, queriesAlong_bind, first a b agree, rest _ _ a b agree]

theorem bind_clear {c : FreeQuery Programs.Spec α} (clear : AllQ (Clear bits) c)
    {f g : α → FreeQuery Programs.Spec β} (rest : ∀ x, PathSame bits (f x) (g x)) :
    PathSame bits (c >>= f) (c >>= g) := by
  intro a b agree
  obtain ⟨sameQ, sameV⟩ := clear_agree bits clear a b agree
  rw [queriesAlong_bind, queriesAlong_bind, sameQ, sameV, rest _ a b agree]

theorem ask (q : Request) :
    PathSame bits (FreeQuery.ask (spec := Programs.Spec) q) (FreeQuery.ask (spec := Programs.Spec) q) :=
  fun _ _ _ => rfl

theorem vector : ∀ (count : Nat) {p p' : Fin count → FreeQuery Programs.Spec α},
    (∀ k, PathSame bits (p k) (p' k)) →
      PathSame bits (FreeQuery.vector count p) (FreeQuery.vector count p')
  | 0, _, _, _ => fun _ _ _ => rfl
  | count + 1, p, p', each => by
      show PathSame bits (FreeQuery.vector count (fun k => p k.castSucc) >>= fun values =>
          p (Fin.last count) >>= fun value => Pure.pure (values.push value))
        (FreeQuery.vector count (fun k => p' k.castSucc) >>= fun values =>
          p' (Fin.last count) >>= fun value => Pure.pure (values.push value))
      exact bind (vector count fun k => each k.castSucc) fun _ _ =>
        bind (each _) fun _ _ => pure' _ _

end PathSame

end Paths

/-! ### 2. The opening's path does not depend on the designated answers -/

section Opening

variable (bits : BitInput)

theorem clear_hot (lane : Lane) (chunk : Fin chunkCount) (fold : Fin chunkBits)
    (entry : Fin (2 ^ chunkBits)) (half : Bool) (x : Block) :
    Clear bits (.fixedForward (.hot lane chunk fold entry half) x) := by
  classical
  refine ⟨?_, trivial⟩
  have notDesignated : ¬ IsDesignated bits (.hot lane chunk fold entry half) := by
    rintro ⟨d, c, b, same⟩
    unfold designatedIndex scaleIndexOf scaleIndexNat at same
    cases same
  simp [NotIntercepted, interceptAnswer, notDesignated]

theorem clear_of_encAt {r : Request} (inside : EncAt r) : Clear bits r := by
  cases r with
  | encForward _ _ => exact ⟨rfl, trivial⟩
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem clear_of_hashAt {r : Request} (inside : HashAt r) : Clear bits r := by
  cases r with
  | hash _ => exact ⟨rfl, trivial⟩
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encForward _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim

theorem clear_hashM_hot (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (half : Bool)
    (label : Block) : AllQ (Clear bits) (Programs.hashM (hotIndexNat lane chunk step entry half) label) :=
  AllQ.bind (.query _ _ (clear_hot bits _ _ _ _ _ _) fun _ => .pure _) fun _ => .pure _

theorem clear_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    AllQ (Clear bits) (Programs.evalStepM lane chunk step bitLabel join active parent) :=
  (AllQ.vector fun _ => AllQ.ite (.pure _)
    ((clear_hashM_hot bits _ _ _ _ _ _).bind fun _ =>
      (clear_hashM_hot bits _ _ _ _ _ _).bind fun _ => .pure _)).bind fun _ => .pure _

theorem clear_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) :
    ∀ steps, AllQ (Clear bits) (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (clear_evalFoldM lane chunk value bitLabel join steps).bind fun _ =>
      (clear_evalStepM bits lane chunk _ _ _ _ _).bind fun _ => .pure _

theorem pathSame_hashM (index : FixedIndex) (label : Block) :
    PathSame bits (Programs.hashM index label) (Programs.hashM index label) := by
  unfold Programs.hashM Programs.askFixed
  exact PathSame.bind (PathSame.ask _) fun _ _ => PathSame.pure' _ _

theorem pathSame_switchMaskM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) :
    PathSame bits (Programs.switchMaskM count lane chunk switch label)
      (Programs.switchMaskM count lane chunk switch label) := by
  unfold Programs.switchMaskM
  exact PathSame.bind (PathSame.vector _ fun _ => PathSame.bind (pathSame_hashM bits _ _) fun _ _ =>
    PathSame.bind (pathSame_hashM bits _ _) fun _ _ =>
      PathSame.bind (pathSame_hashM bits _ _) fun _ _ => PathSame.pure' _ _) fun _ _ =>
    PathSame.pure' _ _

theorem pathSame_evalMasksM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : Fin (2 ^ width) → Block) (alpha : Fin (2 ^ width)) :
    PathSame bits (Programs.evalMasksM count lane chunk width hot alpha)
      (Programs.evalMasksM count lane chunk width hot alpha) := by
  unfold Programs.evalMasksM
  refine PathSame.bind (PathSame.vector _ fun switch => ?_) fun _ _ => PathSame.pure' _ _
  by_cases active : switch = alpha
  · rw [if_pos active]
    exact PathSame.pure' _ _
  · rw [if_neg active]
    exact pathSame_switchMaskM bits _ _ _ _ _

/-- **A lane's path does not depend on its scale answers.** -/
theorem pathSame_evalLaneM (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    PathSame bits (Programs.evalLaneM count lane joins scale word labels)
      (Programs.evalLaneM count lane joins scale word labels) := by
  unfold Programs.evalLaneM
  refine PathSame.bind (PathSame.vector _ fun c => ?_) fun _ _ => PathSame.pure' _ _
  unfold Programs.evalChunkM
  exact PathSame.bind_clear (clear_evalFoldM bits _ _ _ _ _ _) fun _ =>
    PathSame.bind (pathSame_evalMasksM bits _ _ _ _ _ _) fun _ _ => PathSame.pure' _ _

variable [FieldCertificate]

/-- A lane other than `pointX` asks no designated question. -/
theorem clear_lane (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (other : lane ≠ .pointX) :
    AllQ (Clear bits) (Programs.evalLaneM count lane joins scale word labels) :=
  (Kriterion.ArgoMAC.Phase3.Lazy.evalLaneM_allQ count lane joins scale word labels).mono fun r inside => by
    classical
    cases r with
    | fixedForward index input =>
        refine ⟨?_, trivial⟩
        obtain ⟨c, at_c⟩ := inside
        have notDesignated : ¬ IsDesignated bits index := by
          rintro ⟨digit, collector, block, same⟩
          have point := Kriterion.ArgoMAC.Phase3.Lazy.scaleIndexOf_indexAt (count := pointElementCountX)
            .pointX Kriterion.ArgoMAC.Phase3.Glue.chunkZero
            (Kriterion.ArgoMAC.Phase3.Glue.designatedSwitch bits).val
            (xElementIndex digit (Kriterion.ArgoMAC.Phase3.Glue.collectorElement collector)) block
          change IndexAt .pointX _ (designatedIndex bits digit collector block) at point
          rw [same] at point
          exact other (Kriterion.ArgoMAC.Phase3.Lazy.indexAt_unique at_c point).1
        simp [NotIntercepted, interceptAnswer, notDesignated]
    | fixedInverse _ _ => exact inside.elim
    | encForward _ _ => exact inside.elim
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim

/-- **The opening's path does not depend on the designated answers.** -/
theorem pathSame_opening (table : Public) (mac : InputMac) :
    PathSame bits (openingQueriesM table bits mac) (openingQueriesM table bits mac) := by
  unfold openingQueriesM
  refine PathSame.bind_clear (clear_lane bits _ _ _ _ _ _ (by decide)) fun _ => ?_
  refine PathSame.bind_clear (clear_lane bits _ _ _ _ _ _ (by decide)) fun _ => ?_
  refine PathSame.bind_clear ((Kriterion.ArgoMAC.Phase3.Lazy.askHash_allQ _).mono
    fun _ inside => clear_of_hashAt bits inside) fun _ => ?_
  refine PathSame.bind_clear ((Kriterion.ArgoMAC.Phase3.Lazy.whitePadsM_allQ _).mono
    fun _ inside => clear_of_encAt bits inside) fun _ => ?_
  refine PathSame.bind (pathSame_evalLaneM bits _ _ _ _ _ _) fun _ _ => ?_
  exact PathSame.bind_clear (clear_lane bits _ _ _ _ _ _ (by decide)) fun _ => PathSame.pure' _ _

end Opening

/-! ### 3. Each site index at most once -/

section Once

variable {α : Type}

theorem cellOnce_inside {X : Set FixedIndex} {c : FreeQuery Programs.Spec α} (once : CellOnce X c) :
    ∀ (ans : (r : Request) → r.Answer) (i : FixedIndex) (x : Block), i ∈ Set.range siteIndex →
      (PublicQuery.fixedForward i x : Request) ∈ queriesAlong ans c → i ∈ X := by
  induction once with
  | pure X value => intro _ _ _ _ member; nomatch member
  | site X cell input next inside rest ih =>
      intro ans i x _ member
      rcases List.mem_cons.mp member with same | later
      · injection same with hi _
        rw [hi]
        exact inside
      · exact (ih _ ans i x ‹_› later).1
  | other X request next notSite forward rest ih =>
      intro ans i x site member
      rcases List.mem_cons.mp member with same | later
      · exact absurd site (notSite i x same.symm)
      · exact ih _ ans i x site later

/-- **A site index is asked at one input only.** -/
theorem cellOnce_unique {X : Set FixedIndex} {c : FreeQuery Programs.Spec α} (once : CellOnce X c) :
    ∀ (ans : (r : Request) → r.Answer) (i : FixedIndex) (x y : Block), i ∈ Set.range siteIndex →
      (PublicQuery.fixedForward i x : Request) ∈ queriesAlong ans c →
      (PublicQuery.fixedForward i y : Request) ∈ queriesAlong ans c → x = y := by
  induction once with
  | pure X value => intro _ _ _ _ _ member; nomatch member
  | site X cell input next inside rest ih =>
      intro ans i x y site mx my
      rcases List.mem_cons.mp mx with hx | hx <;> rcases List.mem_cons.mp my with hy | hy
      · injection hx with _ hx'
        injection hy with _ hy'
        rw [hx', hy']
      · injection hx with hi _
        exact absurd hi (cellOnce_inside (rest _) ans i y site hy).2
      · injection hy with hi _
        exact absurd hi (cellOnce_inside (rest _) ans i x site hx).2
      · exact ih _ ans i x y site hx hy
  | other X request next notSite forward rest ih =>
      intro ans i x y site mx my
      rcases List.mem_cons.mp mx with hx | hx
      · exact absurd site (notSite i x hx.symm)
      rcases List.mem_cons.mp my with hy | hy
      · exact absurd site (notSite i y hy.symm)
      · exact ih _ ans i x y site hx hy

theorem cellOnce_forward {X : Set FixedIndex} {c : FreeQuery Programs.Spec α} (once : CellOnce X c) :
    ∀ (ans : (r : Request) → r.Answer) (r : Request), r ∈ queriesAlong ans c → NoInverse r := by
  induction once with
  | pure X value => intro _ _ member; nomatch member
  | site X cell input next inside rest ih =>
      intro ans r member
      rcases List.mem_cons.mp member with same | later
      · subst same
        trivial
      · exact ih _ ans r later
  | other X request next notSite forward rest ih =>
      intro ans r member
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact forward
      · exact ih _ ans r later

end Once

/-! ### 4. The record -/

section Record

variable [DecidableEq FixedIndex] (bits : BitInput)

theorem recordOf_cons (e : Entry FixedIndex EncPRF.PermutationIndex)
    (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record) :
    recordOf bits (e :: es) record = recordOf bits es (recordAfter bits e.1 record) := rfl

theorem recordAfter_other (index : FixedIndex) (request : Request)
    (other : ∀ x, request ≠ .fixedForward index x) (record : Record) :
    recordAfter bits request record index = record index := by
  classical
  cases request with
  | fixedForward index' input =>
      simp only [recordAfter]
      split
      · rw [Function.update_of_ne]
        rintro rfl
        exact other input rfl
      · rfl
  | fixedInverse _ _ => rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

theorem recordAfter_self (index : FixedIndex) (designated : IsDesignated bits index) (x : Block)
    (record : Record) : recordAfter bits (.fixedForward index x) record index = some x := by
  classical
  simp only [recordAfter, if_pos designated, Function.update_self]

theorem recordOf_absent (index : FixedIndex) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      (∀ x, (PublicQuery.fixedForward index x : Request) ∉ es.map Sigma.fst) →
        recordOf bits es record index = record index
  | [], _, _ => rfl
  | e :: es, record, absent => by
      rw [recordOf_cons, recordOf_absent index es _ fun x member =>
        absent x (List.mem_cons_of_mem _ member)]
      refine recordAfter_other bits index e.1 (fun x same => absent x ?_) record
      rw [List.map_cons, ← same]
      exact List.mem_cons_self

/-- **The record holds the unique designated input.** -/
theorem recordOf_unique (index : FixedIndex) (designated : IsDesignated bits index) (x : Block) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      (PublicQuery.fixedForward index x : Request) ∈ es.map Sigma.fst →
      (∀ y, (PublicQuery.fixedForward index y : Request) ∈ es.map Sigma.fst → y = x) →
        recordOf bits es record index = some x
  | [], _, member, _ => nomatch member
  | e :: es, record, member, unique => by
      rw [recordOf_cons]
      have uniqueTail : ∀ y, (PublicQuery.fixedForward index y : Request) ∈ es.map Sigma.fst → y = x :=
        fun y later => unique y (List.mem_cons_of_mem _ later)
      by_cases head : ∃ y, e.1 = .fixedForward index y
      · obtain ⟨y, hy⟩ := head
        have yx : y = x := unique y (by rw [List.map_cons, ← hy]; exact List.mem_cons_self)
        subst yx
        by_cases later : (PublicQuery.fixedForward index y : Request) ∈ es.map Sigma.fst
        · exact recordOf_unique index designated y es _ later uniqueTail
        · have absent : ∀ z, (PublicQuery.fixedForward index z : Request) ∉ es.map Sigma.fst := by
            intro z inZ
            have zy := uniqueTail z inZ
            subst zy
            exact later inZ
          rw [recordOf_absent bits index es _ absent, hy]
          exact recordAfter_self bits index designated y record
      · have other : ∀ z, e.1 ≠ .fixedForward index z := fun z same => head ⟨z, same⟩
        rcases List.mem_cons.mp (show (PublicQuery.fixedForward index x : Request) ∈
            e.1 :: es.map Sigma.fst from member) with same | later
        · exact absurd same.symm (other x)
        · exact recordOf_unique index designated x es _ later uniqueTail

/-- A recorded input is an input of the list (or of the record before). -/
theorem recordOf_some (index : FixedIndex) (x : Block) :
    ∀ (es : List (Entry FixedIndex EncPRF.PermutationIndex)) (record : Record),
      recordOf bits es record index = some x →
        record index = some x ∨ (PublicQuery.fixedForward index x : Request) ∈ es.map Sigma.fst
  | [], _, found => Or.inl found
  | e :: es, record, found => by
      rw [recordOf_cons] at found
      rcases recordOf_some index x es _ found with before | later
      · by_cases head : ∃ y, e.1 = .fixedForward index y
        · obtain ⟨y, hy⟩ := head
          rw [hy] at before
          classical
          by_cases designated : IsDesignated bits index
          · rw [recordAfter_self bits index designated y] at before
            cases before
            right
            rw [List.map_cons, hy]
            exact List.mem_cons_self
          · left
            simp only [recordAfter, if_neg designated] at before
            exact before
        · left
          rw [recordAfter_other bits index e.1 (fun z same => head ⟨z, same⟩)] at before
          exact before
      · exact Or.inr (List.mem_cons_of_mem _ later)

end Record

/-! ### 5. The installation is a plant -/

section Plant

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The entry of a program request (none if its input is missing). -/
def reqEntry (request : FixedIndex × Option Block × Block) :
    Option (Entry FixedIndex EncPRF.PermutationIndex) :=
  request.2.1.map fun input => ⟨.fixedForward request.1 input, request.2.2 ^^^ input⟩

theorem programAllSkip_eq (requests : List (FixedIndex × Option Block × Block)) :
    ∀ state : LState, Kriterion.ArgoMAC.Security.Phase3.programAllSkip requests state =
      plantAll (requests.filterMap reqEntry) state := by
  induction requests with
  | nil => intro _; rfl
  | cons request rest ih =>
      intro state
      obtain ⟨index, input, output⟩ := request
      cases input with
      | none => exact ih state
      | some x => exact ih _

theorem plantAll_append_empty (first second : List (Entry FixedIndex EncPRF.PermutationIndex)) :
    plantAll second (plantAll first LazyOracle.empty) = plantAll (first ++ second) (LazyOracle.empty : LState) := by
  unfold plantAll
  rw [List.foldl_append]

theorem mem_installEntries (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (e : Entry FixedIndex EncPRF.PermutationIndex) :
    e ∈ (programRequests bits record blocks).filterMap reqEntry ↔
      ∃ (d : Fin digitCount) (c b : Fin 3) (x : Block), record (designatedIndex bits d c b) = some x ∧
        e = ⟨.fixedForward (designatedIndex bits d c b) x, limbAt b (blocks (d, c)) ^^^ x⟩ := by
  unfold programRequests
  simp only [List.mem_filterMap, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨request, ⟨d, c, b, rfl⟩, found⟩
    simp only [reqEntry, Option.map_eq_some_iff] at found
    obtain ⟨x, hx, rfl⟩ := found
    exact ⟨d, c, b, x, hx, rfl⟩
  · rintro ⟨d, c, b, x, hx, rfl⟩
    refine ⟨_, ⟨d, c, b, rfl⟩, ?_⟩
    simp only [reqEntry, hx, Option.map_some]

/-- **Two consistent lists with the same entries plant the same lookups.** -/
theorem sameLookups_of_mem_iff (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (first second : List (Entry FixedIndex EncPRF.PermutationIndex))
    (firstConsistent : Hidden.Consistent O first) (secondConsistent : Hidden.Consistent O second)
    (same : ∀ e, e ∈ first ↔ e ∈ second) :
    SameLookups (plantAll first LazyOracle.empty) (plantAll second LazyOracle.empty) := by
  refine sameLookups_of_forward (fun i z => ?_) (fun i z => ?_) (fun key => ?_)
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [look_plantAll_empty O first firstConsistent, look_plantAll_empty O second secondConsistent]
    simp only [same]
  · apply Option.ext
    intro y
    change Hidden.look _ z = some y ↔ Hidden.look _ z = some y
    rw [encLook_plantAll_empty O first firstConsistent, encLook_plantAll_empty O second secondConsistent]
    simp only [same]
  · rw [hashLookup_plantAll_empty O first firstConsistent,
      hashLookup_plantAll_empty O second secondConsistent]
    by_cases hit : ∃ e ∈ first, ∃ value, Hidden.hashPair e = some (key, value)
    · have hit' : ∃ e ∈ second, ∃ value, Hidden.hashPair e = some (key, value) := by
        obtain ⟨e, member, rest⟩ := hit
        exact ⟨e, (same e).mp member, rest⟩
      rw [if_pos hit, if_pos hit']
    · have hit' : ¬ ∃ e ∈ second, ∃ value, Hidden.hashPair e = some (key, value) := by
        rintro ⟨e, member, rest⟩
        exact hit ⟨e, (same e).mpr member, rest⟩
      rw [if_neg hit, if_neg hit']

end Plant

/-! ### 6. The installed tape -/

section Tape

/-- **The installed tape**: the preimage blocks' limbs at the designated cells, the tape elsewhere. -/
def installTape (bits : BitInput) (T : Tape) (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    Tape := fun cell =>
  @dite _ (∃ s : Fin digitCount × Fin 3 × Fin 3, designatedIndex bits s.1 s.2.1 s.2.2 = siteIndex cell)
    (Classical.propDecidable _)
    (fun hit => limbAt (Classical.choose hit).2.2 (blocks ((Classical.choose hit).1, (Classical.choose hit).2.1)))
    (fun _ => T cell)

theorem designatedIndex_inj (bits : BitInput) {d d' : Fin digitCount} {c c' b b' : Fin 3}
    (same : designatedIndex bits d c b = designatedIndex bits d' c' b') : d = d' ∧ c = c' ∧ b = b' := by
  rw [Kriterion.ArgoMAC.Phase3.Glue.designatedIndex_eq_candidateIndex,
    Kriterion.ArgoMAC.Phase3.Glue.designatedIndex_eq_candidateIndex] at same
  have pair := Kriterion.ArgoMAC.Phase3.Glue.candidateIndex_injective same
  simp only [Prod.mk.injEq] at pair
  exact ⟨pair.1, pair.2.1, pair.2.2.1⟩

theorem installTape_designated (bits : BitInput) (T : Tape)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (cell : Cell) (d : Fin digitCount)
    (c b : Fin 3) (same : designatedIndex bits d c b = siteIndex cell) :
    installTape bits T blocks cell = limbAt b (blocks (d, c)) := by
  have hit : ∃ s : Fin digitCount × Fin 3 × Fin 3, designatedIndex bits s.1 s.2.1 s.2.2 = siteIndex cell :=
    ⟨(d, c, b), same⟩
  unfold installTape
  rw [dif_pos hit]
  obtain ⟨h1, h2, h3⟩ := designatedIndex_inj bits ((Classical.choose_spec hit).trans same.symm)
  rw [h1, h2, h3]

theorem installTape_other (bits : BitInput) (T : Tape)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (cell : Cell)
    (notDesignated : ¬ IsDesignated bits (siteIndex cell)) :
    installTape bits T blocks cell = T cell := by
  unfold installTape
  rw [dif_neg]
  rintro ⟨s, same⟩
  exact notDesignated ⟨s.1, s.2.1, s.2.2, same⟩

theorem zeroDesig_other (bits : BitInput) (T : Tape) (cell : Cell)
    (notDesignated : ¬ IsDesignated bits (siteIndex cell)) : zeroDesig bits T cell = T cell := by
  unfold zeroDesig
  exact if_neg notDesignated

variable [DecidableEq FixedIndex]

theorem notDesignated_of_clear (bits : BitInput) {index : FixedIndex} {x : Block}
    (clear : Clear bits (.fixedForward index x)) : ¬ IsDesignated bits index := by
  classical
  intro designated
  have none := clear.1
  simp [NotIntercepted, interceptAnswer, designated] at none

/-- **The zeroed and the installed overlay agree off the designated questions.** -/
theorem agreeOff_install (bits : BitInput) (T : Tape)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    AgreeOff bits (publicAnswer (overlay (zeroDesig bits T) O))
      (publicAnswer (overlay (installTape bits T blocks) O)) := by
  intro r clear
  cases r with
  | fixedForward index x =>
      have notDesignated := notDesignated_of_clear bits clear
      by_cases site : index ∈ Set.range siteIndex
      · obtain ⟨cell, rfl⟩ := site
        rw [overlay_site, overlay_site, installTape_other bits T blocks cell notDesignated,
          zeroDesig_other bits T cell notDesignated]
      · rw [overlay_fixed_other _ _ _ site, overlay_fixed_other _ _ _ site]
  | fixedInverse _ _ => exact clear.2.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-- The installed overlay at a designated question. -/
theorem install_designated_answer (bits : BitInput) (T : Tape)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (d : Fin digitCount) (c b : Fin 3) (x : Block) :
    publicAnswer (overlay (installTape bits T blocks) O) (.fixedForward (designatedIndex bits d c b) x) =
      limbAt b (blocks (d, c)) ^^^ x := by
  obtain ⟨cell, hcell⟩ := designated_site bits ⟨d, c, b, rfl⟩
  rw [← hcell, overlay_site, installTape_designated bits T blocks cell d c b hcell.symm,
    BitVec.xor_comm]

end Tape

/-! ### 7. The installed state -/

section Install

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designated installation, generically**: for a computation asking each site index at most
once, forward, whose path does not depend on the designated answers, installing the preimage limbs
on its zeroed non-designated transcript gives the lookups of its transcript on the installed
overlay. -/
theorem install_generic (bits : BitInput) (T : Tape)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) {α : Type} {X : Set FixedIndex}
    (P : FreeQuery Programs.Spec α) (once : CellOnce X P) (path : PathSame bits P P) :
    SameLookups
      (Kriterion.ArgoMAC.Security.Phase3.programAllSkip (programRequests bits
          (recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) P) (fun _ => none))
          blocks)
        (plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) P).filter (notDesig bits))
          LazyOracle.empty))
      (plantAll (transcript (publicAnswer (overlay (installTape bits T blocks) O)) P) LazyOracle.empty) := by
  classical
  have agree := agreeOff_install bits T blocks O
  have sameQ : queriesAlong (publicAnswer (overlay (zeroDesig bits T) O)) P =
      queriesAlong (publicAnswer (overlay (installTape bits T blocks) O)) P := path _ _ agree
  have forward := cellOnce_forward once
  -- a question off the designated indices is clear
  have clearOf : ∀ r ∈ queriesAlong (publicAnswer (overlay (zeroDesig bits T) O)) P,
      (∀ index x, r = .fixedForward index x → ¬ IsDesignated bits index) → Clear bits r := by
    intro r member notD
    refine ⟨?_, forward _ r member⟩
    cases r with
    | fixedForward index x =>
        have := notD index x rfl
        simp [NotIntercepted, interceptAnswer, this]
    | _ => rfl
  rw [programAllSkip_eq, plantAll_append_empty]
  refine sameLookups_of_mem_iff (overlay (installTape bits T blocks) O) _ _ ?_ ?_ ?_
  · -- consistency of the zeroed transcript and the installed entries
    intro e member
    rcases List.mem_append.mp member with zeroed | installed
    · obtain ⟨inT, keep⟩ := List.mem_filter.mp zeroed
      obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp inT
      rw [← answer]
      refine agree _ (clearOf _ q fun index x same designated => ?_)
      obtain ⟨request, value⟩ := e
      simp only at same
      subst same
      simp [notDesig, designated] at keep
    · obtain ⟨d, c, b, x, _, rfl⟩ := (mem_installEntries bits _ blocks e).mp installed
      exact (install_designated_answer bits T blocks O d c b x).symm
  · intro e member
    exact ((mem_transcript_iff _ _ e).mp member).2.symm
  · intro e
    constructor
    · intro member
      rcases List.mem_append.mp member with zeroed | installed
      · obtain ⟨inT, keep⟩ := List.mem_filter.mp zeroed
        obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp inT
        refine (mem_transcript_iff _ _ e).mpr ⟨sameQ ▸ q, ?_⟩
        rw [← answer]
        refine (agree _ (clearOf _ q fun index x same designated => ?_)).symm
        obtain ⟨request, value⟩ := e
        simp only at same
        subst same
        simp [notDesig, designated] at keep
      · obtain ⟨d, c, b, x, hx, rfl⟩ := (mem_installEntries bits _ blocks e).mp installed
        refine (mem_transcript_iff _ _ _).mpr ⟨?_, install_designated_answer bits T blocks O d c b x⟩
        rcases recordOf_some bits _ x _ _ hx with none | inList
        · cases none
        · rw [map_fst_transcript] at inList
          exact sameQ ▸ inList
    · intro member
      obtain ⟨q, answer⟩ := (mem_transcript_iff _ _ e).mp member
      rw [← sameQ] at q
      obtain ⟨request, value⟩ := e
      simp only at q answer
      subst answer
      by_cases designatedQ : ∃ index x, request = .fixedForward index x ∧ IsDesignated bits index
      · obtain ⟨index, x, rfl, designated⟩ := designatedQ
        obtain ⟨d, c, b, rfl⟩ := designated
        refine List.mem_append_right _ ((mem_installEntries bits _ blocks _).mpr ⟨d, c, b, x, ?_, ?_⟩)
        · refine recordOf_unique bits _ ⟨d, c, b, rfl⟩ x _ _ ?_ fun y my => ?_
          · rw [map_fst_transcript]
            exact q
          · rw [map_fst_transcript] at my
            exact cellOnce_unique once _ _ y x (designated_site bits ⟨d, c, b, rfl⟩) my q
        · rw [install_designated_answer bits T blocks O d c b x]
      · have notD : ∀ index x, request = .fixedForward index x → ¬ IsDesignated bits index :=
          fun index x same designated => designatedQ ⟨index, x, same, designated⟩
        refine List.mem_append_left _ (List.mem_filter.mpr ⟨?_, ?_⟩)
        · refine (mem_transcript_iff _ _ _).mpr ⟨q, ?_⟩
          exact agree _ (clearOf _ q notD)
        · cases request with
          | fixedForward index x => simp [notDesig, notD index x rfl]
          | _ => rfl

variable [FieldCertificate]

/-- **(D3) The designated installation on the opening's state**: it has the lookups of the
opening's transcript on the oracle overlaid by the installed tape. -/
theorem install_state (bits : BitInput) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (table : Public) (mac : InputMac) (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    SameLookups
      (Kriterion.ArgoMAC.Security.Phase3.programAllSkip (programRequests bits
          (recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)) (fun _ => none)) blocks)
        (plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
          (openingQueriesM table bits mac)).filter (notDesig bits)) LazyOracle.empty))
      (plantAll (transcript (publicAnswer (overlay (installTape bits T blocks) O))
        (openingQueriesM table bits mac)) LazyOracle.empty) :=
  install_generic bits T blocks O _ (cellOnce_opening table bits mac) (pathSame_opening bits table mac)

end Install

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
