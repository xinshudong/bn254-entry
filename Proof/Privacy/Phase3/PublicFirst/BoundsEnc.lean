/-
**Phase 3, P1k — (B1), the EncPRF and structural part: the shape of the EncPRF and hash parts of
`M'`'s private stage 2 on the curve.**

* `opening_hash_length` — `HW`'s opening stores exactly one hash pair (the prefix's `hash(t)`), so
  the key potential of its final state is the indicator of the prefix's key
  (`keyPotential_opening`).
* `shadow_enc_final` — after the shadow, the EncPRF part stores at every position only the inputs
  `0 ⊕ k₁`, `1 ⊕ k₁` (the opening's whitening pads, the shadow's bit-`true` pads; the shadow's
  re-run of the evaluator reads them back: `onCurveM_eq_prefix`, `storedPath_of_allQ`).
* `onCurve_event_le` — the on-curve private stage 2's event mass factors through the opening's
  final state (aborts have no mass: `runRefill_ne_none`, `preimages_ne_none`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsEncRun

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM interceptAnswer whitePadsM
  idealSamplers collectorTargets preimages programRequests)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape runRefill uniformMaskTape consumeCell
  refillAnswer consumeCell_spec AllQ FixedAt EncAt evalLaneM_allQ padM_allQ fq_bind_assoc)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Generic run facts -/

section Generic

/-- A question that is not a hash question. -/
def HashFree : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => True
  | .fixedInverse _ _ => True
  | .encForward _ _ => True
  | .encInverse _ _ => True
  | .hash _ => False

theorem hashFree_of_fixedAt {S : FixedIndex → Prop}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : FixedAt S request) :
    HashFree request := by
  cases request with
  | hash _ => exact inside.elim
  | _ => trivial

theorem hashFree_of_encInputIs {value : Block}
    {request : PublicQuery FixedIndex EncPRF.PermutationIndex} (inside : EncInputIs value request) :
    HashFree request := by
  cases request with
  | hash _ => exact inside.elim
  | _ => trivial

/-- **A refill run of a hash-free program keeps the hash part.** -/
theorem runRefill_hash_same (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (computation : FreeQuery Programs.Spec α) (free : AllQ HashFree computation) (oracle : LState)
    (record : Record) (touched : Set FixedIndex) (outcome : α × LState × Record)
    (member : some outcome ∈ (runRefill bits draw computation oracle record touched).support) :
    outcome.2.1.hash = oracle.hash :=
  runRefill_invariant bits draw HashFree (fun state => state.hash = oracle.hash)
    (fun request state holds same answer answerMember => by
      cases request with
      | hash _ => exact holds.elim
      | fixedForward _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | fixedInverse _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | encForward _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | encInverse _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same)
    (fun request state _ _ _ updated _ same consumed success => by
      obtain ⟨index, input, rfl, _⟩ := consumeCell_spec consumed
      simp only [LazyOracle.program, Option.map_eq_some_iff] at success
      obtain ⟨next, _, rfl⟩ := success
      exact same)
    computation free oracle record touched outcome rfl member

/-- **An invariant of the lazy runner**, for a program all of whose questions satisfy `Q`. -/
theorem runLazyQ_invariant (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop)
    (Inv : LState → Prop)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request → Inv state → ∀ answer ∈ (LazyOracle.query request state).support, Inv answer.2)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (state : LState) (outcome : α × LState), Inv state →
      outcome ∈ (runLazyQ computation state).support → Inv outcome.2 := by
  induction computation with
  | pure value =>
    intro state outcome invariant member
    simp only [runLazyQ, PMF.mem_support_pure_iff] at member
    subst member
    exact invariant
  | query request next ih =>
    intro state outcome invariant member
    simp only [runLazyQ, PMF.mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, rest⟩ := member
    exact ih answer.1 (AllQ.tail holds _) answer.2 outcome
      (step request state (AllQ.head holds) invariant answer answerMember) rest

/-- **A program all of whose questions are stored is a stored path.** -/
theorem storedPath_of_allQ (P : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop)
    (state : LState) (stored : ∀ request, P request → ∃ answer, StoredAs state ⟨request, answer⟩)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ P computation) :
    StoredPath state computation := by
  induction computation with
  | pure value => exact fun _ member => by cases member
  | query request next ih =>
    obtain ⟨answer, here⟩ := stored request (AllQ.head holds)
    have same : answerOf state request = answer := answerOf_of_stored here
    refine storedPath_query.mpr ⟨by rw [same]; exact here, ih _ (AllQ.tail holds _)⟩

end Generic

/-! ### The opening's hash part -/

section OpeningHash

variable [FieldCertificate]

theorem curveLanes_hashFree (table : Public) (bits : BitInput) (mac : InputMac) (lane : Lane)
    (count : Nat) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ HashFree (Programs.evalLaneM count lane joins scale word labels) :=
  (evalLaneM_allQ count lane joins scale word labels).mono fun _ inside =>
    hashFree_of_fixedAt inside

/-- **`HW`'s opening stores at most one hash key.** -/
theorem opening_hash_oneKey (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF Block)
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈ (runRefill bits draw (openingQueriesM table bits mac) LazyOracle.empty
      (fun _ => none) ∅).support) :
    ∀ k k', outcome.2.1.hash.lookup k ≠ none → outcome.2.1.hash.lookup k' ≠ none → k = k' := by
  rw [openingQueriesM_eq_prefix] at member
  obtain ⟨mid, _, midMember, restMember⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ member
  -- the part after the prefix asks no hash question
  have restFree : AllQ HashFree (whitePadsM ⟨mid.1.1, mid.1.2⟩ >>= fun pads =>
      Programs.evalLaneM pointElementCountX .pointX table.pointXHot
          (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
        >>= fun pointX =>
      Programs.evalLaneM pointElementCountY .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
        >>= fun pointY => pure (pointX, pointY)) :=
    ((whitePadsM_encInput _).mono fun _ inside => hashFree_of_encInputIs inside).bind fun _ =>
      (curveLanes_hashFree table bits mac _ _ _ _ _ _).bind fun _ =>
        (curveLanes_hashFree table bits mac _ _ _ _ _ _).bind fun _ => .pure _
  have restSame := runRefill_hash_same bits draw _ restFree _ _ _ _ restMember
  rw [restSame]
  -- the prefix: two hash-free lanes, then one hash question
  unfold curvePrefixM at midMember
  obtain ⟨lane1, _, lane1Member, rest1⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ midMember
  obtain ⟨lane2, _, lane2Member, rest2⟩ := runRefill_bind_mem bits draw _ _ _ _ _ _ rest1
  have empty1 := runRefill_hash_same bits draw _ (curveLanes_hashFree table bits mac _ _ _ _ _ _)
    _ _ _ _ lane1Member
  have empty2 := runRefill_hash_same bits draw _ (curveLanes_hashFree table bits mac _ _ _ _ _ _)
    _ _ _ _ lane2Member
  -- the hash question on an empty table: every stored key is its input
  set key := CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues lane1.1 lane2.1) with keyDef
  have only := runRefill_invariant bits draw (fun request => request = .hash key)
    (fun state => ∀ k, state.hash.lookup k ≠ none → k = key)
    (fun request state holds invariant answer answerMember => by
      subst holds
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
      intro k found
      unfold HashTable.query at drawnMember
      split at drawnMember
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at drawnMember
        subst drawnMember
        exact invariant k found
      · simp only [Draw.distribution] at drawnMember
        obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp drawnMember
        by_cases same : k = key
        · exact same
        · have different : (k == key) = false := by simpa [beq_iff_eq] using same
          exact invariant k (by simpa [List.lookup, different] using found))
    (fun request state _ _ _ _ _ _ consumed _ => by
      obtain ⟨index, input, rfl, _⟩ := consumeCell_spec consumed
      cases (show False from by simp_all))
    (Programs.askHash key) (.query _ _ rfl fun _ => .pure _) _ _ _ _
    (fun k found => by
      rw [empty2, empty1] at found
      exact absurd rfl found) rest2
  exact fun k k' hk hk' => (only k hk).trans (only k' hk').symm

/-- The prefix's key is its hash answer. -/
theorem prefixKeysOn_eq (state : LState) (table : Public) (bits : BitInput) (mac : InputMac) :
    ∃ input, prefixKeysOn state table bits mac = answerOf state (.hash input) ∧
      (⟨.hash input, answerOf state (.hash input)⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript (answerOf state) (curvePrefixM table bits mac) := by
  refine ⟨CurveMembership.evaluate table.curve bits.toAffine (Pipeline.curveValues
    (FreeQuery.eval (answerOf state) (Programs.evalLaneM curveElementCountX .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)))
    (FreeQuery.eval (answerOf state) (Programs.evalLaneM curveElementCountY .curveY table.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)))), ?_, ?_⟩
  · unfold prefixKeysOn curvePrefixM
    simp only [FreeQuery.eval_bind]
    rfl
  · unfold curvePrefixM
    exact mem_transcript_right _ (mem_transcript_right _ List.mem_cons_self)

/-- **At the opening's final state, the key potential is at least the indicator of its key.** -/
theorem keyPotential_opening (table : Public) (bits : BitInput) (mac : InputMac)
    (draw : Cell → PMF Block) (S : Finset Block)
    (outcome : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some outcome ∈ (runRefill bits draw (openingQueriesM table bits mac) LazyOracle.empty
      (fun _ => none) ∅).support) :
    ind ((prefixKeysOn outcome.2.1 table bits mac).1 ∈ S) ≤ keyPotential S outcome.2.1 := by
  classical
  have stored := opening_stores_prefix table bits mac draw _ _ _ outcome member
  obtain ⟨input, keyEq, onPath⟩ := prefixKeysOn_eq outcome.2.1 table bits mac
  have here := stored _ onPath
  have oneKey := opening_hash_oneKey table bits mac draw outcome member
  have present : outcome.2.1.hash.lookup input ≠ none := by
    intro missing
    change (outcome.2.1.hash.lookup input).map _ = some _ at here
    rw [missing] at here
    cases here
  have nonempty : outcome.2.1.hash ≠ [] := by
    intro empty
    rw [empty] at present
    exact present rfl
  by_cases hit : (prefixKeysOn outcome.2.1 table bits mac).1 ∈ S
  · rw [ind_pos hit]
    unfold keyPotential
    rw [if_neg nonempty, if_pos oneKey, if_pos]
    refine ⟨input, answerOf outcome.2.1 (.hash input), here, ?_⟩
    rw [← keyEq]
    exact hit
  · rw [ind_neg hit]
    exact zero_le

end OpeningHash

/-! ### The shadow's EncPRF part -/

section ShadowEnc

variable [FieldCertificate] [GroupCertificate]

/-- The evaluator after its prefix and its pads. -/
def onCurveRest (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Programs.M (Option (Option Point)) :=
  Programs.evalLaneM pointElementCountX .pointX table.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
    >>= fun pointX =>
  Programs.evalLaneM pointElementCountY .pointY table.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
    >>= fun pointY =>
  Programs.unlockM (Pipeline.pointTable table) bits.toAffine (Programs.transformMacOf pads mac)
    >>= fun digits =>
  pure (some (Garbling.decodeResult
    { point := bits.toAffine
      pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
        (Pipeline.digitValues pointX pointY) bits.toAffine
      exceptionDigits := digits }))

/-- **The evaluator starts with the prefix and its pads.** -/
theorem onCurveM_eq_prefix (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.onCurveM table bits mac = curvePrefixM table bits mac >>= fun hashed =>
      Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
        onCurveRest table bits mac pads := by
  unfold Programs.onCurveM curvePrefixM onCurveRest
  simp only [fq_bind_assoc]

theorem hashM_encFree (index : FixedIndex) (label : Block) :
    AllQ EncFree (Programs.hashM index label) := by
  refine AllQ.bind ?_ fun _ => .pure _
  exact .query _ _ trivial fun _ => .pure _

theorem onCurveRest_encFree (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    AllQ EncFree (onCurveRest table bits mac pads) :=
  ((evalLaneM_allQ _ _ _ _ _ _).mono fun _ inside => encFree_of_fixedAt inside).bind fun _ =>
    ((evalLaneM_allQ _ _ _ _ _ _).mono fun _ inside => encFree_of_fixedAt inside).bind fun _ =>
      (AllQ.vector fun _ =>
        (((AllQ.vector fun _ => hashM_encFree _ _).bind fun _ => .pure _).bind fun _ =>
          ((AllQ.vector fun _ => hashM_encFree _ _).bind fun _ => .pure _).bind fun _ =>
            .pure _).bind fun _ => .pure _).bind fun _ => .pure _

/-- An EncPRF forward question at one of the two pad inputs of key `w`. -/
def EncPad (w : Block) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward _ _ => False
  | .fixedInverse _ _ => False
  | .encForward _ input => input = encodeBit false ^^^ w ∨ input = encodeBit true ^^^ w
  | .encInverse _ _ => False
  | .hash _ => False

theorem padM_encPad (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    AllQ (EncPad keys.first) (Programs.padM keys coordinate index bit) :=
  (padM_encInput keys coordinate index bit).mono fun request inside => by
    cases request with
    | encForward _ input =>
      change input = encodeBit bit ^^^ keys.first at inside
      cases bit
      · exact Or.inl inside
      · exact Or.inr inside
    | fixedForward _ _ => exact inside.elim
    | fixedInverse _ _ => exact inside.elim
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim

theorem evalPadsM_encPad (keys : WhiteningKeys) (bits : BitInput) :
    AllQ (EncPad keys.first) (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (padM_encPad _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_encPad _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (padM_encPad _ _ _ _).bind fun _ =>
      AllQ.ite ((padM_encPad _ _ _ _).bind fun _ => .pure _) (.pure _)).bind fun _ => .pure _

/-- A known EncPRF input is a stored question. -/
theorem storedAs_of_enc {state : LState} {j : EncPRF.PermutationIndex} {input : Block}
    (known : lk (state.enc j) input.toFin ≠ none) :
    ∃ answer, StoredAs state ⟨.encForward j input, answer⟩ := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp known
  refine ⟨BitVec.ofFin a, ?_⟩
  change (lk (state.enc j) input.toFin).map BitVec.ofFin = some (BitVec.ofFin a)
  rw [ha]
  rfl

/-- **After the shadow, every stored EncPRF input is one of the two pad inputs.** -/
theorem shadow_enc_final (table : Public) (bits : BitInput) (mac : InputMac) (state : LState)
    (stored : StoredPath state (curvePrefixM table bits mac))
    (exact : EncExact state (prefixKeysOn state table bits mac).1)
    (final : Unit × LState) (member : final ∈ (runLazyQ (shadowOnM table bits mac) state).support) :
    ∀ j z, lk (final.2.enc j) z ≠ none →
      z = padInput false (prefixKeysOn state table bits mac).1 ∨
        z = padInput true (prefixKeysOn state table bits mac).1 := by
  rw [shadowOnM_run _ _ _ state stored, runLazyQ_bind] at member
  generalize hk : prefixKeysOn state table bits mac = k at member exact ⊢
  obtain ⟨pads, padsMember, restMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨padsGrow, padsStored, _⟩ := runLazyQ_stores _ state pads padsMember
  -- after the bit-`true` pads: only the two inputs
  have padsOnly := runLazyQ_invariant
    (EncInputIs (encodeBit true ^^^ k.1))
    (fun s => ∀ j z, lk (s.enc j) z ≠ none → z = padInput false k.1 ∨ z = padInput true k.1)
    (fun request s holds invariant answer answerMember => by
      cases request with
      | encForward index input =>
        change input = _ at holds
        subst holds
        obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        intro j z found
        by_cases same : j = index
        · subst same
          simp only [Function.update_self] at found
          rcases forward_new _ _ drawn drawnMember z found with old | new
          · exact invariant j z old
          · exact Or.inr new
        · simp only [Function.update_of_ne same] at found
          exact invariant j z found
      | fixedForward _ _ => exact holds.elim
      | fixedInverse _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | hash _ => exact holds.elim)
    _ (truePadsM_encInput ⟨k.1, k.2⟩) state pads
    (fun j z found => Or.inl ((exact j z).mp found)) padsMember
  -- the evaluator re-run keeps the EncPRF part
  have prefixStored := (storedPath_grows _ padsGrow stored).1
  have keysSame := (storedPath_grows _ padsGrow stored).2
  rw [onCurveM_eq_prefix, fq_bind_assoc, runLazyQ_bind, runLazyQ_storedPath _ _ prefixStored,
    PMF.pure_bind] at restMember
  dsimp only at restMember
  have padsPath : StoredPath pads.2 (Programs.evalPadsM
      ⟨(FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).1,
        (FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).2⟩ bits) := by
    refine storedPath_of_allQ _ pads.2 (fun request inside => ?_) _ (evalPadsM_encPad _ _)
    cases request with
    | encForward j input =>
      have keyEq : (FreeQuery.eval (answerOf pads.2) (curvePrefixM table bits mac)).1 = k.1 := by
        rw [← hk]
        unfold prefixKeysOn
        exact congrArg Prod.fst keysSame
      change input = _ ∨ input = _ at inside
      rw [keyEq] at inside
      rcases inside with rfl | rfl
      · exact storedAs_of_enc (ne_none_of_grows (padsGrow.enc j) ((exact j _).mpr rfl))
      · exact storedAs_of_enc (enc_ne_none_of_stored
          (padsStored _ (truePad_mem_transcript _ _ j)))
    | fixedForward _ _ => exact inside.elim
    | fixedInverse _ _ => exact inside.elim
    | encInverse _ _ => exact inside.elim
    | hash _ => exact inside.elim
  rw [fq_bind_assoc, runLazyQ_bind, runLazyQ_storedPath _ _ padsPath, PMF.pure_bind] at restMember
  dsimp only at restMember
  have encSame := runLazyQ_invariant EncFree (fun s => s.enc = pads.2.enc)
    (fun request s holds same answer answerMember => by
      cases request with
      | encForward _ _ => exact holds.elim
      | encInverse _ _ => exact holds.elim
      | fixedForward _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | fixedInverse _ _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same
      | hash _ =>
        obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
        exact same)
    _ ((onCurveRest_encFree _ _ _ _).bind fun _ => .pure _) pads.2 final rfl restMember
  intro j z found
  rw [encSame] at found
  exact padsOnly j z found

end ShadowEnc

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
