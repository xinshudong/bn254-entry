/-
**Phase 3, P1m — (B1) the fixed-key part: where every fixed-key pair of `M'`'s private state comes
from, and what its input is.**

For an index `i`, `inputOf … i` is its **canonical input**: at a fold index of (lane, chunk) the
level-1 label `W`, at a scale index the one-hot label of its switch (read from the opening's fold
answers), at a gadget index the transformed label. On the curve, after the opening, the designated
installation and the shadow:

* `final_input` — every stored pair at `i` has input `inputOf i` (so at most one pair per index),
  and every designated request at `i` too (`request_input`);
* `final_site_output` — at a non-designated mask site the output is `tape ⊕ input`;
* `final_designated_output` — at a designated index the output is `o ⊕ input` for its request.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsHashOn

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests designatedIndex candidateIndex candidateIndex_injective)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request AllQ EncAt FixedAt IndexAt
  queriesAlong queriesAlong_bind queriesAlong_pure queriesAlong_vector cellOf maskIndex
  foldLabels inactiveEntry program_frame)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The designated installation -/

section Install

/-- **Every pair the installation adds is a request's.** -/
theorem programAllSkip_pairs :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (state : LState) (i : FixedIndex)
      (x y : Fin (2 ^ 128)), lk ((programAllSkip requests state).fixed i) x = some y →
        lk (state.fixed i) x = some y ∨
          ∃ input output, (i, some input, output) ∈ requests ∧ x = input.toFin ∧
            y = (output ^^^ input).toFin := by
  intro requests
  induction requests with
  | nil => exact fun _ _ _ _ found => Or.inl found
  | cons request rest ih =>
    intro state i x y found
    obtain ⟨index, input, output⟩ := request
    cases input with
    | none =>
      rcases ih state i x y found with old | ⟨a, b, member, hx, hy⟩
      · exact Or.inl old
      · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ member, hx, hy⟩
    | some input =>
      change lk ((programAllSkip rest ((LazyOracle.program (.fixedForward index input)
        (output ^^^ input) state).getD state)).fixed i) x = some y at found
      rcases ih _ i x y found with old | ⟨a, b, member, hx, hy⟩
      · cases success : LazyOracle.program (.fixedForward index input) (output ^^^ input) state with
        | none =>
          rw [success] at old
          exact Or.inl old
        | some updated =>
          rw [success] at old
          rcases program_fixed_pairs index input _ state updated success i x y old
            with older | ⟨rfl, rfl, rfl⟩
          · exact Or.inl older
          · exact Or.inr ⟨input, output, List.mem_cons_self, rfl, rfl⟩
      · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ member, hx, hy⟩

/-- The installation changes only the requests' indices. -/
theorem programAllSkip_other :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (state : LState) (i : FixedIndex),
      (∀ request ∈ requests, request.1 ≠ i) → (programAllSkip requests state).fixed i = state.fixed i := by
  intro requests
  induction requests with
  | nil => exact fun _ _ _ => rfl
  | cons request rest ih =>
    intro state i avoid
    obtain ⟨index, input, output⟩ := request
    have different : index ≠ i := avoid _ List.mem_cons_self
    have restAvoid : ∀ r ∈ rest, r.1 ≠ i := fun r member => avoid r (List.mem_cons_of_mem _ member)
    cases input with
    | none => exact ih state i restAvoid
    | some input =>
      show (programAllSkip rest ((LazyOracle.program (.fixedForward index input)
        (output ^^^ input) state).getD state)).fixed i = _
      rw [ih _ i restAvoid]
      cases success : LazyOracle.program (.fixedForward index input) (output ^^^ input) state with
      | none => rfl
      | some updated => exact program_frame index input _ state updated success i (Ne.symm different)

/-- A program at an index with no pairs succeeds and stores its pair. -/
theorem program_fresh_stores (state : LState) (i : FixedIndex) (input output : Block)
    (fresh : ∀ z, lk (state.fixed i) z = none) :
    ∃ updated, LazyOracle.program (.fixedForward i input) output state = some updated ∧
      lk (updated.fixed i) input.toFin = some output.toFin := by
  have notIn : ¬ (state.fixed i).knownInput input.toFin := fun known =>
    (knownInput_iff _ _).mp known (fresh _)
  have notOut : ¬ (state.fixed i).knownOutput output.toFin := fun known => by
    obtain ⟨z, found⟩ := (knownOutput_iff _ _).mp known
    rw [fresh z] at found
    cases found
  have succeeds : LazyOracle.permutationProgram (state.fixed i) input.toFin output.toFin ≠ none := by
    unfold LazyOracle.permutationProgram
    rw [dif_pos ⟨notIn, notOut⟩]
    exact Option.some_ne_none _
  cases hp : LazyOracle.permutationProgram (state.fixed i) input.toFin output.toFin with
  | none => exact absurd hp succeeds
  | some next =>
    refine ⟨{ state with fixed := Function.update state.fixed i next }, ?_, ?_⟩
    · simp only [LazyOracle.program, hp]
      rfl
    · simp only [Function.update_self]
      exact LazyOracle.permutationProgram_lookup _ _ _ _ hp

/-- **A request at an index with no pairs, alone at its index, is installed.** -/
theorem programAllSkip_installs :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (state : LState) (i : FixedIndex)
      (input output : Block), (i, some input, output) ∈ requests →
        (requests.map Prod.fst).Nodup → (∀ z, lk (state.fixed i) z = none) →
          lk ((programAllSkip requests state).fixed i) input.toFin =
            some (output ^^^ input).toFin := by
  intro requests
  induction requests with
  | nil => exact fun _ _ _ _ member => absurd member List.not_mem_nil
  | cons request rest ih =>
    intro state i input output member distinct fresh
    obtain ⟨index, input', output'⟩ := request
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
    rcases List.mem_cons.mp member with same | inRest
    · simp only [Prod.mk.injEq, Option.some.injEq] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      obtain ⟨updated, success, stored⟩ := program_fresh_stores state i input (output ^^^ input) fresh
      show lk ((programAllSkip rest ((LazyOracle.program (.fixedForward i input)
        (output ^^^ input) state).getD state)).fixed i) input.toFin = _
      rw [programAllSkip_other rest _ i fun r inside same => distinct.1 ⟨r, inside, same⟩,
        success, Option.getD_some]
      exact stored
    · have different : index ≠ i := fun same =>
        distinct.1 ⟨(i, some input, output), inRest, same.symm⟩
      cases input' with
      | none => exact ih state i input output inRest distinct.2 fresh
      | some input' =>
        show lk ((programAllSkip rest ((LazyOracle.program (.fixedForward index input')
          (output' ^^^ input') state).getD state)).fixed i) input.toFin = _
        refine ih _ i input output inRest distinct.2 ?_
        cases success : LazyOracle.program (.fixedForward index input') (output' ^^^ input') state with
        | none => exact fresh
        | some updated =>
          rw [Option.getD_some, program_frame index input' _ state updated success i
            (Ne.symm different)]
          exact fresh

/-- The designated requests sit at pairwise distinct indices. -/
theorem programRequests_nodup (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    ((programRequests bits record blocks).map Prod.fst).Nodup := by
  unfold programRequests
  rw [List.map_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun digit _ => ?_, ?_⟩
  · rw [List.map_flatMap]
    refine List.nodup_flatMap.mpr ⟨fun collector _ => ?_, ?_⟩
    · rw [List.map_map]
      refine (List.nodup_finRange 3).map fun b b' same => ?_
      have := candidateIndex_injective (a₁ := (digit, collector, b, _))
        (a₂ := (digit, collector, b', _)) same
      simp only [Prod.mk.injEq] at this
      exact this.2.2.1
    · refine (List.nodup_finRange 3).pairwise_of_forall_ne fun c _ c' _ different => ?_
      simp only [Function.onFun, List.disjoint_left, List.mem_map, List.map_map]
      rintro _ ⟨b, _, rfl⟩ ⟨b', _, same⟩
      have := candidateIndex_injective (a₁ := (digit, c', b', _)) (a₂ := (digit, c, b, _)) same
      simp only [Prod.mk.injEq] at this
      exact different this.2.1.symm
  · refine (List.nodup_finRange digitCount).pairwise_of_forall_ne fun d _ d' _ different => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_flatMap, List.mem_map, List.map_flatMap,
      List.map_map]
    rintro _ ⟨c, _, b, _, rfl⟩ ⟨c', _, b', _, same⟩
    have := candidateIndex_injective (a₁ := (d', c', b', _)) (a₂ := (d, c, b, _)) same
    simp only [Prod.mk.injEq] at this
    exact different this.1.symm

/-- A designated request is at a designated index, with the record's input. -/
theorem mem_programRequests {bits : BitInput} {record : Record}
    {blocks : Fin digitCount × Fin 3 → Block × Block × Block} {i : FixedIndex} {input : Block}
    {output : Block} (member : (i, some input, output) ∈ programRequests bits record blocks) :
    ∃ d c b, i = designatedIndex bits d c b ∧ record i = some input ∧
      output = Kriterion.ArgoMAC.Phase3.Glue.limbAt b (blocks (d, c)) := by
  unfold programRequests at member
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, Prod.mk.injEq] at member
  obtain ⟨d, c, b, rfl, hr, ho⟩ := member
  exact ⟨d, c, b, rfl, hr, ho.symm⟩

end Install

/-! ### The canonical input of an index -/

section Canonical

/-- The joins of a lane. -/
def laneJoins (table : Public) : Lane → Vector Block foldStepCount
  | .curveX => table.curveXHot
  | .curveY => table.curveYHot
  | .pointX => table.pointXHot
  | .pointY => table.pointYHot

/-- The cleartext word of a lane. -/
def laneWord (bits : BitInput) : Lane → BitVec coordinateBitCount
  | .curveX => Pipeline.coordBits bits .x
  | .curveY => Pipeline.coordBits bits .y
  | .pointX => Pipeline.coordBits bits .x
  | .pointY => Pipeline.coordBits bits .y

/-- The labels of a lane: the MAC labels (system A) or the whitened ones (system B). -/
def laneLabels (mac : InputMac) (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Lane → Fin coordinateBitCount → Block
  | .curveX => Pipeline.macLabels mac .x
  | .curveY => Pipeline.macLabels mac .y
  | .pointX => Pipeline.macLabels (Programs.whitenMacOf pads mac) .x
  | .pointY => Pipeline.macLabels (Programs.whitenMacOf pads mac) .y

theorem switch_lt (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) : s.val < 2 ^ chunkWidth c := by
  rw [chunkWidth_eq_two]
  exact s.isLt

/-- **The canonical input of an index.** -/
def inputOf (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (ans : (request : Request) → request.Answer) (tmac : InputMac) : FixedIndex → Block
  | .hot lane c _ _ _ => laneW (laneJoins table lane) (laneLabels mac pads lane) c
  | .scale lane c s _ _ => laneHot lane (laneJoins table lane) (laneWord bits lane)
      (laneLabels mac pads lane) ans c ⟨s.val, switch_lt c s⟩
  | .gadget _ κ pos => Pipeline.macLabels tmac κ pos

/-- **A question of a lane is at its index's canonical input.** -/
theorem laneQuery_inputOf (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (ans : (request : Request) → request.Answer) (tmac : InputMac) (lane : Lane) (count : ℕ)
    (scale : Fin chunkCount → Fin count → BaseField) (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (Programs.evalLaneM count lane
      (laneJoins table lane) scale (laneWord bits lane) (laneLabels mac pads lane))) :
    x = inputOf table bits mac pads ans tmac i := by
  obtain ⟨c, ⟨half, same⟩ | ⟨switch, _, el, b, same⟩⟩ :=
    lane_query count lane (laneJoins table lane) scale (laneWord bits lane)
      (laneLabels mac pads lane) ans _ member
  · injection same with iEq xEq
    subst iEq
    subst xEq
    rfl
  · injection same with iEq xEq
    subst iEq
    subst xEq
    have small : switch.val < 2 ^ chunkBits := lt_of_lt_of_eq switch.isLt (by
      rw [chunkWidth_eq_two]; rfl)
    show _ = laneHot lane (laneJoins table lane) (laneWord bits lane) (laneLabels mac pads lane) ans c
      ⟨switch.val % 2 ^ chunkBits, _⟩
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt small).symm

/-- **The fold questions of every chunk are on a lane's path.** -/
theorem fold_mem_lane (ans : (request : Request) → request.Answer) (count : ℕ) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (word : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (c : Fin chunkCount) (half : Bool) :
    .fixedForward (foldIdx lane c (chunkValue word c).toNat half) (laneW joins labels c) ∈
      queriesAlong ans (Programs.evalLaneM count lane joins scale word labels) := by
  unfold Programs.evalLaneM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
  rw [evalChunkM_eq]
  unfold chunkProg
  rw [queriesAlong_bind, queriesAlong_evalFoldM lane c ans _ _ _ _ (chunkWidth_eq_two c)]
  refine List.mem_append_left _ ?_
  cases half <;> simp

end Canonical

/-! ### The opening's and the shadow's questions at their canonical inputs -/

section Paths

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

theorem hash_mem_opening (ans : (request : Request) → request.Answer) :
    .hash (tOf table bits mac ans) ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    eval_askHash, List.mem_append, List.mem_singleton]
  exact Or.inr (Or.inr (Or.inl trivial))

theorem whitePads_mem_opening (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans
      (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩)) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    eval_askHash, List.mem_append, List.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inl member)))

theorem pointX_mem_opening (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (pointXM table bits
      (Programs.whitenMacOf (wPadsOf table bits mac ans) mac))) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    eval_askHash, List.mem_append, List.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member))))

theorem pointY_mem_opening (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (pointYM table bits
      (Programs.whitenMacOf (wPadsOf table bits mac ans) mac))) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    eval_askHash, List.mem_append, List.mem_singleton]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr member))))

theorem curveX_mem_opening' (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveXM table bits mac)) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq, queriesAlong_bind]
  exact List.mem_append_left _ member

theorem curveY_mem_opening' (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveYM table bits mac)) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  rw [openingQueriesM_eq, queriesAlong_bind, queriesAlong_bind]
  exact List.mem_append_right _ (List.mem_append_left _ member)

variable [GroupCertificate]

/-- **Every fixed-key question of the opening is at its canonical input.** -/
theorem opening_fixed_input (ans : (request : Request) → request.Answer) (tmac : InputMac)
    (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    x = inputOf table bits mac (wPadsOf table bits mac ans) ans tmac i := by
  rcases mem_opening table bits mac ans _ member with a | b | c | d | e | f
  · exact laneQuery_inputOf table bits mac (wPadsOf table bits mac ans) ans tmac .curveX _ _ i x a
  · exact laneQuery_inputOf table bits mac (wPadsOf table bits mac ans) ans tmac .curveY _ _ i x b
  · cases c
  · exact absurd (mem_queriesAlong_allQ ans (Kriterion.ArgoMAC.Phase3.Lazy.whitePadsM_allQ _) _ d)
      not_encAt_fixed
  · exact laneQuery_inputOf table bits mac (wPadsOf table bits mac ans) ans tmac .pointX _ _ i x e
  · exact laneQuery_inputOf table bits mac (wPadsOf table bits mac ans) ans tmac .pointY _ _ i x f

/-- **Every fixed-key question of the shadow is at its canonical input**, read along its own
answers (the gadget at the evaluator's transformed labels). -/
theorem shadow_fixed_input (ans : (request : Request) → request.Answer) (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (shadowOnM table bits mac)) :
    x = inputOf table bits mac (wPadsOf table bits mac ans) ans
      (Programs.transformMacOf (ePadsOf table bits mac ans) mac) i := by
  rcases mem_shadow_fixed table bits mac ans i x member with a | b | c | d | e
  · exact laneQuery_inputOf table bits mac _ ans _ .curveX _ _ i x a
  · exact laneQuery_inputOf table bits mac _ ans _ .curveY _ _ i x b
  · exact laneQuery_inputOf table bits mac _ ans _ .pointX _ _ i x c
  · exact laneQuery_inputOf table bits mac _ ans _ .pointY _ _ i x d
  · obtain ⟨dd, κ, pos, same⟩ := mem_queriesAlong_allQ ans (unlockM_gadgetQ _ _ _) _ e
    injection same with iEq xEq
    subst iEq
    subst xEq
    rfl

end Paths

/-! ### The lanes as one family -/

section LaneFamily

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

/-- The scale readers of a lane. -/
def laneScale : (lane : Lane) → Fin chunkCount → Fin (laneCount lane) → BaseField
  | .curveX => fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk))
  | .curveY => fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk))
  | .pointX => fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk))
  | .pointY => fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk))

/-- **A lane's program**, with its labels read from the given pads. -/
abbrev laneProg (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) (lane : Lane) :
    Programs.M (Fin (laneCount lane) → BaseField) :=
  Programs.evalLaneM (laneCount lane) lane (laneJoins table lane) (laneScale table lane)
    (laneWord bits lane) (laneLabels mac pads lane)

variable [GroupCertificate]

/-- **Every lane of the opening is on its path.** -/
theorem lane_mem_opening (ans : (request : Request) → request.Answer) (lane : Lane) (q : Request)
    (member : q ∈ queriesAlong ans (laneProg table bits mac (wPadsOf table bits mac ans) lane)) :
    q ∈ queriesAlong ans (openingQueriesM table bits mac) := by
  cases lane with
  | curveX => exact curveX_mem_opening' table bits mac ans q member
  | curveY => exact curveY_mem_opening' table bits mac ans q member
  | pointX => exact pointX_mem_opening table bits mac ans q member
  | pointY => exact pointY_mem_opening table bits mac ans q member

/-- **A mask question of a lane, along one answer function, is asked along any other one** (at
that one's one-hot label). -/
theorem lane_mask_transfer (ans other : (request : Request) → request.Answer) (count : ℕ)
    (lane : Lane) (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (word : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block) (i : FixedIndex)
    (x : Block) (member : .fixedForward i x ∈ queriesAlong ans
      (Programs.evalLaneM count lane joins scale word labels))
    (isScale : ∃ l c s e b, i = .scale l c s e b) :
    ∃ x', .fixedForward i x' ∈ queriesAlong other
      (Programs.evalLaneM count lane joins scale word labels) := by
  obtain ⟨c, ⟨half, same⟩ | ⟨switch, active, el, b, same⟩⟩ :=
    lane_query count lane joins scale word labels ans _ member
  · injection same with iEq _
    obtain ⟨l, c', s, e, b', rfl⟩ := isScale
    simp [foldIdx, hotIndexNat] at iEq
  · injection same with iEq _
    subst iEq
    exact ⟨_, mask_mem_lane count lane joins scale word labels other c switch active el b⟩

end LaneFamily

theorem intercept_none_of_encAt {bits : BitInput} {r : Request} (inside : EncAt r) :
    interceptAnswer bits r = none := by
  cases r with
  | encForward _ _ => rfl
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem intercept_none_of_hot {bits : BitInput} (lane : Lane) (c : Fin chunkCount) (value : ℕ)
    (half : Bool) (x : Block) :
    interceptAnswer bits (.fixedForward (foldIdx lane c value half) x) = none :=
  Kriterion.ArgoMAC.Phase3.Lazy.hot_intercept bits lane c 1 _ half x

/-! ### The final state, described -/

section Final

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)

include member

/-- **A later state agrees with the opening along its non-intercepted path.** -/
theorem opening_agree (later : LState) (grow : Grows ran.2.1 later) (q : Request)
    (onPath : q ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)))
    (notIntercepted : interceptAnswer (restoredBits source input) q = none) :
    answerOf later q = refillAns (restoredBits source input) ran.2.1 q := by
  obtain ⟨stored, same⟩ := curve_stored_answer source input tape ran member q onPath notIntercepted
  rw [same]
  exact answerOf_of_stored (storedAs_grows grow stored)

theorem wPads_agree (later : LState) (grow : Grows ran.2.1 later) :
    wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf later) =
      wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  have tEq := tOf_agree source input tape ran member later grow
  have kEq : kOf source.publicValue (restoredBits source input) (restoredMac source input)
      (answerOf later) =
      kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
    show answerOf later (.hash (tOf _ _ _ (answerOf later))) = _
    rw [tEq]
    exact opening_agree source input tape ran member later grow _
      (hash_mem_opening _ _ _ _) rfl
  show FreeQuery.eval (answerOf later) (whitePadsM ⟨(kOf _ _ _ (answerOf later)).1,
      (kOf _ _ _ (answerOf later)).2⟩) = _
  rw [kEq]
  refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
  refine opening_agree source input tape ran member later grow q
    (whitePads_mem_opening _ _ _ _ q onPath) ?_
  exact intercept_none_of_encAt
    (mem_queriesAlong_allQ _ (Kriterion.ArgoMAC.Phase3.Lazy.whitePadsM_allQ _) q onPath)

/-- **A later state reads every chunk's fold material as the opening did.** -/
theorem material_agree (later : LState) (grow : Grows ran.2.1 later) (lane : Lane)
    (c : Fin chunkCount) :
    chunkMaterial lane c (answerOf later)
        (chunkValue (laneWord (restoredBits source input) lane) c).toNat
        (labelAt (chunkLabels (laneLabels (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) c))
        (joinAt (hotSlice (laneJoins source.publicValue lane) c)) =
      chunkMaterial lane c (refillAns (restoredBits source input) ran.2.1)
        (chunkValue (laneWord (restoredBits source input) lane) c).toNat
        (labelAt (chunkLabels (laneLabels (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) c))
        (joinAt (hotSlice (laneJoins source.publicValue lane) c)) := by
  have each : ∀ half, fwdAns (answerOf later) (foldIdx lane c
      (chunkValue (laneWord (restoredBits source input) lane) c).toNat half)
        (laneW (laneJoins source.publicValue lane) (laneLabels (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) c) =
      fwdAns (refillAns (restoredBits source input) ran.2.1) (foldIdx lane c
        (chunkValue (laneWord (restoredBits source input) lane) c).toNat half)
        (laneW (laneJoins source.publicValue lane) (laneLabels (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)) lane) c) := fun half =>
    opening_agree source input tape ran member later grow _
      (lane_mem_opening _ _ _ _ lane _ (fold_mem_lane _ _ lane _ _ _ _ c half))
      (intercept_none_of_hot lane c _ half _)
  unfold chunkMaterial
  rw [each false, each true]

/-- **A later state's canonical inputs are the opening's.** -/
theorem inputOf_agree (later : LState) (grow : Grows ran.2.1 later) (tmac : InputMac)
    (i : FixedIndex) :
    inputOf source.publicValue (restoredBits source input) (restoredMac source input)
        (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
          (answerOf later)) (answerOf later) tmac i =
      inputOf source.publicValue (restoredBits source input) (restoredMac source input)
        (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1))
        (refillAns (restoredBits source input) ran.2.1) tmac i := by
  rw [wPads_agree source input tape ran member later grow]
  cases i with
  | hot lane c _ _ _ => rfl
  | scale lane c s _ _ =>
    show foldLabels _ _ _ (chunkMaterial lane c (answerOf later) _ _ _) _ =
      foldLabels _ _ _ (chunkMaterial lane c _ _ _ _) _
    rw [material_agree source input tape ran member later grow lane c]
  | gadget _ _ _ => rfl

/-- **Every designated request is at its index's canonical input.** -/
theorem request_input (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (tmac : InputMac)
    (i : FixedIndex) (x output : Block)
    (inRequests : (i, some x, output) ∈ programRequests (restoredBits source input) ran.2.2 blocks) :
    x = inputOf source.publicValue (restoredBits source input) (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1))
      (refillAns (restoredBits source input) ran.2.1) tmac i := by
  obtain ⟨d, c, b, rfl, recorded, _⟩ := mem_programRequests inRequests
  rcases (opening_described source input tape ran member).records (designatedIndex _ d c b)
    with same | ⟨_, x', recorded', onPath⟩
  · rw [same] at recorded
    cases recorded
  · rw [recorded] at recorded'
    cases recorded'
    exact opening_fixed_input _ _ _ _ tmac _ _ onPath

variable (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 blocks) ran.2.1)).support)

include resultMember

theorem final_grows : Grows ran.2.1 result.2 :=
  (programAllSkip_grows _ _).trans (runLazyQ_grows _ _ result resultMember)

/-- **Every stored pair of the final state is at its index's canonical input.** -/
theorem final_input (i : FixedIndex) (x y : Fin (2 ^ 128)) (found : lk (result.2.fixed i) x = some y) :
    BitVec.ofFin x = inputOf source.publicValue (restoredBits source input) (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1))
      (refillAns (restoredBits source input) ran.2.1)
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) i := by
  have grow := final_grows source input tape ran member blocks result resultMember
  rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).1 i x y found
    with old | onPath
  · rcases programAllSkip_pairs _ _ i x y old with older | ⟨inp, out, inReq, hx, _⟩
    · rcases (opening_described source input tape ran member).fixed i x y older
        with none' | ⟨onPath, _, _⟩
      · rw [lk_empty_fixed] at none'
        cases none'
      · exact opening_fixed_input _ _ _ _ _ i _ onPath
    · rw [hx, BitVec.ofFin_toFin]
      exact request_input source input tape ran member blocks _ i inp out inReq
  · rw [shadow_fixed_input _ _ _ _ i _ onPath]
    exact inputOf_agree source input tape ran member result.2 grow _ i

/-- **At a non-designated mask site the final output is `tape ⊕ input`.** -/
theorem final_site_output (i : FixedIndex) (isScale : ∃ l c s e b, i = .scale l c s e b)
    (notDesignated : ¬ IsDesignated (restoredBits source input) i)
    {cell : Kriterion.ArgoMAC.Phase3.Lazy.Cell} (cellEq : cellOf i = some cell)
    (x y : Fin (2 ^ 128)) (found : lk (result.2.fixed i) x = some y) :
    BitVec.ofFin y = tape cell ^^^ BitVec.ofFin x := by
  have grow := final_grows source input tape ran member blocks result resultMember
  rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).1 i x y found
    with old | onPath
  · rcases programAllSkip_pairs _ _ i x y old with older | ⟨inp, out, inReq, _, _⟩
    · rcases (opening_described source input tape ran member).fixed i x y older
        with none' | ⟨_, _, tapeOut⟩
      · rw [lk_empty_fixed] at none'
        cases none'
      · exact tapeOut cell cellEq
    · obtain ⟨d, c, b, rfl, _, _⟩ := mem_programRequests inReq
      exact absurd ⟨d, c, b, rfl⟩ notDesignated
  · obtain ⟨x', onA⟩ : ∃ x', .fixedForward i x' ∈ queriesAlong
        (refillAns (restoredBits source input) ran.2.1)
        (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)) := by
      rcases mem_shadow_fixed _ _ _ (answerOf result.2) i _ onPath with a | b | c | d | e
      · obtain ⟨x', h⟩ := lane_mask_transfer (answerOf result.2)
          (refillAns (restoredBits source input) ran.2.1) _ .curveX _ _ _ _ i _ a isScale
        exact ⟨x', curveX_mem_opening' _ _ _ _ _ h⟩
      · obtain ⟨x', h⟩ := lane_mask_transfer (answerOf result.2)
          (refillAns (restoredBits source input) ran.2.1) _ .curveY _ _ _ _ i _ b isScale
        exact ⟨x', curveY_mem_opening' _ _ _ _ _ h⟩
      · rw [wPads_agree source input tape ran member result.2 grow] at c
        obtain ⟨x', h⟩ := lane_mask_transfer (answerOf result.2)
          (refillAns (restoredBits source input) ran.2.1) _ .pointX _ _ _ _ i _ c isScale
        exact ⟨x', pointX_mem_opening _ _ _ _ _ h⟩
      · rw [wPads_agree source input tape ran member result.2 grow] at d
        obtain ⟨x', h⟩ := lane_mask_transfer (answerOf result.2)
          (refillAns (restoredBits source input) ran.2.1) _ .pointY _ _ _ _ i _ d isScale
        exact ⟨x', pointY_mem_opening _ _ _ _ _ h⟩
      · obtain ⟨_, _, _, same⟩ := mem_queriesAlong_allQ _ (unlockM_gadgetQ _ _ _) _ e
        injection same with iEq _
        obtain ⟨l, c, s, e', b, rfl⟩ := isScale
        cases iEq
    have x'Eq := opening_fixed_input _ _ _ _ (Programs.transformMacOf (ePadsOf source.publicValue
      (restoredBits source input) (restoredMac source input) (answerOf result.2))
        (restoredMac source input)) i x' onA
    have xEq := final_input source input tape ran member blocks result resultMember i x y found
    have same : x' = BitVec.ofFin x := x'Eq.trans xEq.symm
    subst same
    obtain ⟨stored, _⟩ := curve_stored_answer source input tape ran member _ onA
      (Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain _ _ notDesignated)
    have lkA := stored_fixed_lk (a := fwdAns (answerOf ran.2.1) i (BitVec.ofFin x)) stored
    rw [BitVec.toFin_ofFin] at lkA
    rcases (opening_described source input tape ran member).fixed i _ _ lkA
      with none' | ⟨_, _, tapeOut⟩
    · rw [lk_empty_fixed] at none'
      cases none'
    · have lk3 := grow.fixed i _ _ lkA
      rw [found] at lk3
      cases lk3
      exact tapeOut cell cellEq

/-- A designated request of every designated index. -/
theorem request_mem (d : Fin digitCount) (c b : Fin 3) (r : Block)
    (recorded : ran.2.2 (designatedIndex (restoredBits source input) d c b) = some r) :
    (designatedIndex (restoredBits source input) d c b, some r,
      Kriterion.ArgoMAC.Phase3.Glue.limbAt b (blocks (d, c))) ∈
        programRequests (restoredBits source input) ran.2.2 blocks := by
  unfold programRequests
  refine List.mem_flatMap.mpr ⟨d, List.mem_finRange d, ?_⟩
  refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
  refine List.mem_map.mpr ⟨b, List.mem_finRange b, ?_⟩
  dsimp only
  rw [recorded]

/-- **At a designated index the final pair is its request's: `(E*, o ⊕ E*)`.** -/
theorem final_designated_output (i : FixedIndex)
    (designated : IsDesignated (restoredBits source input) i) (x y : Fin (2 ^ 128))
    (found : lk (result.2.fixed i) x = some y) :
    ∃ inp out, (i, some inp, out) ∈ programRequests (restoredBits source input) ran.2.2 blocks ∧
      BitVec.ofFin x = inp ∧ BitVec.ofFin y = out ^^^ inp := by
  have grow := final_grows source input tape ran member blocks result resultMember
  rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).1 i x y found
    with old | onPath
  · rcases programAllSkip_pairs _ _ i x y old with older | ⟨inp, out, inReq, hx, hy⟩
    · rcases (opening_described source input tape ran member).fixed i x y older
        with none' | ⟨_, notDesignated, _⟩
      · rw [lk_empty_fixed] at none'
        cases none'
      · exact absurd designated notDesignated
    · exact ⟨inp, out, inReq, by rw [hx, BitVec.ofFin_toFin], by rw [hy, BitVec.ofFin_toFin]⟩
  · obtain ⟨d, c, b, rfl⟩ := designated
    have recorded := Kriterion.ArgoMAC.Phase3.Lazy.runRefill_records (restoredBits source input) _ _
      ⟨d, c, b, rfl⟩ (Kriterion.ArgoMAC.Phase3.Lazy.openingQueriesM_queriesAt source.publicValue
        (restoredBits source input) (restoredMac source input) d c b) LazyOracle.empty
      (fun _ => none) ∅ (some ran) (openingRun_mem member) ran rfl
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp recorded
    have inReq := request_mem source input tape ran member blocks result resultMember d c b r hr
    have rEq := request_input source input tape ran member blocks
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) _ r _ inReq
    have xEq := final_input source input tape ran member blocks result resultMember _ x y found
    have fresh : ∀ z, lk (ran.2.1.fixed (designatedIndex (restoredBits source input) d c b)) z =
        none := by
      intro z
      cases hz : lk (ran.2.1.fixed (designatedIndex (restoredBits source input) d c b)) z with
      | none => rfl
      | some w =>
        rcases (opening_described source input tape ran member).fixed _ z w hz
          with none' | ⟨_, notDesignated, _⟩
        · rw [lk_empty_fixed] at none'
          cases none'
        · exact absurd ⟨d, c, b, rfl⟩ notDesignated
    have install := programAllSkip_installs _ ran.2.1 _ r _ inReq (programRequests_nodup _ _ _) fresh
    have lk3 := (runLazyQ_grows _ _ result resultMember).fixed _ _ _ install
    have xr : BitVec.ofFin x = r := xEq.trans rEq.symm
    have xFin : x = r.toFin := by rw [← xr, BitVec.toFin_ofFin]
    rw [← xFin, found] at lk3
    cases lk3
    exact ⟨r, _, inReq, xr, by rw [BitVec.ofFin_toFin]⟩

end Final

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
