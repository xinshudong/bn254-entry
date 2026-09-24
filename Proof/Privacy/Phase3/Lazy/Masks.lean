/-
**Phase 3, P4b — (b) the switch masks of a chunk on a tape.**

The masks of chunk `c` of a lane (`evalMasksM`) ask, for every inactive switch `s`, element `e`
and block `b`, one forward query at `scale(lane, c, s, e, b)` at the switch label `hot s`
(`queriesAlong_evalMasksM`). If every non-designated one is a first touch at an unknown input,
the tape runner answers all of them (`masks_detRun_ne_none`), and the value is

  `maskValues`: `sampleFp` of the tape limbs (`0` at a designated block) -- **independent of
  the labels** (`masks_value`).

This is the output-independence step: once the masks are consumed, nothing the run computes
afterwards reads the labels of the chunk, in particular not `E*`.
-/

import Proof.Privacy.Phase3.Lazy.ChunkZero

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (laneCount laneCount_le siteIndex)
open scoped ENNReal

noncomputable section

section Masks

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (bits : BitInput) (tape : Tape)

/-! ### The queries -/

theorem queriesAlong_switchMaskM (answer : (request : Request) → request.Answer) (count : Nat)
    (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) (label : Block) :
    queriesAlong answer (Programs.switchMaskM count lane chunk switch label) =
      (List.finRange count).flatMap fun element =>
        [.fixedForward (scaleIndexOf lane chunk switch element 0) label,
          .fixedForward (scaleIndexOf lane chunk switch element 1) label,
          .fixedForward (scaleIndexOf lane chunk switch element 2) label] := by
  unfold Programs.switchMaskM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  rfl

theorem queriesAlong_evalMasksM (answer : (request : Request) → request.Answer) (count : Nat)
    (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (alpha : Fin (2 ^ width)) :
    queriesAlong answer (Programs.evalMasksM count lane chunk width hot alpha) =
      (List.finRange (2 ^ width)).flatMap fun switch =>
        if switch = alpha then [] else
          queriesAlong answer (Programs.switchMaskM count lane chunk switch.val (hot switch)) := by
  unfold Programs.evalMasksM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  congr 1
  funext switch
  split <;> rfl

/-- The index of one mask query. -/
abbrev maskIndex {count : Nat} (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (element : Fin count) (block : Fin 3) : FixedIndex :=
  scaleIndexOf lane chunk switch element block

/-- Membership in the query list of the masks. -/
theorem mem_queriesAlong_evalMasksM (answer : (request : Request) → request.Answer) (count : Nat)
    (lane : Lane) (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (alpha : Fin (2 ^ width)) (request : Request)
    (member : request ∈ queriesAlong answer (Programs.evalMasksM count lane chunk width hot alpha)) :
    ∃ switch : Fin (2 ^ width), switch ≠ alpha ∧ ∃ (element : Fin count) (block : Fin 3),
      request = .fixedForward (maskIndex lane chunk switch.val element block) (hot switch) := by
  rw [queriesAlong_evalMasksM] at member
  obtain ⟨switch, _, inner⟩ := List.mem_flatMap.mp member
  split at inner
  · simp at inner
  · rename_i active
    rw [queriesAlong_switchMaskM] at inner
    obtain ⟨element, _, three⟩ := List.mem_flatMap.mp inner
    refine ⟨switch, active, element, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at three
    rcases three with same | same | same
    · exact ⟨0, same⟩
    · exact ⟨1, same⟩
    · exact ⟨2, same⟩

/-! ### Distinct indices -/

/-- The indices a list of requests touches. -/
def touchedIndices (requests : List Request) : List FixedIndex := requests.filterMap touchedIndex

theorem consumed_sublist (requests : List Request) :
    (requests.filterMap (consumedIndex bits)).Sublist (touchedIndices requests) := by
  induction requests with
  | nil => exact List.Sublist.slnil
  | cons request rest ih =>
      simp only [touchedIndices, List.filterMap_cons] at ih ⊢
      cases request with
      | fixedForward index input =>
          by_cases designated : IsDesignated bits index
          · rw [consumedIndex_designated bits input designated]
            exact ih.cons _
          · rw [consumedIndex_plain bits input designated]
            exact ih.cons_cons _
      | fixedInverse index output => exact ih.cons _
      | encForward _ _ => exact ih
      | encInverse _ _ => exact ih
      | hash _ => exact ih

/-- The mask index is injective in (switch, element, block) for switches below `2 ^ chunkBits` and
elements below `elementCountX`. -/
theorem maskIndex_injective {count : Nat} (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (widthLe : width ≤ chunkBits) (countLe : count ≤ elementCountX)
    {switch switch' : Fin (2 ^ width)} {element element' : Fin count} {block block' : Fin 3}
    (same : maskIndex lane chunk switch.val element block =
      maskIndex lane chunk switch'.val element' block') :
    switch = switch' ∧ element = element' ∧ block = block' := by
  have widthBound : 2 ^ width ≤ 2 ^ chunkBits := Nat.pow_le_pow_right (by norm_num) widthLe
  rw [maskIndex, maskIndex, scaleIndexOf_eq _ _ _ _ _ (lt_of_lt_of_le element.isLt countLe)
      (lt_of_lt_of_le switch.isLt widthBound),
    scaleIndexOf_eq _ _ _ _ _ (lt_of_lt_of_le element'.isLt countLe)
      (lt_of_lt_of_le switch'.isLt widthBound)] at same
  simp only [FixedIndex.scale.injEq, Fin.mk.injEq, true_and] at same
  exact ⟨Fin.ext same.1, Fin.ext same.2.1, same.2.2⟩

theorem three_nodup {γ : Type} {a b c : γ} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    [a, b, c].Nodup := by
  simp [ab, ac, bc]

/-- A mask index names its mask site. -/
theorem cellOf_maskIndex {count : Nat} (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (element : Fin count) (block : Fin 3)
    (countLe : count ≤ laneCount lane) :
    cellOf (maskIndex lane chunk switch.val element block) =
      some (⟨lane, chunk, switch, ⟨element.val, lt_of_lt_of_le element.isLt countLe⟩⟩, block) := by
  have same : maskIndex lane chunk switch.val element block =
      siteIndex (⟨lane, chunk, switch, ⟨element.val, lt_of_lt_of_le element.isLt countLe⟩⟩,
        block) := by
    simp only [maskIndex, siteIndex, scaleIndexOf]
  rw [same]
  exact cellOf_siteIndex _

theorem touchedIndices_nodup (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (widthLe : width ≤ chunkBits) (countLe : count ≤ elementCountX) (hot : HotLabels width)
    (alpha : Fin (2 ^ width)) (answer : (request : Request) → request.Answer) :
    (touchedIndices (queriesAlong answer
      (Programs.evalMasksM count lane chunk width hot alpha))).Nodup := by
  rw [queriesAlong_evalMasksM, touchedIndices, List.filterMap_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun switch _ => ?_, ?_⟩
  · split
    · simp
    · rw [queriesAlong_switchMaskM, List.filterMap_flatMap]
      refine List.nodup_flatMap.mpr ⟨fun element _ => ?_, ?_⟩
      · simp only [List.filterMap_cons, touchedIndex, List.filterMap_nil]
        have different : ∀ first second : Fin 3, first ≠ second →
            maskIndex lane chunk switch.val element first ≠
              maskIndex lane chunk switch.val element second := fun first second ne same =>
          ne (maskIndex_injective lane chunk width widthLe countLe same).2.2
        exact three_nodup (different 0 1 (by decide)) (different 0 2 (by decide))
          (different 1 2 (by decide))
      · refine (List.nodup_finRange count).pairwise_of_forall_ne fun first _ second _ different => ?_
        simp only [Function.onFun, List.filterMap_cons, touchedIndex, List.filterMap_nil,
          List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) (same | same | same) <;>
          exact different (maskIndex_injective lane chunk width widthLe countLe same).2.1
  · refine (List.nodup_finRange (2 ^ width)).pairwise_of_forall_ne
      fun first _ second _ different => ?_
    simp only [Function.onFun]
    split
    · simp
    · split
      · simp
      · rw [queriesAlong_switchMaskM, queriesAlong_switchMaskM, List.filterMap_flatMap,
          List.filterMap_flatMap]
        simp only [List.disjoint_left, List.mem_flatMap, List.filterMap_cons, touchedIndex,
          List.filterMap_nil, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ ⟨element, _, (rfl | rfl | rfl)⟩ ⟨element', _, (same | same | same)⟩ <;>
          exact different (maskIndex_injective lane chunk width widthLe countLe same).1

/-! ### The tape runner succeeds -/

/-- **The masks run on the tape** when every non-designated mask query is a first touch at an
unknown input. -/
theorem masks_detRun_ne_none (lane : Lane) (chunk : Fin chunkCount) (count : Nat)
    (countLe : count ≤ laneCount lane) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) (oracle : LState) (record : Record)
    (touched : Set FixedIndex)
    (untouched : ∀ switch, switch ≠ alpha → ∀ (element : Fin count) (block : Fin 3),
      ¬ IsDesignated bits (maskIndex lane chunk switch.val element block) →
        maskIndex lane chunk switch.val element block ∉ touched)
    (fresh : ∀ switch, switch ≠ alpha → ∀ (element : Fin count) (block : Fin 3),
      ¬ IsDesignated bits (maskIndex lane chunk switch.val element block) →
        ¬ (oracle.fixed (maskIndex lane chunk switch.val element block)).knownInput
          (hot switch).toFin) :
    detRun bits tape (Programs.evalMasksM count lane chunk (chunkWidth chunk) hot alpha) oracle
      record touched ≠ none := by
  refine detRun_ne_none bits tape _ oracle record touched (fun request member => ?_)
    ((consumed_sublist bits _).nodup (touchedIndices_nodup count lane chunk (chunkWidth chunk)
      (chunkWidth_le chunk) (countLe.trans (laneCount_le lane)) hot alpha _))
  obtain ⟨switch, active, element, block, rfl⟩ :=
    mem_queriesAlong_evalMasksM _ count lane chunk (chunkWidth chunk) hot alpha request member
  by_cases designated : IsDesignated bits (maskIndex lane chunk switch.val element block)
  · exact Or.inl designated
  · refine Or.inr ⟨untouched switch active element block designated,
      fresh switch active element block designated, ?_⟩
    rw [cellOf_maskIndex lane chunk switch element block countLe]
    exact Option.some_ne_none _

/-! ### The value is the tape's -/

open Classical in
/-- The Davies–Meyer hash the tape gives an index: `0` if designated, else the tape limb. -/
def tapeHash (index : FixedIndex) : Block :=
  if IsDesignated bits index then 0 else
    match cellOf index with
    | some cell => tape cell
    | none => 0

theorem tapeBlock_hash (index : FixedIndex) (label : Block)
    (isCell : IsDesignated bits index ∨ cellOf index ≠ none) :
    tapeBlock bits tape index label ^^^ label = tapeHash bits tape index := by
  by_cases designated : IsDesignated bits index
  · rw [tapeBlock_designated bits tape label designated, BitVec.xor_self]
    unfold tapeHash
    rw [if_pos designated]
    rfl
  · obtain ⟨cell, found⟩ := Option.ne_none_iff_exists'.mp (isCell.resolve_left designated)
    rw [tapeBlock_cell bits tape label designated found, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
    unfold tapeHash
    rw [if_neg designated, found]

/-- **The mask values on the tape**: `sampleFp` of the tape hashes, `0` at the active switch. They
do not depend on the labels. -/
def maskValues (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (alpha : Fin (2 ^ width)) : Fin (2 ^ width) → Fin count → BaseField :=
  fun switch element => if switch = alpha then 0 else
    sampleFp (tapeHash bits tape (maskIndex lane chunk switch.val element 0))
      (tapeHash bits tape (maskIndex lane chunk switch.val element 1))
      (tapeHash bits tape (maskIndex lane chunk switch.val element 2))

theorem eval_hashM_tape (index : FixedIndex) (label : Block)
    (isCell : IsDesignated bits index ∨ cellOf index ≠ none) :
    FreeQuery.eval (tapeAnswer bits tape) (Programs.hashM index label) =
      tapeHash bits tape index :=
  tapeBlock_hash bits tape index label isCell

/-- **(b) The masks' value on the tape is `maskValues`, whatever the labels.** -/
theorem masks_value (lane : Lane) (chunk : Fin chunkCount) (count : Nat)
    (countLe : count ≤ laneCount lane) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) :
    FreeQuery.eval (tapeAnswer bits tape)
        (Programs.evalMasksM count lane chunk (chunkWidth chunk) hot alpha) =
      maskValues bits tape count lane chunk (chunkWidth chunk) alpha := by
  have isCell : ∀ (switch : Fin (2 ^ chunkWidth chunk)) (element : Fin count) (block : Fin 3),
      IsDesignated bits (maskIndex lane chunk switch.val element block) ∨
        cellOf (maskIndex lane chunk switch.val element block) ≠ none := by
    intro switch element block
    right
    rw [cellOf_maskIndex lane chunk switch element block countLe]
    exact Option.some_ne_none _
  funext switch element
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_vector, FreeQuery.eval_pure,
    Vector.get_ofFn, maskValues]
  split
  · simp
  · simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_vector,
      FreeQuery.eval_pure, Vector.get_ofFn]
    rw [eval_hashM_tape bits tape _ _ (isCell switch element 0),
      eval_hashM_tape bits tape _ _ (isCell switch element 1),
      eval_hashM_tape bits tape _ _ (isCell switch element 2)]

end Masks

end

end Kriterion.ArgoMAC.Phase3.Lazy
