/-
**Phase 3, P1m — (B1) tools: one lane of the evaluator, along any answer function.**

Every chunk is `2` bits wide (`chunkWidth_eq_two`). For a lane `evalLaneM count lane joins scale word
labels` and an answer function `ans`:

* `mem_queriesAlong_chunkProg` / `lane_query` — every question on the path is a **fold** question of
  some chunk `c`, at one of the two halves of the inactive level-1 gate, at the level-1 label
  `W_c = join₀ ⊕ bitLabel₀` (`chunkW`), or a **mask** question at `scale(lane, c, s, e, b)` for an
  inactive switch `s`, at the one-hot label `foldLabels … (material) s`, where the material is the
  xor of the two fold answers (`chunkMaterial`); nothing else.
* `fresh_chunkProg`, `lane_fresh` — along every path the non-designated indices are distinct
  (`Fresh`).
* `lane_eval_eq` — **the value**: if the Davies–Meyer value of every mask question on the path is
  `h` of its index, the lane's value is `laneValue h`, a function of `h` alone (not of the labels,
  not of the fold answers).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsPath

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (IsDesignated)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Request AllQ FixedAt IndexAt queriesAlong
  queriesAlong_bind queriesAlong_pure queriesAlong_vector consumedIndex foldLabels inactiveEntry
  evalFoldM_two maskIndex maskIndex_injective queriesAlong_evalMasksM queriesAlong_switchMaskM
  evalFoldM_allQ evalMasksM_allQ hotIndexNat_indexAt scaleIndexOf_indexAt hot_not_designated
  indexAt_unique evalLaneM_allQ)
open scoped ENNReal

noncomputable section

theorem chunkWidth_eq_two (c : Fin chunkCount) : chunkWidth c = 2 := by
  unfold chunkWidth chunkWidthNat
  split <;> rfl

/-- A forward fixed-key answer, as a block. -/
def fwdAns (ans : (request : Request) → request.Answer) (index : FixedIndex) (input : Block) :
    Block :=
  ans (.fixedForward index input)

/-! ### The fold of one chunk -/

section Fold

variable (lane : Lane) (c : Fin chunkCount)

/-- The level-1 label of a chunk. -/
def chunkW (bitLabel join : ℕ → Block) : Block := join 0 ^^^ bitLabel 0

/-- The two fold indices of a chunk. -/
abbrev foldIdx (value : ℕ) (half : Bool) : FixedIndex :=
  hotIndexNat lane c 1 (inactiveEntry value) half

/-- **The fold material** of a chunk along an answer function: the xor of the two fold answers. -/
def chunkMaterial (ans : (request : Request) → request.Answer) (value : ℕ)
    (bitLabel join : ℕ → Block) : Block :=
  fwdAns ans (foldIdx lane c value false) (chunkW bitLabel join) ^^^
    fwdAns ans (foldIdx lane c value true) (chunkW bitLabel join)

theorem xor_cancel_label (a b label : Block) : (a ^^^ label) ^^^ (b ^^^ label) = a ^^^ b := by
  rw [BitVec.xor_assoc, BitVec.xor_comm label, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem queriesAlong_foldMaskM (ans : (request : Request) → request.Answer) (step entry : ℕ)
    (label : Block) :
    queriesAlong ans (Programs.foldMaskM lane c step entry label) =
      [.fixedForward (hotIndexNat lane c step entry false) label,
        .fixedForward (hotIndexNat lane c step entry true) label] := rfl

theorem eval_foldMaskM (ans : (request : Request) → request.Answer) (step entry : ℕ)
    (label : Block) :
    FreeQuery.eval ans (Programs.foldMaskM lane c step entry label) =
      (fwdAns ans (hotIndexNat lane c step entry false) label ^^^ label) ^^^
        (fwdAns ans (hotIndexNat lane c step entry true) label ^^^ label) := rfl

theorem two_lt {w : ℕ} (hw : w = 2) (s : Fin (2 ^ w)) : s.val < 2 ^ 2 :=
  lt_of_lt_of_eq s.isLt (by rw [hw])

/-- **The fold's two questions**, for a `2`-bit chunk. -/
theorem queriesAlong_evalFoldM (ans : (request : Request) → request.Answer) (value : ℕ)
    (bitLabel join : ℕ → Block) (w : ℕ) (hw : w = 2) :
    queriesAlong ans (Programs.evalFoldM lane c value bitLabel join w) =
      [.fixedForward (foldIdx lane c value false) (chunkW bitLabel join),
        .fixedForward (foldIdx lane c value true) (chunkW bitLabel join)] := by
  subst hw
  rw [evalFoldM_two, queriesAlong_bind, queriesAlong_foldMaskM, queriesAlong_pure, List.append_nil]
  rfl

/-- **The fold's labels**, for a `2`-bit chunk. -/
theorem eval_evalFoldM (ans : (request : Request) → request.Answer) (value : ℕ)
    (bitLabel join : ℕ → Block) (w : ℕ) (hw : w = 2) (s : Fin (2 ^ w)) :
    FreeQuery.eval ans (Programs.evalFoldM lane c value bitLabel join w) s =
      foldLabels value bitLabel join (chunkMaterial lane c ans value bitLabel join)
        ⟨s.val, two_lt hw s⟩ := by
  subst hw
  rw [evalFoldM_two, FreeQuery.eval_bind, eval_foldMaskM, xor_cancel_label]
  rfl

end Fold

/-! ### One chunk -/

section Chunk

variable (lane : Lane) (c : Fin chunkCount)

/-- A chunk's program, with its width a parameter. -/
def chunkProg (count : ℕ) (value : ℕ) (bitLabel join : ℕ → Block) (w : ℕ) (alpha : Fin (2 ^ w))
    (sc : Fin count → BaseField) : Programs.M (Fin count → BaseField) :=
  Programs.evalFoldM lane c value bitLabel join w >>= fun hot =>
    Programs.evalMasksM count lane c w hot alpha >>= fun masks =>
      pure (Programs.evalScaleOf w masks alpha sc)

theorem evalChunkM_eq (count : ℕ) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    Programs.evalChunkM count lane joins scale word labels c =
      chunkProg lane c count (chunkValue word c).toNat (labelAt (chunkLabels labels c))
        (joinAt (hotSlice joins c)) (chunkWidth c) (chunkOf word c) (scale c) := rfl

/-- **The questions of one chunk.** -/
theorem mem_queriesAlong_chunkProg (ans : (request : Request) → request.Answer) (count value : ℕ)
    (bitLabel join : ℕ → Block) (w : ℕ) (hw : w = 2) (alpha : Fin (2 ^ w))
    (sc : Fin count → BaseField) (r : Request)
    (member : r ∈ queriesAlong ans (chunkProg lane c count value bitLabel join w alpha sc)) :
    (∃ half, r = .fixedForward (foldIdx lane c value half) (chunkW bitLabel join)) ∨
      ∃ switch : Fin (2 ^ w), switch ≠ alpha ∧ ∃ (el : Fin count) (b : Fin 3),
        r = .fixedForward (scaleIndexOf lane c switch.val el b)
          (foldLabels value bitLabel join (chunkMaterial lane c ans value bitLabel join)
            ⟨switch.val, two_lt hw switch⟩) := by
  unfold chunkProg at member
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil,
    queriesAlong_evalFoldM lane c ans value bitLabel join w hw] at member
  rcases List.mem_append.mp member with fold | masks
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fold
    rcases fold with rfl | rfl
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inl ⟨true, rfl⟩
  · obtain ⟨switch, active, el, b, rfl⟩ :=
      Kriterion.ArgoMAC.Phase3.Lazy.mem_queriesAlong_evalMasksM ans count lane c w _ alpha r masks
    refine Or.inr ⟨switch, active, el, b, ?_⟩
    rw [eval_evalFoldM lane c ans value bitLabel join w hw switch]

theorem inIdx_of_fixedAt (bits : BitInput) {S : FixedIndex → Prop} {r : Request}
    (inside : FixedAt S r) : InIdx bits {i | S i} r := by
  intro i hi
  cases r with
  | fixedForward index input =>
    have : index = i := by
      simp only [consumedIndex] at hi
      split at hi
      · cases hi
      · exact Option.some.inj hi
    subst this
    exact inside
  | fixedInverse _ _ => exact inside.elim
  | encForward _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem consumedIndex_eq {bits : BitInput} {index i : FixedIndex} {input : Block}
    (hi : consumedIndex bits (.fixedForward index input) = some i) : i = index := by
  simp only [consumedIndex] at hi
  split at hi
  · cases hi
  · exact (Option.some.inj hi).symm

/-- One forward fixed-key hash at a fresh index is fresh. -/
theorem fresh_hashM (bits : BitInput) (index : FixedIndex) (label : Block) (used : Set FixedIndex)
    (notUsed : index ∉ used) : Fresh bits used (Programs.hashM index label) :=
  .query used _ _ (fun i hi => by rw [consumedIndex_eq hi]; exact notUsed) fun _ => .pure _ _

theorem inIdx_hashM (bits : BitInput) (index : FixedIndex) (label : Block) (S : Set FixedIndex)
    (inside : index ∈ S) : AllQ (InIdx bits S) (Programs.hashM index label) :=
  .query _ _ (fun i hi => by rw [consumedIndex_eq hi]; exact inside) fun _ => .pure _

/-- The mask indices of one element of one switch. -/
def elementSet (switch : ℕ) {count : ℕ} (el : Fin count) : Set FixedIndex :=
  {i | ∃ b : Fin 3, i = maskIndex lane c switch el b}

/-- The mask indices of one switch. -/
def switchSet (switch : ℕ) (count : ℕ) : Set FixedIndex :=
  {i | ∃ (el : Fin count) (b : Fin 3), i = maskIndex lane c switch el b}

/-- The mask indices of one chunk. -/
def maskSet (count : ℕ) (w : ℕ) : Set FixedIndex :=
  {i | ∃ (switch : Fin (2 ^ w)) (el : Fin count) (b : Fin 3), i = maskIndex lane c switch.val el b}

theorem inIdx_element (bits : BitInput) (switch : ℕ) {count : ℕ} (el : Fin count) (label : Block) :
    AllQ (InIdx bits (elementSet lane c switch el))
      (Programs.hashM (scaleIndexOf lane c switch el 0) label >>= fun first =>
        Programs.hashM (scaleIndexOf lane c switch el 1) label >>= fun second =>
          Programs.hashM (scaleIndexOf lane c switch el 2) label >>= fun third =>
            pure (sampleFp first second third)) :=
  AllQ.bind (inIdx_hashM bits _ label (elementSet lane c switch el) ⟨0, rfl⟩) fun _ =>
    AllQ.bind (inIdx_hashM bits _ label (elementSet lane c switch el) ⟨1, rfl⟩) fun _ =>
      AllQ.bind (inIdx_hashM bits _ label (elementSet lane c switch el) ⟨2, rfl⟩) fun _ =>
        .pure _

theorem inIdx_switchMaskM (bits : BitInput) (count : ℕ) (switch : ℕ) (label : Block) :
    AllQ (InIdx bits (switchSet lane c switch count))
      (Programs.switchMaskM count lane c switch label) := by
  unfold Programs.switchMaskM
  exact (AllQ.vector fun el => (inIdx_element lane c bits switch el label).mono
    fun r holds i hi => let ⟨b, same⟩ := holds i hi; ⟨el, b, same⟩).bind fun _ => .pure _

/-- The masks of one switch are fresh. -/
theorem fresh_switchMaskM (bits : BitInput) (count : ℕ) (countLe : count ≤ elementCountX)
    (w : ℕ) (widthLe : w ≤ chunkBits) (switch : Fin (2 ^ w)) (label : Block) :
    Fresh bits ∅ (Programs.switchMaskM count lane c switch.val label) := by
  unfold Programs.switchMaskM
  refine Fresh.bind (S := switchSet lane c switch.val count) ?_ ?_ fun _ => .pure _ _
  · refine Fresh.vector (fun el => elementSet lane c switch.val el)
      (fun el => ?_) (fun el => inIdx_element lane c bits switch.val el label)
      (fun el el' different i ⟨b, hi⟩ ⟨b', hi'⟩ => ?_) ∅ (fun _ _ _ inside => inside)
    · refine Fresh.bind (S := {maskIndex lane c switch.val el 0})
        (fresh_hashM bits _ label ∅ fun h => h) (inIdx_hashM bits _ label _ rfl) fun _ => ?_
      refine Fresh.bind (S := {maskIndex lane c switch.val el 1})
        (fresh_hashM bits _ label _ fun inside => ?_) (inIdx_hashM bits _ label _ rfl) fun _ => ?_
      · rcases inside with inside | inside
        · exact inside
        · exact absurd (maskIndex_injective lane c w widthLe countLe inside).2.2 (by decide)
      · refine Fresh.bind (S := {maskIndex lane c switch.val el 2})
          (fresh_hashM bits _ label _ fun inside => ?_) (inIdx_hashM bits _ label _ rfl)
          fun _ => .pure _ _
        rcases inside with (inside | inside) | inside
        · exact inside
        · exact absurd (maskIndex_injective lane c w widthLe countLe inside).2.2 (by decide)
        · exact absurd (maskIndex_injective lane c w widthLe countLe inside).2.2 (by decide)
    · rw [hi] at hi'
      exact different (maskIndex_injective lane c w widthLe countLe hi').2.1
  · exact AllQ.vector fun el => (inIdx_element lane c bits switch.val el label).mono
      fun r holds i hi => let ⟨b, same⟩ := holds i hi; ⟨el, b, same⟩

theorem inIdx_evalMasksM (bits : BitInput) (count : ℕ) (w : ℕ) (hot : Fin (2 ^ w) → Block)
    (alpha : Fin (2 ^ w)) :
    AllQ (InIdx bits (maskSet lane c count w)) (Programs.evalMasksM count lane c w hot alpha) := by
  unfold Programs.evalMasksM
  exact (AllQ.vector fun switch => AllQ.ite (.pure _)
    ((inIdx_switchMaskM lane c bits count switch.val _).mono fun r holds i hi =>
      let ⟨el, b, same⟩ := holds i hi
      ⟨switch, el, b, same⟩)).bind fun _ => .pure _

/-- The masks of one chunk are fresh. -/
theorem fresh_evalMasksM (bits : BitInput) (count : ℕ) (countLe : count ≤ elementCountX)
    (w : ℕ) (widthLe : w ≤ chunkBits) (hot : Fin (2 ^ w) → Block) (alpha : Fin (2 ^ w)) :
    Fresh bits ∅ (Programs.evalMasksM count lane c w hot alpha) := by
  unfold Programs.evalMasksM
  refine Fresh.bind (S := maskSet lane c count w) ?_ ?_ fun _ => .pure _ _
  · refine Fresh.vector (fun switch => switchSet lane c switch.val count) (fun switch => ?_)
      (fun switch => ?_) (fun switch switch' different i ⟨el, b, hi⟩ ⟨el', b', hi'⟩ => ?_) ∅
      (fun _ _ _ inside => inside)
    · exact Fresh.ite (.pure _ _) (fresh_switchMaskM lane c bits count countLe w widthLe switch _)
    · exact AllQ.ite (.pure _) (inIdx_switchMaskM lane c bits count switch.val _)
    · rw [hi] at hi'
      exact different (maskIndex_injective lane c w widthLe countLe hi').1
  · exact AllQ.vector fun switch => AllQ.ite (.pure _)
      ((inIdx_switchMaskM lane c bits count switch.val _).mono fun r holds i hi =>
        let ⟨el, b, same⟩ := holds i hi
        ⟨switch, el, b, same⟩)

/-- The fold indices of one chunk. -/
def foldSet (value : ℕ) : Set FixedIndex := {i | ∃ half, i = foldIdx lane c value half}

theorem fresh_foldMaskM (bits : BitInput) (value : ℕ) (label : Block) :
    Fresh bits ∅ (Programs.foldMaskM lane c 1 (inactiveEntry value) label) := by
  unfold Programs.foldMaskM
  refine Fresh.bind (S := {foldIdx lane c value false}) (fresh_hashM bits _ _ ∅ fun h => h)
    (inIdx_hashM bits _ _ _ rfl) fun _ => ?_
  refine Fresh.bind (S := {foldIdx lane c value true}) (fresh_hashM bits _ _ _ fun inside => ?_)
    (inIdx_hashM bits _ _ _ rfl) fun _ => .pure _ _
  rcases inside with inside | inside
  · exact inside
  · simp [foldIdx, hotIndexNat] at inside

theorem inIdx_foldMaskM (bits : BitInput) (value : ℕ) (label : Block) :
    AllQ (InIdx bits (foldSet lane c value))
      (Programs.foldMaskM lane c 1 (inactiveEntry value) label) := by
  unfold Programs.foldMaskM
  exact (inIdx_hashM bits _ _ (foldSet lane c value) ⟨false, rfl⟩).bind fun _ =>
    (inIdx_hashM bits _ _ (foldSet lane c value) ⟨true, rfl⟩).bind fun _ => .pure _

/-- **One chunk is fresh.** -/
theorem fresh_chunkProg (bits : BitInput) (count : ℕ) (countLe : count ≤ elementCountX)
    (value : ℕ) (bitLabel join : ℕ → Block) (w : ℕ) (hw : w = 2) (alpha : Fin (2 ^ w))
    (sc : Fin count → BaseField) :
    Fresh bits ∅ (chunkProg lane c count value bitLabel join w alpha sc) := by
  have widthLe : w ≤ chunkBits := by rw [hw]; decide
  unfold chunkProg
  have foldAll : AllQ (InIdx bits (foldSet lane c value))
      (Programs.evalFoldM lane c value bitLabel join w) := by
    subst hw
    rw [evalFoldM_two]
    exact (inIdx_foldMaskM lane c bits value _).bind fun _ => .pure _
  refine Fresh.bind ?_ foldAll fun hot => ?_
  · subst hw
    rw [evalFoldM_two]
    exact Fresh.bind (fresh_foldMaskM lane c bits value _) (inIdx_foldMaskM lane c bits value _)
      fun _ => .pure _ _
  · refine Fresh.bind (S := maskSet lane c count w) ?_ (inIdx_evalMasksM lane c bits count w hot
      alpha) fun _ => .pure _ _
    have base := Fresh.union_disjoint (fresh_evalMasksM lane c bits count countLe w widthLe hot
      alpha) (inIdx_evalMasksM lane c bits count w hot alpha) (U := ∅ ∪ foldSet lane c value)
      fun i ⟨switch, el, b, same⟩ outside => by
        rcases outside with outside | ⟨half, same'⟩
        · exact outside
        · rw [same] at same'
          simp [foldIdx, hotIndexNat, maskIndex, scaleIndexOf, scaleIndexNat] at same'
    exact base.mono fun i member => Or.inr member

end Chunk

/-! ### One lane -/

section Lane

variable (count : ℕ) (lane : Lane) (joins : Vector Block foldStepCount)
  (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
  (labels : Fin coordinateBitCount → Block)

/-- The level-1 label of chunk `c` of the lane. -/
abbrev laneW (c : Fin chunkCount) : Block :=
  chunkW (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c))

/-- The one-hot label of switch `s` of chunk `c` of the lane, along `ans`. -/
abbrev laneHot (ans : (request : Request) → request.Answer) (c : Fin chunkCount)
    (s : Fin (2 ^ chunkWidth c)) : Block :=
  foldLabels (chunkValue word c).toNat (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c))
    (chunkMaterial lane c ans (chunkValue word c).toNat (labelAt (chunkLabels labels c))
      (joinAt (hotSlice joins c))) ⟨s.val, two_lt (chunkWidth_eq_two c) s⟩

theorem mem_queriesAlong_evalLaneM (ans : (request : Request) → request.Answer) (r : Request)
    (member : r ∈ queriesAlong ans (Programs.evalLaneM count lane joins scale word labels)) :
    ∃ c, r ∈ queriesAlong ans (Programs.evalChunkM count lane joins scale word labels c) := by
  unfold Programs.evalLaneM at member
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil] at member
  obtain ⟨c, _, inside⟩ := List.mem_flatMap.mp member
  exact ⟨c, inside⟩

/-- **The questions of one lane.** -/
theorem lane_query (ans : (request : Request) → request.Answer) (r : Request)
    (member : r ∈ queriesAlong ans (Programs.evalLaneM count lane joins scale word labels)) :
    ∃ c : Fin chunkCount,
      (∃ half, r = .fixedForward (foldIdx lane c (chunkValue word c).toNat half)
        (laneW joins labels c)) ∨
      ∃ switch : Fin (2 ^ chunkWidth c), switch ≠ chunkOf word c ∧ ∃ (el : Fin count) (b : Fin 3),
        r = .fixedForward (scaleIndexOf lane c switch.val el b)
          (laneHot lane joins word labels ans c switch) := by
  obtain ⟨c, inside⟩ := mem_queriesAlong_evalLaneM count lane joins scale word labels ans r member
  rw [evalChunkM_eq] at inside
  exact ⟨c, mem_queriesAlong_chunkProg lane c ans count _ _ _ _ (chunkWidth_eq_two c) _ _ r inside⟩

/-- The lane's index set. -/
def laneSet : Set FixedIndex := {i | ∃ c, IndexAt lane c i}

variable [FieldCertificate] in
/-- **One lane is fresh**, and asks at its own indices. -/
theorem lane_fresh (bits : BitInput) (countLe : count ≤ elementCountX) :
    Fresh bits ∅ (Programs.evalLaneM count lane joins scale word labels) := by
  unfold Programs.evalLaneM
  refine Fresh.bind (S := laneSet lane) ?_ ?_ fun _ => .pure _ _
  · refine Fresh.vector (fun c => {i | IndexAt lane c i}) (fun c => ?_) (fun c => ?_)
      (fun c c' different i inside inside' => different (indexAt_unique inside inside').2) ∅
      (fun _ _ _ inside => inside)
    · rw [evalChunkM_eq]
      exact fresh_chunkProg lane c bits count countLe _ _ _ _ (chunkWidth_eq_two c) _ _
    · exact (Kriterion.ArgoMAC.Phase3.Lazy.evalChunkM_allQ lane count joins scale word labels c).mono
        fun r inside => inIdx_of_fixedAt bits inside
  · exact AllQ.vector fun c =>
      (Kriterion.ArgoMAC.Phase3.Lazy.evalChunkM_allQ lane count joins scale word labels c).mono
        fun r inside i hi => ⟨c, inIdx_of_fixedAt bits inside i hi⟩

variable [FieldCertificate] in
theorem allQ_inIdx_lane (bits : BitInput) :
    AllQ (InIdx bits (laneSet lane)) (Programs.evalLaneM count lane joins scale word labels) :=
  (evalLaneM_allQ count lane joins scale word labels).mono fun r inside =>
    inIdx_of_fixedAt bits inside

/-- A mask question of the lane is on its path. -/
theorem mask_mem_lane (ans : (request : Request) → request.Answer) (c : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth c)) (active : switch ≠ chunkOf word c) (el : Fin count)
    (b : Fin 3) :
    .fixedForward (maskIndex lane c switch.val el b)
        (FreeQuery.eval ans (Programs.evalFoldM lane c (chunkValue word c).toNat
          (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)) switch) ∈
      queriesAlong ans (Programs.evalLaneM count lane joins scale word labels) := by
  unfold Programs.evalLaneM
  rw [queriesAlong_bind, queriesAlong_vector, queriesAlong_pure, List.append_nil]
  refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
  unfold Programs.evalChunkM
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_pure, List.append_nil]
  refine List.mem_append_right _ ?_
  rw [queriesAlong_evalMasksM]
  refine List.mem_flatMap.mpr ⟨switch, List.mem_finRange switch, ?_⟩
  rw [if_neg active, queriesAlong_switchMaskM]
  refine List.mem_flatMap.mpr ⟨el, List.mem_finRange el, ?_⟩
  fin_cases b <;> simp

/-- The mask values of a chunk, from the Davies–Meyer values `h`. -/
def maskValuesOf (h : FixedIndex → Block) (c : Fin chunkCount) (alpha : Fin (2 ^ chunkWidth c)) :
    Fin (2 ^ chunkWidth c) → Fin count → BaseField :=
  fun switch el => if switch = alpha then 0 else
    sampleFp (h (maskIndex lane c switch.val el 0)) (h (maskIndex lane c switch.val el 1))
      (h (maskIndex lane c switch.val el 2))

/-- **The lane's value from the Davies–Meyer values of its masks.** -/
def laneValue (h : FixedIndex → Block) : Fin count → BaseField :=
  fun el => ∑ c : Fin chunkCount, Programs.evalScaleOf (chunkWidth c)
    (maskValuesOf count lane h c (chunkOf word c)) (chunkOf word c) (scale c) el

/-- **The value of a lane is `laneValue h`** when every mask question on its path has
Davies–Meyer value `h` of its index. -/
theorem lane_eval_eq (ans : (request : Request) → request.Answer) (h : FixedIndex → Block)
    (dm : ∀ i x, .fixedForward i x ∈ queriesAlong ans
        (Programs.evalLaneM count lane joins scale word labels) →
      (∃ (c : Fin chunkCount) (switch : Fin (2 ^ chunkWidth c)) (el : Fin count) (b : Fin 3),
        i = maskIndex lane c switch.val el b) →
      fwdAns ans i x ^^^ x = h i) :
    FreeQuery.eval ans (Programs.evalLaneM count lane joins scale word labels) =
      laneValue count lane scale word h := by
  funext el
  simp only [Programs.evalLaneM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, laneValue]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Programs.evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  congr 2
  funext switch el'
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_vector, FreeQuery.eval_pure,
    Vector.get_ofFn, maskValuesOf]
  split
  · rfl
  · rename_i active
    simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_vector,
      FreeQuery.eval_pure, Vector.get_ofFn]
    have each : ∀ b : Fin 3, FreeQuery.eval ans (Programs.hashM (scaleIndexOf lane c switch.val el' b)
        (FreeQuery.eval ans (Programs.evalFoldM lane c (chunkValue word c).toNat
          (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)) switch)) =
        h (maskIndex lane c switch.val el' b) := fun b =>
      dm _ _ (mask_mem_lane count lane joins scale word labels ans c switch active el' b)
        ⟨c, switch, el', b, rfl⟩
    rw [each 0, each 1, each 2]

end Lane

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
