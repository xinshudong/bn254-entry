/-
**Phase 3, P4b — the honest evaluation, chunk 0 of `curveX` first and chunk 0 of `pointX` inside.**

* `evalLaneM_split`: a lane's evaluation is its chunk-0 fold, its chunk-0 masks, then `laneRest`
  (the other 126 chunks and the continuation), which reads the chunk-0 masks only through their
  value.
* `openingQueriesM_split`: the honest evaluation is the `curveX` chunk-0 fold and masks, then
  `curveRest` (the other `curveX` chunks, `curveY`, the hash, the pads), then `pointPart`
  (the `pointX` lane, then `pointY`).
* `pointPart_split`: `pointPart` is the `pointX` chunk-0 fold and masks, then `pointRest`.
* Where the rests ask: `curveRest_plain` (plain queries away from `curveX` chunk 0 and from both
  point lanes) and `pointRest_plain` (plain queries away from `pointX` chunk 0 and the curve lanes).
-/

import Proof.Privacy.Phase3.Lazy.Masks

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### A lane with chunk 0 split off -/

/-- The chunks `1 … 126` of a lane, then the continuation on the lane value, given the chunk-0
masks. -/
def laneRest {β : Type} (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin count → BaseField)
    (k : (Fin count → BaseField) → FreeQuery Programs.Spec β) : FreeQuery Programs.Spec β :=
  FreeQuery.vector 126 (fun index : Fin 126 =>
      Programs.evalChunkM count lane joins scale bits labels index.succ) >>= fun rest =>
    k fun element => ∑ c : Fin chunkCount,
      ((vcons (Programs.evalScaleOf (chunkWidth chunkZero) masks (chunkOf bits chunkZero)
        (scale chunkZero)) rest : Vector (Fin count → BaseField) chunkCount)).get c element

/-- **A lane's evaluation is its chunk-0 fold and masks, then the rest.** -/
theorem evalLaneM_split {β : Type} (count : Nat) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (k : (Fin count → BaseField) → FreeQuery Programs.Spec β) :
    Programs.evalLaneM count lane joins scale bits labels >>= k =
      Programs.evalFoldM lane chunkZero (chunkValue bits chunkZero).toNat
          (labelAt (chunkLabels labels chunkZero)) (joinAt (hotSlice joins chunkZero))
          (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM count lane chunkZero (chunkWidth chunkZero) hot
            (chunkOf bits chunkZero) >>= fun masks =>
          laneRest count lane joins scale bits labels masks k := by
  have split : FreeQuery.vector chunkCount (Programs.evalChunkM count lane joins scale bits labels)
      = Programs.evalChunkM count lane joins scale bits labels chunkZero >>= fun x =>
        FreeQuery.vector 126 (fun index : Fin 126 =>
          Programs.evalChunkM count lane joins scale bits labels index.succ) >>= fun v =>
            (Pure.pure (vcons x v) :
              FreeQuery Programs.Spec (Vector (Fin count → BaseField) chunkCount)) :=
    vector_succ_first 126 (Programs.evalChunkM count lane joins scale bits labels)
  unfold Programs.evalLaneM
  rw [fq_bind_assoc, split, fq_bind_assoc]
  unfold Programs.evalChunkM
  simp only [fq_bind_assoc, fq_pure_bind]
  rfl

/-! ### The honest evaluation -/

variable [FieldCertificate]

/-- After `curveX`: the `curveY` lane, the bridge hash and the pads. -/
def curveTail (table : Public) (bits : BitInput) (mac : InputMac)
    (curveX : Fin curveElementCountX → BaseField) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  Programs.evalLaneM curveElementCountY .curveY table.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
    Programs.askHash (CurveMembership.evaluate table.curve bits.toAffine
        (Pipeline.curveValues curveX curveY)) >>= fun hashed =>
      whitePadsM ⟨hashed.1, hashed.2⟩

/-- After the pads: the `pointX` lane, then the `pointY` lane. -/
def pointPart (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  Programs.evalLaneM pointElementCountX .pointX table.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
    >>= fun pointX =>
  Programs.evalLaneM pointElementCountY .pointY table.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
    >>= fun pointY => Pure.pure (pointX, pointY)

/-- After the `curveX` chunk-0 masks: the other `curveX` chunks, `curveY`, the hash, the pads. -/
def curveRest (table : Public) (bits : BitInput) (mac : InputMac)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin curveElementCountX → BaseField) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  laneRest curveElementCountX .curveX table.curveXHot
    (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) masks (curveTail table bits mac)

/-- **The honest evaluation, split**: the `curveX` chunk-0 fold and masks, then `curveRest`, then
`pointPart`. -/
theorem openingQueriesM_split (table : Public) (bits : BitInput) (mac : InputMac) :
    openingQueriesM table bits mac =
      Programs.evalFoldM .curveX chunkZero (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat
          (labelAt (chunkLabels (Pipeline.macLabels mac .x) chunkZero))
          (joinAt (hotSlice table.curveXHot chunkZero)) (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM curveElementCountX .curveX chunkZero (chunkWidth chunkZero) hot
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
          curveRest table bits mac masks >>= pointPart table bits mac := by
  have shape : openingQueriesM table bits mac =
      Programs.evalLaneM curveElementCountX .curveX table.curveXHot
        (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
          curveTail table bits mac curveX >>= pointPart table bits mac := by
    unfold openingQueriesM curveTail pointPart
    simp only [fq_bind_assoc]
  rw [shape, evalLaneM_split]
  unfold curveRest laneRest
  simp only [fq_bind_assoc]

/-- The rest of the `pointX` lane, then `pointY`. -/
def pointRest (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin pointElementCountX → BaseField) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  laneRest pointElementCountX .pointX table.pointXHot
    (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) masks
    fun pointX =>
      Programs.evalLaneM pointElementCountY .pointY table.pointYHot
          (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
          (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
        >>= fun pointY => Pure.pure (pointX, pointY)

/-- **`pointPart` is the `pointX` chunk-0 fold and masks, then `pointRest`.** -/
theorem pointPart_split (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    pointPart table bits mac pads =
      Programs.evalFoldM .pointX chunkZero (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat
          (labelAt (chunkLabels (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x) chunkZero))
          (joinAt (hotSlice table.pointXHot chunkZero)) (chunkWidth chunkZero) >>= fun hot =>
        Programs.evalMasksM pointElementCountX .pointX chunkZero (chunkWidth chunkZero) hot
            (chunkOf (Pipeline.coordBits bits .x) chunkZero) >>= fun masks =>
          pointRest table bits mac pads masks := by
  unfold pointPart pointRest
  rw [evalLaneM_split]

/-! ### Where the rests ask -/

/-- A designated index is at chunk 0 of `pointX`. -/
theorem designated_indexAt {bits : BitInput} {index : FixedIndex}
    (designated : IsDesignated bits index) : IndexAt .pointX chunkZero index := by
  obtain ⟨digit, collector, block, rfl⟩ := designated
  exact scaleIndexOf_indexAt _ _ _ _ _

/-- An index is at one (lane, chunk) only. -/
theorem indexAt_unique {lane lane' : Lane} {chunk chunk' : Fin chunkCount} {index : FixedIndex}
    (first : IndexAt lane chunk index) (second : IndexAt lane' chunk' index) :
    lane = lane' ∧ chunk = chunk' := by
  cases index with
  | hot l c _ _ _ => exact ⟨first.1.symm.trans second.1, first.2.symm.trans second.2⟩
  | scale l c _ _ _ => exact ⟨first.1.symm.trans second.1, first.2.symm.trans second.2⟩
  | gadget _ _ _ => exact first.elim

/-- The indices the rest of `curveX`, `curveY` and the hash and pads may touch. -/
def CurveRestIndex (index : FixedIndex) : Prop :=
  (∃ c : Fin 126, IndexAt .curveX c.succ index) ∨ ∃ c, IndexAt .curveY c index

/-- The indices the rest of `pointX` and `pointY` may touch. -/
def PointRestIndex (index : FixedIndex) : Prop :=
  (∃ c : Fin 126, IndexAt .pointX c.succ index) ∨ ∃ c, IndexAt .pointY c index

theorem chunk_succ_ne_zero (c : Fin 126) : (c.succ : Fin chunkCount) ≠ chunkZero := by
  intro same
  have := congrArg Fin.val same
  simp [chunkZero] at this

theorem evalLaneM_allQ (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    AllQ (FixedAt fun index => ∃ c, IndexAt lane c index)
      (Programs.evalLaneM count lane joins scale bits labels) :=
  (AllQ.vector fun c => (evalChunkM_allQ lane count joins scale bits labels c).mono
    fun r inside => by
      cases r with
      | fixedForward index _ => exact ⟨c, inside⟩
      | fixedInverse _ _ => exact inside.elim
      | encForward _ _ => exact inside.elim
      | encInverse _ _ => exact inside.elim
      | hash _ => exact inside.elim).bind fun _ => .pure _

/-- The chunks `1 … 126` of a lane ask at their own chunks. -/
theorem laneRest_allQ {β : Type} (P : Request → Prop) (count : Nat) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin count → BaseField)
    (k : (Fin count → BaseField) → FreeQuery Programs.Spec β)
    (chunks : ∀ (c : Fin 126) (r : Request), FixedAt (IndexAt lane c.succ) r → P r)
    (rest : ∀ value, AllQ P (k value)) :
    AllQ P (laneRest count lane joins scale bits labels masks k) :=
  (AllQ.vector fun c => (evalChunkM_allQ lane count joins scale bits labels c.succ).mono
    (chunks c)).bind fun _ => rest _

theorem plain_of_fixedAt {bits : BitInput} {Y : FixedIndex → Prop} {lane : Lane}
    {chunk : Fin chunkCount} (away : ¬ (lane = .pointX ∧ chunk = chunkZero))
    (inside : ∀ index, IndexAt lane chunk index → Y index) (r : Request)
    (fixed : FixedAt (IndexAt lane chunk) r) : Plain bits Y r := by
  cases r with
  | fixedForward index _ =>
      refine ⟨inside index fixed, fun designated => away ?_⟩
      exact (indexAt_unique fixed (designated_indexAt designated))
  | fixedInverse _ _ => exact fixed.elim
  | encForward _ _ => exact fixed.elim
  | encInverse _ _ => exact fixed.elim
  | hash _ => exact fixed.elim

/-- **`curveRest` asks plain queries in `CurveRestIndex`, the hash and the pads.** -/
theorem curveRest_plain (bits : BitInput) (table : Public) (bits' : BitInput) (mac : InputMac)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin curveElementCountX → BaseField) :
    AllQ (Plain bits CurveRestIndex) (curveRest table bits' mac masks) := by
  refine laneRest_allQ _ _ _ _ _ _ _ _ _ (fun c r fixed => plain_of_fixedAt (by simp)
    (fun index inside => Or.inl ⟨c, inside⟩) r fixed) fun curveX => ?_
  refine ((evalLaneM_allQ _ _ _ _ _ _).mono fun r fixed => ?_).bind fun _ =>
    ((askHash_allQ _).mono fun r hashed => ?_).bind fun _ =>
      (whitePadsM_allQ _).mono fun r enc => ?_
  · cases r with
    | fixedForward index _ =>
        obtain ⟨c, inside⟩ := fixed
        exact plain_of_fixedAt (by simp) (fun index inside => Or.inr ⟨c, inside⟩) _ inside
    | fixedInverse _ _ => exact fixed.elim
    | encForward _ _ => exact fixed.elim
    | encInverse _ _ => exact fixed.elim
    | hash _ => exact fixed.elim
  · cases r with
    | hash _ => trivial
    | _ => exact hashed.elim
  · cases r with
    | encForward _ _ => trivial
    | _ => exact enc.elim

/-- **`pointRest` asks plain queries in `PointRestIndex`.** -/
theorem pointRest_plain (bits : BitInput) (table : Public) (bits' : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (masks : Fin (2 ^ chunkWidth chunkZero) → Fin pointElementCountX → BaseField) :
    AllQ (Plain bits PointRestIndex) (pointRest table bits' mac pads masks) := by
  refine laneRest_allQ _ _ _ _ _ _ _ _ _ (fun c r fixed => plain_of_fixedAt
    (fun both => chunk_succ_ne_zero c both.2)
    (fun index inside => Or.inl ⟨c, inside⟩) r fixed) fun pointX => ?_
  refine ((evalLaneM_allQ _ _ _ _ _ _).mono fun r fixed => ?_).bind fun _ => .pure _
  cases r with
  | fixedForward index _ =>
      obtain ⟨c, inside⟩ := fixed
      exact plain_of_fixedAt (by simp) (fun index inside => Or.inr ⟨c, inside⟩) _ inside
  | fixedInverse _ _ => exact fixed.elim
  | encForward _ _ => exact fixed.elim
  | encInverse _ _ => exact fixed.elim
  | hash _ => exact fixed.elim

end

end Kriterion.ArgoMAC.Phase3.Lazy
