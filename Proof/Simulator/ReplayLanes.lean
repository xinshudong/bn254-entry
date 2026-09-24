/-
**The replay, whole lanes.**

* `agree_laneG`: a lane's chunk loop with a general frame and an extra (record, memory)
  invariant (`agree_lane` with `OffChunk` and a record-only invariant is the plain case);
* `LaneCells`: the RAM a lane reads (coordinate, `254` labels, `127` fold joins, the scale joins),
  and `agree_plainChunk`: one plain chunk against `evalChunkM`, from `LaneCells`;
* `agree_plainLane`: a plain lane (`curveX`, `curveY`, `pointY`) against `evalLaneM`;
* `agree_desLane`: lane `pointX` (`designatedLane`, chunk `0` designated) against `evalLaneM`,
  leaving `j*`, `E*`, `κ` and the complete record of the `819` designated inputs.
-/

import Proof.Simulator.ReplayDesChunk

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### The general lane loop -/

/-- The invariant of a lane's chunk loop, with a frame and an extra invariant. -/
def LaneInvG (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory)
    (Frame : Word → Prop) (Extra : Nat → Record → Memory → Prop) (count : Nat)
    (state : Vector (Fin spec.count → BaseField) count × Record) (memory : Memory) : Prop :=
  (∀ e : Fin spec.count, memory.ram (accCell spec e) = fieldWord (acc0 e +
      ∑ chunk : Fin count, state.1[chunk] e)) ∧
    (∀ address, Frame address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ Extra count state.2 memory

/-- **A lane's chunk loop**, general frame and extra invariant. -/
theorem agree_laneG [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (bodies : Nat → Prog)
    (chunkProg : Fin chunkCount → FreeQuery Programs.Spec (Fin spec.count → BaseField))
    (Frame : Word → Prop) (Extra : Nat → Record → Memory → Prop) (start : Memory)
    (record0 : Record) (acc0 : Nat → BaseField)
    (step : ∀ (chunk : Fin chunkCount) (memory : Memory) (record : Record)
      (accNow : Nat → BaseField), Extra chunk.val record memory →
      (∀ e, e < spec.count → memory.ram (accCell spec e) = fieldWord (accNow e)) →
      (∀ address, Frame address → memory.ram address = start.ram address) →
      memory.bits = start.bits →
      Agree (fun (result : (Fin spec.count → BaseField) × Record) after =>
          (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (accNow e + result.1 e)) ∧
          (∀ address, Frame address → after.ram address = memory.ram address) ∧
          after.bits = memory.bits ∧ Extra (chunk.val + 1) result.2 after)
        (rtree (bodies chunk.val) memory) (interceptT bits (chunkProg chunk) record))
    (extraStart : Extra 0 record0 start)
    (cells : ∀ e, e < spec.count → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (fun (result : (Fin spec.count → BaseField) × Record) after =>
        (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, Frame address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ Extra chunkCount result.2 after)
      (rtree (Prog.rep chunkCount bodies) start)
      (interceptT bits (FreeQuery.bind (FreeQuery.vector chunkCount chunkProg) fun perChunk =>
        .pure fun e => ∑ chunk : Fin chunkCount, perChunk.get chunk e) record0) := by
  rw [interceptT_bind]
  have initial : LaneInvG spec acc0 start Frame Extra 0 (#v[], record0) start := by
    refine ⟨fun e => ?_, fun _ _ => rfl, rfl, extraStart⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact cells e e.isLt
  have loop := agree_rep_vector bits bodies (LaneInvG spec acc0 start Frame Extra) chunkCount
    chunkProg (fun chunk values record memory holds => by
      obtain ⟨accs, frame, bitsSame, extraHolds⟩ := holds
      have agree := step chunk memory record
        (fun e => if bound : e < spec.count then acc0 e + ∑ earlier : Fin chunk.val,
          values[earlier] ⟨e, bound⟩ else 0) extraHolds
        (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩) frame bitsSame
      refine agree.mono fun result after post => ?_
      obtain ⟨accsAfter, frameAfter, bitsAfter, extraAfter⟩ := post
      refine ⟨fun e => ?_, fun address off => ?_, bitsAfter.trans bitsSame, extraAfter⟩
      · rw [accsAfter e]
        simp only [dif_pos e.isLt]
        rw [Fin.sum_univ_castSucc]
        try simp only [Fin.val_castSucc, Fin.val_last]
        rw [add_assoc]
        congr 3
        · refine Finset.sum_congr rfl fun earlier _ => ?_
          simp only [Fin.getElem_fin, Fin.val_castSucc, Vector.getElem_push_lt earlier.isLt]
        · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      · rw [frameAfter address off, frame address off]
      ) record0 start initial
  simp only [interceptT]
  have mapped := Agree.map (Post' := fun (result : (Fin spec.count → BaseField) × Record) after =>
      (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, Frame address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ Extra chunkCount result.2 after)
    (fun (state : Vector (Fin spec.count → BaseField) chunkCount × Record) =>
      ((fun e => ∑ chunk : Fin chunkCount, state.1.get chunk e), state.2))
    (fun state after holds => ⟨fun e => by
      rw [holds.1 e]
      simp only [Vector.get_eq_getElem, Fin.getElem_fin], holds.2.1, holds.2.2.1, holds.2.2.2⟩) loop
  exact mapped

/-! ### Addresses outside the replay's work cells -/

/-- An address outside the accumulators, the one-hot labels and `E*`, and the temporaries. -/
def OffWork (address : Word) : Prop :=
  (∀ e, e < 824 → address ≠ word (accBase + e)) ∧ (∀ j, j < 5 → address ≠ word (hotLabelBase + j)) ∧
    ∀ k, k < 16 → address ≠ word (tmpBase + k)

/-- Every address below `accBase` is outside the work cells. -/
theorem offWork_of_lt {value : Nat} (small : value < 2 ^ 46) : OffWork (word value) := by
  refine ⟨fun e bound => ?_, fun j bound => ?_, fun k bound => ?_⟩
  · exact word_ne (by omega) (by unfold accBase; omega) (by unfold accBase; omega)
  · exact word_ne (by omega) (by unfold hotLabelBase; omega) (by unfold hotLabelBase; omega)
  · exact word_ne (by omega) (by unfold tmpBase; omega) (by unfold tmpBase; omega)

omit [FieldCertificate] in
theorem OffWork.offScratch {address : Word} (off : OffWork address) : OffScratch address :=
  ⟨off.2.1, off.2.2⟩

theorem OffWork.offChunk {spec : Replay.LaneSpec} (fits : spec.slot + spec.count ≤ 824)
    {address : Word} (off : OffWork address) : OffChunk spec address := by
  refine ⟨fun e bound => ?_, fun j bound => off.2.1 j (by omega), ?_, ?_⟩
  · have := off.1 (spec.slot + e) (by omega)
    rwa [← Nat.add_assoc] at this
  · exact tmpAlpha_eq ▸ off.2.2 0 (by omega)
  · exact tmpBit0_eq ▸ off.2.2 1 (by omega)

omit [FieldCertificate] in
theorem OffWork.jstar {address : Word} (off : OffWork address) : address ≠ word tmpJStar :=
  off.2.2 6 (by omega)

omit [FieldCertificate] in
theorem OffWork.star {address : Word} (off : OffWork address) : address ≠ word (hotLabelBase + 4) :=
  off.2.1 4 (by omega)

omit [FieldCertificate] in
theorem OffWork.kappa {address : Word} (off : OffWork address) : address ≠ word tmpKappa :=
  off.2.2 5 (by omega)

/-! ### What a lane reads -/

/-- The static facts of a lane description. -/
structure SpecOK (spec : Replay.LaneSpec) : Prop where
  fits : spec.slot + spec.count ≤ 824
  small : spec.count ≤ elementCountX
  labelsLow : spec.labels + 254 < 2 ^ 46
  hotLow : spec.hotRow < 4
  coordLow : spec.coordinate < 2 ^ 46

/-- The RAM a lane reads: its coordinate, its `254` labels, its `127` fold joins, and its scale
joins of every chunk. -/
structure LaneCells (spec : Replay.LaneSpec) (coord : Nat) (labels : Fin coordinateBitCount → Block)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin spec.count → BaseField)
    (memory : Memory) : Prop where
  coordCell : memory.ram (word spec.coordinate) = word coord
  labelCells : ∀ i : Fin coordinateBitCount,
    memory.ram (word (spec.labels + i.val)) = blockWord (labels i)
  hotCells : ∀ c : Fin chunkCount,
    memory.ram (word (hotBase + 127 * spec.hotRow + c.val)) = blockWord (joins.get ⟨c.val, c.isLt⟩)
  scaleCells : ∀ (c : Fin chunkCount) (e : Fin spec.count),
    memory.ram (word (scaleCellBase + 824 * c.val + spec.slot + e.val)) = fieldWord (scale c e)

omit [FieldCertificate] in
theorem scaleAddress_small (spec : Replay.LaneSpec) (fits : spec.slot + spec.count ≤ 824)
    (c : Fin chunkCount) (e : Nat) (bound : e < spec.count) :
    scaleCellBase + 824 * c.val + spec.slot + e < 2 ^ 46 := by
  have chunkBound := c.isLt
  unfold chunkCount at chunkBound
  unfold scaleCellBase fieldBase curveCellCount rowCellCount
  omega

omit [FieldCertificate] in
theorem hotAddress_small (spec : Replay.LaneSpec) (ok : spec.hotRow < 4) (c : Fin chunkCount) :
    hotBase + 127 * spec.hotRow + c.val < 2 ^ 46 := by
  have chunkBound := c.isLt
  unfold chunkCount at chunkBound
  unfold hotBase
  omega

/-- The lane's cells survive every write outside them. -/
theorem LaneCells.transfer {spec : Replay.LaneSpec} (ok : SpecOK spec) {coord : Nat}
    {labels : Fin coordinateBitCount → Block} {joins : Vector Block foldStepCount}
    {scale : Fin chunkCount → Fin spec.count → BaseField} {start memory : Memory}
    (cellsStart : LaneCells spec coord labels joins scale start)
    (frame : ∀ address, OffWork address → memory.ram address = start.ram address) :
    LaneCells spec coord labels joins scale memory where
  coordCell := by rw [frame _ (offWork_of_lt ok.coordLow), cellsStart.coordCell]
  labelCells i := by
    have bound : i.val < 254 := i.isLt
    rw [frame _ (offWork_of_lt (by have := ok.labelsLow; omega)), cellsStart.labelCells i]
  hotCells c := by rw [frame _ (offWork_of_lt (hotAddress_small spec ok.hotLow c)), cellsStart.hotCells c]
  scaleCells c e := by
    rw [frame _ (offWork_of_lt (scaleAddress_small spec ok.fits c e.val e.isLt)),
      cellsStart.scaleCells c e]

/-! ### One chunk from the lane's data -/

omit [FieldCertificate] in
theorem chunkWidth_two (c : Fin chunkCount) : chunkWidth c = 2 := by
  unfold chunkWidth chunkWidthNat
  split <;> rfl

omit [FieldCertificate] in
/-- `evalChunkM` with its switch index read as `chunkOf`. -/
theorem evalChunkM_eq (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (coordBV : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) :
    Programs.evalChunkM count lane joins scale coordBV labels c =
      FreeQuery.bind (Programs.evalFoldM lane c (chunkOf coordBV c).val
          (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)) fun hot =>
        FreeQuery.bind (Programs.evalMasksM count lane c (chunkWidth c) hot (chunkOf coordBV c))
          fun masks => .pure (Programs.evalScaleOf (chunkWidth c) masks (chunkOf coordBV c) (scale c)) := by
  unfold Programs.evalChunkM
  rw [show (chunkValue coordBV c).toNat = (chunkOf coordBV c).val from chunkValue_toNat coordBV c]
  rfl

omit [FieldCertificate] in
theorem chunkOf_value (coordBV : BitVec coordinateBitCount) (c : Fin chunkCount) :
    (chunkOf coordBV c).val = (coordBV.toNat >>> (2 * c.val)) % 4 := by
  show coordBV.toNat >>> (chunkBits * c.val) % 2 ^ chunkWidth c = _
  rw [chunkWidth_two]
  rfl

omit [FieldCertificate] in
theorem labelAt_chunk (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) (k : Nat)
    (small : k < 2) :
    labelAt (chunkLabels labels c) k =
      labels ⟨2 * c.val + k, by have := c.isLt; unfold chunkCount at this; unfold coordinateBitCount; omega⟩ := by
  unfold labelAt
  rw [dif_pos (by rw [chunkWidth_two]; exact small)]
  exact congrArg labels (Fin.ext rfl)

omit [FieldCertificate] in
theorem joinAt_zero (c : Fin chunkCount) (joins : Vector Block foldStepCount) :
    joinAt (hotSlice joins c) 0 = 0 := by
  unfold joinAt
  rw [if_pos rfl]

omit [FieldCertificate] in
theorem joinAt_one (c : Fin chunkCount) (joins : Vector Block foldStepCount) :
    joinAt (hotSlice joins c) 1 = joins.get ⟨c.val, c.isLt⟩ := by
  unfold joinAt
  rw [if_neg (by omega), dif_pos (by rw [chunkWidth_two]; omega)]
  simp only [hotSlice, Vector.get_ofFn]
  congr 1
  apply Fin.ext
  show foldBase c + 0 = c.val
  rw [foldBase_eq]
  unfold chunkBits
  omega

/-- **One plain chunk**, from the lane's cells. -/
theorem agree_plainChunk [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (ok : SpecOK spec) (coordBV : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin spec.count → BaseField)
    (chunk : Fin chunkCount) (memory : Memory) (record : Record) (accNow : Nat → BaseField)
    (lane : LaneCells spec coordBV.toNat labels joins scale memory)
    (cells : ∀ e, e < spec.count → memory.ram (accCell spec e) = fieldWord (accNow e))
    (clean : ∀ (switch : Fin (2 ^ 2)) (e : Fin spec.count) block,
      ¬ IsDesignated bits (scaleIndexOf spec.lane chunk switch.val e block)) :
    Agree (ChunkPost spec accNow memory record)
      (rtree (Replay.chunkBody ordF0 spec false chunk.val) memory)
      (interceptT bits (Programs.evalChunkM spec.count spec.lane joins scale coordBV labels chunk)
        record) := by
  have chunkBound := chunk.isLt
  unfold chunkCount at chunkBound
  have labelSmall : spec.labels + 254 < 2 ^ 46 := ok.labelsLow
  rw [evalChunkM_eq]
  refine agree_chunkBody bits spec ok.fits ok.small chunk (chunkWidth chunk) (chunkWidth_two chunk)
    (chunkOf coordBV chunk) (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk))
    (scale chunk) memory record accNow coordBV.toNat coordBV.isLt _ _ _ (chunkOf_value coordBV chunk)
    (labelAt_chunk labels chunk 0 (by omega)) (labelAt_chunk labels chunk 1 (by omega))
    (joinAt_zero chunk joins) (joinAt_one chunk joins) lane.coordCell ?_ ?_ (lane.hotCells chunk)
    (offWork_of_lt (by omega)).offScratch (offWork_of_lt (by omega)).offScratch
    (offWork_of_lt (hotAddress_small spec ok.hotLow chunk)).offScratch cells
    (lane.scaleCells chunk) (fun e first bound firstBound => ?_) (fun e bound =>
      (offWork_of_lt (scaleAddress_small spec ok.fits chunk e bound)).offScratch) clean
  · exact lane.labelCells ⟨2 * chunk.val + 0, by unfold coordinateBitCount; omega⟩
  · exact lane.labelCells ⟨2 * chunk.val + 1, by unfold coordinateBitCount; omega⟩
  · exact ((offWork_of_lt (scaleAddress_small spec ok.fits chunk e bound)).offChunk ok.fits).1
      first firstBound

omit [FieldCertificate] in
/-- A scale index of another lane, or of another chunk, is never designated. -/
theorem not_designated_of (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    {count : Nat} (element : Fin count) (block : Fin 3)
    (away : lane ≠ .pointX ∨ chunk ≠ chunkZero) :
    ¬ IsDesignated bits (scaleIndexOf lane chunk switch element block) := by
  rintro ⟨digit, collector, block', same⟩
  unfold designatedIndex scaleIndexOf scaleIndexNat at same
  simp only [FixedIndex.scale.injEq] at same
  rcases away with other | other
  · exact other same.1.symm
  · exact other same.2.1.symm

/-! ### A plain lane -/

/-- **A plain lane** (no designated chunk). -/
theorem agree_plainLane [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (ok : SpecOK spec) (coordBV : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin spec.count → BaseField)
    (start : Memory) (record0 : Record) (acc0 : Nat → BaseField)
    (lane : LaneCells spec coordBV.toNat labels joins scale start)
    (cells : ∀ e, e < spec.count → start.ram (accCell spec e) = fieldWord (acc0 e))
    (clean : ∀ (chunk : Fin chunkCount) (switch : Fin (2 ^ 2)) (e : Fin spec.count) block,
      ¬ IsDesignated bits (scaleIndexOf spec.lane chunk switch.val e block)) :
    Agree (fun (result : (Fin spec.count → BaseField) × Record) after =>
        (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, OffChunk spec address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ result.2 = record0)
      (rtree (Replay.lane ordF0 spec) start)
      (interceptT bits (Programs.evalLaneM spec.count spec.lane joins scale coordBV labels)
        record0) := by
  have loop := agree_laneG bits spec (fun chunk => Replay.chunkBody ordF0 spec false chunk)
    (Programs.evalChunkM spec.count spec.lane joins scale coordBV labels) (OffChunk spec)
    (fun _ record _ => record = record0) start record0 acc0
    (fun chunk memory record accNow extra accs frame bitsSame => by
      have agree := agree_plainChunk bits spec ok coordBV labels joins scale chunk memory record
        accNow (lane.transfer ok fun address off => frame address (off.offChunk ok.fits)) accs
        (clean chunk)
      refine agree.mono fun result after post => ?_
      obtain ⟨accsAfter, frameAfter, bitsAfter, recordAfter⟩ := post
      exact ⟨accsAfter, frameAfter, bitsAfter, recordAfter.trans extra⟩)
    rfl cells
  exact loop

/-! ### The designated lane -/

/-- The chunk bodies of `designatedLane`, as one family. -/
def desBodies (chunk : Nat) : Prog :=
  if chunk = 0 then Replay.chunkBody ordF0 Replay.pointXSpec true 0
  else Replay.chunkBody ordF0 Replay.pointXSpec false chunk

theorem rtree_designatedLane (memory : Memory) :
    rtree (Replay.designatedLane ordF0 Replay.pointXSpec) memory =
      rtree (Prog.rep chunkCount desBodies) memory := by
  rw [show chunkCount = 126 + 1 from rfl, tree_rep_front]
  unfold Replay.designatedLane
  rw [rtree_seq]
  have first : desBodies 0 = Replay.chunkBody ordF0 Replay.pointXSpec true 0 := if_pos rfl
  have rest : (fun index => desBodies (index + 1)) =
      fun chunk => Replay.chunkBody ordF0 Replay.pointXSpec false (chunk + 1) := by
    funext index
    exact if_neg (Nat.succ_ne_zero index)
  rw [first, rest]
  rfl

/-- The frame of the designated lane: `OffChunk` without `j*`, `E*`, `κ`. -/
def DesFrame (address : Word) : Prop :=
  OffChunk Replay.pointXSpec address ∧ address ≠ word tmpJStar ∧
    address ≠ word (hotLabelBase + 4) ∧ address ≠ word tmpKappa

/-- What the designated chunk leaves for the rest of the lane. -/
def DesExtra (bits : BitInput) (count : Nat) (record : Record) (memory : Memory) : Prop :=
  1 ≤ count → ∃ star : Block, RecordUpTo bits star pointElementCountX record ∧
    memory.ram (word tmpJStar) = word (designatedSwitch bits).val ∧
    memory.ram (word (hotLabelBase + 4)) = blockWord star ∧
    memory.ram (word tmpKappa) = fieldWord (kappa bits)

omit [FieldCertificate] in
theorem specOK_pointX : SpecOK Replay.pointXSpec where
  fits := by decide
  small := by decide
  labelsLow := by unfold Replay.pointXSpec whiteBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.pointXSpec reqX requestBase; norm_num

theorem offChunk_three (address : Word) (off : address = word tmpJStar ∨
    address = word (hotLabelBase + 4) ∨ address = word tmpKappa) :
    OffChunk Replay.pointXSpec address := by
  have fits : Replay.pointXSpec.slot + Replay.pointXSpec.count ≤ 824 := by decide
  rcases off with rfl | rfl | rfl
  · exact ⟨fun e bound => tmp_ne_acc Replay.pointXSpec fits 6 (by omega) e bound,
      fun j small => (hotLabel_ne_tmp j 6 (by omega) (by omega)).symm,
      tmp_ne 6 0 (by omega) (by omega) (by omega), tmp_ne 6 1 (by omega) (by omega) (by omega)⟩
  · exact ⟨fun e bound => hotLabel_ne_acc Replay.pointXSpec fits 4 (by omega) e bound,
      fun j small => hotLabel_ne 4 j (by omega) (by omega) (by omega),
      hotLabel_ne_tmp 4 0 (by omega) (by omega), hotLabel_ne_tmp 4 1 (by omega) (by omega)⟩
  · exact ⟨fun e bound => tmp_ne_acc Replay.pointXSpec fits 5 (by omega) e bound,
      fun j small => (hotLabel_ne_tmp j 5 (by omega) (by omega)).symm,
      tmp_ne 5 0 (by omega) (by omega) (by omega), tmp_ne 5 1 (by omega) (by omega) (by omega)⟩

/-- **Lane `pointX`**, chunk `0` designated. -/
theorem agree_desLane [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (labels : Fin coordinateBitCount → Block) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin pointElementCountX → BaseField)
    (start : Memory) (record0 : Record) (acc0 : Nat → BaseField)
    (lane : LaneCells Replay.pointXSpec (Pipeline.coordBits bits .x).toNat labels joins scale start)
    (cells : ∀ e, e < pointElementCountX →
      start.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e)) :
    Agree (fun (result : (Fin pointElementCountX → BaseField) × Record) after =>
        (∀ e : Fin pointElementCountX,
          after.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, DesFrame address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ DesExtra bits chunkCount result.2 after)
      (rtree (Replay.designatedLane ordF0 Replay.pointXSpec) start)
      (interceptT bits (Programs.evalLaneM pointElementCountX .pointX joins scale
        (Pipeline.coordBits bits .x) labels) record0) := by
  have ok := specOK_pointX
  have chunkBound : ∀ chunk : Fin chunkCount, chunk.val < 127 := fun chunk => chunk.isLt
  rw [rtree_designatedLane]
  refine agree_laneG bits Replay.pointXSpec desBodies
    (Programs.evalChunkM pointElementCountX .pointX joins scale (Pipeline.coordBits bits .x) labels)
    DesFrame (DesExtra bits) start record0 acc0 ?_ (fun small => absurd small (by omega)) cells
  intro chunk memory record accNow extra accs frame bitsSame
  have laneNow := lane.transfer ok fun address off => frame address
    ⟨off.offChunk ok.fits, off.jstar, off.star, off.kappa⟩
  have labelSmall : Replay.pointXSpec.labels + 254 < 2 ^ 46 := ok.labelsLow
  by_cases zero : chunk.val = 0
  · -- the designated chunk
    have body : desBodies chunk.val = Replay.chunkBody ordF0 Replay.pointXSpec true chunk.val := by
      rw [zero]; exact if_pos rfl
    rw [body, evalChunkM_eq]
    have agree := agree_desChunkBody bits chunk zero (chunkWidth chunk) (chunkWidth_two chunk)
      (chunkOf (Pipeline.coordBits bits .x) chunk) (by
        show (chunkOf (Pipeline.coordBits bits .x) chunkZero).val = _
        rw [show chunkZero = chunk from Fin.ext zero.symm])
      (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk)) (scale chunk) memory
      record accNow (Pipeline.coordBits bits .x).toNat (Pipeline.coordBits bits .x).isLt _ _ _
      (by rw [chunkOf_value, zero, Nat.mul_zero, Nat.shiftRight_zero])
      (labelAt_chunk labels chunk 0 (by omega)) (labelAt_chunk labels chunk 1 (by omega))
      (joinAt_zero chunk joins) (joinAt_one chunk joins) laneNow.coordCell
      (laneNow.labelCells ⟨2 * chunk.val + 0, by have := chunkBound chunk; unfold coordinateBitCount; omega⟩)
      (laneNow.labelCells ⟨2 * chunk.val + 1, by have := chunkBound chunk; unfold coordinateBitCount; omega⟩)
      (laneNow.hotCells chunk)
      (offWork_of_lt (by have := chunkBound chunk; omega)).offScratch
      (offWork_of_lt (by have := chunkBound chunk; omega)).offScratch
      (offWork_of_lt (hotAddress_small _ ok.hotLow chunk)).offScratch accs (laneNow.scaleCells chunk)
      (fun e first bound firstBound =>
        ((offWork_of_lt (scaleAddress_small _ ok.fits chunk e bound)).offChunk ok.fits).1 first
          firstBound)
      (fun e bound => (offWork_of_lt (scaleAddress_small _ ok.fits chunk e bound)).offScratch)
    refine agree.mono fun result after post => ?_
    obtain ⟨star, accsAfter, frameAfter, jstarCell, starCell, kappaCell, bitsAfter, recorded⟩ := post
    exact ⟨accsAfter, fun address off => frameAfter address off.1 off.2.1 off.2.2.1 off.2.2.2,
      bitsAfter, fun _ => ⟨star, recorded, jstarCell, starCell, kappaCell⟩⟩
  · -- a plain chunk of lane `pointX`
    have body : desBodies chunk.val = Replay.chunkBody ordF0 Replay.pointXSpec false chunk.val :=
      if_neg zero
    rw [body]
    have agree := agree_plainChunk bits Replay.pointXSpec ok (Pipeline.coordBits bits .x) labels
      joins scale chunk memory record accNow laneNow accs (fun switch e block =>
        not_designated_of bits .pointX chunk switch.val e block
          (Or.inr fun same => zero (by rw [same]; rfl)))
    refine agree.mono fun result after post => ?_
    obtain ⟨accsAfter, frameAfter, bitsAfter, recordSame⟩ := post
    refine ⟨accsAfter, fun address off => frameAfter address off.1, bitsAfter, fun _ => ?_⟩
    obtain ⟨star, recorded, jstarCell, starCell, kappaCell⟩ := extra (by omega)
    refine ⟨star, by rw [recordSame]; exact recorded, ?_, ?_, ?_⟩
    · rw [frameAfter _ (offChunk_three _ (Or.inl rfl)), jstarCell]
    · rw [frameAfter _ (offChunk_three _ (Or.inr (Or.inl rfl))), starCell]
    · rw [frameAfter _ (offChunk_three _ (Or.inr (Or.inr rfl))), kappaCell]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
