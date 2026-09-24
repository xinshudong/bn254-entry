/-
**The replay's inputs and pieces, for the whole `Replay.program`.**

* `ReplayStart`: what the replay reads from the memory the prefix leaves (request, curve constants,
  selected labels, fold joins, scale joins), in terms of a `Stage1Source` and the label vector;
* `OffReplay`: the cells the replay never writes (outside the accumulators, the one-hot labels and
  `E*`, the temporaries, the whitened labels);
* `rtree_initAcc`: the accumulator clear;
* `laneCells_*`: each lane's `LaneCells` from `ReplayStart` (the point lanes' labels from the
  whitening);
* `bridge_value`: the bridge value of `CurveMembership.evaluate` in the machine's order;
* `replay_treeOps`: the replay is a tree block (no coin, no lookup, no program).
-/

import Proof.Simulator.ReplayLanes
import Proof.Simulator.ReplayWhitenAll

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Cells the replay never writes -/

/-- Outside the work cells and the whitened labels. -/
def OffReplay (address : Word) : Prop :=
  OffWork address ∧ ∀ i, i < 508 → address ≠ word (whiteBase + i)

/-- Every address below `whiteBase` is never written by the replay. -/
theorem offReplay_of_lt {value : Nat} (small : value < 2 ^ 45) : OffReplay (word value) :=
  ⟨offWork_of_lt (by omega), fun i bound =>
    word_ne (by omega) (by unfold whiteBase; omega) (by unfold whiteBase; omega)⟩

/-! ### What the replay reads -/

/-- **The replay's start memory**, read through a source and the selected labels. -/
structure ReplayStart (source : Stage1Source) (input : AffineInput) (labels : LamportSignature)
    (memory : Memory) : Prop where
  reqXCell : memory.ram (word reqX) = fieldWord input.x
  reqYCell : memory.ram (word reqY) = fieldWord input.y
  curve0 : memory.ram (word fieldBase) = fieldWord source.curve.1
  curve1 : memory.ram (word (fieldBase + 1)) = fieldWord source.curve.2.1
  curve2 : memory.ram (word (fieldBase + 2)) = fieldWord source.curve.2.2
  labelCells : ∀ (i : Nat) (bound : i < 508),
    memory.ram (word (labelBase + i)) = blockWord (labels[i]'bound)
  hotX : ∀ c : Fin chunkCount,
    memory.ram (word (hotBase + 127 * 0 + c.val)) = blockWord (source.curveXHot.get ⟨c.val, c.isLt⟩)
  hotY : ∀ c : Fin chunkCount,
    memory.ram (word (hotBase + 127 * 1 + c.val)) = blockWord (source.curveYHot.get ⟨c.val, c.isLt⟩)
  hotPX : ∀ c : Fin chunkCount,
    memory.ram (word (hotBase + 127 * 2 + c.val)) = blockWord (source.pointXHot.get ⟨c.val, c.isLt⟩)
  hotPY : ∀ c : Fin chunkCount,
    memory.ram (word (hotBase + 127 * 3 + c.val)) = blockWord (source.pointYHot.get ⟨c.val, c.isLt⟩)
  scaleCells : ∀ (c : Fin chunkCount) (slot : Fin elementCount),
    memory.ram (word (scaleCellBase + 824 * c.val + slot.val)) = fieldWord (source.joins c slot)

/-! ### The accumulator clear -/

theorem fieldWord_zero : fieldWord (0 : BaseField) = 0 := by
  unfold fieldWord
  rw [ZMod.val_zero]
  rfl

theorem rtree_initStores (memory : Memory) (zero : memory.registers rA = 0) :
    ∀ count, count ≤ 824 → ∃ after,
      rtree (Prog.rep count fun index => storeAt (accBase + index) rA) memory = .pure (some after) ∧
      (∀ e, e < count → after.ram (word (accBase + e)) = fieldWord 0) ∧
      (∀ address, (∀ e, e < count → address ≠ word (accBase + e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits ∧ after.registers rA = 0
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, fun e bound => absurd bound (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, zero⟩
  | count + 1, bound => by
      obtain ⟨middle, run, cells, frame, bitsSame, regA⟩ :=
        rtree_initStores memory zero count (by omega)
      refine ⟨storeRam (setReg middle rAddr (word (accBase + count))) (word (accBase + count))
        (middle.registers rA), ?_, fun e small => ?_, fun address outside => ?_, ?_, ?_⟩
      · rw [Prog.rep, rtree_seq, run, bindOpt_pure, rtree_storeAt _ _ _ (by decide)]
      · rw [storeRam_ram]
        by_cases last : e = count
        · subst last
          rw [Function.update_self, regA, fieldWord_zero]
        · rw [Function.update_of_ne (word_ne (by unfold accBase; omega) (by unfold accBase; omega)
            (by omega))]
          simp only [setReg_ram]
          exact cells e (by omega)
      · rw [storeRam_ram, Function.update_of_ne (outside count (by omega))]
        simp only [setReg_ram]
        exact frame address fun e small => outside e (by omega)
      · simp only [storeRam_bits, setReg_bits]
        exact bitsSame
      · simp only [storeRam_registers, setReg_registers]
        simp (config := {decide := true}) only [reduceIte]
        exact regA

/-- **The accumulator clear.** -/
theorem rtree_initAcc (memory : Memory) : ∃ after,
    rtree Replay.initAcc memory = .pure (some after) ∧
      (∀ e, e < 824 → after.ram (word (accBase + e)) = fieldWord 0) ∧
      (∀ address, (∀ e, e < 824 → address ≠ word (accBase + e)) →
        after.ram address = memory.ram address) ∧
      after.bits = memory.bits := by
  unfold Replay.initAcc
  rw [rtree_cst_seq]
  obtain ⟨after, run, cells, frame, bitsSame, _⟩ :=
    rtree_initStores (setReg memory rA (word 0)) (by rw [reg_same]; rfl) 824 le_rfl
  exact ⟨after, run, cells, fun address outside => by rw [frame address outside]; rfl,
    by rw [bitsSame]; rfl⟩

/-! ### The lanes' cells -/

omit [FieldCertificate] in
theorem unpack_scale (source : Stage1Source) (c : Fin chunkCount) :
    unpack (source.publicValue.scale.get c) = source.joins c := by
  simp only [Stage1Source.publicValue, Vector.get_ofFn, unpack_pack_eq]

omit [FieldCertificate] in
theorem coordBits_x (input : AffineInput) :
    (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat = input.x.val :=
  coordinateBitsToNat input.x

omit [FieldCertificate] in
theorem coordBits_y (input : AffineInput) :
    (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat = input.y.val :=
  coordinateBitsToNat input.y

omit [FieldCertificate] in
theorem restore_x (input : AffineInput) (labels : LamportSignature) (i : Fin coordinateBitCount) :
    Pipeline.macLabels (Lamport.restore input labels).inputMac .x i =
      labels[i.val]'(by have := i.isLt; unfold coordinateBitCount at this; omega) := by
  simp only [Pipeline.macLabels, Lamport.restore, Vector.get_ofFn]

omit [FieldCertificate] in
theorem restore_y (input : AffineInput) (labels : LamportSignature) (i : Fin coordinateBitCount) :
    Pipeline.macLabels (Lamport.restore input labels).inputMac .y i =
      labels[254 + i.val]'(by have := i.isLt; unfold coordinateBitCount at this; omega) := by
  simp only [Pipeline.macLabels, Lamport.restore, Vector.get_ofFn]

omit [FieldCertificate] in
theorem readCurveY_eq (values : Fin elementCount → BaseField) (e : Fin curveElementCountY) :
    Pipeline.readCurveY values e =
      values ⟨822 + e.val, by have := e.isLt; unfold curveElementCountY at this; unfold elementCount; omega⟩ := by
  unfold Pipeline.readCurveY Pipeline.yCurvePart Pipeline.yPart
  congr 1
  apply Fin.ext
  show elementCountX + (pointElementCountY + e.val) = 822 + e.val
  unfold elementCountX pointElementCountY
  omega

theorem reqX_small : reqX < 2 ^ 45 := by unfold reqX requestBase; norm_num
theorem reqY_small : reqY < 2 ^ 45 := by unfold reqY requestBase; norm_num

theorem hot_small (row : Nat) (small : row < 4) (c : Fin chunkCount) :
    hotBase + 127 * row + c.val < 2 ^ 45 := by
  have := c.isLt
  unfold chunkCount at this
  unfold hotBase
  omega

theorem scale_small (c : Fin chunkCount) (slot : Nat) (small : slot < 824) :
    scaleCellBase + 824 * c.val + slot < 2 ^ 45 := by
  have := c.isLt
  unfold chunkCount at this
  unfold scaleCellBase fieldBase curveCellCount rowCellCount
  omega

theorem label_small (i : Nat) (small : i < 508) : labelBase + i < 2 ^ 45 := by
  unfold labelBase
  omega

omit [FieldCertificate] in
theorem specOK_curveX : SpecOK Replay.curveXSpec where
  fits := by decide
  small := by decide
  labelsLow := by unfold Replay.curveXSpec labelBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.curveXSpec reqX requestBase; norm_num

omit [FieldCertificate] in
theorem specOK_curveY : SpecOK Replay.curveYSpec where
  fits := by decide
  small := by decide
  labelsLow := by unfold Replay.curveYSpec labelBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.curveYSpec reqY requestBase; norm_num

omit [FieldCertificate] in
theorem specOK_pointY : SpecOK Replay.pointYSpec where
  fits := by decide
  small := by decide
  labelsLow := by unfold Replay.pointYSpec whiteBase; norm_num
  hotLow := by decide
  coordLow := by unfold Replay.pointYSpec reqY requestBase; norm_num

section Lanes

variable {source : Stage1Source} {input : AffineInput} {labels : LamportSignature}
  {start memory : Memory}

theorem laneCells_curveX (cells : ReplayStart source input labels start)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address) :
    LaneCells Replay.curveXSpec (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat
      (Pipeline.macLabels (Lamport.restore input labels).inputMac .x) source.publicValue.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqX) = _
    rw [frame (word reqX) (offReplay_of_lt reqX_small), cells.reqXCell, coordBits_x]
    rfl
  labelCells i := by
    have small : i.val < 254 := i.isLt
    show memory.ram (word (labelBase + i.val)) = _
    rw [frame (word (labelBase + i.val)) (offReplay_of_lt (label_small i.val (by omega))),
      cells.labelCells i.val (by omega),
      restore_x]
  hotCells c := by
    show memory.ram (word (hotBase + 127 * 0 + c.val)) = _
    rw [frame (word (hotBase + 127 * 0 + c.val)) (offReplay_of_lt (hot_small 0 (by omega) c)),
      cells.hotX c]
    rfl
  scaleCells c e := by
    have small : e.val < 3 := e.isLt
    show memory.ram (word (scaleCellBase + 824 * c.val + 455 + e.val)) = _
    rw [frame (word (scaleCellBase + 824 * c.val + 455 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (455 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + 824 * c.val), cells.scaleCells c ⟨455 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rfl

theorem laneCells_curveY (cells : ReplayStart source input labels start)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address) :
    LaneCells Replay.curveYSpec (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat
      (Pipeline.macLabels (Lamport.restore input labels).inputMac .y) source.publicValue.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqY) = _
    rw [frame (word reqY) (offReplay_of_lt reqY_small), cells.reqYCell, coordBits_y]
    rfl
  labelCells i := by
    have small : i.val < 254 := i.isLt
    show memory.ram (word (labelBase + 254 + i.val)) = _
    rw [frame (word (labelBase + 254 + i.val))
        (offReplay_of_lt (by unfold labelBase; omega)),
      Nat.add_assoc, cells.labelCells (254 + i.val) (by omega), restore_y]
  hotCells c := by
    show memory.ram (word (hotBase + 127 * 1 + c.val)) = _
    rw [frame (word (hotBase + 127 * 1 + c.val)) (offReplay_of_lt (hot_small 1 (by omega) c)),
      cells.hotY c]
    rfl
  scaleCells c e := by
    have small : e.val < 2 := e.isLt
    show memory.ram (word (scaleCellBase + 824 * c.val + 822 + e.val)) = _
    rw [frame (word (scaleCellBase + 824 * c.val + 822 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (822 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + 824 * c.val), cells.scaleCells c ⟨822 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rw [readCurveY_eq (source.joins c) e]

/-- The point lanes read the whitened labels. -/
theorem laneCells_pointX (cells : ReplayStart source input labels start) (white : InputMac)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address)
    (whites : ∀ i : Fin coordinateBitCount,
      memory.ram (word (whiteBase + i.val)) = blockWord (white.x.get i)) :
    LaneCells Replay.pointXSpec (Pipeline.coordBits (BitInput.ofAffine input) .x).toNat
      (Pipeline.macLabels white .x) source.publicValue.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqX) = _
    rw [frame (word reqX) (offReplay_of_lt reqX_small), cells.reqXCell, coordBits_x]
    rfl
  labelCells i := whites i
  hotCells c := by
    show memory.ram (word (hotBase + 127 * 2 + c.val)) = _
    rw [frame (word (hotBase + 127 * 2 + c.val)) (offReplay_of_lt (hot_small 2 (by omega) c)),
      cells.hotPX c]
    rfl
  scaleCells c e := by
    have small : e.val < 455 := e.isLt
    show memory.ram (word (scaleCellBase + 824 * c.val + 0 + e.val)) = _
    rw [frame (word (scaleCellBase + 824 * c.val + 0 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (0 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + 824 * c.val), cells.scaleCells c ⟨0 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    congr 1
    exact congrArg (source.joins c) (Fin.ext (Nat.zero_add _))

theorem laneCells_pointY (cells : ReplayStart source input labels start) (white : InputMac)
    (frame : ∀ address, OffReplay address → memory.ram address = start.ram address)
    (whites : ∀ i : Fin coordinateBitCount,
      memory.ram (word (whiteBase + 254 + i.val)) = blockWord (white.y.get i)) :
    LaneCells Replay.pointYSpec (Pipeline.coordBits (BitInput.ofAffine input) .y).toNat
      (Pipeline.macLabels white .y) source.publicValue.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (source.publicValue.scale.get chunk))) memory where
  coordCell := by
    show memory.ram (word reqY) = _
    rw [frame (word reqY) (offReplay_of_lt reqY_small), cells.reqYCell, coordBits_y]
    rfl
  labelCells i := whites i
  hotCells c := by
    show memory.ram (word (hotBase + 127 * 3 + c.val)) = _
    rw [frame (word (hotBase + 127 * 3 + c.val)) (offReplay_of_lt (hot_small 3 (by omega) c)),
      cells.hotPY c]
    rfl
  scaleCells c e := by
    have small : e.val < 364 := e.isLt
    show memory.ram (word (scaleCellBase + 824 * c.val + 458 + e.val)) = _
    rw [frame (word (scaleCellBase + 824 * c.val + 458 + e.val))
        (offReplay_of_lt (by rw [Nat.add_assoc]; exact scale_small c (458 + e.val) (by omega))),
      Nat.add_assoc (scaleCellBase + 824 * c.val), cells.scaleCells c ⟨458 + e.val, by
        unfold elementCount; omega⟩]
    simp only [unpack_scale]
    rfl

end Lanes

/-! ### The bridge value -/

/-- The bridge value in the machine's order. -/
theorem bridge_value (table : CurveMembership.Table) (input : AffineInput)
    (curveX : Fin curveElementCountX → BaseField) (curveY : Fin curveElementCountY → BaseField) :
    CurveMembership.evaluate table (BitInput.ofAffine input).toAffine
        (Pipeline.curveValues curveX curveY) =
      table.1 + table.2.1 * input.x ^ 3 + table.2.2 * input.y ^ 2 +
        curveX ⟨0, by decide⟩ * input.x ^ 2 + curveY ⟨0, by decide⟩ * input.y +
        curveX ⟨1, by decide⟩ * input.x + curveY ⟨1, by decide⟩ + curveX ⟨2, by decide⟩ := by
  rw [BitInput.toAffineOfAffine]
  rfl

/-! ### The replay is a tree block -/

section Ops

variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

omit [FieldCertificate] in
theorem tree_element (spec : Replay.LaneSpec) (chunk switch index : Nat) :
    (Replay.element ordF spec chunk switch index).OpsSatisfy TreeOp := by
  unfold Replay.element
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial,
    ⟨trivial, trivial⟩⟩

omit [FieldCertificate] in
theorem tree_guarded (spec : Replay.LaneSpec) (chunk switch index : Nat) :
    (Replay.guardedElement ordF spec chunk switch index).OpsSatisfy TreeOp := by
  unfold Replay.guardedElement
  split
  · exact ⟨⟨trivial, trivial⟩, trivial, trivial, tree_element ordF spec chunk switch index, trivial⟩
  · exact tree_element ordF spec chunk switch index

omit [FieldCertificate] in
theorem tree_chunkBody (spec : Replay.LaneSpec) (designated : Bool) (chunk : Nat) :
    (Replay.chunkBody ordF spec designated chunk).OpsSatisfy TreeOp := by
  unfold Replay.chunkBody
  have foldArm (entry : Nat) : (Replay.foldArm ordF spec chunk entry).OpsSatisfy TreeOp := by
    unfold Replay.foldArm Replay.foldPair
    exact ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩,
      ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩,
      ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩
  refine ⟨?_, ?_, opsSatisfy_rep _ _ fun switch _ => ?_, ⟨trivial, trivial⟩,
    opsSatisfy_rep _ _ fun _ _ => ?_⟩
  · unfold Replay.chunkPrefix
    exact ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial,
      trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, foldArm 0, foldArm 1⟩
  · split
    · unfold Replay.designatedPrefix
      exact ⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial, trivial,
        ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩⟩
    · trivial
  · unfold Replay.switchStep Replay.switchBody
    refine ⟨⟨trivial, trivial⟩, trivial, trivial, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial,
      trivial, ?_⟩, trivial⟩
    unfold Replay.switchElements
    split
    · exact opsSatisfy_rep _ _ fun digit _ => by
        unfold Replay.designatedDigit
        exact ⟨tree_element ordF spec chunk switch _, tree_guarded ordF spec chunk switch _,
          tree_element ordF spec chunk switch _, tree_guarded ordF spec chunk switch _,
          tree_guarded ordF spec chunk switch _⟩
    · exact opsSatisfy_rep _ _ fun _ _ => tree_element ordF spec chunk switch _
  · unfold Replay.joinTerm
    exact ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

omit [FieldCertificate] in
/-- **The replay is a tree block.** -/
theorem replay_treeOps : (Replay.program ordF ordE).OpsSatisfy TreeOp := by
  unfold Replay.program
  refine ⟨?_, opsSatisfy_rep _ _ fun _ _ => tree_chunkBody ordF _ _ _,
    opsSatisfy_rep _ _ fun _ _ => tree_chunkBody ordF _ _ _, ?_, ?_,
    ⟨tree_chunkBody ordF _ _ _, opsSatisfy_rep _ _ fun _ _ => tree_chunkBody ordF _ _ _⟩,
    opsSatisfy_rep _ _ fun _ _ => tree_chunkBody ordF _ _ _⟩
  · unfold Replay.initAcc
    exact ⟨trivial, opsSatisfy_rep _ _ fun _ _ => ⟨trivial, trivial⟩⟩
  · unfold Replay.bridge
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩,
      trivial, trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  · unfold Replay.whiten
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, opsSatisfy_rep _ _ fun _ _ => by
      unfold Replay.whitenOne
      exact ⟨trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩⟩

end Ops

end

end Kriterion.ArgoMAC.PlanB.SimMachine
