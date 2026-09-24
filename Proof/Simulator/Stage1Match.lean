/-
**The serialized RAM is the wire.**

`serial_wire`: the bits the serializer pushes, read from the RAM stage 1 stores, are the byte bits
of `Wire.encoding.encode` of the drawn source's public value. Both sides are regrouped by
`List.ofFn_add` / `List.ofFn_mul` into the same segments (curve and rows, gadget bytes, the four
fold-join vectors, the chunk words slot by slot) and compared cell by cell.
-/

import Proof.Simulator.Stage1Ram
import Proof.Simulator.Stage1Wire

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### Regrouping flattened lists -/

theorem flatten_ofFn_add {α : Type} {first second : Nat} (lists : Fin (first + second) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun index : Fin first => lists (index.castAdd second)).flatten ++
        (List.ofFn fun index : Fin second => lists (index.natAdd first)).flatten := by
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem flatten_ofFn_mul {α : Type} {outer inner : Nat} (lists : Fin (outer * inner) → List α) :
    (List.ofFn lists).flatten =
      (List.ofFn fun block : Fin outer => (List.ofFn fun index : Fin inner =>
        lists ⟨block.val * inner + index.val, by
          have blockSmall := block.isLt
          have indexSmall := index.isLt
          calc block.val * inner + index.val < (block.val + 1) * inner := by
                rw [Nat.add_mul, Nat.one_mul]; omega
            _ ≤ outer * inner := Nat.mul_le_mul_right _ blockSmall⟩).flatten).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  rfl

/-- The emitted bits of a stored word. -/
theorem bitRun_ofNat (value width : Nat) (small : width ≤ 256) :
    bitRun (BitVec.ofNat 256 value) 0 width = lsbs width value := by
  unfold bitRun lsbs
  refine congrArg List.ofFn (funext fun index => ?_)
  rw [Nat.zero_add, BitVec.getLsbD_ofNat]
  have : index.val < 256 := lt_of_lt_of_le index.isLt small
  simp [this]

/-! ### Reading the drawn source -/

section Match

variable [FieldCertificate]

theorem publicValue_rows (source : Stage1Source) : source.publicValue.rows = source.rows := rfl

theorem publicValue_exception (source : Stage1Source) :
    source.publicValue.exception = source.exception := rfl

theorem drawSource_row (draw : Stage1Draw) (digit : Fin digitCount) (field : Nat)
    (small : field < 11) :
    rowField (drawSource draw).rows[digit.val] field = total 0 draw.1 (3 + 11 * digit.val + field) := by
  simp only [drawSource, sourceOfDraws, Vector.getElem_ofFn]
  interval_cases field <;> rfl

/-- The stored field cell at a position, read as its drawn value. -/
theorem stored_field (memory : Memory) (draw : Stage1Draw) (index : Nat) (bound : index < fieldCellCount)
    (width : Nat) (small : width ≤ 256) :
    bitRun ((storedMemory memory draw).ram (word (fieldBase + index))) 0 width =
      lsbs width (total 0 draw.1 index).val := by
  rw [show fieldBase + index = fieldBase + (⟨index, bound⟩ : Fin fieldCellCount).val from rfl,
    ram_field, bitRun_ofNat _ _ small, total_apply _ _ _ bound]

theorem stored_byte (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < exceptionByteCount) :
    bitRun ((storedMemory memory draw).ram (word (exceptionBase + index))) 0 8 =
      lsbs 8 (BitVec.ofNat 8 (total 0 draw.2.1 index)).toNat := by
  rw [show exceptionBase + index =
      exceptionBase + (⟨index, bound⟩ : Fin exceptionByteCount).val from rfl,
    ram_byte, bitRun_ofNat _ _ (by norm_num), total_apply _ _ _ bound, BitVec.toNat_ofNat,
    lsbs_mod]

theorem stored_hot (memory : Memory) (draw : Stage1Draw) (index : Nat)
    (bound : index < hotBlockCount) :
    bitRun ((storedMemory memory draw).ram (word (hotBase + index))) 0 128 =
      lsbs 128 (BitVec.ofNat 128 (total 0 draw.2.2.1 index)).toNat := by
  rw [show hotBase + index = hotBase + (⟨index, bound⟩ : Fin hotBlockCount).val from rfl,
    ram_hot, bitRun_ofNat _ _ (by norm_num), total_apply _ _ _ bound, BitVec.toNat_ofNat,
    lsbs_mod]

/-! ### The four segments -/

/-- **Curve and rows.** -/
theorem serial_fields (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin (curveCellCount + rowCellCount) =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + index.val))) 0 256).flatten =
      (lsbs 256 (drawSource draw).publicValue.curve.1.val ++
        (lsbs 256 (drawSource draw).publicValue.curve.2.1.val ++
          lsbs 256 (drawSource draw).publicValue.curve.2.2.val)) ++
      (List.ofFn fun digit : Fin digitCount =>
        (List.ofFn fun index : Fin 11 =>
          lsbs 256 (rowField (drawSource draw).publicValue.rows[digit.val] index.val).val).flatten).flatten := by
  have cellCount := fieldCellCount_eq
  rw [flatten_ofFn_add]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · show (List.ofFn fun index : Fin 3 =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + index.val))) 0 256).flatten = _
    simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
      Fin.val_zero, Fin.val_succ]
    rw [show fieldBase + 0 = fieldBase + 0 from rfl, stored_field memory draw 0 (by omega) 256 le_rfl,
      stored_field memory draw (0 + 1) (by omega) 256 le_rfl,
      stored_field memory draw (0 + 1 + 1) (by omega) 256 le_rfl]
    rfl
  · show (List.ofFn fun index : Fin (digitCount * 11) =>
        bitRun ((storedMemory memory draw).ram (word (fieldBase + (3 + index.val)))) 0 256).flatten = _
    rw [flatten_ofFn_mul]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
    refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
    have digitSmall : digit.val < 91 := digit.isLt
    have indexSmall := index.isLt
    simp only [Fin.val_mk]
    rw [stored_field memory draw _ (by omega) 256 le_rfl, publicValue_rows,
      drawSource_row draw digit index.val indexSmall,
      show 3 + (digit.val * 11 + index.val) = 3 + 11 * digit.val + index.val by ring]

/-- **The gadget bytes.** -/
theorem serial_bytes (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin exceptionByteCount =>
        bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 8).flatten =
      (List.ofFn fun digit : Fin digitCount =>
        (List.ofFn fun index : Fin 6 =>
          lsbs 8 (drawSource draw).publicValue.exception[digit.val][index.val].toNat).flatten).flatten := by
  show (List.ofFn fun index : Fin (digitCount * 6) =>
      bitRun ((storedMemory memory draw).ram (word (exceptionBase + index.val))) 0 8).flatten = _
  rw [flatten_ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun digit => ?_))
  refine congrArg List.flatten (congrArg List.ofFn (funext fun index => ?_))
  have digitSmall : digit.val < 91 := digit.isLt
  have indexSmall := index.isLt
  simp only [Fin.val_mk]
  rw [stored_byte memory draw _ (by unfold exceptionByteCount; omega), publicValue_exception]
  simp only [drawSource, sourceOfDraws, Vector.getElem_ofFn]
  rw [show digit.val * 6 + index.val = 6 * digit.val + index.val by ring]

/-- **The fold joins.** -/
theorem serial_hot (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin hotBlockCount =>
        bitRun ((storedMemory memory draw).ram (word (hotBase + index.val))) 0 128).flatten =
      (List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.curveXHot[chunk.val].toNat).flatten ++
        ((List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.curveYHot[chunk.val].toNat).flatten ++
        ((List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.pointXHot[chunk.val].toNat).flatten ++
        (List.ofFn fun chunk : Fin foldStepCount =>
          lsbs 128 (drawSource draw).publicValue.pointYHot[chunk.val].toNat).flatten)) := by
  show (List.ofFn fun index : Fin (foldStepCount + (foldStepCount + (foldStepCount + foldStepCount))) =>
      bitRun ((storedMemory memory draw).ram (word (hotBase + index.val))) 0 128).flatten = _
  rw [flatten_ofFn_add, flatten_ofFn_add, flatten_ofFn_add]
  have lane : ∀ (offset : Nat) (small : offset ≤ 381) (vector : Vector Block foldStepCount)
      (position : Fin foldStepCount → Nat),
      (∀ chunk : Fin foldStepCount, position chunk = offset + chunk.val) →
      (∀ chunk : Fin foldStepCount,
        vector[chunk.val] = BitVec.ofNat 128 (total 0 draw.2.2.1 (offset + chunk.val))) →
      (List.ofFn fun chunk : Fin foldStepCount =>
          bitRun ((storedMemory memory draw).ram (word (hotBase + position chunk))) 0 128).flatten =
        (List.ofFn fun chunk : Fin foldStepCount => lsbs 128 vector[chunk.val].toNat).flatten := by
    intro offset small vector position located read
    refine congrArg List.flatten (congrArg List.ofFn (funext fun chunk => ?_))
    have chunkSmall : chunk.val < 127 := chunk.isLt
    rw [located chunk, stored_hot memory draw _ (by unfold hotBlockCount; omega), read chunk]
  refine congrArg₂ (· ++ ·) (lane 0 (by omega) _ _
      (fun chunk => by simp [Fin.castAdd, Fin.castLE]) (fun chunk => ?_))
    (congrArg₂ (· ++ ·) (lane 127 (by omega) _ _
      (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount])
      (fun chunk => ?_)) (congrArg₂ (· ++ ·) (lane 254 (by omega) _ _
        (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount]; omega)
        (fun chunk => ?_))
        (lane 381 (by omega) _ _
          (fun chunk => by simp [Fin.castAdd, Fin.castLE, Fin.natAdd, foldStepCount]; omega)
          (fun chunk => ?_))))
  all_goals
    simp only [drawSource, sourceOfDraws, Stage1Source.publicValue, Vector.getElem_ofFn, Nat.zero_add]

theorem publicValue_scale (source : Stage1Source) (chunk : Fin chunkCount) :
    source.publicValue.scale[chunk.val] = pack (source.joins chunk) := by
  simp [Stage1Source.publicValue]

/-- **The chunk words.** -/
theorem serial_scale (memory : Memory) (draw : Stage1Draw) :
    (List.ofFn fun index : Fin scaleCellCount =>
        bitRun ((storedMemory memory draw).ram
          (word (fieldBase + (curveCellCount + rowCellCount) + index.val))) 0 254).flatten =
      (List.ofFn fun chunk : Fin chunkCount =>
          lsbs (8 * chunkJoinBytes) (drawSource draw).publicValue.scale[chunk.val].toNat).flatten := by
  show (List.ofFn fun index : Fin (chunkCount * elementCount) =>
      bitRun ((storedMemory memory draw).ram
        (word (fieldBase + (curveCellCount + rowCellCount) + index.val))) 0 254).flatten = _
  rw [flatten_ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun chunk => ?_))
  rw [publicValue_scale, pack_bits]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun slot => ?_))
  have chunkSmall : chunk.val < 127 := chunk.isLt
  have slotSmall : slot.val < 824 := slot.isLt
  have cellCount := fieldCellCount_eq
  simp only [Fin.val_mk]
  rw [Nat.add_assoc, stored_field memory draw _ (by unfold curveCellCount rowCellCount elementCount; omega)
    254 (by norm_num)]
  show lsbs 254 _ = lsbs 254 (total 0 draw.1 (1004 + 824 * chunk.val + slot.val)).val
  rw [show curveCellCount + rowCellCount + (chunk.val * elementCount + slot.val) =
    1004 + 824 * chunk.val + slot.val by unfold curveCellCount rowCellCount elementCount; ring]

/-- **The serialized RAM is the wire.** -/
theorem serial_wire (memory : Memory) (draw : Stage1Draw) :
    serialBits (storedMemory memory draw).ram =
      byteBits (Wire.encoding.encode (drawSource draw).publicValue) := by
  rw [Wire.wire_bits]
  unfold serialBits
  rw [serial_fields, serial_bytes, serial_hot, serial_scale]
  simp only [List.append_assoc]

end Match

end

end Kriterion.ArgoMAC.PlanB.SimMachine
