/-
**The replay, one chunk**: `chunkPrefix` against the evaluator's fold (`agree_chunkPrefix`).
-/

import Proof.Simulator.ReplayFold

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What the chunk prefix leaves: the four one-hot labels, `α` and its bit `0`. -/
def FoldPost (memory : Memory) (value : Nat) (hot : Fin (2 ^ 2) → Block) (after : Memory) : Prop :=
  (∀ j : Fin (2 ^ 2), after.ram (word (hotLabelBase + j.val)) = blockWord (hot j)) ∧
    after.ram (word tmpAlpha) = word value ∧ after.ram (word tmpBit0) = word (value % 2) ∧
    (∀ address, (∀ j, j < 4 → address ≠ word (hotLabelBase + j)) → address ≠ word tmpAlpha →
      address ≠ word tmpBit0 → after.ram address = memory.ram address) ∧
    after.bits = memory.bits

/-- An address outside the replay's scratch cells. -/
def OffScratch (address : Word) : Prop :=
  (∀ j, j < 5 → address ≠ word (hotLabelBase + j)) ∧ ∀ k, k < 16 → address ≠ word (tmpBase + k)

/-- The fold arm after the fold pair: recover the active entry, store the four labels. -/
theorem agree_foldTail (spec : Replay.LaneSpec) (chunk : Nat) (entry : Nat) (entrySmall : entry < 2)
    (memory : Memory) (L0 L1 J M : Block) (value : Nat) (active : value % 2 = 1 - entry)
    (input : memory.registers rInput = blockWord L0) (mask : memory.registers rC = blockWord M)
    (joinCell : memory.ram (word (hotBase + 127 * spec.hotRow + chunk)) = blockWord J)
    (label1 : memory.ram (word (spec.labels + 2 * chunk + 1)) = blockWord L1) :
    Agree (fun hot after =>
        (∀ j : Fin (2 ^ 2), after.ram (word (hotLabelBase + j.val)) = blockWord (hot j)) ∧
          (∀ address, (∀ j, j < 4 → address ≠ word (hotLabelBase + j)) →
            after.ram address = memory.ram address) ∧ after.bits = memory.bits)
      (rtree (.seq (loadAt rD (hotBase + 127 * spec.hotRow + chunk))
        (.seq (loadAt rE (spec.labels + 2 * chunk + 1))
        (.seq (ar .xor rD rD rE)
        (.seq (ar .xor rD rD rC)
        (.seq (storeAt (hotLabelBase + 2) (if entry = 0 then rC else rD))
        (.seq (storeAt (hotLabelBase + 3) (if entry = 0 then rD else rC))
        (.seq (ar .xor rE rInput (if entry = 0 then rC else rD))
        (.seq (storeAt hotLabelBase rE)
        (.seq (ar .xor rE rInput (if entry = 0 then rD else rC))
          (storeAt (hotLabelBase + 1) rE)))))))))) memory)
      (.pure (foldHot L0 L1 J M (value % 2))) := by
  rw [rtree_loadAt_seq, joinCell, rtree_loadAt_seq]
  simp only [setReg_ram, label1]
  rw [rtree_ar_val _ _ _ _ _ _ (blockWord J) (blockWord L1)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _),
    eval_xor, blockWord_xor,
    rtree_ar_val _ _ _ _ _ _ (blockWord (J ^^^ L1)) (blockWord M) (reg_same _ _ _)
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), mask]),
    eval_xor, blockWord_xor]
  have hl1 := hotLabel_ne 1 2 (by omega) (by omega) (by omega)
  have hl2 := hotLabel_ne 1 3 (by omega) (by omega) (by omega)
  have hl3 := hotLabel_ne 2 3 (by omega) (by omega) (by omega)
  have hl0a : word hotLabelBase ≠ word (hotLabelBase + 1) := hotLabel_ne 0 1 (by omega) (by omega) (by omega)
  have hl0b : word hotLabelBase ≠ word (hotLabelBase + 2) := hotLabel_ne 0 2 (by omega) (by omega) (by omega)
  have hl0c : word hotLabelBase ≠ word (hotLabelBase + 3) := hotLabel_ne 0 3 (by omega) (by omega) (by omega)
  interval_cases entry
  · -- entry 0: `m0 = rC = M`, `m1 = rD`
    have odd : value % 2 = 1 := by omega
    simp only [if_true]
    rw [rtree_storeAt_seq _ _ _ _ (by decide), rtree_storeAt_seq _ _ _ _ (by decide),
      rtree_ar_val _ _ _ _ _ _ (blockWord L0) (blockWord M)
        (by simp only [storeRam_registers, setReg_registers, input]; simp (config := {decide := true}))
        (by simp only [storeRam_registers, setReg_registers, mask]; simp (config := {decide := true})),
      eval_xor, blockWord_xor, rtree_storeAt_seq _ _ _ _ (by decide),
      rtree_ar_val _ _ _ _ _ _ (blockWord L0) (blockWord (J ^^^ L1 ^^^ M))
        (by simp only [storeRam_registers, setReg_registers, input]; simp (config := {decide := true}))
        (by simp only [storeRam_registers, setReg_registers]; simp (config := {decide := true})),
      eval_xor, blockWord_xor, rtree_storeAt _ _ _ (by decide)]
    refine .leaf ⟨fun j => ?_, fun address outside => ?_, by simp only [storeRam_bits, setReg_bits]⟩
    · rw [odd]
      simp only [storeRam_ram, setReg_ram, storeRam_registers, setReg_registers]
      simp (config := {decide := true}) only [mask, reduceIte]
      fin_cases j <;> simp only [foldHot, foldRight, Function.update_apply, Fin.isValue,
        Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, hl1, hl2, hl3, hl0a, hl0b, hl0c,
        hl1.symm, hl2.symm, hl3.symm, hl0a.symm, hl0b.symm, hl0c.symm, if_true, if_false,
        Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte, Fin.mk_zero] <;> rfl
    · simp only [storeRam_ram, setReg_ram]
      rw [Function.update_of_ne (outside 1 (by omega)), Function.update_of_ne (by
          simpa using outside 0 (by omega)), Function.update_of_ne (outside 3 (by omega)),
        Function.update_of_ne (outside 2 (by omega))]
  · -- entry 1: `m0 = rD`, `m1 = rC = M`
    have even : value % 2 = 0 := by omega
    simp only [show (1 : Nat) ≠ 0 by decide, if_false]
    rw [rtree_storeAt_seq _ _ _ _ (by decide), rtree_storeAt_seq _ _ _ _ (by decide),
      rtree_ar_val _ _ _ _ _ _ (blockWord L0) (blockWord (J ^^^ L1 ^^^ M))
        (by simp only [storeRam_registers, setReg_registers, input]; simp (config := {decide := true}))
        (by simp only [storeRam_registers, setReg_registers]; simp (config := {decide := true})),
      eval_xor, blockWord_xor, rtree_storeAt_seq _ _ _ _ (by decide),
      rtree_ar_val _ _ _ _ _ _ (blockWord L0) (blockWord M)
        (by simp only [storeRam_registers, setReg_registers, input]; simp (config := {decide := true}))
        (by simp only [storeRam_registers, setReg_registers, mask]; simp (config := {decide := true})),
      eval_xor, blockWord_xor, rtree_storeAt _ _ _ (by decide)]
    refine .leaf ⟨fun j => ?_, fun address outside => ?_, by simp only [storeRam_bits, setReg_bits]⟩
    · rw [even]
      simp only [storeRam_ram, setReg_ram, storeRam_registers, setReg_registers]
      simp (config := {decide := true}) only [mask, reduceIte]
      fin_cases j <;> simp only [foldHot, foldRight, Function.update_apply, Fin.isValue,
        Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, hl1, hl2, hl3, hl0a, hl0b, hl0c,
        hl1.symm, hl2.symm, hl3.symm, hl0a.symm, hl0b.symm, hl0c.symm, if_true, if_false,
        Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, reduceIte, Fin.mk_zero] <;> rfl
    · simp only [storeRam_ram, setReg_ram]
      rw [Function.update_of_ne (outside 1 (by omega)), Function.update_of_ne (by
          simpa using outside 0 (by omega)), Function.update_of_ne (outside 3 (by omega)),
        Function.update_of_ne (outside 2 (by omega))]

/-- The chunk-prefix memory before the fold arm. -/
theorem tmpAlpha_eq : word tmpAlpha = word (tmpBase + 0) := rfl
theorem tmpBit0_eq : word tmpBit0 = word (tmpBase + 1) := rfl

/-- **The chunk prefix**: `α`, its bit `0`, and the fold. -/
theorem agree_chunkPrefix (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (memory : Memory)
    (coord : Nat) (coordSmall : coord < 2 ^ 254) (L0 L1 J : Block)
    (coordCell : memory.ram (word spec.coordinate) = word coord)
    (label0 : memory.ram (word (spec.labels + 2 * chunk.val)) = blockWord L0)
    (label1 : memory.ram (word (spec.labels + 2 * chunk.val + 1)) = blockWord L1)
    (joinCell : memory.ram (word (hotBase + 127 * spec.hotRow + chunk.val)) = blockWord J)
    (off0 : OffScratch (word (spec.labels + 2 * chunk.val)))
    (off1 : OffScratch (word (spec.labels + 2 * chunk.val + 1)))
    (offJ : OffScratch (word (hotBase + 127 * spec.hotRow + chunk.val))) :
    Agree (FoldPost memory ((coord >>> (2 * chunk.val)) % 4))
      (rtree (Replay.chunkPrefix ordF0 spec chunk.val) memory)
      (FreeQuery.bind (Programs.foldMaskM spec.lane chunk 1 (1 - (coord >>> (2 * chunk.val)) % 4 % 2) L0)
        fun mask => .pure (foldHot L0 L1 J mask ((coord >>> (2 * chunk.val)) % 4 % 2))) := by
  have valueSmall : (coord >>> (2 * chunk.val)) % 4 < 4 := Nat.mod_lt _ (by omega)
  have chunkSmall : 2 * chunk.val < 2 ^ 256 := by have := chunk.isLt; unfold chunkCount at this; omega
  generalize valueDef : (coord >>> (2 * chunk.val)) % 4 = value at valueSmall ⊢
  unfold Replay.chunkPrefix
  rw [rtree_loadAt_seq, coordCell, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word coord) (word (2 * chunk.val))
      (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (Arithmetic.shiftRight.eval (word coord) (word (2 * chunk.val)))
      (word 3) (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _),
    word_chunkValue coord chunk.val (by omega) chunkSmall, valueDef,
    rtree_storeAt_seq _ _ _ _ (by decide), reg_same, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word value) (word 1)
      (by rw [reg_ne _ _ _ _ (by decide), storeRam_registers, reg_ne _ _ _ _ (by decide), reg_same])
      (reg_same _ _ _), word_bitZero value valueSmall,
    rtree_storeAt_seq _ _ _ _ (by decide), reg_same, rtree_loadAt_seq, rtree_ite]
  have alphaBit : word tmpAlpha ≠ word tmpBit0 := tmp_ne 0 1 (by omega) (by omega) (by omega)
  have finish : ∀ (start : Memory) (startRam : start.ram = Function.update (Function.update
      memory.ram (word tmpAlpha) (word value)) (word tmpBit0) (word (value % 2)))
      (startInput : start.registers rInput = blockWord L0) (startBits : start.bits = memory.bits)
      (entry : Nat) (entrySmall : entry < 2) (active : value % 2 = 1 - entry),
      Agree (FoldPost memory value) (rtree (Replay.foldArm ordF0 spec chunk.val entry) start)
        (FreeQuery.bind (Programs.foldMaskM spec.lane chunk 1 entry L0)
          fun mask => .pure (foldHot L0 L1 J mask (value % 2))) := by
    intro start startRam startInput startBits entry entrySmall active
    have startJoin : start.ram (word (hotBase + 127 * spec.hotRow + chunk.val)) = blockWord J := by
      rw [startRam, Function.update_of_ne (tmpBit0_eq ▸ offJ.2 1 (by omega)),
        Function.update_of_ne (tmpAlpha_eq ▸ offJ.2 0 (by omega)), joinCell]
    have startLabel1 : start.ram (word (spec.labels + 2 * chunk.val + 1)) = blockWord L1 := by
      rw [startRam, Function.update_of_ne (tmpBit0_eq ▸ off1.2 1 (by omega)),
        Function.update_of_ne (tmpAlpha_eq ▸ off1.2 0 (by omega)), label1]
    unfold Replay.foldArm
    rw [rtree_seq]
    refine Agree.bindOpt (fun mask after pair => ?_) (agree_foldPair spec chunk entry start L0 startInput)
    obtain ⟨pairRam, pairBits, pairInput, pairMask⟩ := pair
    have tail := agree_foldTail spec chunk.val entry entrySmall after L0 L1 J mask value active
      (pairInput.trans startInput) pairMask (by rw [pairRam, startJoin]) (by rw [pairRam, startLabel1])
    refine tail.mono fun hot final post => ?_
    obtain ⟨hots, frame, bitsFinal⟩ := post
    refine ⟨hots, ?_, ?_, fun address outside notAlpha notBit => ?_, ?_⟩
    · rw [frame (word tmpAlpha) fun j small => (hotLabel_ne_tmp j 0 (by omega) (by omega)).symm,
        pairRam, startRam, Function.update_of_ne alphaBit, Function.update_self]
    · rw [frame (word tmpBit0) fun j small => (hotLabel_ne_tmp j 1 (by omega) (by omega)).symm,
        pairRam, startRam, Function.update_self]
    · rw [frame address outside, pairRam, startRam, Function.update_of_ne notBit,
        Function.update_of_ne notAlpha]
    · rw [bitsFinal, pairBits, startBits]
  split
  · rename_i zero
    have even : value % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one value with even | odd
      · exact even
      · exfalso
        revert zero
        simp only [setReg_registers, storeRam_registers]
        simp (config := {decide := true}) only [reduceIte, odd]
    rw [show 1 - value % 2 = 1 by omega]
    refine finish _ ?_ ?_ ?_ 1 (by omega) (by omega)
    · simp only [setReg_ram, storeRam_ram]
    · simp only [setReg_registers]
      simp (config := {decide := true}) only [reduceIte, setReg_ram, storeRam_ram]
      rw [Function.update_of_ne (show word (spec.labels + 2 * chunk.val) ≠ word tmpBit0 from
          off0.2 1 (by omega)), Function.update_of_ne (show word (spec.labels + 2 * chunk.val) ≠
          word tmpAlpha from off0.2 0 (by omega)), label0]
    · simp only [setReg_bits, storeRam_bits]
  · rename_i nonzero
    have odd : value % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one value with even | odd
      · exfalso
        apply nonzero
        simp only [setReg_registers, storeRam_registers]
        simp (config := {decide := true}) only [reduceIte, even]
      · exact odd
    rw [show 1 - value % 2 = 0 by omega]
    refine finish _ ?_ ?_ ?_ 0 (by omega) (by omega)
    · simp only [setReg_ram, storeRam_ram]
    · simp only [setReg_registers]
      simp (config := {decide := true}) only [reduceIte, setReg_ram, storeRam_ram]
      rw [Function.update_of_ne (show word (spec.labels + 2 * chunk.val) ≠ word tmpBit0 from
          off0.2 1 (by omega)), Function.update_of_ne (show word (spec.labels + 2 * chunk.val) ≠
          word tmpAlpha from off0.2 0 (by omega)), label0]
    · simp only [setReg_bits, storeRam_bits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine