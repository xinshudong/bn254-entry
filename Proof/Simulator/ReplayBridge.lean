/-
**The replay, the bridge** (`agree_bridge`): the bridge value
`t = c0 + c1 x³ + c2 y² + x3 x² + y4 y + x5 x + y6 + x7` (`CurveMembership.evaluate`) from the curve
constants and the curve lanes' accumulators, one hash query, and the two keys stored at
`tmpK1`, `tmpK2`.
-/

import Proof.Simulator.ReplayDesChunk

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What the bridge leaves: the two hash keys. -/
def BridgePost (memory : Memory) (keys : Block × Block) (after : Memory) : Prop :=
  after.ram = Function.update (Function.update memory.ram (word tmpK1) (blockWord keys.1))
    (word tmpK2) (blockWord keys.2) ∧ after.bits = memory.bits

theorem fieldMul_words_self (value : BaseField) :
    Arithmetic.fieldMul.eval (fieldWord value) (fieldWord value) = fieldWord (value * value) :=
  fieldMul_words value value

/-- **The bridge.** -/
theorem agree_bridge (memory : Memory) (x y c0 c1 c2 x3 x5 x7 y4 y6 : BaseField)
    (xCell : memory.ram (word reqX) = fieldWord x) (yCell : memory.ram (word reqY) = fieldWord y)
    (c0Cell : memory.ram (word fieldBase) = fieldWord c0)
    (c1Cell : memory.ram (word (fieldBase + 1)) = fieldWord c1)
    (c2Cell : memory.ram (word (fieldBase + 2)) = fieldWord c2)
    (x3Cell : memory.ram (word (accBase + 455)) = fieldWord x3)
    (y4Cell : memory.ram (word (accBase + 822)) = fieldWord y4)
    (x5Cell : memory.ram (word (accBase + 456)) = fieldWord x5)
    (y6Cell : memory.ram (word (accBase + 823)) = fieldWord y6)
    (x7Cell : memory.ram (word (accBase + 457)) = fieldWord x7) :
    Agree (BridgePost memory) (rtree Replay.bridge memory)
      (Programs.askHash (c0 + c1 * x ^ 3 + c2 * y ^ 2 + x3 * x ^ 2 + y4 * y + x5 * x + y6 + x7)) := by
  unfold Replay.bridge
  rw [rtree_loadAt_seq, xCell, rtree_loadAt_seq]
  simp only [setReg_ram, yCell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x) (fieldWord x)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte])
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (x * x)) (fieldWord x) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord y) (fieldWord y)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte])
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_loadAt_seq]
  simp only [setReg_ram, c0Cell]
  rw [rtree_loadAt_seq]
  simp only [setReg_ram, c1Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord c1) (fieldWord (x * x * x)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord c0) (fieldWord (c1 * (x * x * x)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, c2Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord c2) (fieldWord (y * y)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x))) (fieldWord (c2 * (y * y)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x3Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x3) (fieldWord (x * x)) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y))) (fieldWord (x3 * (x * x)))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, y4Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord y4) (fieldWord y) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _ (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x)))
      (fieldWord (y4 * y))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x5Cell]
  rw [rtree_ar_val _ _ _ _ _ _ (fieldWord x5) (fieldWord x) (reg_same _ _ _)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]), fieldMul_words,
    rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y)) (fieldWord (x5 * x))
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, y6Cell]
  rw [rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x))
      (fieldWord y6)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words, rtree_loadAt_seq]
  simp only [setReg_ram, x7Cell]
  rw [rtree_ar_val _ _ _ _ _ _
      (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x + y6))
      (fieldWord x7)
      (by simp (config := {decide := true}) only [setReg_registers, reduceIte]) (reg_same _ _ _),
    fieldAdd_words]
  have decode : ∀ index : Word, @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex
      (Fintype.ofFinite _) (Fintype.ofFinite _) 4 index
        (fieldWord (c0 + c1 * (x * x * x) + c2 * (y * y) + x3 * (x * x) + y4 * y + x5 * x + y6 + x7)) =
      some (.hash (c0 + c1 * x ^ 3 + c2 * y ^ 2 + x3 * x ^ 2 + y4 * y + x5 * x + y6 + x7)) := by
    intro index
    rw [query_hash, fieldWord_cast]
    congr 2
    ring
  refine Agree.query 4 rIndex rInput rFirst rSecond _ _
    (by rw [reg_same, decode]) (rtree (.seq (storeAt tmpK1 rFirst) (storeAt tmpK2 rSecond))) _
    fun keys => ?_
  refine .leaf ⟨?_, ?_⟩
  · show (storeRam (setReg (storeRam (setReg _ rAddr (word tmpK1)) (word tmpK1) _) rAddr
      (word tmpK2)) (word tmpK2) _).ram = _
    simp only [storeRam_ram, setReg_ram, writePair_ram, writePair_registers, setReg_registers,
      storeRam_registers]
    simp (config := {decide := true}) only [reduceIte]
    rfl
  · show (storeRam (setReg (storeRam (setReg _ rAddr (word tmpK1)) (word tmpK1) _) rAddr
      (word tmpK2)) (word tmpK2) _).bits = _
    simp only [storeRam_bits, setReg_bits, writePair_bits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
