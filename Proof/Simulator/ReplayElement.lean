/-
**The replay, one element of one switch.**

* the straight-line tree steps (`rtree_cst_seq`, …) and one Davies–Meyer hash step
  (`agree_hashStep`: an index constant, a fixed forward query, the xor with the label);
* `agree_element`: `Replay.element` asks the element's three blocks exactly as the evaluator's
  `switchMaskM` does and adds `coef · sampleFp` to the element's accumulator cell.
-/

import Proof.Simulator.ReplayBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Straight-line tree steps -/

theorem rtree_cst_seq (target : Register) (value : Nat) (rest : Prog) (memory : Memory) :
    rtree (.seq (cst target value) rest) memory = rtree rest (setReg memory target (word value)) :=
  rfl

theorem rtree_ar_seq (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) :
    rtree (.seq (ar operation target left right) rest) memory =
      rtree rest (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))) := rfl

theorem rtree_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory) :
    rtree (.seq (loadAt target address) rest) memory =
      rtree rest (setReg (setReg memory rAddr (word address)) target (memory.ram (word address))) :=
  rfl

theorem rtree_storeAt_seq (address : Nat) (source : Register) (rest : Prog) (memory : Memory)
    (other : source ≠ rAddr) :
    rtree (.seq (storeAt address source) rest) memory =
      rtree rest (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source)) := by
  show rtree rest (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source)) = _
  simp only [setReg_registers, if_neg other, ↓reduceIte]

theorem rtree_storeAt (address : Nat) (source : Register) (memory : Memory)
    (other : source ≠ rAddr) :
    rtree (storeAt address source) memory =
      .pure (some (storeRam (setReg memory rAddr (word address)) (word address)
        (memory.registers source))) := by
  show FreeQuery.pure (some (storeRam (setReg memory rAddr (word address))
    ((setReg memory rAddr (word address)).registers rAddr)
    ((setReg memory rAddr (word address)).registers source))) = _
  simp only [setReg_registers, if_neg other, ↓reduceIte]

theorem rtree_ar (operation : Arithmetic) (target left right : Register) (memory : Memory) :
    rtree (ar operation target left right) memory =
      .pure (some (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right)))) := rfl

/-! ### Memory bookkeeping -/

omit [FieldCertificate] in
theorem writePair_ram (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem writePair_bits (memory : Memory) (first second : Register) (values : Word × Word) :
    (writePair memory first second values).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem writePair_registers (memory : Memory) (first second : Register) (values : Word × Word)
    (index : Register) :
    (writePair memory first second values).registers index =
      if index = second then values.2 else if index = first then values.1 else
        memory.registers index := by
  simp only [writePair, Function.update_apply]

omit [FieldCertificate] in
theorem storeRam_registers (memory : Memory) (address value : Word) :
    (storeRam memory address value).registers = memory.registers := rfl

omit [FieldCertificate] in
theorem storeRam_bits (memory : Memory) (address value : Word) :
    (storeRam memory address value).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem storeRam_ram (memory : Memory) (address value : Word) :
    (storeRam memory address value).ram = Function.update memory.ram address value := rfl

/-! ### One hash step -/

/-- The memory after one hash step: the index constant, the answer, the xor into `target`. -/
def hashMem (memory : Memory) (index : Nat) (target : Register) (answer label : Block) : Memory :=
  setReg (writePair (setReg memory rIndex (word index)) rFirst rSecond (blockWord answer, 0))
    target (blockWord (answer ^^^ label))

omit [FieldCertificate] in
theorem hashMem_ram (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).ram = memory.ram := rfl

omit [FieldCertificate] in
theorem hashMem_bits (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).bits = memory.bits := rfl

omit [FieldCertificate] in
theorem hashMem_target (memory : Memory) (index : Nat) (target : Register) (answer label : Block) :
    (hashMem memory index target answer label).registers target = blockWord (answer ^^^ label) := by
  simp only [hashMem, setReg_registers, ↓reduceIte]

omit [FieldCertificate] in
theorem hashMem_other (memory : Memory) (index : Nat) (target : Register) (answer label : Block)
    (register : Register) (notTarget : register ≠ target) (notIndex : register ≠ rIndex)
    (notFirst : register ≠ rFirst) (notSecond : register ≠ rSecond) :
    (hashMem memory index target answer label).registers register = memory.registers register := by
  simp only [hashMem, setReg_registers, writePair_registers, if_neg notTarget, if_neg notSecond,
    if_neg notFirst, if_neg notIndex]

/-- **One Davies–Meyer hash step** against the evaluator's `hashM`. -/
theorem agree_hashStep {β : Type} {Post : β → Memory → Prop} (index : PlanB.FixedIndex)
    (target : Register) (rest : Prog) (memory : Memory) (label : Block)
    (input : memory.registers rInput = blockWord label)
    (next : Block → FreeQuery Programs.Spec β)
    (each : ∀ answer, Agree Post (rtree rest (hashMem memory (ordF0 index) target answer label))
      (next (answer ^^^ label))) :
    Agree Post (rtree (.seq (cst rIndex (ordF0 index))
        (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
          (.seq (ar .xor target rFirst rInput) rest))) memory)
      (FreeQuery.bind (Programs.hashM index label) next) := by
  rw [rtree_cst_seq]
  have decode : @queryFromRegisters PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) 0 ((setReg memory rIndex (word (ordF0 index))).registers rIndex)
      ((setReg memory rIndex (word (ordF0 index))).registers rInput) =
        some (.fixedForward index label) := by
    rw [setReg_registers, if_pos rfl, setReg_registers, if_neg (by decide), input, query_fixed,
      blockWord_block]
  refine Agree.query 0 rIndex rInput rFirst rSecond _ _ decode
    (rtree (.seq (ar .xor target rFirst rInput) rest)) _ fun answer => ?_
  rw [rtree_ar_seq]
  have same : setReg (writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
      (answerWords (.fixedForward index label) answer)) target
      (Arithmetic.xor.eval
        ((writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
          (answerWords (.fixedForward index label) answer)).registers rFirst)
        ((writePair (setReg memory rIndex (word (ordF0 index))) rFirst rSecond
          (answerWords (.fixedForward index label) answer)).registers rInput)) =
      hashMem memory (ordF0 index) target answer label := by
    unfold hashMem
    congr 1
    rw [writePair_registers, writePair_registers, if_neg (by decide), if_pos rfl, if_neg (by decide),
      if_neg (by decide), setReg_registers, if_neg (by decide), input]
    exact blockWord_xor answer label
  rw [same]
  exact each answer

/-! ### One element -/

/-- The evaluator's body for one element of one switch: three hashes, then `sampleFp`. -/
def elemProg (index : Fin 3 → PlanB.FixedIndex) (label : Block) : FreeQuery Programs.Spec BaseField :=
  FreeQuery.bind (Programs.hashM (index 0) label) fun first =>
    FreeQuery.bind (Programs.hashM (index 1) label) fun second =>
      FreeQuery.bind (Programs.hashM (index 2) label) fun third =>
        .pure (sampleFp first second third)

/-- What one element leaves: its accumulator cell advanced by `coef · y`; the stacks, the label
register and the coefficient register unchanged. -/
def ElemPost (cell : Nat) (accOld coef : BaseField) (memory : Memory) (value : BaseField)
    (after : Memory) : Prop :=
  after.ram = Function.update memory.ram (word cell) (fieldWord (accOld + coef * value)) ∧
    after.bits = memory.bits ∧ after.registers rInput = memory.registers rInput ∧
    after.registers rF = memory.registers rF

omit [FieldCertificate] in
theorem word_two_pow_128 : (word (2 ^ 128)).toNat = 2 ^ 128 := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]

theorem c256_lt : c256 < 2 ^ 256 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by unfold pNat; norm_num)) (by unfold pNat; norm_num)

theorem word_c256 : ((word c256).toNat : BaseField) = 2 ^ 256 := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c256_lt]
  unfold c256
  rw [pNat_eq, ZMod.natCast_mod]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem sampleFp_eq (first second third : Block) :
    sampleFp first second third =
      (first.toNat : BaseField) + (second.toNat : BaseField) * 2 ^ 128 +
        (third.toNat : BaseField) * 2 ^ 256 := by
  unfold sampleFp blocksToNat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem reg_same (memory : Memory) (target : Register) (value : Word) :
    (setReg memory target value).registers target = value := by
  rw [setReg_registers, if_pos rfl]

theorem reg_ne (memory : Memory) (target other : Register) (value : Word) (different : other ≠ target) :
    (setReg memory target value).registers other = memory.registers other := by
  rw [setReg_registers, if_neg different]

theorem rtree_ar_val (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (first second : Word) (hfirst : memory.registers left = first)
    (hsecond : memory.registers right = second) :
    rtree (.seq (ar operation target left right) rest) memory =
      rtree rest (setReg memory target (operation.eval first second)) := by
  rw [rtree_ar_seq, hfirst, hsecond]

theorem fieldMul_words (first second : BaseField) :
    Arithmetic.fieldMul.eval (fieldWord first) (fieldWord second) = fieldWord (first * second) := by
  rw [eval_fieldMul, fieldWord_cast, fieldWord_cast]

theorem fieldAdd_words (first second : BaseField) :
    Arithmetic.fieldAdd.eval (fieldWord first) (fieldWord second) = fieldWord (first + second) := by
  rw [eval_fieldAdd, fieldWord_cast, fieldWord_cast]

theorem blockWord_eq_fieldWord (block : Block) :
    Arithmetic.fieldMul.eval (blockWord block) (word (2 ^ 128)) =
      fieldWord ((block.toNat : BaseField) * 2 ^ 128) := by
  rw [eval_fieldMul, blockWord_toNat, word_two_pow_128, Nat.cast_pow, Nat.cast_ofNat]

theorem blockWord_c256 (block : Block) :
    Arithmetic.fieldMul.eval (blockWord block) (word c256) =
      fieldWord ((block.toNat : BaseField) * 2 ^ 256) := by
  rw [eval_fieldMul, blockWord_toNat, word_c256]

theorem fieldAdd_block (block : Block) (value : BaseField) :
    Arithmetic.fieldAdd.eval (blockWord block) (fieldWord value) =
      fieldWord ((block.toNat : BaseField) + value) := by
  rw [eval_fieldAdd, blockWord_toNat, fieldWord_cast]

/-- The arithmetic tail of an element: `acc += coef · (C + 2^128 D + 2^256 E)`. -/
theorem agree_elementTail {β : Type} {Post : β → Memory → Prop} (cell : Nat) (memory : Memory)
    (c d e : Block) (coef accOld : BaseField) (value : β)
    (hc : memory.registers rC = blockWord c) (hd : memory.registers rD = blockWord d)
    (he : memory.registers rE = blockWord e) (hf : memory.registers rF = fieldWord coef)
    (hacc : memory.ram (word cell) = fieldWord accOld)
    (leaf : ∀ after : Memory, after.ram = Function.update memory.ram (word cell)
        (fieldWord (accOld + ((c.toNat : BaseField) + (d.toNat : BaseField) * 2 ^ 128 +
          (e.toNat : BaseField) * 2 ^ 256) * coef)) → after.bits = memory.bits →
        after.registers rInput = memory.registers rInput → after.registers rF = memory.registers rF →
        Post value after) :
    Agree Post (rtree (.seq (cst rAcc (2 ^ 128)) (.seq (ar .fieldMul rD rD rAcc)
      (.seq (ar .fieldAdd rC rC rD) (.seq (cst rAcc c256) (.seq (ar .fieldMul rE rE rAcc)
      (.seq (ar .fieldAdd rC rC rE) (.seq (ar .fieldMul rC rC rF) (.seq (loadAt rD cell)
      (.seq (ar .fieldAdd rD rD rC) (storeAt cell rD)))))))))) memory) (.pure value) := by
  rw [rtree_cst_seq]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (by rw [reg_ne _ _ _ _ (by decide), hd]) (reg_same _ _ _),
    blockWord_eq_fieldWord]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), hc])
    (reg_same _ _ _), fieldAdd_block]
  rw [rtree_cst_seq]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (by
      rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_ne _ _ _ _ (by decide), he]) (reg_same _ _ _), blockWord_c256]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
      reg_same]) (reg_same _ _ _), fieldAdd_words]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (reg_same _ _ _) (by
      rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), hf]),
    fieldMul_words]
  rw [rtree_loadAt_seq]
  simp only [setReg_ram, hacc]
  rw [rtree_ar_val _ _ _ _ _ _ _ _ (reg_same _ _ _) (by
      rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_same]), fieldAdd_words,
    rtree_storeAt _ _ _ (by decide), reg_same]
  refine .leaf (leaf _ ?_ rfl ?_ ?_)
  · rw [storeRam_ram]
    simp only [setReg_ram]
  · simp only [storeRam_registers, setReg_registers]
    simp (config := {decide := true})
  · simp only [storeRam_registers, setReg_registers]
    simp (config := {decide := true})

/-- **One element.** -/
theorem agree_element (spec : Replay.LaneSpec) (chunk switch index : Nat) (memory : Memory)
    (label : Block) (coef accOld : BaseField) (idx : Fin 3 → PlanB.FixedIndex)
    (index0 : Replay.scaleIdx spec.lane chunk switch index 0 = idx 0)
    (index1 : Replay.scaleIdx spec.lane chunk switch index 1 = idx 1)
    (index2 : Replay.scaleIdx spec.lane chunk switch index 2 = idx 2)
    (input : memory.registers rInput = blockWord label)
    (factor : memory.registers rF = fieldWord coef)
    (cell : memory.ram (word (accBase + spec.slot + index)) = fieldWord accOld) :
    Agree (ElemPost (accBase + spec.slot + index) accOld coef memory)
      (rtree (Replay.element ordF0 spec chunk switch index) memory) (elemProg idx label) := by
  unfold Replay.element
  rw [index0, index1, index2]
  refine agree_hashStep (idx 0) rC _ memory label input _ fun first => ?_
  set m1 := hashMem memory (ordF0 (idx 0)) rC first label with m1Def
  have input1 : m1.registers rInput = blockWord label := by
    rw [m1Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), input]
  refine agree_hashStep (idx 1) rD _ m1 label input1 _ fun second => ?_
  set m2 := hashMem m1 (ordF0 (idx 1)) rD second label with m2Def
  have input2 : m2.registers rInput = blockWord label := by
    rw [m2Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), input1]
  refine agree_hashStep (idx 2) rE _ m2 label input2 _ fun third => ?_
  set m3 := hashMem m2 (ordF0 (idx 2)) rE third label with m3Def
  have c3 : m3.registers rC = blockWord (first ^^^ label) := by
    rw [m3Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), m2Def,
      hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), m1Def,
      hashMem_target]
  have d3 : m3.registers rD = blockWord (second ^^^ label) := by
    rw [m3Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), m2Def,
      hashMem_target]
  have e3 : m3.registers rE = blockWord (third ^^^ label) := by
    rw [m3Def, hashMem_target]
  have f3 : m3.registers rF = fieldWord coef := by
    rw [m3Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), m2Def,
      hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), m1Def,
      hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), factor]
  have i3 : m3.registers rInput = memory.registers rInput := by
    rw [m3Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), input2,
      input]
  have ram3 : m3.ram = memory.ram := rfl
  have bits3 : m3.bits = memory.bits := rfl
  refine agree_elementTail _ m3 _ _ _ coef accOld _ c3 d3 e3 f3 (by rw [ram3]; exact cell)
    fun after ram bits input coefReg => ⟨?_, bits.trans bits3, input.trans i3, ?_⟩
  · rw [ram, ram3, sampleFp_eq, mul_comm coef]
  · rw [coefReg, f3, factor]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
