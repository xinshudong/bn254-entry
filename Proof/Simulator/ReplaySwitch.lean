/-
**The replay, one chunk's switches.**

* `agree_elements`: `rep count element` against the evaluator's element vector of one switch
  (every element's accumulator cell advanced by `coef · y_e`);
* `agree_switchStep`: one switch step: skipped at `α`, otherwise the switch's label and coefficient
  `ι(j) − ι(α)` loaded and its elements run;
* `agree_switches`: the four switch steps against the evaluator's `evalMasksM` vector;
* `joinTerms`: the published-join terms `acc[e] += ι(α) · J[e]`;
* `evalScaleOf_eq`: `evalScaleOf` in the machine's accumulation order.
-/

import Proof.Simulator.ReplayElement

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Accumulator cells -/

/-- The accumulator cell of element `index` of a lane. -/
abbrev accCell (spec : Replay.LaneSpec) (index : Nat) : Word := word (accBase + spec.slot + index)

omit [FieldCertificate] in
theorem accCell_lt (spec : Replay.LaneSpec) (index : Nat) (fits : spec.slot + index < 824) :
    accBase + spec.slot + index < 2 ^ 256 := by
  unfold accBase; omega

theorem accCell_ne (spec : Replay.LaneSpec) {first second : Nat} (firstFits : spec.slot + first < 824)
    (secondFits : spec.slot + second < 824) (different : first ≠ second) :
    accCell spec first ≠ accCell spec second :=
  word_ne (accCell_lt spec first firstFits) (accCell_lt spec second secondFits) (by omega)

omit [FieldCertificate] in
theorem word_small {value : Nat} (small : value < 2 ^ 256) : (word value).toNat = value := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-! ### Clean evaluator bodies -/

omit [FieldCertificate] in
theorem interceptAnswer_fixed (bits : BitInput) (index : PlanB.FixedIndex) (input : Block)
    (clean : ¬ IsDesignated bits index) : interceptAnswer bits (.fixedForward index input) = none := by
  simp only [interceptAnswer, if_neg clean]

omit [FieldCertificate] in
theorem clean_hashM (bits : BitInput) (index : PlanB.FixedIndex) (label : Block)
    (clean : ¬ IsDesignated bits index) : Clean bits (Programs.hashM index label) :=
  (Clean.ask _ (interceptAnswer_fixed bits index label clean)).bind fun _ => .pure _

omit [FieldCertificate] in
theorem clean_elemProg (bits : BitInput) (index : Fin 3 → PlanB.FixedIndex) (label : Block)
    (clean : ∀ block, ¬ IsDesignated bits (index block)) : Clean bits (elemProg index label) :=
  (clean_hashM bits _ label (clean 0)).bind fun _ => (clean_hashM bits _ label (clean 1)).bind
    fun _ => (clean_hashM bits _ label (clean 2)).bind fun _ => .pure _

/-! ### The elements of one switch -/

/-- The invariant of the element loop of one switch. -/
def ElemsInv (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (coef : BaseField) (start : Memory)
    (record0 : Record) (count : Nat) (state : Vector BaseField count × Record) (memory : Memory) :
    Prop :=
  (∀ e (bound : e < count), memory.ram (accCell spec e) = fieldWord (acc0 e + coef * state.1[e])) ∧
    (∀ address, (∀ e, e < count → address ≠ accCell spec e) → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ memory.registers rInput = start.registers rInput ∧
    memory.registers rF = start.registers rF ∧ state.2 = record0

/-- **The element loop of one switch.** -/
theorem agree_elements [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (chunk switch count : Nat) (fits : spec.slot + count ≤ 824) (start : Memory) (record0 : Record)
    (label : Block) (coef : BaseField) (acc0 : Nat → BaseField)
    (index : Fin count → Fin 3 → PlanB.FixedIndex)
    (named : ∀ (e : Fin count) (block : Fin 3),
      Replay.scaleIdx spec.lane chunk switch e.val block.val = index e block)
    (clean : ∀ e block, ¬ IsDesignated bits (index e block))
    (input : start.registers rInput = blockWord label) (factor : start.registers rF = fieldWord coef)
    (cells : ∀ e, e < count → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (ElemsInv spec acc0 coef start record0 count)
      (rtree (Prog.rep count (Replay.element ordF0 spec chunk switch)) start)
      (interceptT bits (FreeQuery.vector count fun e => elemProg (index e) label) record0) := by
  refine agree_rep_vector bits _ (ElemsInv spec acc0 coef start record0) count _ ?_ record0 start
    ⟨fun e bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  intro e values record memory holds
  obtain ⟨accs, frame, bitsSame, inputSame, coefSame, recordSame⟩ := holds
  subst recordSame
  rw [interceptT_clean bits _ (clean_elemProg bits _ label (clean e))]
  have cell : memory.ram (word (accBase + spec.slot + e.val)) = fieldWord (acc0 e.val) := by
    rw [frame _ fun other bound => accCell_ne spec (by omega) (by omega) (by omega),
      cells e.val e.isLt]
  have agree := agree_element spec chunk switch e.val memory label coef (acc0 e.val) (index e)
    (named e 0) (named e 1) (named e 2) (inputSame.trans input) (coefSame.trans factor) cell
  refine agree.map (fun value => (value, record)) fun value after post => ?_
  obtain ⟨ram, bitsAfter, inputAfter, coefAfter⟩ := post
  refine ⟨fun other bound => ?_, fun address outside => ?_, bitsAfter.trans bitsSame,
    inputAfter.trans inputSame, coefAfter.trans coefSame, rfl⟩
  · rw [ram]
    by_cases last : other = e.val
    · subst last
      rw [Function.update_self, Vector.getElem_push_eq]
    · rw [Function.update_of_ne (accCell_ne spec (by omega) (by omega) last),
        Vector.getElem_push_lt (by omega)]
      exact accs other (by omega)
  · rw [ram, Function.update_of_ne (outside e.val (by omega)),
      frame address fun other bound => outside other (by omega)]

/-! ### One switch step -/

theorem rtree_ite (source : Register) (whenSet whenClear : Prog) (memory : Memory) :
    rtree (.ite source whenSet whenClear) memory =
      if memory.registers source = 0 then rtree whenClear memory else rtree whenSet memory := rfl

theorem rtree_skip (count : Nat) (memory : Memory) :
    rtree (.skip count) memory = .pure (some memory) := rfl

omit [FieldCertificate] in
theorem eval_xor (first second : Word) : Arithmetic.xor.eval first second = first ^^^ second := rfl

theorem word_xor_eq_zero {first second : Nat} (firstSmall : first < 2 ^ 256)
    (secondSmall : second < 2 ^ 256) : word first ^^^ word second = 0 ↔ first = second := by
  constructor
  · intro zero
    have same : word first = word second := by
      have := congrArg (fun value => value ^^^ word second) zero
      simpa [BitVec.xor_assoc] using this
    exact word_injective firstSmall secondSmall same
  · intro same
    rw [same, BitVec.xor_self]
    rfl

omit [FieldCertificate] in
theorem scaleIdx_eq (lane : Lane) (chunk : Fin chunkCount) (switch : Nat) {count : Nat}
    (element : Fin count) (small : element.val < elementCountX) (block : Fin 3) :
    Replay.scaleIdx lane chunk.val switch element.val block.val =
      scaleIndexOf lane chunk switch element block := by
  unfold Replay.scaleIdx scaleIndexOf scaleIndexNat
  have chunkSame : Replay.chunkFin chunk.val = chunk := Fin.ext (Nat.mod_eq_of_lt chunk.isLt)
  have blockSame : (⟨block.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = block :=
    Fin.ext (Nat.mod_eq_of_lt block.isLt)
  rw [chunkSame, blockSame]

/-- What one switch step leaves. -/
def SwitchPost (spec : Replay.LaneSpec) (acc1 : Nat → BaseField) (coef : BaseField) (start : Memory)
    (record : Record) (result : (Fin spec.count → BaseField) × Record) (after : Memory) : Prop :=
  (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc1 e + coef * result.1 e)) ∧
    (∀ address, (∀ e, e < spec.count → address ≠ accCell spec e) →
      after.ram address = start.ram address) ∧ after.bits = start.bits ∧ result.2 = record

/-- **One switch step** (not the designated chunk). -/
theorem agree_switchStep [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (fits : spec.slot + spec.count ≤ 824) (small : spec.count ≤ elementCountX)
    (chunk : Fin chunkCount) (alpha switch : Fin (2 ^ 2)) (hot : Fin (2 ^ 2) → Block)
    (memory : Memory) (record : Record) (acc1 : Nat → BaseField)
    (clean : ∀ (e : Fin spec.count) block,
      ¬ IsDesignated bits (scaleIndexOf spec.lane chunk switch.val e block))
    (alphaCell : memory.ram (word tmpAlpha) = word alpha.val)
    (hotCell : memory.ram (word (hotLabelBase + switch.val)) = blockWord (hot switch))
    (cells : ∀ e, e < spec.count → memory.ram (accCell spec e) = fieldWord (acc1 e)) :
    Agree (SwitchPost spec acc1 ((switch.val : BaseField) - (alpha.val : BaseField)) memory record)
      (rtree (Replay.switchStep ordF0 spec false chunk.val switch.val) memory)
      (interceptT bits (if switch = alpha then FreeQuery.pure (fun _ => 0) else
        Programs.switchMaskM spec.count spec.lane chunk switch.val (hot switch)) record) := by
  have alphaSmall : alpha.val < 2 ^ 256 := lt_trans alpha.isLt (by norm_num)
  have switchSmall : switch.val < 2 ^ 256 := lt_trans switch.isLt (by norm_num)
  unfold Replay.switchStep
  rw [rtree_loadAt_seq, rtree_cst_seq, rtree_ar_val _ _ _ _ _ _ (word alpha.val) (word switch.val)
    (by rw [reg_ne _ _ _ _ (by decide), reg_same, alphaCell]) (reg_same _ _ _), rtree_ite, reg_same,
    eval_xor]
  by_cases same : switch = alpha
  · subst same
    rw [if_pos ((word_xor_eq_zero switchSmall switchSmall).mpr rfl), if_pos rfl, rtree_skip]
    refine .leaf ⟨fun e => ?_, fun _ _ => rfl, rfl, rfl⟩
    simp only [setReg_ram, sub_self, zero_mul, add_zero]
    exact cells e.val e.isLt
  · have different : switch.val ≠ alpha.val := fun equal => same (Fin.ext equal)
    rw [if_neg (fun zero => different ((word_xor_eq_zero alphaSmall switchSmall).mp zero).symm),
      if_neg same]
    unfold Replay.switchBody Programs.switchMaskM
    rw [rtree_loadAt_seq, rtree_loadAt_seq, rtree_cst_seq,
      rtree_ar_val _ _ _ _ _ _ (word switch.val) (word alpha.val) (reg_same _ _ _)
        (by rw [reg_ne _ _ _ _ (by decide), reg_same]; simp only [setReg_ram, alphaCell])]
    unfold Replay.switchElements
    rw [if_neg (by decide), TreeLaws.monad_bind, interceptT_bind]
    refine Agree.map (fun state => (state.1.get, state.2)) (fun state after holds => ?post)
      (agree_elements bits spec chunk.val switch.val spec.count fits _ record (hot switch)
        ((switch.val : BaseField) - (alpha.val : BaseField)) acc1
        (fun e block => scaleIndexOf spec.lane chunk switch.val e block)
        (fun e block => scaleIdx_eq spec.lane chunk switch.val e (lt_of_lt_of_le e.isLt small) block)
        clean ?input ?factor ?cells)
    case input =>
      simp only [setReg_registers, setReg_ram, hotCell]
      simp (config := {decide := true})
    case factor =>
      simp only [setReg_registers, if_true, eval_fieldSub, word_small switchSmall,
        word_small alphaSmall]
    case cells =>
      intro e bound
      simp only [setReg_ram]
      exact cells e bound
    case post =>
      obtain ⟨accs, frame, bitsSame, _, _, recordSame⟩ := holds
      refine ⟨fun e => ?_, fun address outside => ?_, bitsSame, recordSame⟩
      · rw [accs e.val e.isLt]
        rfl
      · rw [frame address outside]
        rfl

/-! ### The four switch steps -/

/-- The invariant of the switch loop: every accumulator cell holds its start value plus the
processed switches' `(ι(j) − ι(α)) · Y_j[e]`. -/
def SwInv (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (alpha : Nat) (start : Memory)
    (record0 : Record) (count : Nat) (state : Vector (Fin spec.count → BaseField) count × Record)
    (memory : Memory) : Prop :=
  (∀ e : Fin spec.count, memory.ram (accCell spec e) = fieldWord (acc0 e +
      ∑ switch : Fin count, ((switch.val : BaseField) - (alpha : BaseField)) * state.1[switch] e)) ∧
    (∀ address, (∀ e, e < spec.count → address ≠ accCell spec e) →
      memory.ram address = start.ram address) ∧ memory.bits = start.bits ∧ state.2 = record0

theorem hotLabel_ne_acc (spec : Replay.LaneSpec) (fits : spec.slot + spec.count ≤ 824)
    (offset : Nat) (small : offset < 5) (e : Nat) (bound : e < spec.count) :
    word (hotLabelBase + offset) ≠ accCell spec e :=
  word_ne (by unfold hotLabelBase; omega) (accCell_lt spec e (by omega))
    (by unfold hotLabelBase accBase; omega)

theorem tmp_ne_acc (spec : Replay.LaneSpec) (fits : spec.slot + spec.count ≤ 824)
    (offset : Nat) (small : offset < 16) (e : Nat) (bound : e < spec.count) :
    word (tmpBase + offset) ≠ accCell spec e :=
  word_ne (by unfold tmpBase; omega) (accCell_lt spec e (by omega))
    (by unfold tmpBase accBase; omega)

/-- **The switch loop of a chunk** (not the designated chunk). -/
theorem agree_switches [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (fits : spec.slot + spec.count ≤ 824) (small : spec.count ≤ elementCountX)
    (chunk : Fin chunkCount) (alpha : Fin (2 ^ 2)) (hot : Fin (2 ^ 2) → Block)
    (start : Memory) (record0 : Record) (acc0 : Nat → BaseField)
    (clean : ∀ (switch : Fin (2 ^ 2)) (e : Fin spec.count) block,
      ¬ IsDesignated bits (scaleIndexOf spec.lane chunk switch.val e block))
    (alphaCell : start.ram (word tmpAlpha) = word alpha.val)
    (hotCells : ∀ switch : Fin (2 ^ 2),
      start.ram (word (hotLabelBase + switch.val)) = blockWord (hot switch))
    (cells : ∀ e, e < spec.count → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (SwInv spec acc0 alpha.val start record0 (2 ^ 2))
      (rtree (Prog.rep (2 ^ 2) fun switch => Replay.switchStep ordF0 spec false chunk.val switch)
        start)
      (interceptT bits (FreeQuery.vector (2 ^ 2) fun switch =>
        if switch = alpha then FreeQuery.pure (fun _ => 0) else
          Programs.switchMaskM spec.count spec.lane chunk switch.val (hot switch)) record0) := by
  refine agree_rep_vector bits _ (SwInv spec acc0 alpha.val start record0) (2 ^ 2) _ ?_ record0
    start ⟨fun e => by simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]; exact cells e e.isLt,
      fun _ _ => rfl, rfl, rfl⟩
  intro switch masks record memory holds
  obtain ⟨accs, frame, bitsSame, recordSame⟩ := holds
  subst recordSame
  have agree := agree_switchStep bits spec fits small chunk alpha switch hot memory record
    (fun e => if bound : e < spec.count then acc0 e + ∑ earlier : Fin switch.val,
      ((earlier.val : BaseField) - (alpha.val : BaseField)) * masks[earlier] ⟨e, bound⟩ else 0)
    (clean switch)
    (by rw [frame (word tmpAlpha) fun e bound => tmp_ne_acc spec fits 0 (by omega) e bound,
      alphaCell])
    (by rw [frame _ fun e bound => hotLabel_ne_acc spec fits switch.val (by omega) e bound,
      hotCells])
    (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩)
  refine agree.mono fun result after post => ?_
  obtain ⟨accsAfter, frameAfter, bitsAfter, recordAfter⟩ := post
  refine ⟨fun e => ?_, fun address outside => ?_, bitsAfter.trans bitsSame, recordAfter⟩
  · rw [accsAfter e]
    simp only [dif_pos e.isLt]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun earlier _ => ?_
      simp only [Fin.getElem_fin, Fin.coe_castSucc, Vector.getElem_push_lt earlier.isLt]
    · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
  · rw [frameAfter address outside, frame address outside]

/-! ### The published-join terms -/

/-- `rep n joinTerm` adds `α · J[e]` to the first `n` accumulator cells. -/
theorem rtree_joinTerms (spec : Replay.LaneSpec) (fits : spec.slot + spec.count ≤ 824)
    (chunk : Nat) (alpha : BaseField) (join : Nat → BaseField) (start : Memory)
    (factor : start.registers rF = fieldWord alpha)
    (joins : ∀ e, e < spec.count →
      start.ram (word (scaleCellBase + 824 * chunk + spec.slot + e)) = fieldWord (join e))
    (joinAway : ∀ e first, e < spec.count → first < spec.count →
      word (scaleCellBase + 824 * chunk + spec.slot + e) ≠ accCell spec first)
    (acc0 : Nat → BaseField) (cells : ∀ e, e < spec.count → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    ∀ count, count ≤ spec.count → ∃ after, rtree (Prog.rep count fun index => Replay.joinTerm spec chunk index) start =
        .pure (some after) ∧
      (∀ e, e < count → after.ram (accCell spec e) = fieldWord (acc0 e + join e * alpha)) ∧
      (∀ address, (∀ e, e < count → address ≠ accCell spec e) → after.ram address = start.ram address) ∧
      after.bits = start.bits ∧ after.registers rF = start.registers rF
  | 0, _ => ⟨start, by rw [Prog.rep]; rfl, fun e bound => absurd bound (by omega), fun _ _ => rfl,
      rfl, rfl⟩
  | count + 1, bound => by
      obtain ⟨middle, run, accs, frame, bitsSame, factorSame⟩ :=
        rtree_joinTerms spec fits chunk alpha join start factor joins joinAway acc0 cells count
          (by omega)
      have joinCell : middle.ram (word (scaleCellBase + 824 * chunk + spec.slot + count)) =
          fieldWord (join count) := by
        rw [frame _ fun e small => joinAway count e (by omega) (by omega), joins count (by omega)]
      have accCellValue : middle.ram (accCell spec count) = fieldWord (acc0 count) := by
        rw [frame _ fun e small => accCell_ne spec (by omega) (by omega) (by omega),
          cells count (by omega)]
      refine ⟨storeRam (setReg (setReg (setReg (setReg (setReg (setReg (setReg middle rAddr
          (word (scaleCellBase + 824 * chunk + spec.slot + count))) rC (fieldWord (join count)))
          rC (fieldWord (join count * alpha))) rAddr (accCell spec count)) rD
          (fieldWord (acc0 count))) rD (fieldWord (acc0 count + join count * alpha))) rAddr
          (accCell spec count))
          (accCell spec count) (fieldWord (acc0 count + join count * alpha)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Prog.rep, rtree_seq, run, bindOpt_pure]
        unfold Replay.joinTerm
        rw [rtree_loadAt_seq, joinCell]
        rw [rtree_ar_val _ _ _ _ _ _ (fieldWord (join count)) (fieldWord alpha) (reg_same _ _ _)
          (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), factorSame, factor]),
          fieldMul_words, rtree_loadAt_seq]
        simp only [setReg_ram, accCellValue]
        rw [rtree_ar_val _ _ _ _ _ _ (fieldWord (acc0 count)) (fieldWord (join count * alpha))
          (reg_same _ _ _) (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
            reg_same]), fieldAdd_words, rtree_storeAt _ _ _ (by decide), reg_same]
      · intro e small
        rw [storeRam_ram]
        by_cases last : e = count
        · subst last
          rw [Function.update_self]
        · rw [Function.update_of_ne (accCell_ne spec (by omega) (by omega) last)]
          simp only [setReg_ram]
          exact accs e (by omega)
      · intro address outside
        rw [storeRam_ram, Function.update_of_ne (outside count (by omega))]
        simp only [setReg_ram]
        exact frame address fun e small => outside e (by omega)
      · simp only [storeRam_bits, setReg_bits]
        exact bitsSame
      · simp only [storeRam_registers, setReg_registers]
        simp (config := {decide := true}) only [if_false]
        exact factorSame

/-! ### `evalScaleOf` in accumulation order -/

/-- **The evaluator's free fold** is the published-join term plus the switch terms
`(ι(j) − ι(α)) · Y_j`. -/
theorem evalScaleOf_eq {count width : Nat} (masks : Fin (2 ^ width) → Fin count → BaseField)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) (e : Fin count) :
    Programs.evalScaleOf width masks alpha join e =
      (∑ switch, ((switch.val : BaseField) - (alpha.val : BaseField)) * masks switch e) +
        join e * (alpha.val : BaseField) := by
  unfold Programs.evalScaleOf iota
  have split : ∑ switch : Fin (2 ^ width), (switch.val : BaseField) *
      (if switch = alpha then join e - ∑ other ∈ Finset.univ.erase alpha, masks other e
        else masks switch e) =
      (alpha.val : BaseField) * (join e - ∑ other ∈ Finset.univ.erase alpha, masks other e) +
        ∑ switch ∈ Finset.univ.erase alpha, (switch.val : BaseField) * masks switch e := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl fun switch member => by
      rw [if_neg (Finset.ne_of_mem_erase member)]
  have peel : ∑ switch : Fin (2 ^ width), ((switch.val : BaseField) - (alpha.val : BaseField)) *
      masks switch e = ((alpha.val : BaseField) - (alpha.val : BaseField)) * masks alpha e +
        ∑ switch ∈ Finset.univ.erase alpha,
          ((switch.val : BaseField) - (alpha.val : BaseField)) * masks switch e :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ alpha)).symm
  rw [split, peel, sub_self, zero_mul, zero_add]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end

end Kriterion.ArgoMAC.PlanB.SimMachine
