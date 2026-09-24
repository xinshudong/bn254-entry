/-
**The replay, the designated chunk** — one guarded element (`agree_guarded`).

Off `j*` or off the collectors the element runs as usual (its queries are not designated); at
`j*` on a collector the machine skips it and the evaluator's three designated queries are
answered inline by their input (Davies–Meyer output `0`, so the element value is `0`) and recorded.
-/

import Proof.Simulator.ReplayDesignated

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- The three scale indices of element `index` of switch `switch` in chunk `0` of `pointX`. -/
def desIdx (switch : Nat) (index : Fin pointElementCountX) (block : Fin 3) : PlanB.FixedIndex :=
  scaleIndexOf .pointX chunkZero switch index block

/-- The record after the three queries of one element. -/
def record3 [DecidableEq PlanB.FixedIndex] (bits : BitInput) (switch : Nat)
    (index : Fin pointElementCountX) (label : Block)
    (record : Record) : Record :=
  recordAfter bits (.fixedForward (desIdx switch index 2) label)
    (recordAfter bits (.fixedForward (desIdx switch index 1) label)
      (recordAfter bits (.fixedForward (desIdx switch index 0) label) record))

theorem sampleFp_self (label : Block) : sampleFp (label ^^^ label) (label ^^^ label) (label ^^^ label) = 0 := by
  simp [sampleFp, blocksToNat]

theorem scaleIdx_des (switch : Nat) (index : Fin pointElementCountX) (block : Fin 3) :
    Replay.scaleIdx .pointX 0 switch index.val block.val = desIdx switch index block :=
  scaleIdx_eq .pointX chunkZero switch index
    (lt_of_lt_of_le index.isLt (by unfold pointElementCountX elementCountX; omega)) block

theorem interceptT_query_answered [DecidableEq PlanB.FixedIndex] {α : Type} (bits : BitInput)
    (request : PublicQuery PlanB.FixedIndex EncPRF.PermutationIndex)
    (next : request.Answer → FreeQuery Programs.Spec α) (answer : request.Answer) (r : Record)
    (answered : interceptAnswer bits request = some answer) :
    interceptT bits (.query request next) r = interceptT bits (next answer) (recordAfter bits request r) := by
  simp only [interceptT, answered]
theorem interceptT_hashM_answered [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (idx : PlanB.FixedIndex) (label : Block) (r : Record)
    (answer : interceptAnswer bits (.fixedForward idx label) = some label) :
    interceptT bits (Programs.hashM idx label) r =
      .pure (label ^^^ label, recordAfter bits (.fixedForward idx label) r) :=
  interceptT_query_answered bits (.fixedForward idx label) _ label r answer
theorem interceptT_hashM_designated [DecidableEq PlanB.FixedIndex] (bits : BitInput) (idx : PlanB.FixedIndex) (label : Block) (β : Type) (k : Block → FreeQuery Programs.Spec β) (r : Record)
    (answer : interceptAnswer bits (.fixedForward idx label) = some label) :
    interceptT bits (FreeQuery.bind (Programs.hashM idx label) k) r =
      interceptT bits (k (label ^^^ label)) (recordAfter bits (.fixedForward idx label) r) := by
  rw [interceptT_bind, interceptT_hashM_answered bits idx label r answer]
  rfl

/-- **One guarded element of the designated chunk.** -/
theorem agree_guarded [DecidableEq PlanB.FixedIndex] (bits : BitInput) (switch : Nat)
    (switchSmall : switch < 4) (index : Fin pointElementCountX)
    (memory : Memory) (label : Block) (coef accOld : BaseField) (record : Record)
    (input : memory.registers rInput = blockWord label) (factor : memory.registers rF = fieldWord coef)
    (cell : memory.ram (word (accBase + Replay.pointXSpec.slot + index.val)) = fieldWord accOld)
    (jstarCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    Agree (fun (result : BaseField × Record) after =>
        ElemPost (accBase + Replay.pointXSpec.slot + index.val) accOld coef memory result.1 after ∧
          result.2 = if switch = (designatedSwitch bits).val ∧ Replay.isCollector index.val = true then
            record3 bits switch index label record else record)
      (rtree (Replay.guardedElement ordF0 Replay.pointXSpec 0 switch index.val) memory)
      (interceptT bits (elemProg (desIdx switch index) label) record) := by
  have jSmall : (designatedSwitch bits).val < 4 := (designatedSwitch bits).isLt
  have designated : ∀ block, IsDesignated bits (desIdx switch index block) ↔
      switch = (designatedSwitch bits).val ∧ Replay.isCollector index.val = true :=
    fun block => isDesignated_iff bits switch switchSmall index block
  have plainAgree : ∀ start : Memory, start.ram = memory.ram → start.bits = memory.bits →
      start.registers rInput = memory.registers rInput → start.registers rF = memory.registers rF →
      ¬ (switch = (designatedSwitch bits).val ∧ Replay.isCollector index.val = true) →
      Agree (fun (result : BaseField × Record) after =>
        ElemPost (accBase + Replay.pointXSpec.slot + index.val) accOld coef memory result.1 after ∧
          result.2 = if switch = (designatedSwitch bits).val ∧ Replay.isCollector index.val = true then
            record3 bits switch index label record else record)
        (rtree (Replay.element ordF0 Replay.pointXSpec 0 switch index.val) start)
        (interceptT bits (elemProg (desIdx switch index) label) record) := by
    intro start sameRam sameBits sameInput sameCoef clean
    rw [interceptT_clean bits record (clean_elemProg bits _ label fun block holds =>
      clean ((designated block).mp holds))]
    refine (agree_element Replay.pointXSpec 0 switch index.val start label coef accOld
      (desIdx switch index) (scaleIdx_des switch index 0)
      (scaleIdx_des switch index 1) (scaleIdx_des switch index 2)
      (sameInput.trans input) (sameCoef.trans factor) (by rw [sameRam]; exact cell)).map
      (fun value => (value, record)) fun value after post => ⟨?_, ?_⟩
    · obtain ⟨ram, bitsAfter, inputAfter, coefAfter⟩ := post
      exact ⟨by rw [ram, sameRam], bitsAfter.trans sameBits, inputAfter.trans sameInput,
        coefAfter.trans sameCoef⟩
    · rw [if_neg clean]
  by_cases collector : Replay.isCollector index.val = true
  · by_cases atStar : switch = (designatedSwitch bits).val
    · -- skipped by the machine, answered inline by the evaluator
      have holds : switch = (designatedSwitch bits).val ∧ Replay.isCollector index.val = true :=
        ⟨atStar, collector⟩
      unfold Replay.guardedElement
      rw [if_pos collector, rtree_loadAt_seq, jstarCell, rtree_cst_seq,
        rtree_ar_val _ _ _ _ _ _ (word (designatedSwitch bits).val) (word switch)
          (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), rtree_ite, reg_same,
        eval_xor, if_pos ((word_xor_eq_zero (by omega) (by omega)).mpr atStar.symm), rtree_skip]
      have answer : ∀ block, interceptAnswer bits (.fixedForward (desIdx switch index block) label) =
          some label := by
        intro block
        unfold interceptAnswer
        exact if_pos ((designated block).mpr holds)
      unfold elemProg
      rw [interceptT_hashM_designated bits _ label _ _ _ (answer 0)]
      try dsimp only
      rw [interceptT_hashM_designated bits _ label _ _ _ (answer 1)]
      try dsimp only
      rw [interceptT_hashM_designated bits _ label _ _ _ (answer 2)]
      refine .leaf ⟨⟨?_, rfl, ?_, ?_⟩, ?_⟩
      · simp only [setReg_ram, sampleFp_self, mul_zero, add_zero]
        rw [Function.update_eq_self_iff.mpr cell.symm]
      · simp only [setReg_registers]
        simp (config := {decide := true}) only [reduceIte]
      · simp only [setReg_registers]
        simp (config := {decide := true}) only [reduceIte]
      · rw [if_pos holds]
        rfl
    · unfold Replay.guardedElement
      rw [if_pos collector, rtree_loadAt_seq, jstarCell, rtree_cst_seq,
        rtree_ar_val _ _ _ _ _ _ (word (designatedSwitch bits).val) (word switch)
          (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), rtree_ite, reg_same,
        eval_xor, if_neg (fun zero => atStar ((word_xor_eq_zero (by omega) (by omega)).mp zero).symm)]
      exact plainAgree _ rfl rfl
        (by simp only [setReg_registers]; simp (config := {decide := true}) only [reduceIte])
        (by simp only [setReg_registers]; simp (config := {decide := true}) only [reduceIte])
        fun both => atStar both.1
  · unfold Replay.guardedElement
    rw [if_neg collector]
    exact plainAgree memory rfl rfl rfl rfl fun both => collector both.2

/-! ### The element loop of a designated-chunk switch -/

/-- The record entries the designated switch has set after `count` elements. -/
def RecordUpTo (bits : BitInput) (label : Block) (count : Nat) (record : Record) : Prop :=
  ∀ (digit : Fin digitCount) (collector block : Fin 3),
    (xElementIndex digit (collectorElement collector)).val < count →
      record (designatedIndex bits digit collector block) = some label

theorem recordAfter_designated [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (index : PlanB.FixedIndex) (input : Block) (record : Record) (designated : IsDesignated bits index) :
    recordAfter bits (.fixedForward index input) record = Function.update record index (some input) := by
  unfold recordAfter
  exact if_pos designated

theorem recordAfter_clean [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (index : PlanB.FixedIndex) (input : Block) (record : Record) (clean : ¬ IsDesignated bits index) :
    recordAfter bits (.fixedForward index input) record = record := by
  unfold recordAfter
  exact if_neg clean

omit [FieldCertificate] in
theorem designatedIndex_eq_desIdx (bits : BitInput) (digit : Fin digitCount) (collector block : Fin 3) :
    designatedIndex bits digit collector block =
      desIdx (designatedSwitch bits).val (xElementIndex digit (collectorElement collector)) block := rfl

/-- **`record3` keeps the entries it does not touch and sets its own.** -/
theorem recordUpTo_step [DecidableEq PlanB.FixedIndex] (bits : BitInput) (label : Block)
    (index : Fin pointElementCountX) (record : Record) (earlier : RecordUpTo bits label index.val record)
    (collector : Replay.isCollector index.val = true) :
    RecordUpTo bits label (index.val + 1)
      (record3 bits (designatedSwitch bits).val index label record) := by
  have jSmall : (designatedSwitch bits).val < 4 := (designatedSwitch bits).isLt
  have designated : ∀ block, IsDesignated bits (desIdx (designatedSwitch bits).val index block) :=
    fun block => (isDesignated_iff bits _ jSmall index block).mpr ⟨rfl, collector⟩
  intro digit c block small
  unfold record3
  rw [recordAfter_designated bits _ _ _ (designated 2), recordAfter_designated bits _ _ _ (designated 1),
    recordAfter_designated bits _ _ _ (designated 0), designatedIndex_eq_desIdx]
  by_cases same : xElementIndex digit (collectorElement c) = index
  · rw [same]
    simp only [Function.update_apply]
    fin_cases block <;> simp
  · have below : (xElementIndex digit (collectorElement c)).val < index.val := by
      have : (xElementIndex digit (collectorElement c)).val ≠ index.val := fun equal =>
        same (Fin.ext equal)
      omega
    have ne : ∀ b b', desIdx (designatedSwitch bits).val (xElementIndex digit (collectorElement c)) b ≠
        desIdx (designatedSwitch bits).val index b' := by
      intro b b' equal
      apply same
      have := congrArg (fun idx => match idx with | FixedIndex.scale _ _ _ e _ => e.val | _ => 0) equal
      simp only [desIdx] at this
      rw [scaleIndexOf_eq _ _ _ _ _ (lt_of_lt_of_le (xElementIndex digit (collectorElement c)).isLt
          (by unfold pointElementCountX elementCountX; omega)) (by unfold chunkBits; omega),
        scaleIndexOf_eq _ _ _ _ _ (lt_of_lt_of_le index.isLt
          (by unfold pointElementCountX elementCountX; omega)) (by unfold chunkBits; omega)] at this
      exact Fin.ext this
    rw [Function.update_of_ne (ne block 2), Function.update_of_ne (ne block 1),
      Function.update_of_ne (ne block 0), ← designatedIndex_eq_desIdx]
    exact earlier digit c block below

theorem recordUpTo_skip (bits : BitInput) (label : Block) (index : Nat) (record : Record)
    (earlier : RecordUpTo bits label index record) (plain : Replay.isCollector index = false) :
    RecordUpTo bits label (index + 1) record := by
  intro digit c block small
  refine earlier digit c block ?_
  rcases Nat.lt_succ_iff_lt_or_eq.mp small with below | equal
  · exact below
  · exfalso
    have slot := (isDesignated_iff bits (designatedSwitch bits).val (designatedSwitch bits).isLt
      (xElementIndex digit (collectorElement c)) block).mp ⟨digit, c, block, rfl⟩
    rw [equal] at slot
    rw [slot.2] at plain
    exact absurd plain (by decide)

/-- The invariant of the element loop of a designated-chunk switch. -/
def DesElemsInv (bits : BitInput) (switch : Nat) (label : Block) (acc0 : Nat → BaseField)
    (coef : BaseField) (start : Memory) (record0 : Record) (count : Nat)
    (state : Vector BaseField count × Record) (memory : Memory) : Prop :=
  (∀ e (bound : e < count),
      memory.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e + coef * state.1[e])) ∧
    (∀ address, (∀ e, e < count → address ≠ accCell Replay.pointXSpec e) →
      memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ memory.registers rInput = start.registers rInput ∧
    memory.registers rF = start.registers rF ∧
    (switch ≠ (designatedSwitch bits).val → state.2 = record0) ∧
    (switch = (designatedSwitch bits).val → RecordUpTo bits label count state.2)

/-- **The element loop of a designated-chunk switch.** -/
theorem agree_designatedElements [DecidableEq PlanB.FixedIndex] (bits : BitInput) (switch : Nat)
    (switchSmall : switch < 4) (start : Memory) (record0 : Record) (label : Block)
    (coef : BaseField) (acc0 : Nat → BaseField)
    (input : start.registers rInput = blockWord label) (factor : start.registers rF = fieldWord coef)
    (jstarCell : start.ram (word tmpJStar) = word (designatedSwitch bits).val)
    (cells : ∀ e, e < pointElementCountX → start.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e)) :
    Agree (DesElemsInv bits switch label acc0 coef start record0 pointElementCountX)
      (rtree (Prog.rep pointElementCountX (Replay.guardedElement ordF0 Replay.pointXSpec 0 switch)) start)
      (interceptT bits (FreeQuery.vector pointElementCountX fun e => elemProg (desIdx switch e) label)
        record0) := by
  have fits : Replay.pointXSpec.slot + pointElementCountX ≤ 824 := by decide
  refine agree_rep_vector bits _ (DesElemsInv bits switch label acc0 coef start record0)
    pointElementCountX _ ?_ record0 start
    ⟨fun e bound => absurd bound (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl,
      fun _ digit c block small => absurd small (Nat.not_lt_zero _)⟩
  intro e values record memory holds
  obtain ⟨accs, frame, bitsSame, inputSame, coefSame, offStar, atStar⟩ := holds
  have cell : memory.ram (word (accBase + Replay.pointXSpec.slot + e.val)) = fieldWord (acc0 e.val) := by
    rw [frame _ fun other bound => accCell_ne Replay.pointXSpec (by omega) (by omega) (by omega),
      cells e.val e.isLt]
  have star : memory.ram (word tmpJStar) = word (designatedSwitch bits).val := by
    rw [frame (word tmpJStar) fun other bound =>
      tmp_ne_acc Replay.pointXSpec (by decide) 6 (by omega) other
        (lt_trans bound (show e.val < Replay.pointXSpec.count from e.isLt)), jstarCell]
  refine (agree_guarded bits switch switchSmall e memory label coef (acc0 e.val) record
    (inputSame.trans input) (coefSame.trans factor) cell star).mono fun result after post => ?_
  obtain ⟨⟨ram, bitsAfter, inputAfter, coefAfter⟩, recordAfter⟩ := post
  refine ⟨fun other bound => ?_, fun address outside => ?_, bitsAfter.trans bitsSame,
    inputAfter.trans inputSame, coefAfter.trans coefSame, fun notStar => ?_, fun isStar => ?_⟩
  · rw [ram]
    by_cases last : other = e.val
    · subst last
      rw [Function.update_self, Vector.getElem_push_eq]
    · rw [Function.update_of_ne (accCell_ne Replay.pointXSpec (by omega) (by omega) last),
        Vector.getElem_push_lt (by omega)]
      exact accs other (by omega)
  · rw [ram, Function.update_of_ne (outside e.val (by omega)),
      frame address fun other bound => outside other (by omega)]
  · rw [recordAfter, if_neg fun both => notStar both.1]
    exact offStar notStar
  · have earlier := atStar isStar
    by_cases collector : Replay.isCollector e.val = true
    · rw [recordAfter, if_pos ⟨isStar, collector⟩, isStar]
      exact recordUpTo_step bits label e record earlier collector
    · rw [recordAfter, if_neg fun both => collector both.2]
      exact recordUpTo_skip bits label e.val record earlier (by simpa using collector)

end

end Kriterion.ArgoMAC.PlanB.SimMachine