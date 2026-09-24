/-
**Stage 2, the program batch** (`rsem_programs`): the `819` machine programs `E* ↦ o_b ⊕ E*` of
`Opening.programs` (digit → collector → block, the index selected on `j*`) are P3's
`programAll (programRequests …)`, from any memory holding `E*`, `j*` and the limbs; the RAM and the
stacks are unchanged. Also: the split of `Opening.program` into `openingFree` and the batch, and
the oracle-freeness of `openingFree`.
-/

import Proof.Simulator.ReplayProgram
import Proof.Simulator.Stage2Spec

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A machine block's law at the `planBSimulator` index instances. -/
abbrev rsem (program : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (Memory × OState PlanB.FixedIndex EncPRF.PermutationIndex)) :=
  @Prog.sem _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _) (Fintype.ofFinite _) _ _
    program memory oracle

/-! ### Sequencing -/

theorem rsem_seq (first second : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq first second) memory oracle = andThen (rsem first) (rsem second) memory oracle := rfl

theorem rsem_seq_pure (first rest : Prog) (memory after : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex)
    (run : rsem first memory oracle = PMF.pure (some (after, oracle))) :
    rsem (.seq first rest) memory oracle = rsem rest after oracle := by
  rw [rsem_seq]
  unfold andThen
  rw [run, PMF.pure_bind]

theorem rsem_seq_skip (first : Prog) (count : Nat) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq first (.skip count)) memory oracle = rsem first memory oracle := by
  rw [rsem_seq]
  unfold andThen
  conv_rhs => rw [← PMF.bind_pure (rsem first memory oracle)]
  congr 1
  funext result
  rcases result with _ | ⟨next, updated⟩ <;> rfl

theorem rsem_skip (count : Nat) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.skip count) memory oracle = PMF.pure (some (memory, oracle)) := rfl

/-- `seqList` of an append is the sequence of the two parts. -/
theorem rsem_seqList_append (first second : List Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (Prog.seqList (first ++ second)) memory oracle =
      andThen (rsem (Prog.seqList first)) (rsem (Prog.seqList second)) memory oracle := by
  induction first generalizing memory oracle with
  | nil =>
      rw [List.nil_append]
      show _ = andThen (rsem (.skip 0)) _ memory oracle
      unfold andThen
      rw [rsem_skip, PMF.pure_bind]
  | cons head rest ih =>
      rw [List.cons_append]
      show rsem (.seq head (Prog.seqList (rest ++ second))) memory oracle =
        andThen (rsem (.seq head (Prog.seqList rest))) _ memory oracle
      rw [rsem_seq]
      unfold andThen
      rw [rsem_seq]
      unfold andThen
      rw [PMF.bind_bind]
      congr 1
      funext result
      rcases result with _ | ⟨next, updated⟩
      · simp only [PMF.pure_bind]
      · exact ih next updated

/-- A tree block runs as its tree. -/
theorem rsem_of_tree (program : Prog) (ops : program.OpsSatisfy TreeOp) (memory after : Memory)
    (run : rtree program memory = .pure (some after))
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem program memory oracle = PMF.pure (some (after, oracle)) := by
  rw [rsem, @sem_eq_runT _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
    (Fintype.ofFinite _) _ _ program ops memory oracle]
  change (runT (rtree program memory) oracle).map lower = _
  rw [run]
  simp [runT, lower, PMF.pure_map]

/-! ### The index selection -/

theorem rtree_selectStep (digit collector block jstar switch : Nat) (jSmall : jstar < 4)
    (switchSmall : switch < 4) (memory : Memory)
    (jCell : memory.ram (word tmpJStar) = word jstar) :
    ∃ after, rtree (Prog.seqList [loadAt rA tmpJStar, cst rB switch, ar .xor rA rA rB,
        .ite rA (.skip 0) (cst rIndex (ordF0 (Replay.scaleIdx .pointX 0 switch
          (5 * digit + Opening.collectorSlot collector) block)))]) memory = .pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rIndex = (if jstar = switch then word (ordF0 (Replay.scaleIdx .pointX 0 switch
          (5 * digit + Opening.collectorSlot collector) block)) else memory.registers rIndex) ∧
      after.registers rInput = memory.registers rInput ∧
      after.registers rFirst = memory.registers rFirst := by
  have jWord : jstar < 2 ^ 256 := by omega
  have switchWord : switch < 2 ^ 256 := by omega
  simp only [Prog.seqList]
  rw [rtree_loadAt_seq, jCell, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word jstar) (word switch)
      (by rw [reg_ne _ _ _ _ (by decide), reg_same]) (reg_same _ _ _), eval_xor, rtree_seq,
    rtree_ite, reg_same]
  by_cases same : jstar = switch
  · rw [if_pos ((word_xor_eq_zero jWord switchWord).mpr same), if_pos same]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [setReg_ram]
    · simp only [setReg_bits]
    · rw [reg_same]
    · simp (config := {decide := true}) only [setReg_registers, reduceIte]
    · simp (config := {decide := true}) only [setReg_registers, reduceIte]
  · rw [if_neg (fun zero => same ((word_xor_eq_zero jWord switchWord).mp zero)), if_neg same]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [setReg_ram]
    · simp only [setReg_bits]
    · simp (config := {decide := true}) only [setReg_registers, reduceIte]
    · simp (config := {decide := true}) only [setReg_registers, reduceIte]
    · simp (config := {decide := true}) only [setReg_registers, reduceIte]

theorem rtree_selectLoop (digit collector block jstar : Nat) (jSmall : jstar < 4) (memory : Memory)
    (jCell : memory.ram (word tmpJStar) = word jstar) :
    ∀ count, count ≤ 4 → ∃ after, rtree (Prog.rep count fun switch =>
        Prog.seqList [loadAt rA tmpJStar, cst rB switch, ar .xor rA rA rB,
          .ite rA (.skip 0) (cst rIndex (ordF0 (Replay.scaleIdx .pointX 0 switch
            (5 * digit + Opening.collectorSlot collector) block)))]) memory = .pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rIndex = (if jstar < count then word (ordF0 (Replay.scaleIdx .pointX 0 jstar
          (5 * digit + Opening.collectorSlot collector) block)) else memory.registers rIndex) ∧
      after.registers rInput = memory.registers rInput ∧
      after.registers rFirst = memory.registers rFirst
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, rfl, rfl, by rw [if_neg (by omega)], rfl, rfl⟩
  | count + 1, bound => by
      obtain ⟨middle, run, ram, bitsSame, index, input, first⟩ :=
        rtree_selectLoop digit collector block jstar jSmall memory jCell count (by omega)
      obtain ⟨after, run', ram', bits', index', input', first'⟩ :=
        rtree_selectStep digit collector block jstar count jSmall (by omega) middle
          (by rw [ram, jCell])
      refine ⟨after, by rw [Prog.rep, rtree_seq, run, bindOpt_pure]; exact run', ram'.trans ram,
        bits'.trans bitsSame, ?_, input'.trans input, first'.trans first⟩
      rw [index']
      by_cases same : jstar = count
      · subst same
        rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg same, index]
        by_cases below : jstar < count
        · rw [if_pos below, if_pos (by omega)]
        · rw [if_neg below, if_neg (by omega)]

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem select_ops (digit collector block switch : Nat) :
    (Prog.seqList [loadAt rA tmpJStar, cst rB switch, ar .xor rA rA rB,
      .ite rA (.skip 0) (cst rIndex (ordF0 (Replay.scaleIdx .pointX 0 switch
        (5 * digit + Opening.collectorSlot collector) block)))]).OpsSatisfy TreeOp :=
  ⟨⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial⟩

/-! ### One program -/

theorem rsem_loadAt_seq (target : Register) (address : Nat) (rest : Prog) (memory : Memory)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq (loadAt target address) rest) memory oracle =
      rsem rest (setReg (setReg memory rAddr (word address)) target (memory.ram (word address)))
        oracle :=
  rsem_seq_pure _ _ _ _ _ (rsem_of_tree (loadAt target address) ⟨trivial, trivial⟩ memory _ rfl oracle)

theorem rsem_ar_seq (operation : Arithmetic) (target left right : Register) (rest : Prog)
    (memory : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (.seq (ar operation target left right) rest) memory oracle =
      rsem rest (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))) oracle :=
  rsem_seq_pure _ _ _ _ _ (rsem_of_tree (ar operation target left right) trivial memory _ rfl oracle)

/-- **One program** `E* ↦ o ⊕ E*` at the index of `(d, c, b)` at switch `j`. -/
theorem rsem_programOne (digit collector block jstar : Nat) (jSmall : jstar < 4) (memory : Memory)
    (star limb : Block) (starCell : memory.ram (word (hotLabelBase + 4)) = blockWord star)
    (limbCell : memory.ram (word (openLimb digit collector block)) = blockWord limb)
    (jCell : memory.ram (word tmpJStar) = word jstar) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem (Opening.programOne ordF0 digit collector block) memory oracle =
        PMF.pure ((LazyOracle.program (.fixedForward (Replay.scaleIdx .pointX 0 jstar
            (5 * digit + Opening.collectorSlot collector) block) star) (limb ^^^ star) oracle).map
          fun updated => (after, updated)) := by
  set m1 := setReg (setReg memory rAddr (word (hotLabelBase + 4))) rInput
    (memory.ram (word (hotLabelBase + 4))) with m1Def
  set m2 := setReg (setReg m1 rAddr (word (openLimb digit collector block))) rFirst
    (m1.ram (word (openLimb digit collector block))) with m2Def
  set loaded := setReg m2 rFirst (Arithmetic.xor.eval (m2.registers rFirst) (m2.registers rInput))
    with loadedDef
  have loadedRam : loaded.ram = memory.ram := by simp only [loadedDef, m2Def, m1Def, setReg_ram]
  have loadedBits : loaded.bits = memory.bits := by simp only [loadedDef, m2Def, m1Def, setReg_bits]
  have loadedInput : loaded.registers rInput = blockWord star := by
    simp (config := {decide := true}) only [loadedDef, m2Def, m1Def, setReg_registers, reduceIte]
    exact starCell
  have loadedFirst : loaded.registers rFirst = blockWord (limb ^^^ star) := by
    have first : m2.registers rFirst = blockWord limb := by
      simp only [m2Def, reg_same, m1Def, setReg_ram]
      exact limbCell
    have input : m2.registers rInput = blockWord star := by
      simp (config := {decide := true}) only [m2Def, m1Def, setReg_registers, reduceIte]
      exact starCell
    rw [loadedDef, reg_same, first, input, eval_xor, blockWord_xor]
  obtain ⟨selected, runSelect, ramSelect, bitsSelect, indexSelect, inputSelect, firstSelect⟩ :=
    rtree_selectLoop digit collector block jstar jSmall loaded (by rw [loadedRam, jCell]) 4 le_rfl
  refine ⟨selected, by rw [ramSelect, loadedRam], by rw [bitsSelect, loadedBits], fun oracle => ?_⟩
  unfold Opening.programOne
  simp only [Prog.seqList]
  rw [rsem_loadAt_seq, rsem_loadAt_seq, rsem_ar_seq, ← m1Def, ← m2Def, ← loadedDef]
  unfold Opening.selectIndex
  rw [rsem_seq_pure _ _ _ _ _ (rsem_of_tree _ (opsSatisfy_rep _ _ fun switch _ =>
      select_ops digit collector block switch) _ _ runSelect oracle), rsem_seq_skip]
  have indexSel : selected.registers rIndex = word (ordF0 (Replay.scaleIdx .pointX 0 jstar
      (5 * digit + Opening.collectorSlot collector) block)) := by
    rw [indexSelect, if_pos jSmall]
  simp only [rsem, Prog.sem, Op.sem]
  rw [indexSel, inputSelect.trans loadedInput, firstSelect.trans loadedFirst, query_fixed,
    blockWord_block]
  simp only [answerFromWords, blockWord_block]

/-! ### The batch -/

omit [FieldCertificate] in
theorem programAll_append (first second : List (PlanB.FixedIndex × Option Block × Block))
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    programAll (first ++ second) oracle = (programAll first oracle).bind (programAll second) := by
  induction first generalizing oracle with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨index, input, output⟩ := head
      cases input with
      | none => rfl
      | some input =>
          simp only [List.cons_append, programAll]
          rw [Option.bind_assoc]
          congr 1
          funext updated
          exact ih updated

omit [FieldCertificate] in
theorem programAll_single (index : PlanB.FixedIndex) (input output : Block)
    (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    programAll [(index, some input, output)] oracle =
      LazyOracle.program (.fixedForward index input) (output ^^^ input) oracle := by
  show (LazyOracle.program (.fixedForward index input) (output ^^^ input) oracle).bind
    (programAll []) = _
  cases LazyOracle.program (.fixedForward index input) (output ^^^ input) oracle <;> rfl

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem finRange_flatMap_succ {β : Type} (count : Nat) (f : Nat → List β) :
    (List.finRange (count + 1)).flatMap (fun index => f index.val) =
      (List.finRange count).flatMap (fun index => f index.val) ++ f count := by
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp

/-- **A batch of programs**: a `rep` whose steps are programs is the program list. -/
theorem rsem_rep_programs (count : Nat) (body : Nat → Prog)
    (requests : Nat → List (PlanB.FixedIndex × Option Block × Block)) (ram0 : Word → Word)
    (bits0 : Fin 4 → List Bool)
    (step : ∀ index memory, index < count → memory.ram = ram0 → memory.bits = bits0 →
      ∃ after, after.ram = ram0 ∧ after.bits = bits0 ∧ ∀ oracle,
        rsem (body index) memory oracle =
          PMF.pure ((programAll (requests index) oracle).map fun updated => (after, updated))) :
    ∀ done memory, done ≤ count → memory.ram = ram0 → memory.bits = bits0 →
      ∃ after, after.ram = ram0 ∧ after.bits = bits0 ∧ ∀ oracle,
        rsem (Prog.rep done body) memory oracle =
          PMF.pure ((programAll ((List.finRange done).flatMap fun index => requests index.val)
            oracle).map fun updated => (after, updated))
  | 0, memory, _, ram, bits => ⟨memory, ram, bits, fun oracle => by rw [Prog.rep]; rfl⟩
  | done + 1, memory, bound, ram, bits => by
      obtain ⟨middle, middleRam, middleBits, run⟩ :=
        rsem_rep_programs count body requests ram0 bits0 step done memory (by omega) ram bits
      obtain ⟨after, afterRam, afterBits, run'⟩ := step done middle (by omega) middleRam middleBits
      refine ⟨after, afterRam, afterBits, fun oracle => ?_⟩
      rw [Prog.rep, rsem_seq]
      unfold andThen
      rw [run, PMF.pure_bind, finRange_flatMap_succ, programAll_append]
      cases programAll ((List.finRange done).flatMap fun index => requests index.val) oracle with
      | none => rfl
      | some updated =>
          simp only [Option.map_some, Option.bind_some]
          exact run' updated

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem collectorSlot_eq (digit : Fin digitCount) (collector : Fin 3) :
    5 * digit.val + Opening.collectorSlot collector.val =
      (xElementIndex digit (collectorElement collector)).val := by
  fin_cases collector <;> rfl

omit [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem scaleIdx_designated (bits : BitInput) (digit : Fin digitCount) (collector block : Fin 3) :
    Replay.scaleIdx .pointX 0 (designatedSwitch bits).val
        (5 * digit.val + Opening.collectorSlot collector.val) block.val =
      designatedIndex bits digit collector block := by
  rw [collectorSlot_eq, scaleIdx_des, designatedIndex_eq_desIdx]

/-- The requests of one (digit, collector, block), by natural numbers. -/
def natRequest (bits : BitInput) (star : Block)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (digit collector block : Nat) :
    List (PlanB.FixedIndex × Option Block × Block) :=
  if inside : digit < digitCount ∧ collector < 3 ∧ block < 3 then
    [(designatedIndex bits ⟨digit, inside.1⟩ ⟨collector, inside.2.1⟩ ⟨block, inside.2.2⟩, some star,
      limbAt ⟨block, inside.2.2⟩ (blocks (⟨digit, inside.1⟩, ⟨collector, inside.2.1⟩)))]
  else []

/-- **The `819` programs.** -/
theorem rsem_programs (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (star : Block) (memory : Memory)
    (recorded : RecordUpTo bits star pointElementCountX record)
    (starCell : memory.ram (word (hotLabelBase + 4)) = blockWord star)
    (limbCells : ∀ (digit : Fin digitCount) (collector block : Fin 3),
      memory.ram (word (openLimb digit.val collector.val block.val)) =
        blockWord (limbAt block (blocks (digit, collector))))
    (jCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem (Opening.programs ordF0) memory oracle =
        PMF.pure ((programAll (programRequests bits record blocks) oracle).map
          fun updated => (after, updated)) := by
  have jSmall : (designatedSwitch bits).val < 4 := (designatedSwitch bits).isLt
  have blockStep : ∀ (digit : Fin digitCount) (collector : Fin 3) (block : Nat) (inner : Memory),
      block < 3 → inner.ram = memory.ram → inner.bits = memory.bits →
      ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
        rsem (Opening.programOne ordF0 digit.val collector.val block) inner oracle =
          PMF.pure ((programAll (natRequest bits star blocks digit.val collector.val block)
            oracle).map fun updated => (after, updated)) := by
    intro digit collector block inner small ram bitsSame
    obtain ⟨after, afterRam, afterBits, run⟩ := rsem_programOne digit.val collector.val block
      (designatedSwitch bits).val jSmall inner star
      (limbAt ⟨block, small⟩ (blocks (digit, collector))) (by rw [ram, starCell])
      (by rw [ram]; exact limbCells digit collector ⟨block, small⟩) (by rw [ram, jCell])
    refine ⟨after, afterRam.trans ram, afterBits.trans bitsSame, fun oracle => ?_⟩
    rw [run oracle]
    unfold natRequest
    rw [dif_pos ⟨digit.isLt, collector.isLt, small⟩, programAll_single]
    rw [show Replay.scaleIdx .pointX 0 (designatedSwitch bits).val
        (5 * digit.val + Opening.collectorSlot collector.val) block =
      designatedIndex bits ⟨digit.val, digit.isLt⟩ ⟨collector.val, collector.isLt⟩ ⟨block, small⟩ from
      scaleIdx_designated bits digit collector ⟨block, small⟩]
  have collectorStep : ∀ (digit : Fin digitCount) (collector : Nat) (inner : Memory),
      collector < 3 → inner.ram = memory.ram → inner.bits = memory.bits →
      ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
        rsem (Prog.rep 3 fun block => Opening.programOne ordF0 digit.val collector block) inner
            oracle =
          PMF.pure ((programAll ((List.finRange 3).flatMap fun block =>
            natRequest bits star blocks digit.val collector block.val) oracle).map
              fun updated => (after, updated)) := by
    intro digit collector inner small ram bitsSame
    exact rsem_rep_programs 3 _ _ memory.ram memory.bits
      (fun block inner' bound ram' bits' => blockStep digit ⟨collector, small⟩ block inner' bound ram'
        bits') 3 inner le_rfl ram bitsSame
  have digitStep : ∀ (digit : Nat) (inner : Memory),
      digit < digitCount → inner.ram = memory.ram → inner.bits = memory.bits →
      ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
        rsem (Prog.rep 3 fun collector => Prog.rep 3 fun block =>
            Opening.programOne ordF0 digit collector block) inner oracle =
          PMF.pure ((programAll ((List.finRange 3).flatMap fun collector =>
            (List.finRange 3).flatMap fun block =>
              natRequest bits star blocks digit collector.val block.val) oracle).map
              fun updated => (after, updated)) := by
    intro digit inner small ram bitsSame
    exact rsem_rep_programs 3 _ _ memory.ram memory.bits
      (fun collector inner' bound ram' bits' => collectorStep ⟨digit, small⟩ collector inner' bound
        ram' bits') 3 inner le_rfl ram bitsSame
  obtain ⟨after, afterRam, afterBits, run⟩ := rsem_rep_programs digitCount _ _ memory.ram
    memory.bits (fun digit inner bound ram bitsSame => digitStep digit inner bound ram bitsSame)
    digitCount memory le_rfl rfl rfl
  refine ⟨after, afterRam, afterBits, fun oracle => (run oracle).trans ?_⟩
  simp only [programRequests]
  congr 3
  congr 1
  funext digit
  congr 1
  funext collector
  rw [List.map_eq_flatMap]
  congr 1
  funext block
  unfold natRequest
  rw [dif_pos ⟨digit.isLt, collector.isLt, block.isLt⟩, recorded digit collector block
    (xElementIndex digit (collectorElement collector)).isLt]

/-! ### The opening, split -/

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
/-- `openingFree` makes no oracle call. -/
theorem openingFree_noOracle : openingFree.NoOracle := by
  unfold openingFree
  simp only [Prog.seqList]
  have curveRoot (source : Register) : (Opening.curveRoot source).NoOracle := by
    unfold Opening.curveRoot
    simp only [Prog.seqList]
    exact ⟨rfl, rfl, rfl, rfl, rfl, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.sqrtRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  have betaMul : Opening.betaMul.NoOracle := by
    unfold Opening.betaMul Opening.copyPoint Opening.clearP
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, ⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
      unfold Opening.betaRound
      exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.tailOne
      simp only [Prog.seqList]
      refine ⟨noOracle_bounded _ _ _ _ ?_ ?_, noOracle_zeroRegs _, trivial⟩
      · unfold Opening.testCurveX
        simp only [Prog.seqList]
        exact ⟨rfl, rfl, curveRoot _, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · unfold Opening.storeCurvePoint
        simp only [Prog.seqList]
        exact ⟨curveRoot _, ⟨rfl, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, trivial⟩
  · unfold Opening.horner Opening.clearP Opening.head Opening.storePoint
    simp only [Prog.seqList]
    exact ⟨⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.hornerStep Opening.loadPoint
        simp only [Prog.seqList]
        exact ⟨betaMul, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, trivial⟩),
      ⟨betaMul, ⟨⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩, trivial⟩,
        trivial⟩, trivial⟩
  · exact noOracle_rep _ _ fun _ _ =>
      ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.liftOne Opening.loadPoint
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
        noOracle_zeroRegs _, trivial⟩
  · exact noOracle_rep _ _ fun _ _ => by
      unfold Opening.solveDigit Opening.addScaled Opening.addCell Opening.finishTarget
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, ⟨rfl, rfl⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩,
        ⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩, ⟨⟨rfl, rfl⟩, rfl, trivial⟩,
        ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩
  · exact noOracle_rep _ _ fun _ _ => noOracle_rep _ _ fun _ _ => by
      unfold Opening.preimageOne Opening.limbsOf Opening.shr128
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, noOracle_bounded _ _ _ _ rfl ⟨rfl, rfl⟩,
        noOracle_zeroRegs _,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, noOracle_zeroRegs _, trivial⟩,
        trivial⟩

theorem rtree_zeroRegs (registers : List Register) (memory : Memory) :
    ∃ after, rtree (zeroRegs registers) memory = .pure (some after) ∧ after.ram = memory.ram ∧
      after.bits = memory.bits := by
  induction registers generalizing memory with
  | nil => exact ⟨memory, rfl, rfl, rfl⟩
  | cons register rest ih =>
      obtain ⟨after, run, ram, bitsSame⟩ := ih (setReg memory register (word 0))
      exact ⟨after, by rw [zeroRegs, rtree_cst_seq, run], ram, bitsSame⟩

omit [FieldCertificate] [DecidableEq PlanB.FixedIndex] [DecidableEq EncPRF.PermutationIndex] in
theorem zeroRegs_treeOps (registers : List Register) : (zeroRegs registers).OpsSatisfy TreeOp := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨trivial, ih⟩

/-- **The opening, split**: the oracle-free part, then the batch and the register clear. -/
theorem rsem_opening (memory : Memory) (oracle : OState PlanB.FixedIndex EncPRF.PermutationIndex) :
    rsem (Opening.program ordF0) memory oracle =
      (openingFree.memSem memory).bind fun result => match result with
        | none => PMF.pure none
        | some next => rsem (Prog.seqList [Opening.programs ordF0, zeroRegs allRegisters]) next
            oracle := by
  have free : rsem openingFree memory oracle =
      (openingFree.memSem memory).map (Option.map fun next => (next, oracle)) :=
    @sem_noOracle _ PlanB.FixedIndex EncPRF.PermutationIndex (Fintype.ofFinite _)
      (Fintype.ofFinite _) _ _ openingFree openingFree_noOracle memory oracle
  rw [show Opening.program ordF0 = Prog.seqList ([Opening.tail, Opening.horner, Opening.lambdas,
      Opening.lifts, Opening.solve, Opening.preimages] ++
      [Opening.programs ordF0, zeroRegs allRegisters]) from rfl, rsem_seqList_append,
    show Prog.seqList [Opening.tail, Opening.horner, Opening.lambdas, Opening.lifts, Opening.solve,
      Opening.preimages] = openingFree from rfl]
  unfold andThen
  rw [free, PMF.bind_map]
  congr 1
  funext result
  cases result <;> rfl

/-- **The batch and the register clear.** -/
theorem rsem_programsTail (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (star : Block) (memory : Memory)
    (recorded : RecordUpTo bits star pointElementCountX record)
    (starCell : memory.ram (word (hotLabelBase + 4)) = blockWord star)
    (limbCells : ∀ (digit : Fin digitCount) (collector block : Fin 3),
      memory.ram (word (openLimb digit.val collector.val block.val)) =
        blockWord (limbAt block (blocks (digit, collector))))
    (jCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val) :
    ∃ after, after.ram = memory.ram ∧ after.bits = memory.bits ∧ ∀ oracle,
      rsem (Prog.seqList [Opening.programs ordF0, zeroRegs allRegisters]) memory oracle =
        PMF.pure ((programAll (programRequests bits record blocks) oracle).map
          fun updated => (after, updated)) := by
  obtain ⟨middle, middleRam, middleBits, run⟩ :=
    rsem_programs bits record blocks star memory recorded starCell limbCells jCell
  obtain ⟨after, runZero, afterRam, afterBits⟩ := rtree_zeroRegs allRegisters middle
  refine ⟨after, afterRam.trans middleRam, afterBits.trans middleBits, fun oracle => ?_⟩
  simp only [Prog.seqList]
  rw [rsem_seq]
  unfold andThen
  rw [run oracle, PMF.pure_bind]
  cases programAll (programRequests bits record blocks) oracle with
  | none => rfl
  | some updated =>
      simp only [Option.map_some]
      rw [rsem_seq_skip, rsem_of_tree _ (zeroRegs_treeOps _) _ _ runZero updated]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
