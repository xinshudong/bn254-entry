/-
Which oracle instructions the machine issues.

* **Stage 1 issues none.** `Stage1.program` is `NoOracle`, so its law is an oracle-free law on
  memory and leaves the lazy oracle untouched (`sem_noOracle`); with `stage1_run`, the whole
  stage-1 run returns the incoming oracle state unchanged (`stage1_run_oracle`).
* **The invalid branch issues none**: the stage-2 prefix and `Stage2.invalid` are `NoOracle`
  (`stage2_invalid_oracle`).
* **The valid branch issues only the four fixed shapes** `query 0` (fixed forward), `query 2`
  (EncPRF forward), `query 4` (hash) and `program 0` (fixed forward), all on the operand
  registers `R12 … R15` (`valid_oracleOps`); every constant loaded into the index register is
  the ordinal of a fold index `hotIdx`, a scale index `scaleIdx`, or an EncPRF index `encIdx`
  (`valid_indexConstants`).
-/

import Proof.Simulator.Runs

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography Cryptography.BoundedMachine Design Blocks

/-! ### Oracle-free programs -/

/-- Does an operation touch the oracle? -/
def Op.isOracle : Op → Bool
  | .query .. | .lookup .. | .program .. => true
  | _ => false

/-- A program with no oracle operation. -/
def Prog.NoOracle : Prog → Prop
  | .op operation => operation.isOracle = false
  | .popBit _ _ | .skip _ | .abort _ => True
  | .seq first second => first.NoOracle ∧ second.NoOracle
  | .ite _ whenSet whenClear => whenSet.NoOracle ∧ whenClear.NoOracle

section MemoryLaw

variable [BN254.FieldCertificate]

/-- The law of a straight-line operation on memory alone (oracle operations abort). -/
noncomputable def Op.memSem (operation : Op) (memory : Memory) : PMF (Option Memory) :=
  match operation with
  | .constant target value => PMF.pure (some (setReg memory target value))
  | .arith operation target left right =>
      PMF.pure (some (setReg memory target
        (operation.eval (memory.registers left) (memory.registers right))))
  | .load target address =>
      PMF.pure (some (setReg memory target (memory.ram (memory.registers address))))
  | .store address source =>
      PMF.pure (some (storeRam memory (memory.registers address) (memory.registers source)))
  | .push stack bit => PMF.pure (some (pushOn memory stack bit))
  | .pushBit stack source => PMF.pure (some (pushOn memory stack ((memory.registers source).getLsbD 0)))
  | .coin stack => (PMF.uniformOfFintype Bool).bind fun bit => PMF.pure (some (pushOn memory stack bit))
  | .pointAdd target left right =>
      match readPoint memory.registers left, readPoint memory.registers right with
      | some a, some b => PMF.pure (some (writePointMem memory target (a + b)))
      | _, _ => PMF.pure none
  | .query .. | .lookup .. | .program .. => PMF.pure none

/-- The law of an oracle-free program on memory alone. -/
noncomputable def Prog.memSem : Prog → Memory → PMF (Option Memory)
  | .op operation, memory => operation.memSem memory
  | .popBit stack target, memory => PMF.pure (some (popInto memory stack target))
  | .skip _, memory => PMF.pure (some memory)
  | .abort _, _ => PMF.pure none
  | .seq first second, memory => (first.memSem memory).bind fun result => match result with
      | none => PMF.pure none
      | some next => second.memSem next
  | .ite source whenSet whenClear, memory =>
      if memory.registers source = 0 then whenClear.memSem memory else whenSet.memSem memory

variable {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
  [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- **An oracle-free program neither reads nor changes the oracle.** -/
theorem sem_noOracle : ∀ (program : Prog), program.NoOracle →
    ∀ (memory : Memory) (oracle : OState FixedIndex EncIndex),
      program.sem memory oracle = (program.memSem memory).map (Option.map fun next => (next, oracle))
  | .op operation, free, memory, oracle => by
      cases operation with
      | query => simp [Prog.NoOracle, Op.isOracle] at free
      | lookup => simp [Prog.NoOracle, Op.isOracle] at free
      | program => simp [Prog.NoOracle, Op.isOracle] at free
      | pointAdd target left right =>
          simp only [Prog.sem, Prog.memSem, Op.sem, Op.memSem]
          cases readPoint memory.registers left <;> cases readPoint memory.registers right <;>
            simp [PMF.pure_map]
      | coin stack => simp [Prog.sem, Prog.memSem, Op.sem, Op.memSem, PMF.map_bind, PMF.pure_map]
      | _ => simp [Prog.sem, Prog.memSem, Op.sem, Op.memSem, PMF.pure_map]
  | .popBit _ _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .skip _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .abort _, _, memory, oracle => by simp [Prog.sem, Prog.memSem, PMF.pure_map]
  | .seq first second, free, memory, oracle => by
      simp only [Prog.sem, Prog.memSem, andThen, PMF.map_bind]
      rw [sem_noOracle first free.1 memory oracle, PMF.bind_map]
      congr 1
      funext result
      cases result with
      | none => simp [PMF.pure_map]
      | some next => simp only [Function.comp_apply, Option.map_some]; exact sem_noOracle second free.2 next oracle
  | .ite source whenSet whenClear, free, memory, oracle => by
      simp only [Prog.sem, Prog.memSem]
      split
      · exact sem_noOracle whenClear free.2 memory oracle
      · exact sem_noOracle whenSet free.1 memory oracle

end MemoryLaw

theorem noOracle_rep (count : Nat) (body : Nat → Prog)
    (free : ∀ index, index < count → (body index).NoOracle) : (Prog.rep count body).NoOracle := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => free index (by omega), free count (by omega)⟩

theorem noOracle_zeroRegs (registers : List Register) : (zeroRegs registers).NoOracle := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨rfl, ih⟩

theorem noOracle_sampleWord (width : Nat) : (sampleWord width).NoOracle :=
  ⟨rfl, noOracle_rep _ _ fun _ _ => ⟨⟨rfl, trivial⟩, rfl, rfl⟩⟩

theorem noOracle_bounded (width : Nat) (test use : Prog) (count : Nat)
    (freeTest : test.NoOracle) (freeUse : use.NoOracle) :
    (bounded width test count use).NoOracle :=
  ⟨⟨rfl, rfl, noOracle_rep _ _ fun _ _ =>
    ⟨noOracle_sampleWord width, freeTest, rfl, rfl, rfl, rfl, rfl⟩⟩, freeUse, trivial⟩

theorem noOracle_emitWord (address width : Nat) : (emitWord address width).NoOracle :=
  ⟨⟨rfl, rfl⟩, noOracle_rep _ _ fun _ _ => ⟨rfl, rfl, rfl⟩⟩

/-- **Stage 1 has no oracle instruction.** -/
theorem stage1_noOracle : Stage1.program.NoOracle := by
  refine ⟨noOracle_rep _ _ fun _ _ => ?_, noOracle_rep _ _ fun _ _ => ?_,
    noOracle_rep _ _ fun _ _ => ?_, noOracle_rep _ _ fun _ _ => ?_, ?_, noOracle_zeroRegs _⟩
  · exact ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact ⟨noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact ⟨noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact ⟨noOracle_sampleWord _, ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩
  · exact ⟨noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _,
      noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _,
      noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _,
      noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _⟩

theorem noOracle_parseWord (address : Nat) : (Request.parseWord address).NoOracle :=
  ⟨rfl, noOracle_rep _ _ (fun _ _ => ⟨trivial, rfl, rfl, rfl⟩), rfl, rfl⟩

/-- **The stage-2 prefix has no oracle instruction.** -/
theorem prefix_noOracle : Request.prefixProgram.NoOracle :=
  ⟨⟨noOracle_parseWord _, noOracle_parseWord _, trivial, ⟨rfl, rfl⟩, trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
      ⟨⟨noOracle_parseWord _, noOracle_parseWord _⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
      noOracle_zeroRegs _⟩,
    ⟨noOracle_rep _ _ fun _ _ => ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩,
      noOracle_zeroRegs _⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- **The invalid arm has no oracle instruction.** -/
theorem invalid_noOracle : Stage2.invalid.NoOracle :=
  noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _

/-! ### The valid arm's oracle operations -/

/-- The oracle operations the valid arm may issue: fixed forward (`0`), EncPRF forward (`2`) and
hash (`4`) queries, and fixed forward (`0`) programs, on the fixed operands `R12 … R15`; no
lookup. -/
def ValidOracle : Op → Prop
  | .query kind index input first second =>
      (kind = 0 ∨ kind = 2 ∨ kind = 4) ∧ index = rIndex ∧ input = rInput ∧ first = rFirst ∧
        second = rSecond
  | .program kind index input first second =>
      kind = 0 ∧ index = rIndex ∧ input = rInput ∧ first = rFirst ∧ second = rSecond
  | .lookup .. => False
  | _ => True

/-- Every operation of a program satisfies `allowed`. -/
def Prog.OpsSatisfy (allowed : Op → Prop) : Prog → Prop
  | .op operation => allowed operation
  | .popBit _ _ | .skip _ | .abort _ => True
  | .seq first second => first.OpsSatisfy allowed ∧ second.OpsSatisfy allowed
  | .ite _ whenSet whenClear => whenSet.OpsSatisfy allowed ∧ whenClear.OpsSatisfy allowed

theorem opsSatisfy_of_noOracle {allowed : Op → Prop}
    (plain : ∀ operation : Op, operation.isOracle = false → allowed operation) :
    ∀ program : Prog, program.NoOracle → program.OpsSatisfy allowed
  | .op operation, free => plain operation free
  | .popBit _ _, _ | .skip _, _ | .abort _, _ => trivial
  | .seq first second, free =>
      ⟨opsSatisfy_of_noOracle plain first free.1, opsSatisfy_of_noOracle plain second free.2⟩
  | .ite _ whenSet whenClear, free =>
      ⟨opsSatisfy_of_noOracle plain whenSet free.1, opsSatisfy_of_noOracle plain whenClear free.2⟩

theorem validOracle_plain (operation : Op) (plain : operation.isOracle = false) :
    ValidOracle operation := by
  cases operation <;> simp_all [ValidOracle, Op.isOracle]

theorem opsSatisfy_rep {allowed : Op → Prop} (count : Nat) (body : Nat → Prog)
    (each : ∀ index, index < count → (body index).OpsSatisfy allowed) :
    (Prog.rep count body).OpsSatisfy allowed := by
  induction count with
  | zero => rw [Prog.rep]; trivial
  | succ count ih =>
      rw [Prog.rep]
      exact ⟨ih fun index bound => each index (by omega), each count (by omega)⟩

section Valid

variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

private theorem plainOps {program : Prog} (free : program.NoOracle) :
    program.OpsSatisfy ValidOracle :=
  opsSatisfy_of_noOracle validOracle_plain program free

private theorem fixedQuery : ValidOracle (.query 0 rIndex rInput rFirst rSecond) :=
  ⟨Or.inl rfl, rfl, rfl, rfl, rfl⟩

theorem replay_element (spec : Replay.LaneSpec) (chunk switch index : Nat) :
    (Replay.element ordF spec chunk switch index).OpsSatisfy ValidOracle := by
  unfold Replay.element
  exact ⟨trivial, fixedQuery, trivial, trivial, fixedQuery, trivial, trivial, fixedQuery, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial,
    ⟨trivial, trivial⟩⟩

theorem replay_guarded (spec : Replay.LaneSpec) (chunk switch index : Nat) :
    (Replay.guardedElement ordF spec chunk switch index).OpsSatisfy ValidOracle := by
  unfold Replay.guardedElement
  split
  · exact ⟨⟨trivial, trivial⟩, trivial, trivial, replay_element ordF spec chunk switch index, trivial⟩
  · exact replay_element ordF spec chunk switch index

theorem replay_chunkBody (spec : Replay.LaneSpec) (designated : Bool) (chunk : Nat) :
    (Replay.chunkBody ordF spec designated chunk).OpsSatisfy ValidOracle := by
  unfold Replay.chunkBody
  have foldArm (entry : Nat) : (Replay.foldArm ordF spec chunk entry).OpsSatisfy ValidOracle := by
    unfold Replay.foldArm Replay.foldPair
    exact ⟨⟨trivial, fixedQuery, trivial, trivial, fixedQuery, trivial, trivial⟩,
      ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩,
      ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩
  refine ⟨?_, ?_, opsSatisfy_rep _ _ fun switch _ => ?_, ⟨trivial, trivial⟩,
    opsSatisfy_rep _ _ fun _ _ => ?_⟩
  · unfold Replay.chunkPrefix
    exact ⟨⟨trivial, trivial⟩, trivial, trivial, trivial, trivial, ⟨trivial, trivial⟩, trivial,
      trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, foldArm 0, foldArm 1⟩
  · split
    · unfold Replay.designatedPrefix
      exact plainOps ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩,
        rfl, rfl, ⟨rfl, rfl⟩⟩
    · trivial
  · unfold Replay.switchStep Replay.switchBody
    refine ⟨⟨trivial, trivial⟩, trivial, trivial, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial,
      trivial, ?_⟩, trivial⟩
    unfold Replay.switchElements
    split
    · exact opsSatisfy_rep _ _ fun digit _ => by
        unfold Replay.designatedDigit
        exact ⟨replay_element ordF spec chunk switch _, replay_guarded ordF spec chunk switch _,
          replay_element ordF spec chunk switch _, replay_guarded ordF spec chunk switch _,
          replay_guarded ordF spec chunk switch _⟩
    · exact opsSatisfy_rep _ _ fun _ _ => replay_element ordF spec chunk switch _
  · unfold Replay.joinTerm
    exact ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

theorem replay_ops : (Replay.program ordF ordE).OpsSatisfy ValidOracle := by
  unfold Replay.program
  refine ⟨?_, opsSatisfy_rep _ _ fun _ _ => replay_chunkBody ordF _ _ _,
    opsSatisfy_rep _ _ fun _ _ => replay_chunkBody ordF _ _ _, ?_, ?_,
    ⟨replay_chunkBody ordF _ _ _, opsSatisfy_rep _ _ fun _ _ => replay_chunkBody ordF _ _ _⟩,
    opsSatisfy_rep _ _ fun _ _ => replay_chunkBody ordF _ _ _⟩
  · unfold Replay.initAcc
    exact ⟨trivial, opsSatisfy_rep _ _ fun _ _ => ⟨trivial, trivial⟩⟩
  · unfold Replay.bridge
    refine ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial, trivial, ⟨trivial, trivial⟩,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, trivial,
      ⟨trivial, trivial⟩, trivial, trivial, ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩,
      trivial, ⟨Or.inr (Or.inr rfl), rfl, rfl, rfl, rfl⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  · unfold Replay.whiten
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, opsSatisfy_rep _ _ fun _ _ => by
      unfold Replay.whitenOne
      exact ⟨trivial, ⟨Or.inr (Or.inl rfl), rfl, rfl, rfl, rfl⟩, trivial, ⟨trivial, trivial⟩,
        trivial, ⟨trivial, trivial⟩⟩⟩

theorem opening_ops : (Opening.program ordF).OpsSatisfy ValidOracle := by
  unfold Opening.program
  simp only [Prog.seqList]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, plainOps (noOracle_zeroRegs _), trivial⟩
  · have curveRoot (source : Register) : (Opening.curveRoot source).NoOracle := by
      unfold Opening.curveRoot
      simp only [Prog.seqList]
      exact ⟨rfl, rfl, rfl, rfl, rfl, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.sqrtRound
        exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
    exact opsSatisfy_rep _ _ fun _ _ => by
      unfold Opening.tailOne
      simp only [Prog.seqList]
      refine plainOps ⟨noOracle_bounded _ _ _ _ ?_ ?_, noOracle_zeroRegs _, trivial⟩
      · unfold Opening.testCurveX
        simp only [Prog.seqList]
        exact ⟨rfl, rfl, curveRoot _, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · unfold Opening.storeCurvePoint
        simp only [Prog.seqList]
        exact ⟨curveRoot _, ⟨rfl, trivial⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, trivial⟩
  · -- Horner and the head clamp: oracle-free
    unfold Opening.horner Opening.clearP Opening.head Opening.storePoint
    simp only [Prog.seqList]
    have betaMul : Opening.betaMul.NoOracle := by
      unfold Opening.betaMul Opening.copyPoint Opening.clearP
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl, rfl, trivial⟩, ⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.betaRound
        exact ⟨rfl, by split <;> first | rfl | trivial⟩), trivial⟩
    exact plainOps ⟨⟨rfl, rfl, rfl, trivial⟩, noOracle_rep _ _ (fun _ _ => by
        unfold Opening.hornerStep Opening.loadPoint
        simp only [Prog.seqList]
        exact ⟨betaMul, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, trivial⟩),
      ⟨betaMul, ⟨⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩, trivial⟩,
        trivial⟩, trivial⟩
  · -- the randomisers
    exact plainOps (noOracle_rep _ _ fun _ _ =>
      ⟨noOracle_bounded _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩, noOracle_zeroRegs _⟩)
  · -- the lifts
    exact plainOps (noOracle_rep _ _ fun _ _ => by
      unfold Opening.liftOne Opening.loadPoint
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
        noOracle_zeroRegs _, trivial⟩)
  · -- the collector targets
    exact plainOps (noOracle_rep _ _ fun _ _ => by
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
        ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, trivial⟩, noOracle_zeroRegs _, trivial⟩)
  · -- the preimages
    exact plainOps (noOracle_rep _ _ fun _ _ => noOracle_rep _ _ fun _ _ => by
      unfold Opening.preimageOne Opening.limbsOf Opening.shr128
      simp only [Prog.seqList]
      exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, noOracle_bounded _ _ _ _ rfl ⟨rfl, rfl⟩,
        noOracle_zeroRegs _,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
          ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, noOracle_zeroRegs _, trivial⟩,
        trivial⟩)
  · -- the 819 programs
    exact opsSatisfy_rep _ _ fun _ _ => opsSatisfy_rep _ _ fun _ _ => opsSatisfy_rep _ _ fun _ _ => by
      unfold Opening.programOne Opening.selectIndex
      simp only [Prog.seqList]
      exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial,
        opsSatisfy_rep _ _ (fun _ _ => ⟨⟨trivial, trivial⟩, trivial, trivial,
          ⟨trivial, trivial⟩, trivial⟩),
        ⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- **The valid arm issues only the four allowed oracle shapes.** -/
theorem valid_ops : (Stage2.valid ordF ordE).OpsSatisfy ValidOracle := by
  unfold Stage2.valid
  simp only [Prog.seqList]
  exact ⟨replay_ops ordF ordE, opening_ops ordF,
    plainOps (noOracle_rep _ _ fun _ _ => noOracle_emitWord _ _), trivial⟩

end Valid

/-! ### The runs leave the oracle untouched -/

section Runs

variable [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
  [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
variable (ordF : PlanB.FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

/-- **Stage 1 makes no oracle call**: its run is an oracle-free law followed by a halt that
returns the incoming oracle state unchanged. -/
theorem stage1_run_oracle (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: false :: rest) (oracle : OState FixedIndex EncIndex) :
    (Top.machine ordF ordE).run Design.firstFuel ⟨0, memory⟩ oracle =
      (Stage1.program.memSem (Top.afterTag memory rest)).map fun result => result.map fun final =>
        (atPc (Top.machine ordF ordE) stage1Halt final, oracle, Design.firstFuel) := by
  rw [Top.stage1_run ordF ordE memory rest request oracle,
    sem_noOracle _ stage1_noOracle, PMF.bind_map, PMF.map]
  congr 1
  funext result
  cases result <;> rfl

/-- **Stage 2, split at the output tag.** The prefix is oracle-free; on a clear flag (the
invalid output) the arm is oracle-free as well, so the run returns the incoming oracle state
unchanged; on a set flag the valid arm runs on the lazy oracle. -/
theorem stage2_run_split (memory : Memory) (rest : List Bool)
    (request : memory.bits 0 = false :: true :: rest) (oracle : OState FixedIndex EncIndex) :
    (Top.machine ordF ordE).run Design.secondFuel ⟨0, memory⟩ oracle =
      (Request.prefixProgram.memSem (Top.afterTag memory rest)).bind fun result => match result with
        | none => PMF.pure none
        | some middle =>
            if middle.registers rFlag = 0 then
              (Stage2.invalid.memSem middle).map fun final => final.map fun last =>
                (atPc (Top.machine ordF ordE) invalidHalt last, oracle,
                  2 + prefixCost + 1 + invalidSize + 1)
            else
              (Stage2.valid ordF ordE |>.sem middle oracle).bind fun final => match final with
                | none => PMF.pure none
                | some (last, updated) => PMF.pure (some (atPc (Top.machine ordF ordE) validHalt last,
                    updated, Design.secondFuel)) := by
  rw [Top.stage2_run ordF ordE memory rest request oracle, sem_noOracle _ prefix_noOracle,
    PMF.bind_map]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some middle =>
      simp only [Function.comp_apply, Option.map_some]
      split
      · rw [sem_noOracle _ invalid_noOracle, PMF.bind_map, PMF.map]
        congr 1
        funext final
        cases final <;> rfl
      · rfl

end Runs

end Kriterion.ArgoMAC.PlanB.SimMachine
