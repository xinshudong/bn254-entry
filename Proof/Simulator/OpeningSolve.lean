/-
**The opening, step 3: the collector solve** (`Opening.solve`).

For each digit the machine evaluates the three rows `X, Y, Z` on the replayed (designated-free)
accumulators, exactly as `Biquadratic.evaluate{X,Y,Z}` (P3's `evaluateGamma`, the designated-free rows
of `evaluateHomogeneous`), and stores `y*_c = κ · (W_d.c − row_c)` at `openTarget d c`
(`memSem_solveDigit`): P3's `collectorTargets`.

* `memSem_addScaled`, `memSem_addCell`, `memSem_finishTarget`: the three row blocks;
* `run_solvePrefix`, `run_rowX`, `run_rowY`, `run_rowZ`: a digit, in four parts;
* `memSem_solve`: all `91` digits.
-/

import Proof.Simulator.OpeningLift

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

/-- Evaluate a register read through a chain of `setReg` / `storeRam`, then close by `rfl`. -/
macro "regv" : tactic =>
  `(tactic| ((simp only [setReg_registers, storeRam_registers]); (try simp (config := { decide := true }) only [if_true, if_false]); (try rfl)))

/-- Arithmetic on the concrete addresses of the machine's layout. -/
macro "addr_arith" : tactic =>
  `(tactic| ((try simp only [Opening.rowCell, Opening.xCell, Opening.yCell, openRow, openTarget, openPoint, openLambda, openLimb, fieldBase, curveCellCount, accBase, openBase, requestBase, reqX, reqY, reqTag0, reqQX, reqQY, tmpBase, tmpKappa, tmpJStar, tmpM, hotLabelBase]) <;> omega))

/-- Two distinct concrete addresses of the machine's layout. -/
macro "addr_ne" : tactic => `(tactic| (apply word_ne <;> addr_arith))

noncomputable section

variable [FieldCertificate]

/-! ### The row blocks -/

/-- `rAcc += RAM[cell] · R[factor]`. -/
theorem memSem_addScaled (cell : Nat) (factor : Register) (memory : Memory)
    (notSel : factor ≠ rSel) (notAddr : factor ≠ rAddr) :
    ∃ after, (Opening.addScaled cell factor).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rAcc = fieldWord (wordField (memory.registers rAcc) +
        wordField (memory.ram (word cell)) * wordField (memory.registers factor)) ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  unfold Opening.addScaled
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word cell)) (memory.registers factor) (by regv)
      (by simp only [setReg_registers, if_neg notSel, if_neg notAddr]),
    eval_fieldMul,
    memSem_ar_val _ _ _ _ _ _ (memory.registers rAcc) (fieldWord (wordField (memory.ram (word cell)) *
      wordField (memory.registers factor))) (by regv) (by regv), eval_fieldAdd, fieldWord_cast,
    memSem_skip]
  refine ⟨_, rfl, rfl, rfl, by regv, fun index h0 h5 h4 => ?_⟩
  simp only [setReg_registers, if_neg h0, if_neg h5, if_neg h4]

/-- `rAcc += RAM[cell]`. -/
theorem memSem_addCell (cell : Nat) (memory : Memory) :
    ∃ after, (Opening.addCell cell).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      after.registers rAcc = fieldWord (wordField (memory.registers rAcc) +
        wordField (memory.ram (word cell))) ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  unfold Opening.addCell
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.registers rAcc) (memory.ram (word cell)) (by regv) (by regv),
    eval_fieldAdd, memSem_skip]
  refine ⟨_, rfl, rfl, rfl, by regv, fun index h0 h5 h4 => ?_⟩
  simp only [setReg_registers, if_neg h0, if_neg h5, if_neg h4]

/-- `RAM[target] = (RAM[row] − rAcc) · rF`. -/
theorem memSem_finishTarget (row target : Nat) (memory : Memory) :
    ∃ after, (Opening.finishTarget row target).memSem memory = PMF.pure (some after) ∧
      after.ram = Function.update memory.ram (word target)
        (fieldWord ((wordField (memory.ram (word row)) - wordField (memory.registers rAcc)) *
          wordField (memory.registers rF))) ∧
      after.bits = memory.bits ∧
      ∀ index, index ≠ rSel → index ≠ rAddr → after.registers index = memory.registers index := by
  unfold Opening.finishTarget
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word row)) (memory.registers rAcc) (by regv) (by regv),
    eval_fieldSub,
    memSem_ar_val _ _ _ _ _ _ (fieldWord (wordField (memory.ram (word row)) -
      wordField (memory.registers rAcc))) (memory.registers rF) (by regv) (by regv), eval_fieldMul,
    fieldWord_cast, memSem_storeAt_seq _ _ _ _ (by decide), memSem_skip]
  refine ⟨_, rfl, ?_, rfl, fun index h5 h4 => ?_⟩
  · simp only [storeRam_ram, setReg_ram]
    regv
  · simp only [storeRam_registers, setReg_registers, if_neg h5, if_neg h4]

/-! ### Row steps on field values -/

omit [FieldCertificate] in
theorem wordField_fieldWord (value : BaseField) : wordField (fieldWord value) = value :=
  fieldWord_cast value

/-- An `addScaled` step on field values. -/
theorem step_addScaled (cell : Nat) (factor : Register) (memory : Memory) (acc value scale : BaseField)
    (notSel : factor ≠ rSel) (notAddr : factor ≠ rAddr)
    (hacc : wordField (memory.registers rAcc) = acc) (hvalue : wordField (memory.ram (word cell)) = value)
    (hscale : wordField (memory.registers factor) = scale) :
    ∃ after, (Opening.addScaled cell factor).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      wordField (after.registers rAcc) = acc + value * scale ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨after, run, ram, bits, accIs, frame⟩ := memSem_addScaled cell factor memory notSel notAddr
  exact ⟨after, run, ram, bits, by rw [accIs, wordField_fieldWord, hacc, hvalue, hscale], frame⟩

/-- An `addCell` step on field values. -/
theorem step_addCell (cell : Nat) (memory : Memory) (acc value : BaseField)
    (hacc : wordField (memory.registers rAcc) = acc) (hvalue : wordField (memory.ram (word cell)) = value) :
    ∃ after, (Opening.addCell cell).memSem memory = PMF.pure (some after) ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧
      wordField (after.registers rAcc) = acc + value ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨after, run, ram, bits, accIs, frame⟩ := memSem_addCell cell memory
  exact ⟨after, run, ram, bits, by rw [accIs, wordField_fieldWord, hacc, hvalue], frame⟩

/-- The solve's fixed registers, as field values. -/
def SolveRegs (memory : Memory) (x y kappaValue : BaseField) : Prop :=
  wordField (memory.registers rA) = x ∧ wordField (memory.registers rB) = y ∧
    wordField (memory.registers rC) = x * x ∧ wordField (memory.registers rD) = y * y ∧
    wordField (memory.registers rE) = x * y ∧ wordField (memory.registers rF) = kappaValue

theorem SolveRegs.frame {memory after : Memory} {x y kappaValue : BaseField}
    (holds : SolveRegs memory x y kappaValue)
    (same : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      after.registers index = memory.registers index) : SolveRegs after x y kappaValue := by
  obtain ⟨a, b, c, d, e, f⟩ := holds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [same _ (by decide) (by decide) (by decide)] <;> assumption

/-- **The `X` row** of a digit and its collector target `y*_0 = (W.x − X) · κ`. -/
theorem run_rowX (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c0 c1 c2 c4 v7 v9 v10 target : BaseField)
    (h0 : wordField (memory.ram (word (Opening.rowCell digit 0))) = c0)
    (h1 : wordField (memory.ram (word (Opening.rowCell digit 1))) = c1)
    (h2 : wordField (memory.ram (word (Opening.rowCell digit 2))) = c2)
    (h3 : wordField (memory.ram (word (Opening.rowCell digit 3))) = c4)
    (h7 : wordField (memory.ram (word (Opening.xCell (5 * digit)))) = v7)
    (h9 : wordField (memory.ram (word (Opening.xCell (5 * digit + 1)))) = v9)
    (h10 : wordField (memory.ram (word (Opening.yCell (4 * digit)))) = v10)
    (hw : wordField (memory.ram (word (openRow digit))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.rowCell digit 0))
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 1) rA)
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 2) rB)
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 3) rC)
        (Prog.seq (Opening.addScaled (Opening.xCell (5 * digit)) rA)
        (Prog.seq (Opening.addCell (Opening.xCell (5 * digit + 1)))
        (Prog.seq (Opening.addCell (Opening.yCell (4 * digit)))
        (Prog.seq (Opening.finishTarget (openRow digit) (openTarget digit 0)) rest)))))))).memSem
          memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (openTarget digit 0))
        (fieldWord ((target - (c0 + c1 * x + c2 * y + c4 * (x * x) + v7 * x + v9 + v10)) *
          kappaValue)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rd, re, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell digit 0))) rAcc
    (memory.ram (word (Opening.rowCell digit 0))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rd, re, rf⟩ frame1
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addScaled _ rA m1 c0 c1 x (by decide)
    (by decide) (by rw [m1Def, reg_same, h0]) (by rw [m1Def]; exact h1) regs1.1
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, acc3, frame3⟩ := step_addScaled _ rB m2 _ c2 y (by decide)
    (by decide) acc2 (by rw [ram2, m1Def]; exact h2) regs2.2.1
  rw [memSem_pure_seq run3]
  have regs3 := regs2.frame frame3
  obtain ⟨m4, run4, ram4, bits4, acc4, frame4⟩ := step_addScaled _ rC m3 _ c4 (x * x) (by decide)
    (by decide) acc3 (by rw [ram3, ram2, m1Def]; exact h3) regs3.2.2.1
  rw [memSem_pure_seq run4]
  have regs4 := regs3.frame frame4
  obtain ⟨m5, run5, ram5, bits5, acc5, frame5⟩ := step_addScaled _ rA m4 _ v7 x (by decide)
    (by decide) acc4 (by rw [ram4, ram3, ram2, m1Def]; exact h7) regs4.1
  rw [memSem_pure_seq run5]
  have regs5 := regs4.frame frame5
  obtain ⟨m6, run6, ram6, bits6, acc6, frame6⟩ := step_addCell _ m5 _ v9 acc5
    (by rw [ram5, ram4, ram3, ram2, m1Def]; exact h9)
  rw [memSem_pure_seq run6]
  have regs6 := regs5.frame frame6
  obtain ⟨m7, run7, ram7, bits7, acc7, frame7⟩ := step_addCell _ m6 _ v10 acc6
    (by rw [ram6, ram5, ram4, ram3, ram2, m1Def]; exact h10)
  rw [memSem_pure_seq run7]
  have regs7 := regs6.frame frame7
  obtain ⟨m8, run8, ram8, bits8, frame8⟩ := memSem_finishTarget (openRow digit) (openTarget digit 0) m7
  rw [memSem_pure_seq run8]
  have ramChain : m7.ram = memory.ram := by rw [ram7, ram6, ram5, ram4, ram3, ram2, m1Def]; rfl
  refine ⟨m8, rfl, ?_, ?_, regs7.frame fun index _ h5 h4 => frame8 index h5 h4, ?_⟩
  · rw [ram8, acc7, regs7.2.2.2.2.2, ramChain, hw]
  · rw [bits8, bits7, bits6, bits5, bits4, bits3, bits2, m1Def]; rfl
  · intro index h0' h5 h4
    rw [frame8 index h5 h4, frame7 index h0' h5 h4, frame6 index h0' h5 h4, frame5 index h0' h5 h4,
      frame4 index h0' h5 h4, frame3 index h0' h5 h4, frame2 index h0' h5 h4, frame1 index h0' h5 h4]

/-- **The `Y` row** of a digit and its collector target `y*_1 = (W.y − Y) · κ`. -/
theorem run_rowY (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c0 c2 c3 c4 c5 v6 v7 v8 v9 v10 target : BaseField)
    (h0 : wordField (memory.ram (word (Opening.rowCell digit 4))) = c0)
    (h2 : wordField (memory.ram (word (Opening.rowCell digit 5))) = c2)
    (h3 : wordField (memory.ram (word (Opening.rowCell digit 6))) = c3)
    (h4 : wordField (memory.ram (word (Opening.rowCell digit 7))) = c4)
    (h5 : wordField (memory.ram (word (Opening.rowCell digit 8))) = c5)
    (h6 : wordField (memory.ram (word (Opening.yCell (4 * digit + 1)))) = v6)
    (h7 : wordField (memory.ram (word (Opening.xCell (5 * digit + 2)))) = v7)
    (h8 : wordField (memory.ram (word (Opening.yCell (4 * digit + 2)))) = v8)
    (h9 : wordField (memory.ram (word (Opening.xCell (5 * digit + 3)))) = v9)
    (h10 : wordField (memory.ram (word (Opening.yCell (4 * digit + 3)))) = v10)
    (hw : wordField (memory.ram (word (openRow digit + 1))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.rowCell digit 4))
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 5) rB)
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 6) rE)
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 7) rC)
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 8) rD)
        (Prog.seq (Opening.addScaled (Opening.yCell (4 * digit + 1)) rA)
        (Prog.seq (Opening.addScaled (Opening.xCell (5 * digit + 2)) rA)
        (Prog.seq (Opening.addScaled (Opening.yCell (4 * digit + 2)) rB)
        (Prog.seq (Opening.addCell (Opening.xCell (5 * digit + 3)))
        (Prog.seq (Opening.addCell (Opening.yCell (4 * digit + 3)))
        (Prog.seq (Opening.finishTarget (openRow digit + 1) (openTarget digit 1)) rest))))))))))).memSem
          memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (openTarget digit 1))
        (fieldWord ((target - (c0 + c2 * y + c3 * (x * y) + c4 * (x * x) + c5 * (y * y) + v6 * x +
          v7 * x + v8 * y + v9 + v10)) * kappaValue)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rd, re, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell digit 4))) rAcc
    (memory.ram (word (Opening.rowCell digit 4))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rd, re, rf⟩ frame1
  have ram1 : m1.ram = memory.ram := by rw [m1Def]; rfl
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addScaled _ rB m1 c0 c2 y (by decide)
    (by decide) (by rw [m1Def, reg_same, h0]) (by rw [ram1]; exact h2) regs1.2.1
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, acc3, frame3⟩ := step_addScaled _ rE m2 _ c3 (x * y) (by decide)
    (by decide) acc2 (by rw [ram2, ram1]; exact h3) regs2.2.2.2.2.1
  rw [memSem_pure_seq run3]
  have regs3 := regs2.frame frame3
  obtain ⟨m4, run4, ram4, bits4, acc4, frame4⟩ := step_addScaled _ rC m3 _ c4 (x * x) (by decide)
    (by decide) acc3 (by rw [ram3, ram2, ram1]; exact h4) regs3.2.2.1
  rw [memSem_pure_seq run4]
  have regs4 := regs3.frame frame4
  obtain ⟨m5, run5, ram5, bits5, acc5, frame5⟩ := step_addScaled _ rD m4 _ c5 (y * y) (by decide)
    (by decide) acc4 (by rw [ram4, ram3, ram2, ram1]; exact h5) regs4.2.2.2.1
  rw [memSem_pure_seq run5]
  have regs5 := regs4.frame frame5
  obtain ⟨m6, run6, ram6, bits6, acc6, frame6⟩ := step_addScaled _ rA m5 _ v6 x (by decide)
    (by decide) acc5 (by rw [ram5, ram4, ram3, ram2, ram1]; exact h6) regs5.1
  rw [memSem_pure_seq run6]
  have regs6 := regs5.frame frame6
  obtain ⟨m7, run7, ram7, bits7, acc7, frame7⟩ := step_addScaled _ rA m6 _ v7 x (by decide)
    (by decide) acc6 (by rw [ram6, ram5, ram4, ram3, ram2, ram1]; exact h7) regs6.1
  rw [memSem_pure_seq run7]
  have regs7 := regs6.frame frame7
  obtain ⟨m8, run8, ram8, bits8, acc8, frame8⟩ := step_addScaled _ rB m7 _ v8 y (by decide)
    (by decide) acc7 (by rw [ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact h8) regs7.2.1
  rw [memSem_pure_seq run8]
  have regs8 := regs7.frame frame8
  obtain ⟨m9, run9, ram9, bits9, acc9, frame9⟩ := step_addCell _ m8 _ v9 acc8
    (by rw [ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact h9)
  rw [memSem_pure_seq run9]
  have regs9 := regs8.frame frame9
  obtain ⟨m10, run10, ram10, bits10, acc10, frame10⟩ := step_addCell _ m9 _ v10 acc9
    (by rw [ram9, ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact h10)
  rw [memSem_pure_seq run10]
  have regs10 := regs9.frame frame10
  obtain ⟨m11, run11, ram11, bits11, frame11⟩ :=
    memSem_finishTarget (openRow digit + 1) (openTarget digit 1) m10
  rw [memSem_pure_seq run11]
  have ramChain : m10.ram = memory.ram := by
    rw [ram10, ram9, ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1]
  refine ⟨m11, rfl, ?_, ?_, regs10.frame fun index _ h5' h4' => frame11 index h5' h4', ?_⟩
  · rw [ram11, acc10, regs10.2.2.2.2.2, ramChain, hw]
  · rw [bits11, bits10, bits9, bits8, bits7, bits6, bits5, bits4, bits3, bits2, m1Def]; rfl
  · intro index h0' h5' h4'
    rw [frame11 index h5' h4', frame10 index h0' h5' h4', frame9 index h0' h5' h4',
      frame8 index h0' h5' h4', frame7 index h0' h5' h4', frame6 index h0' h5' h4',
      frame5 index h0' h5' h4', frame4 index h0' h5' h4', frame3 index h0' h5' h4',
      frame2 index h0' h5' h4', frame1 index h0' h5' h4']

/-- **The `Z` row** of a digit and its collector target `y*_2 = (W.z − Z) · κ`. -/
theorem run_rowZ (digit : Nat) (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (regsHold : SolveRegs memory x y kappaValue)
    (c0 c1 v9 target : BaseField)
    (h0 : wordField (memory.ram (word (Opening.rowCell digit 9))) = c0)
    (h1 : wordField (memory.ram (word (Opening.rowCell digit 10))) = c1)
    (h9 : wordField (memory.ram (word (Opening.xCell (5 * digit + 4)))) = v9)
    (hw : wordField (memory.ram (word (openRow digit + 2))) = target) :
    ∃ after, (Prog.seq (loadAt rAcc (Opening.rowCell digit 9))
        (Prog.seq (Opening.addScaled (Opening.rowCell digit 10) rA)
        (Prog.seq (Opening.addCell (Opening.xCell (5 * digit + 4)))
        (Prog.seq (Opening.finishTarget (openRow digit + 2) (openTarget digit 2)) rest)))).memSem
          memory = rest.memSem after ∧
      after.ram = Function.update memory.ram (word (openTarget digit 2))
        (fieldWord ((target - (c0 + c1 * x + v9)) * kappaValue)) ∧
      after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
        after.registers index = memory.registers index := by
  obtain ⟨ra, rb, rc, rd, re, rf⟩ := regsHold
  rw [memSem_loadAt_seq]
  set m1 := setReg (setReg memory rAddr (word (Opening.rowCell digit 9))) rAcc
    (memory.ram (word (Opening.rowCell digit 9))) with m1Def
  have frame1 : ∀ index, index ≠ rAcc → index ≠ rSel → index ≠ rAddr →
      m1.registers index = memory.registers index := fun index h0' _ h4' => by
    rw [m1Def]; simp only [setReg_registers, if_neg h0', if_neg h4']
  have regs1 : SolveRegs m1 x y kappaValue := SolveRegs.frame ⟨ra, rb, rc, rd, re, rf⟩ frame1
  have ram1 : m1.ram = memory.ram := by rw [m1Def]; rfl
  obtain ⟨m2, run2, ram2, bits2, acc2, frame2⟩ := step_addScaled _ rA m1 c0 c1 x (by decide)
    (by decide) (by rw [m1Def, reg_same, h0]) (by rw [ram1]; exact h1) regs1.1
  rw [memSem_pure_seq run2]
  have regs2 := regs1.frame frame2
  obtain ⟨m3, run3, ram3, bits3, acc3, frame3⟩ := step_addCell _ m2 _ v9 acc2
    (by rw [ram2, ram1]; exact h9)
  rw [memSem_pure_seq run3]
  have regs3 := regs2.frame frame3
  obtain ⟨m4, run4, ram4, bits4, frame4⟩ :=
    memSem_finishTarget (openRow digit + 2) (openTarget digit 2) m3
  rw [memSem_pure_seq run4]
  refine ⟨m4, rfl, ?_, ?_, regs3.frame fun index _ h5' h4' => frame4 index h5' h4', ?_⟩
  · rw [ram4, acc3, regs3.2.2.2.2.2, ram3, ram2, ram1, hw]
  · rw [bits4, bits3, bits2, m1Def]; rfl
  · intro index h0' h5' h4'
    rw [frame4 index h5' h4', frame3 index h0' h5' h4', frame2 index h0' h5' h4',
      frame1 index h0' h5' h4']

/-- **The solve's prefix**: `x, y, x², y², x y` and `κ` into `rA … rF`. -/
theorem run_solvePrefix (rest : Prog) (memory : Memory) (x y kappaValue : BaseField)
    (hx : wordField (memory.ram (word reqX)) = x) (hy : wordField (memory.ram (word reqY)) = y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue) :
    ∃ after, (Prog.seq (loadAt rA reqX) (Prog.seq (loadAt rB reqY)
        (Prog.seq (ar .fieldMul rC rA rA) (Prog.seq (ar .fieldMul rD rB rB)
        (Prog.seq (ar .fieldMul rE rA rB) (Prog.seq (loadAt rF tmpKappa) rest)))))).memSem memory =
        rest.memSem after ∧
      after.ram = memory.ram ∧ after.bits = memory.bits ∧ SolveRegs after x y kappaValue ∧
      ∀ index, index ≠ rAddr → index ≠ rA → index ≠ rB → index ≠ rC → index ≠ rD → index ≠ rE →
        index ≠ rF → after.registers index = memory.registers index := by
  rw [memSem_loadAt_seq, memSem_loadAt_seq]
  simp only [setReg_ram]
  rw [memSem_ar_val _ _ _ _ _ _ (memory.ram (word reqX)) (memory.ram (word reqX)) (by regv)
      (by regv), eval_fieldMul,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word reqY)) (memory.ram (word reqY)) (by regv)
      (by regv), eval_fieldMul,
    memSem_ar_val _ _ _ _ _ _ (memory.ram (word reqX)) (memory.ram (word reqY)) (by regv)
      (by regv), eval_fieldMul, memSem_loadAt_seq]
  simp only [setReg_ram]
  refine ⟨_, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun index n4 n6 n7 n8 n9 n10 n11 => ?_⟩
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hx
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hy
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [wordField_fieldWord, ← hx]; rfl
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [wordField_fieldWord, ← hy]; rfl
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    rw [wordField_fieldWord, ← hx, ← hy]; rfl
  · simp only [setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    exact hk
  · simp only [setReg_registers, if_neg n4, if_neg n6, if_neg n7, if_neg n8, if_neg n9, if_neg n10,
      if_neg n11]

/-! ### One digit -/

omit [FieldCertificate] in
/-- A row constant by its position in `Opening.rowCell` order (the `Wire` order of `RowGamma`). -/
def gammaConst (gamma : RowGamma) : Nat → BaseField
  | 0 => gamma.xC0
  | 1 => gamma.xC1
  | 2 => gamma.xC2
  | 3 => gamma.xC4
  | 4 => gamma.yC0
  | 5 => gamma.yC2
  | 6 => gamma.yC3
  | 7 => gamma.yC4
  | 8 => gamma.yC5
  | 9 => gamma.zC0
  | _ => gamma.zC1

/-- The three collector targets `κ · (W.c − row.c)` as words. -/
def solveWords (kappaValue : BaseField) (target row : FieldMacToECMac.HomogeneousValue) :
    Word × Word × Word :=
  (fieldWord (kappaValue * (target.x - row.x)), fieldWord (kappaValue * (target.y - row.y)),
    fieldWord (kappaValue * (target.z - row.z)))

omit [FieldCertificate] in
/-- The registers a digit's solve clears. -/
def solveScratch : List Register := [rAcc, rAddr, rSel, rA, rB, rC, rD, rE, rF]

omit [FieldCertificate] in
theorem openTarget_shift (digit collector : Nat) :
    openTarget digit 0 + collector = openTarget digit collector := by
  unfold openTarget; omega

/-- **One digit of the solve**: the rows `evaluateGamma` on the replayed values, and the
three collector targets `κ · (W_d.c − row_c)` at `openTarget d c` (exact). -/
theorem memSem_solveDigit (digit : Nat) (small : digit < 91) (memory : Memory)
    (input : AffineInput) (kappaValue : BaseField) (gamma : RowGamma) (values : Biquadratic.Values)
    (target : FieldMacToECMac.HomogeneousValue)
    (hx : wordField (memory.ram (word reqX)) = input.x)
    (hy : wordField (memory.ram (word reqY)) = input.y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue)
    (hg : ∀ k, k < 11 → wordField (memory.ram (word (Opening.rowCell digit k))) = gammaConst gamma k)
    (hvx : ∀ element : XElement,
      wordField (memory.ram (word (Opening.xCell (5 * digit + element.slot.val)))) =
        values (.inl element))
    (hvy : ∀ element : YElement,
      wordField (memory.ram (word (Opening.yCell (4 * digit + element.slot.val)))) =
        values (.inr element))
    (hw : ∀ position, position < 3 →
      memory.ram (word (openRow digit + position)) = wordAt (rowWords target) position) :
    (Opening.solveDigit digit).memSem memory =
      PMF.pure (some (clearRegs (withRam memory (putPoint memory.ram (openTarget digit 0)
        (solveWords kappaValue target (FieldMacToECMac.evaluateGamma gamma input values))))
          solveScratch)) := by
  have hwx : wordField (memory.ram (word (openRow digit))) = target.x := by
    have := hw 0 (by omega); rw [Nat.add_zero] at this; rw [this]; exact wordField_fieldWord _
  have hwy : wordField (memory.ram (word (openRow digit + 1))) = target.y := by
    rw [hw 1 (by omega)]; exact wordField_fieldWord _
  have hwz : wordField (memory.ram (word (openRow digit + 2))) = target.z := by
    rw [hw 2 (by omega)]; exact wordField_fieldWord _
  unfold Opening.solveDigit
  simp only [Prog.seqList]
  obtain ⟨pre, runPre, ramPre, bitsPre, regsPre, framePre⟩ :=
    run_solvePrefix _ memory input.x input.y kappaValue hx hy hk
  rw [runPre]
  obtain ⟨rowX, runX, ramX, bitsX, regsX, frameX⟩ := run_rowX digit _ pre input.x input.y kappaValue
    regsPre (gammaConst gamma 0) (gammaConst gamma 1) (gammaConst gamma 2) (gammaConst gamma 3)
    (values (.inl .rowX_x7)) (values (.inl .rowX_x9)) (values (.inr .rowX_y10)) target.x
    (by rw [ramPre]; exact hg 0 (by omega)) (by rw [ramPre]; exact hg 1 (by omega))
    (by rw [ramPre]; exact hg 2 (by omega)) (by rw [ramPre]; exact hg 3 (by omega))
    (by rw [ramPre]; exact hvx .rowX_x7) (by rw [ramPre]; exact hvx .rowX_x9)
    (by rw [ramPre]; exact hvy .rowX_y10) (by rw [ramPre]; exact hwx)
  rw [runX]
  have readX : ∀ address, address < 2 ^ 256 → address ≠ openTarget digit 0 →
      rowX.ram (word address) = memory.ram (word address) := by
    intro address bound different
    rw [ramX, Function.update_of_ne (word_ne bound (by unfold openTarget openBase; omega) different),
      ramPre]
  obtain ⟨rowY, runY, ramY, bitsY, regsY, frameY⟩ := run_rowY digit _ rowX input.x input.y
    kappaValue regsX (gammaConst gamma 4) (gammaConst gamma 5) (gammaConst gamma 6)
    (gammaConst gamma 7) (gammaConst gamma 8) (values (.inr .rowY_y6)) (values (.inl .rowY_x7))
    (values (.inr .rowY_y8)) (values (.inl .rowY_x9)) (values (.inr .rowY_y10)) target.y
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 4 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 5 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 6 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 7 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hg 8 (by omega))
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvy .rowY_y6)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvx .rowY_x7)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvy .rowY_y8)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvx .rowY_x9)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hvy .rowY_y10)
    (by rw [readX _ (by addr_arith) (by addr_arith)]; exact hwy)
  rw [runY]
  have readY : ∀ address, address < 2 ^ 256 → address ≠ openTarget digit 0 →
      address ≠ openTarget digit 1 → rowY.ram (word address) = memory.ram (word address) := by
    intro address bound different0 different1
    rw [ramY, Function.update_of_ne (word_ne bound (by unfold openTarget openBase; omega) different1),
      readX address bound different0]
  obtain ⟨rowZ, runZ, ramZ, bitsZ, _, frameZ⟩ := run_rowZ digit _ rowY input.x input.y
    kappaValue regsY (gammaConst gamma 9) (gammaConst gamma 10) (values (.inl .rowZ_x9)) target.z
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hg 9 (by omega))
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hg 10 (by omega))
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hvx .rowZ_x9)
    (by rw [readY _ (by addr_arith) (by addr_arith) (by addr_arith)]; exact hwz)
  rw [runZ, memSem_zeroRegs_seq, memSem_skip]
  refine congrArg (fun final => PMF.pure (some final)) ?_
  apply clearRegs_withRam_eq
  · rw [ramZ, ramY, ramX, ramPre]
    unfold putPoint solveWords
    rw [openTarget_shift digit 1, openTarget_shift digit 2]
    have eX : (target.x - (gammaConst gamma 0 + gammaConst gamma 1 * input.x +
        gammaConst gamma 2 * input.y + gammaConst gamma 3 * (input.x * input.x) +
        values (.inl .rowX_x7) * input.x + values (.inl .rowX_x9) + values (.inr .rowX_y10))) *
          kappaValue =
        kappaValue * (target.x - (FieldMacToECMac.evaluateGamma gamma input values).x) := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateX, FieldMacToECMac.xGammaOf,
        gammaConst]
      ring
    have eY : (target.y - (gammaConst gamma 4 + gammaConst gamma 5 * input.y +
        gammaConst gamma 6 * (input.x * input.y) + gammaConst gamma 7 * (input.x * input.x) +
        gammaConst gamma 8 * (input.y * input.y) + values (.inr .rowY_y6) * input.x +
        values (.inl .rowY_x7) * input.x + values (.inr .rowY_y8) * input.y +
        values (.inl .rowY_x9) + values (.inr .rowY_y10))) * kappaValue =
        kappaValue * (target.y - (FieldMacToECMac.evaluateGamma gamma input values).y) := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateY, FieldMacToECMac.yGammaOf,
        gammaConst]
      ring
    have eZ : (target.z - (gammaConst gamma 9 + gammaConst gamma 10 * input.x +
        values (.inl .rowZ_x9))) * kappaValue =
        kappaValue * (target.z - (FieldMacToECMac.evaluateGamma gamma input values).z) := by
      simp only [FieldMacToECMac.evaluateGamma, Biquadratic.evaluateZ, FieldMacToECMac.zGammaOf,
        gammaConst]
      ring
    rw [eX, eY, eZ]
  · rw [bitsZ, bitsY, bitsX, bitsPre]
  · intro index outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n4, n5, n6, n7, n8, n9, n10, n11⟩ := outside
    rw [frameZ index n0 n5 n4, frameY index n0 n5 n4, frameX index n0 n5 n4,
      framePre index n4 n6 n7 n8 n9 n10 n11]

/-! ### All digits -/

/-- **The solve**: the `273` collector targets `κ · (W_d.c − row_{d,c})` at `openTarget d c`,
nothing else changed off the opening's cells. -/
theorem memSem_solve (memory : Memory) (input : AffineInput) (kappaValue : BaseField)
    (gammas : Fin 91 → RowGamma) (values : Fin 91 → Biquadratic.Values)
    (targets : Fin 91 → FieldMacToECMac.HomogeneousValue)
    (hx : wordField (memory.ram (word reqX)) = input.x)
    (hy : wordField (memory.ram (word reqY)) = input.y)
    (hk : wordField (memory.ram (word tmpKappa)) = kappaValue)
    (hg : ∀ (digit : Fin 91) k, k < 11 →
      wordField (memory.ram (word (Opening.rowCell digit k))) = gammaConst (gammas digit) k)
    (hvx : ∀ (digit : Fin 91) (element : XElement),
      wordField (memory.ram (word (Opening.xCell (5 * digit.val + element.slot.val)))) =
        values digit (.inl element))
    (hvy : ∀ (digit : Fin 91) (element : YElement),
      wordField (memory.ram (word (Opening.yCell (4 * digit.val + element.slot.val)))) =
        values digit (.inr element))
    (hw : ∀ (digit : Fin 91) position, position < 3 →
      memory.ram (word (openRow digit + position)) = wordAt (rowWords (targets digit)) position) :
    ∀ count, count ≤ 91 → ∃ after,
      (Prog.rep count Opening.solveDigit).memSem memory = PMF.pure (some after) ∧
      after.bits = memory.bits ∧ SameOff memory.ram after.ram ∧
      (∀ digit : Fin 91, digit.val < count → ∀ position, position < 3 →
        after.ram (word (openTarget digit 0 + position)) =
          wordAt (solveWords kappaValue (targets digit)
            (FieldMacToECMac.evaluateGamma (gammas digit) input (values digit))) position) ∧
      (∀ target, (∀ digit, digit < count → ∀ position, position < 3 →
        target ≠ word (openTarget digit 0 + position)) → after.ram target = memory.ram target)
  | 0, _ => ⟨memory, by rw [Prog.rep]; rfl, rfl, SameOff.refl _,
      fun _ bound => absurd bound (by omega), fun _ _ => rfl⟩
  | count + 1, bound => by
      obtain ⟨previous, runPrevious, bitsPrevious, samePrevious, targetsPrevious, offPrevious⟩ :=
        memSem_solve memory input kappaValue gammas values targets hx hy hk hg hvx hvy hw count
          (by omega)
      have read : ∀ address, address < 2 ^ 256 →
          (∀ digit, digit < count → ∀ position, position < 3 →
            address ≠ openTarget digit 0 + position) →
          previous.ram (word address) = memory.ram (word address) := fun address small away =>
        offPrevious _ fun digit below position inside =>
          word_ne small (by unfold openTarget openBase; omega) (away digit below position inside)
      set here : Fin 91 := ⟨count, by omega⟩ with hereDef
      have run := memSem_solveDigit count (by omega) previous input kappaValue (gammas here)
        (values here) (targets here)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hx)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hy)
        (by rw [read _ (by addr_arith) (fun digit below position inside => by addr_arith)]; exact hk)
        (fun k inside => by
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hg here k inside)
        (fun element => by
          have slot : element.slot.val < 5 := element.slot.isLt
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hvx here element)
        (fun element => by
          have slot : element.slot.val < 4 := element.slot.isLt
          rw [read _ (by addr_arith) (fun digit below position inside' => by addr_arith)]
          exact hvy here element)
        (fun position inside => by
          rw [read _ (by addr_arith) (fun digit below position' inside' => by addr_arith)]
          exact hw here position inside)
      set written := putPoint previous.ram (openTarget count 0) (solveWords kappaValue (targets here)
        (FieldMacToECMac.evaluateGamma (gammas here) input (values here))) with writtenDef
      have ramNext : (clearRegs (withRam previous written) solveScratch).ram = written := by
        rw [(clearRegs_other _ _).1]; rfl
      refine ⟨clearRegs (withRam previous written) solveScratch, ?_, ?_, ?_, ?_, ?_⟩
      · rw [memSem_rep_succ, runPrevious, PMF.pure_bind]
        exact run
      · rw [(clearRegs_other _ _).2, withRam_bits, bitsPrevious]
      · rw [ramNext, writtenDef]
        have step := sameOff_putPoint previous.ram (1000 + 3 * count) (by omega)
          (solveWords kappaValue (targets here)
            (FieldMacToECMac.evaluateGamma (gammas here) input (values here)))
        rw [show openBase + (1000 + 3 * count) = openTarget count 0 by unfold openTarget; omega]
          at step
        exact samePrevious.trans step
      · intro digit below position inside
        rw [ramNext, writtenDef]
        by_cases same : digit.val = count
        · have digitIs : digit = here := Fin.ext same
          subst digitIs
          exact putPoint_at _ _ _ _ (by unfold openTarget openBase; omega) inside
        · rw [putPoint_off _ _ _ _ (fun position' inside' => word_ne
              (by unfold openTarget openBase; omega) (by unfold openTarget openBase; omega)
              (by unfold openTarget; omega)),
            targetsPrevious digit (by omega) position inside]
      · intro target away
        rw [ramNext, writtenDef,
          putPoint_off _ _ _ _ (fun position inside => away count (by omega) position inside),
          offPrevious target (fun digit below position inside => away digit (by omega) position inside)]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
