/-
Stage 2, part 2: the opening of a valid input to `Q = f_k(u)` (design note B §1.2–§2.2, in the
order of P3's `AbstractSimulator.opening`):

1. `tail`: `90` uniform finite curve points `D_d = (x, ±√(x³ + 3))`, `d = 1 .. 90`: `x` by
   bounded rejection over `254` coins, accepted when `x < p` and `x³ + 3` is a square (the
   candidate `(x³ + 3) ^ ((p + 1) / 4)` squares back; `p ≡ 3 mod 4`), then a fair sign — the
   construction's own offset law (P3's `coinOffsetsLaw`), with no group-order fact;
2. `horner`: `H = pointHorner β (D_1 … D_90)` by `P ← D_d + β · P` from `d = 90` down, with the
   constant multiple `β · P` unrolled over the `192` bits of `β`; the head clamp
   `D_0 = Q − β · H`, aborting when `β · H = O` (no clamped offset exists);
3. `lambdas`: `91` randomisers `λ_d ∈ [1, p)`;
4. `lifts`: `W_d = (λ² x', λ³ y', tag · λ)` with `x' = 1 + tag · (x − 1)`, i.e. `liftRow`;
5. `solve`: the running rows `X, Y, Z` of every digit on the accumulated (designated-free)
   values and `y*_{d,c} = κ · (W_d.c − row_c)`;
6. `preimages`: for every `(d, c)`, `m < q + [y* < ρ]` by bounded rejection over `131` coins and
   the limbs of `y* + p · m`;
7. `programs`: the `819` programs `fixedForward (scale pointX 0 j* (5d + slot c) b) E* ↦ o_b ⊕ E*`,
   digit → collector → block; `j*` is dynamic, so each index constant sits in a four-way
   selection on `j*`.
-/

import Construction.Simulator.Replay

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks Prog

namespace Opening

/-- Point register moves: `target ← source`, one coordinate at a time. -/
def copyPoint (target source : PointRegisters) : Prog :=
  seqList [ar .and target.tag source.tag source.tag, ar .and target.x source.x source.x,
    ar .and target.y source.y source.y]

/-- Load a stored point (tag, x, y) into a point register. -/
def loadPoint (target : PointRegisters) (address : Nat) : Prog :=
  seqList [loadAt target.tag address, loadAt target.x (address + 1), loadAt target.y (address + 2)]

/-- Store a point register. -/
def storePoint (address : Nat) (source : PointRegisters) : Prog :=
  seqList [storeAt address source.tag, storeAt (address + 1) source.x,
    storeAt (address + 2) source.y]

/-- `P ← O`. -/
def clearP : Prog := seqList [cst 6 0, cst 7 0, cst 8 0]

/-- One round of `s ← s² · a^bit` of the square-root exponentiation (`s` in `rB`, `a` in `rA`);
a one-instruction skip when the exponent bit is clear, so every round costs two. -/
def sqrtRound (bit : Nat) : Prog :=
  .seq (ar .fieldMul rB rB rB)
    (if sqrtExponent.testBit bit then ar .fieldMul rB rB rA else .skip 1)

/-- `rB ← (x³ + 3) ^ ((p + 1) / 4)` and `rA ← x³ + 3`, for `x` in register `source`
(clobbers `rAddr`). -/
def curveRoot (source : Register) : Prog :=
  seqList [ar .fieldMul rA source source, ar .fieldMul rA rA source, cst rAddr 3,
    ar .fieldAdd rA rA rAddr, cst rB 1, rep 252 fun round => sqrtRound (251 - round)]

/-- The acceptance test of the curve-point sampler, on `x = rAcc`: `x < p` and `x³ + 3` is a
square (the candidate root squares back to it). Sets `rBit`; clobbers `rAddr`, `rA` … `rD`. -/
def testCurveX : Prog :=
  seqList [cst rAddr pNat, ar .less rBit rAcc rAddr, curveRoot rAcc,
    ar .fieldMul rC rB rB, ar .xor rC rC rA, cst rD 1, ar .less rC rC rD,
    ar .and rBit rBit rC]

/-- One uniform finite point of the curve into the point cell of digit `d`: an accepted `x`
(in `rOut`), its root recomputed, and a fair sign. -/
def storeCurvePoint (digit : Nat) : Prog :=
  seqList [curveRoot rOut, coinBit rBit, cst rAcc 0, ar .fieldSub rC rAcc rB,
    ar .sub rC rC rB, ar .mul rC rC rBit, ar .add rC rC rB,
    cst rD 1, storeAt (openPoint digit) rD, storeAt (openPoint digit + 1) rOut,
    storeAt (openPoint digit + 2) rC]

/-- One tail digit `d ∈ 1 .. 90`: a uniform finite point (the construction's offset law). -/
def tailOne (digit : Nat) : Prog :=
  seqList [bounded fieldWidth testCurveX attempts (storeCurvePoint digit),
    zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD]]

/-- The `90` tail digits. -/
def tail : Prog := rep 90 fun index => tailOne (index + 1)

/-- One round of `P ← β · P` at bit `bit` of `β`: double, then add `Q` iff the bit is set (a
one-instruction skip otherwise, so every round costs two). -/
def betaRound (bit : Nat) : Prog :=
  .seq (.op (.pointAdd pointP pointP pointP))
    (if betaNat.testBit bit then .op (.pointAdd pointP pointP pointQ) else .skip 1)

/-- `P ← β · P` (clobbers `Q`). -/
def betaMul : Prog :=
  seqList [copyPoint pointQ pointP, clearP, rep 192 fun round => betaRound (191 - round)]

/-- One Horner step `P ← D_d + β · P`. -/
def hornerStep (digit : Nat) : Prog :=
  seqList [betaMul, loadPoint pointQ (openPoint digit), .op (.pointAdd pointP pointQ pointP)]

/-- The head clamp `D_0 = Q − β · H`, `H` in `P`; the tail is valid (the construction's clamped
offsets exist) only when `β · H ≠ O`, and the run aborts otherwise. -/
def head : Prog :=
  seqList [betaMul, .ite 6
    (seqList [cst rAcc 0, ar .fieldSub 8 rAcc 8, loadAt 9 reqTag0, loadAt 10 reqQX,
      loadAt 11 reqQY, .op (.pointAdd pointP pointQ pointP), storePoint (openPoint 0) pointP,
      zeroRegs [0, 4, 6, 7, 8, 9, 10, 11]])
    (.abort rSel)]

/-- `H`, then the head clamp. -/
def horner : Prog := seqList [clearP, rep 90 fun index => hornerStep (90 - index), head]

/-- One randomiser `λ_d ∈ [1, p)`. -/
def lambdaOne (digit : Nat) : Prog :=
  .seq (bounded fieldWidth (testPositiveBelow pNat) attempts (storeAt (openLambda digit) rOut))
    (zeroRegs samplerScratch)

def lambdas : Prog := rep 91 lambdaOne

/-- `W_d = liftRow D_d λ_d`. -/
def liftOne (digit : Nat) : Prog :=
  seqList [loadAt rA (openLambda digit), ar .fieldMul rB rA rA, ar .fieldMul rC rB rA,
    loadPoint ⟨rD, rE, rF⟩ (openPoint digit), cst rAcc 1,
    ar .fieldSub rE rE rAcc, ar .fieldMul rE rE rD, ar .fieldAdd rE rE rAcc,
    ar .fieldSub rF rF rAcc, ar .fieldMul rF rF rD, ar .fieldAdd rF rF rAcc,
    ar .fieldMul rE rE rB, ar .fieldMul rF rF rC, ar .fieldMul rD rD rA,
    storeAt (openRow digit) rE, storeAt (openRow digit + 1) rF, storeAt (openRow digit + 2) rD,
    zeroRegs [rAcc, rAddr, rA, rB, rC, rD, rE, rF]]

def lifts : Prog := rep 91 liftOne

/-- The row-constant cell `k` of digit `d`. -/
def rowCell (digit slot : Nat) : Nat := fieldBase + curveCellCount + 11 * digit + slot

/-- `rAcc += RAM[cell] · R[factor]`. -/
def addScaled (cell : Nat) (factor : Register) : Prog :=
  seqList [loadAt rSel cell, ar .fieldMul rSel rSel factor, ar .fieldAdd rAcc rAcc rSel]

/-- `rAcc += RAM[cell]`. -/
def addCell (cell : Nat) : Prog := seqList [loadAt rSel cell, ar .fieldAdd rAcc rAcc rSel]

/-- `RAM[target] = κ · (RAM[row] − rAcc)`. -/
def finishTarget (row target : Nat) : Prog :=
  seqList [loadAt rSel row, ar .fieldSub rSel rSel rAcc, ar .fieldMul rSel rSel rF,
    storeAt target rSel]

/-- The accumulator cell of x-slot `s` and y-slot `s` of the point lanes. -/
def xCell (slot : Nat) : Nat := accBase + slot
def yCell (slot : Nat) : Nat := accBase + 458 + slot

/-- The three collector targets of digit `d` (rows in `evaluateX/Y/Z` order). -/
def solveDigit (digit : Nat) : Prog :=
  seqList [loadAt rA reqX, loadAt rB reqY, ar .fieldMul rC rA rA, ar .fieldMul rD rB rB,
    ar .fieldMul rE rA rB, loadAt rF tmpKappa,
    -- X row: c0 + c1 x + c2 y + c4 x² + v[x7] x + v[x9] + v[y10]
    loadAt rAcc (rowCell digit 0), addScaled (rowCell digit 1) rA, addScaled (rowCell digit 2) rB,
    addScaled (rowCell digit 3) rC, addScaled (xCell (5 * digit)) rA,
    addCell (xCell (5 * digit + 1)), addCell (yCell (4 * digit)),
    finishTarget (openRow digit) (openTarget digit 0),
    -- Y row: c0 + c2 y + c3 x y + c4 x² + c5 y² + v[y6] x + v[x7] x + v[y8] y + v[x9] + v[y10]
    loadAt rAcc (rowCell digit 4), addScaled (rowCell digit 5) rB, addScaled (rowCell digit 6) rE,
    addScaled (rowCell digit 7) rC, addScaled (rowCell digit 8) rD,
    addScaled (yCell (4 * digit + 1)) rA, addScaled (xCell (5 * digit + 2)) rA,
    addScaled (yCell (4 * digit + 2)) rB, addCell (xCell (5 * digit + 3)),
    addCell (yCell (4 * digit + 3)),
    finishTarget (openRow digit + 1) (openTarget digit 1),
    -- Z row: c0 + c1 x + v[x9]
    loadAt rAcc (rowCell digit 9), addScaled (rowCell digit 10) rA, addCell (xCell (5 * digit + 4)),
    finishTarget (openRow digit + 2) (openTarget digit 2),
    zeroRegs [rAcc, rAddr, rSel, rA, rB, rC, rD, rE, rF]]

def solve : Prog := rep 91 solveDigit

/-- `target ← source >> 128` (clobbers `rAddr`). -/
def shr128 (target source : Register) : Prog := .seq (cst rAddr 128) (ar .shiftRight target source rAddr)

/-- The limbs of `y + p · m`: `m` in `tmpM`, `y` at the target cell, limbs to `openLimb d c ·`. -/
def limbsOf (digit collector : Nat) : Prog :=
  seqList [loadAt rA tmpM, loadAt rB (openTarget digit collector), cst rC mask128,
    ar .and rD rA rC, shr128 rE rA, cst rF pLow, cst rSel pHigh,
    ar .mul rAcc rF rD, ar .mul rOut rF rE, ar .mul rFlag rSel rD, ar .mul rBit rSel rE,
    -- s0 = y_lo + t0_lo
    ar .and rD rB rC, ar .and rE rAcc rC, ar .add rD rD rE,
    ar .and rE rD rC, storeAt (openLimb digit collector 0) rE, shr128 rD rD,
    -- s1 = c0 + y_hi + t0_hi + t1_lo + t2_lo
    shr128 rE rB, ar .add rD rD rE, shr128 rE rAcc, ar .add rD rD rE,
    ar .and rE rOut rC, ar .add rD rD rE, ar .and rE rFlag rC, ar .add rD rD rE,
    ar .and rE rD rC, storeAt (openLimb digit collector 1) rE, shr128 rD rD,
    -- s2 = c1 + t1_hi + t2_hi + t3
    shr128 rE rOut, ar .add rD rD rE, shr128 rE rFlag, ar .add rD rD rE, ar .add rD rD rBit,
    storeAt (openLimb digit collector 2) rD,
    zeroRegs [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD, rE, rF]]

/-- The preimage of collector target `(d, c)`: `M = q + [y* < ρ]` in `rB`, then `m < M`. -/
def preimageOne (digit collector : Nat) : Prog :=
  seqList [loadAt rC (openTarget digit collector), cst rAddr preimageRemainder,
    ar .less rD rC rAddr, cst rAddr preimageQuotient, ar .add rB rD rAddr,
    bounded multiplierWidth (testBelowRegister rB) attempts (storeAt tmpM rOut),
    zeroRegs samplerScratch, limbsOf digit collector]

def preimages : Prog := rep 91 fun digit => rep 3 fun collector => preimageOne digit collector

/-- The x-slot of collector `c` inside its digit: `rowX_x9 = 1`, `rowY_x9 = 3`, `rowZ_x9 = 4`. -/
def collectorSlot (collector : Nat) : Nat :=
  if collector = 0 then 1 else if collector = 1 then 3 else 4

variable (ordF : FixedIndex → Nat)

/-- Load the index of `(d, c, b)` at the dynamic switch `j*`. -/
def selectIndex (digit collector block : Nat) : Prog :=
  rep 4 fun switch =>
    seqList [loadAt rA tmpJStar, cst rB switch, ar .xor rA rA rB,
      .ite rA (.skip 0)
        (cst rIndex (ordF (Replay.scaleIdx .pointX 0 switch
          (5 * digit + collectorSlot collector) block)))]

/-- One program `E* ↦ o_b ⊕ E*`. -/
def programOne (digit collector block : Nat) : Prog :=
  seqList [loadAt rInput (hotLabelBase + 4), loadAt rFirst (openLimb digit collector block),
    ar .xor rFirst rFirst rInput, selectIndex ordF digit collector block,
    .op (.program 0 rIndex rInput rFirst rSecond)]

def programs : Prog :=
  rep 91 fun digit => rep 3 fun collector => rep 3 fun block => programOne ordF digit collector block

/-- **The opening.** -/
def program : Prog :=
  seqList [tail, horner, lambdas, lifts, solve, preimages, programs ordF, zeroRegs allRegisters]

/-! ### Sizes and costs -/

section Sizes

/-- The simp set for straight-line blocks. -/
macro "prog_size" : tactic => `(tactic| simp only [seqList, Prog.size_seq, Prog.cost_seq,
  size_cst, cost_cst, size_loadAt, cost_loadAt, size_storeAt, cost_storeAt, size_zeroRegs,
  cost_zeroRegs, ar, Prog.size, Prog.cost, List.length_cons, List.length_nil])

theorem size_sqrtRound (bit : Nat) : (sqrtRound bit).size = 2 := by
  unfold sqrtRound; split <;> rfl
theorem cost_sqrtRound (bit : Nat) : (sqrtRound bit).cost = 2 := by
  unfold sqrtRound; split <;> rfl

theorem size_curveRoot (source : Register) : (curveRoot source).size = 509 := by
  unfold curveRoot; prog_size; rw [size_rep _ _ _ fun _ _ => size_sqrtRound _]
theorem cost_curveRoot (source : Register) : (curveRoot source).cost = 509 := by
  unfold curveRoot; prog_size; rw [cost_rep _ _ _ fun _ _ => cost_sqrtRound _]

theorem size_testCurveX : testCurveX.size = 516 := by
  unfold testCurveX; prog_size; rw [size_curveRoot]
theorem cost_testCurveX : testCurveX.cost = 516 := by
  unfold testCurveX; prog_size; rw [cost_curveRoot]

theorem size_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).size = 526 := by
  unfold storeCurvePoint coinBit; prog_size; rw [size_curveRoot]
theorem cost_storeCurvePoint (digit : Nat) : (storeCurvePoint digit).cost = 524 := by
  unfold storeCurvePoint coinBit; prog_size; rw [cost_curveRoot]

theorem size_tailOne (digit : Nat) : (tailOne digit).size = 589865 := by
  unfold tailOne
  simp only [seqList, Prog.size_seq, size_zeroRegs, List.length_cons, List.length_nil, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), size_testCurveX,
    size_storeCurvePoint, cost_storeCurvePoint]
  rfl
theorem cost_tailOne (digit : Nat) : (tailOne digit).cost = 459290 := by
  unfold tailOne
  simp only [seqList, Prog.cost_seq, cost_zeroRegs, List.length_cons, List.length_nil, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeCurvePoint]; omega), cost_testCurveX,
    cost_storeCurvePoint]
  rfl

theorem size_tail : tail.size = 90 * 589865 := size_rep _ _ _ fun _ _ => size_tailOne _
theorem cost_tail : tail.cost = 90 * 459290 := cost_rep _ _ _ fun _ _ => cost_tailOne _

theorem size_betaRound (bit : Nat) : (betaRound bit).size = 2 := by
  unfold betaRound; split <;> rfl
theorem cost_betaRound (bit : Nat) : (betaRound bit).cost = 2 := by
  unfold betaRound; split <;> rfl

theorem size_betaMul : betaMul.size = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [size_rep _ _ _ fun _ _ => size_betaRound _]
theorem cost_betaMul : betaMul.cost = 390 := by
  unfold betaMul copyPoint clearP
  prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_betaRound _]

theorem size_hornerStep (digit : Nat) : (hornerStep digit).size = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [size_betaMul]
theorem cost_hornerStep (digit : Nat) : (hornerStep digit).cost = 397 := by
  unfold hornerStep loadPoint; prog_size; rw [cost_betaMul]

theorem size_head : head.size = 439 := by
  unfold head storePoint; prog_size; rw [size_betaMul]; simp only [Prog.padSet, Prog.padClear]
  prog_size; norm_num
theorem cost_head : head.cost = 415 := by
  unfold head storePoint; prog_size; rw [cost_betaMul]; norm_num

theorem size_horner : horner.size = 3 + 90 * 397 + 439 := by
  unfold horner clearP; prog_size
  rw [size_rep _ _ _ fun _ _ => size_hornerStep _, size_head]
theorem cost_horner : horner.cost = 3 + 90 * 397 + 415 := by
  unfold horner clearP; prog_size
  rw [cost_rep _ _ _ fun _ _ => cost_hornerStep _, cost_head]

theorem size_lambdaOne (digit : Nat) : (lambdaOne digit).size = 457743 := by
  unfold lambdaOne
  simp only [Prog.size_seq, size_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.size_seq, size_cst, ar, Prog.size, size_storeAt, cost_storeAt,
    fieldWidth, attempts]
theorem cost_lambdaOne (digit : Nat) : (lambdaOne digit).cost = 327692 := by
  unfold lambdaOne
  simp only [Prog.cost_seq, cost_zeroRegs, samplerScratch, List.length_cons, List.length_nil]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testPositiveBelow, Prog.cost_seq, cost_cst, ar, Prog.cost, cost_storeAt,
    fieldWidth, attempts]

theorem size_lambdas : lambdas.size = 91 * 457743 := size_rep _ _ _ fun _ _ => size_lambdaOne _
theorem cost_lambdas : lambdas.cost = 91 * 327692 := cost_rep _ _ _ fun _ _ => cost_lambdaOne _

theorem size_liftOne (digit : Nat) : (liftOne digit).size = 34 := by
  unfold liftOne loadPoint; prog_size
theorem cost_liftOne (digit : Nat) : (liftOne digit).cost = 34 := by
  unfold liftOne loadPoint; prog_size

theorem size_lifts : lifts.size = 91 * 34 := size_rep _ _ _ fun _ _ => size_liftOne _
theorem cost_lifts : lifts.cost = 91 * 34 := cost_rep _ _ _ fun _ _ => cost_liftOne _

theorem size_solveDigit (digit : Nat) : (solveDigit digit).size = 105 := by
  unfold solveDigit addScaled addCell finishTarget; prog_size
theorem cost_solveDigit (digit : Nat) : (solveDigit digit).cost = 105 := by
  unfold solveDigit addScaled addCell finishTarget; prog_size

theorem size_solve : solve.size = 91 * 105 := size_rep _ _ _ fun _ _ => size_solveDigit _
theorem cost_solve : solve.cost = 91 * 105 := cost_rep _ _ _ fun _ _ => cost_solveDigit _

theorem size_limbsOf (digit collector : Nat) : (limbsOf digit collector).size = 58 := by
  unfold limbsOf shr128; prog_size
theorem cost_limbsOf (digit collector : Nat) : (limbsOf digit collector).cost = 58 := by
  unfold limbsOf shr128; prog_size

theorem size_preimageOne (digit collector : Nat) : (preimageOne digit collector).size = 236623 := by
  unfold preimageOne
  simp only [seqList, Prog.size_seq, size_zeroRegs, size_limbsOf, size_loadAt, size_cst, ar,
    samplerScratch, List.length_cons, List.length_nil, Prog.size]
  rw [size_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testBelowRegister, ar, Prog.size, size_storeAt, cost_storeAt, multiplierWidth,
    attempts]
theorem cost_preimageOne (digit collector : Nat) : (preimageOne digit collector).cost = 169548 := by
  unfold preimageOne
  simp only [seqList, Prog.cost_seq, cost_zeroRegs, cost_limbsOf, cost_loadAt, cost_cst, ar,
    samplerScratch, List.length_cons, List.length_nil, Prog.cost]
  rw [cost_bounded _ _ _ _ (by rw [cost_storeAt]; omega)]
  simp only [testBelowRegister, ar, Prog.cost, cost_storeAt, multiplierWidth, attempts]

theorem size_preimages : preimages.size = 91 * (3 * 236623) :=
  size_rep _ _ _ fun _ _ => size_rep _ _ _ fun _ _ => size_preimageOne _ _
theorem cost_preimages : preimages.cost = 91 * (3 * 169548) :=
  cost_rep _ _ _ fun _ _ => cost_rep _ _ _ fun _ _ => cost_preimageOne _ _

theorem size_selectIndex (digit collector block : Nat) :
    (selectIndex ordF digit collector block).size = 4 * 7 := by
  unfold selectIndex
  rw [size_rep _ _ 7 fun _ _ => by
    simp only [seqList, Prog.size_seq, size_loadAt, ar, Prog.size, Prog.padSet,
      Prog.padClear, Prog.cost, cst]
    norm_num]
theorem cost_selectIndex (digit collector block : Nat) :
    (selectIndex ordF digit collector block).cost = 4 * 6 := by
  unfold selectIndex
  rw [cost_rep _ _ 6 fun _ _ => by
    simp only [seqList, Prog.cost_seq, cost_loadAt, ar, Prog.cost, cst]
    norm_num]

theorem size_programOne (digit collector block : Nat) :
    (programOne ordF digit collector block).size = 34 := by
  unfold programOne; prog_size; rw [size_selectIndex]
theorem cost_programOne (digit collector block : Nat) :
    (programOne ordF digit collector block).cost = 30 := by
  unfold programOne; prog_size; rw [cost_selectIndex]

theorem size_programs : (programs ordF).size = 91 * (3 * (3 * 34)) :=
  size_rep _ _ _ fun _ _ => size_rep _ _ _ fun _ _ => size_rep _ _ _ fun _ _ =>
    size_programOne ordF _ _ _
theorem cost_programs : (programs ordF).cost = 91 * (3 * (3 * 30)) :=
  cost_rep _ _ _ fun _ _ => cost_rep _ _ _ fun _ _ => cost_rep _ _ _ fun _ _ =>
    cost_programOne ordF _ _ _

/-- The opening's code size. -/
def programSize : Nat :=
  90 * 589865 + (3 + 90 * 397 + 439) + 91 * 457743 + 91 * 34 + 91 * 105 + 91 * (3 * 236623) +
    91 * (3 * (3 * 34)) + 16

/-- The opening's cost. -/
def programCost : Nat :=
  90 * 459290 + (3 + 90 * 397 + 415) + 91 * 327692 + 91 * 34 + 91 * 105 + 91 * (3 * 169548) +
    91 * (3 * (3 * 30)) + 16

theorem size_program : (program ordF).size = programSize := by
  unfold program
  rw [seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList,
    Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq, Prog.size_seq,
    Prog.size_seq, Prog.size_seq, size_tail, size_horner, size_lambdas, size_lifts, size_solve,
    size_preimages, size_programs, size_zeroRegs, allRegisters, List.length_finRange]
  rfl

theorem cost_program : (program ordF).cost = programCost := by
  unfold program
  rw [seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList, seqList,
    Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq, Prog.cost_seq,
    Prog.cost_seq, Prog.cost_seq, cost_tail, cost_horner, cost_lambdas, cost_lifts, cost_solve,
    cost_preimages, cost_programs, cost_zeroRegs, allRegisters, List.length_finRange]
  rfl

end Sizes

end Opening

end Kriterion.ArgoMAC.PlanB.SimMachine
