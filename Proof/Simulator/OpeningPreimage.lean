/-
**The opening, step 4: the `sampleFp` preimages** (`Opening.preimages`).

For every collector target `y* = y_{d,c}` the machine draws `m < q + [y* < ρ]` by bounded
rejection over `131` coins (`preimageLaw`'s draw), then computes the three `128`-bit limbs of
`y* + p · m` by limb arithmetic (`limbsOf`), which are exactly `limbs (y*.val + p · m)`. The draw's
test `m < R[rB]` reads a register the attempts never write, so the attempt laws are re-derived with
that register as a guard (`IsTestAt`, `attempt_law_at`, `rep_attempt_law_at`).

The cutoff mass of these draws (`preimageAbort_le`, `≤ 2^-399` each) is part of `SamplerCutoff`,
already proved (`samplerCutoff`); the machine law here is exact against `preimageLaw`.
-/

import Proof.Simulator.OpeningSolve

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Attempts whose test reads a guarded register -/

/-- A test block valid on memories whose register `guard` holds `value`. -/
def IsTestAt (test : Prog) (accept : Nat → Bool) (junk : List Register) (guard : Register)
    (value : Word) : Prop :=
  ∀ memory : Memory, memory.registers guard = value → ∃ result : Memory,
    test.memSem memory = PMF.pure (some (setReg result rBit
      (bitWord (accept (memory.registers rAcc).toNat)))) ∧
    clearRegs result junk = clearRegs memory junk

/-- **One attempt**, on a memory whose guard holds its value. -/
theorem attempt_law_at (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (guard : Register) (guardValue : Word)
    (isTest : IsTestAt test accept junk guard guardValue) (guardAcc : guard ≠ rAcc)
    (guardBit : guard ≠ rBit) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (memory : Memory) (flag : Bool)
    (flagged : memory.registers rFlag = bitWord flag) (guarded : memory.registers guard = guardValue) :
    ((attempt width test).memSem memory).map (Option.map fun final =>
        clearRegs final (attemptScratch junk)) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map fun value =>
        some (clearRegs (keepMem accept memory value.val) (attemptScratch junk)) := by
  unfold attempt
  simp only [Prog.memSem, memSem_sampleWord, PMF.bind_map, PMF.map_bind]
  rw [PMF.map]
  congr 1
  funext value
  simp only [Function.comp_apply]
  obtain ⟨result, testLaw, sameOutside⟩ := isTest (wordMem (setReg memory rAcc 0) width value.val)
    (by rw [wordMem_other memory width value.val guard guardAcc guardBit, guarded])
  rw [testLaw, PMF.pure_bind]
  simp only [ar, Prog.memSem, Op.memSem, PMF.pure_bind, PMF.pure_map, Option.map_some]
  rw [clearRegs_eq_iff] at sameOutside
  obtain ⟨sameRam, sameBits, sameRegs⟩ := sameOutside
  have valueSmall : value.val < 2 ^ 256 :=
    lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by norm_num) small)
  have accValue : (wordMem (setReg memory rAcc 0) width value.val).registers rAcc =
      BitVec.ofNat 256 value.val := wordMem_acc memory width value.val
  have accToNat : ((wordMem (setReg memory rAcc 0) width value.val).registers rAcc).toNat =
      value.val := by
    rw [accValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueSmall]
  rw [accToNat]
  have resultAcc : result.registers rAcc = BitVec.ofNat 256 value.val := by
    rw [sameRegs rAcc keepAcc, accValue]
  have resultOut : result.registers rOut = memory.registers rOut := by
    rw [sameRegs rOut keepOut, wordMem_other memory width value.val rOut (by decide) (by decide)]
  have resultFlag : result.registers rFlag = bitWord flag := by
    rw [sameRegs rFlag keepFlag, wordMem_other memory width value.val rFlag (by decide) (by decide),
      flagged]
  congr 1
  congr 1
  have ne1 : rFlag ≠ rBit := by decide
  have ne2 : rAcc ≠ rSel := by decide
  have ne3 : rAcc ≠ rBit := by decide
  have ne4 : rOut ≠ rSel := by decide
  have ne5 : rOut ≠ rBit := by decide
  have ne6 : rAddr ≠ rOut := by decide
  have ne7 : rSel ≠ rAddr := by decide
  have ne8 : rSel ≠ rOut := by decide
  have ne9 : rFlag ≠ rSel := by decide
  have ne10 : rFlag ≠ rAddr := by decide
  have ne11 : rFlag ≠ rOut := by decide
  simp only [setReg_registers, if_pos rfl, if_neg ne1, if_neg ne2, if_neg ne3, if_neg ne4,
    if_neg ne5, if_neg ne6, if_neg ne7, if_neg ne8, if_neg ne9, if_neg ne10, if_neg ne11,
    resultAcc, resultOut, resultFlag, less_bitWord]
  rw [clearRegs_eq_iff]
  refine ⟨?_, ?_, fun index outside => ?_⟩
  · rw [keepMem_ram_bits.1]
    exact sameRam
  · rw [keepMem_ram_bits.2]
    exact sameBits
  · simp only [attemptScratch, List.mem_cons, not_or] at outside
    obtain ⟨notAcc, notBit, notAddr, notSel, notJunk⟩ := outside
    have base := sameRegs index notJunk
    rw [wordMem_other memory width value.val index notAcc notBit] at base
    by_cases isFlag : index = rFlag
    · subst isFlag
      rw [setReg_registers, if_pos rfl, keepMem_flag accept memory value.val flag flagged]
      simp (config := { decide := true }) only [setReg_registers, if_true, if_false]
      cases flag <;> cases accept value.val <;> rfl
    · rw [setReg_registers, if_neg isFlag]
      by_cases isOut : index = rOut
      · subst isOut
        rw [setReg_registers, if_pos rfl, keepMem_out accept memory value.val flag flagged]
        simp (config := { decide := true }) only [setReg_registers, if_true, if_false]
        cases flag <;> cases accept value.val <;>
          simp [Arithmetic.eval, bitWord, BitVec.toNat_ofNat]
      · rw [setReg_registers, if_neg isOut, setReg_registers, if_neg notAddr, setReg_registers,
          if_neg notAddr, setReg_registers, if_neg notSel, setReg_registers, if_neg notBit, base,
          keepMem_other accept memory value.val index isFlag isOut]

/-- What an attempt keeps: the guard, and a flag that is a bit. -/
theorem attempt_keeps (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (guard : Register) (guardValue : Word)
    (isTest : IsTestAt test accept junk guard guardValue) (guardAcc : guard ≠ rAcc)
    (guardBit : guard ≠ rBit) (guardOut : guard ≠ rOut) (guardFlag : guard ≠ rFlag)
    (guardScratch : guard ∉ attemptScratch junk) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (memory : Memory) (flag : Bool)
    (flagged : memory.registers rFlag = bitWord flag) (guarded : memory.registers guard = guardValue) :
    ∀ result ∈ ((attempt width test).memSem memory).support, ∀ reached ∈ result,
      reached.registers guard = guardValue ∧ FlagBit reached := by
  intro result member reached inResult
  have flagOut : rFlag ∉ attemptScratch junk := by
    simp only [attemptScratch, List.mem_cons, not_or]
    exact ⟨by decide, by decide, by decide, by decide, keepFlag⟩
  have mapped : Option.map (fun final => clearRegs final (attemptScratch junk)) result ∈
      (((attempt width test).memSem memory).map (Option.map fun final =>
        clearRegs final (attemptScratch junk))).support := by
    rw [PMF.support_map]
    exact ⟨result, member, rfl⟩
  rw [attempt_law_at width small test accept junk guard guardValue isTest guardAcc guardBit keepOut
    keepFlag keepAcc memory flag flagged guarded, PMF.support_map] at mapped
  obtain ⟨value, _, same⟩ := mapped
  simp only [Option.mem_def] at inResult
  subst inResult
  simp only [Option.map_some, Option.some.injEq] at same
  refine ⟨?_, flag || accept value.val, ?_⟩
  · rw [← regs_of_clearRegs same guardScratch, keepMem_other accept memory value.val guard guardFlag
      guardOut, guarded]
  · rw [← regs_of_clearRegs same flagOut, keepMem_flag accept memory value.val flag flagged]

/-- Every memory `count` attempts reach keeps the guard and has a flag bit. -/
theorem rep_attempt_keeps (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (guard : Register) (guardValue : Word)
    (isTest : IsTestAt test accept junk guard guardValue) (guardAcc : guard ≠ rAcc)
    (guardBit : guard ≠ rBit) (guardOut : guard ≠ rOut) (guardFlag : guard ≠ rFlag)
    (guardScratch : guard ∉ attemptScratch junk) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (memory : Memory) (bit : FlagBit memory)
    (guarded : memory.registers guard = guardValue) :
    ∀ count, ∀ result ∈ ((Prog.rep count fun _ => attempt width test).memSem memory).support,
      ∀ reached ∈ result, reached.registers guard = guardValue ∧ FlagBit reached
  | 0, result, member, reached, inResult => by
      rw [Prog.rep] at member
      simp only [Prog.memSem, PMF.support_pure, Set.mem_singleton_iff] at member
      subst member
      simp only [Option.mem_def, Option.some.injEq] at inResult
      subst inResult
      exact ⟨guarded, bit⟩
  | count + 1, result, member, reached, inResult => by
      rw [memSem_rep_succ, PMF.mem_support_bind_iff] at member
      obtain ⟨middle, middleIn, member⟩ := member
      cases middle with
      | none =>
          simp only [kleisli, PMF.support_pure, Set.mem_singleton_iff] at member
          subst member
          simp at inResult
      | some middle =>
          obtain ⟨middleGuard, flag, flagged⟩ := rep_attempt_keeps width small test accept junk guard
            guardValue isTest guardAcc guardBit guardOut guardFlag guardScratch keepOut keepFlag
            keepAcc memory bit guarded count (some middle) middleIn middle rfl
          exact attempt_keeps width small test accept junk guard guardValue isTest guardAcc guardBit
            guardOut guardFlag guardScratch keepOut keepFlag keepAcc middle flag flagged middleGuard
            result member reached inResult

/-- **`count` guarded attempts** are `attemptsLaw`, read with the scratch cleared. -/
theorem rep_attempt_law_at (width : Nat) (small : width ≤ 256) (test : Prog) (accept : Nat → Bool)
    (junk : List Register) (guard : Register) (guardValue : Word)
    (isTest : IsTestAt test accept junk guard guardValue) (guardAcc : guard ≠ rAcc)
    (guardBit : guard ≠ rBit) (guardOut : guard ≠ rOut) (guardFlag : guard ≠ rFlag)
    (guardScratch : guard ∉ attemptScratch junk) (keepOut : rOut ∉ junk)
    (keepFlag : rFlag ∉ junk) (keepAcc : rAcc ∉ junk) (count : Nat) (memory : Memory)
    (bit : FlagBit memory) (guarded : memory.registers guard = guardValue) :
    ((Prog.rep count fun _ => attempt width test).memSem memory).map
        (Option.map fun final => clearRegs final (attemptScratch junk)) =
      attemptsLaw width accept (attemptScratch junk) count (clearRegs memory (attemptScratch junk)) := by
  have outOut : rOut ∉ attemptScratch junk := by
    simp only [attemptScratch, List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, keepOut⟩
  have flagOut : rFlag ∉ attemptScratch junk := by
    simp only [attemptScratch, List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, keepFlag⟩
  induction count with
  | zero =>
      rw [Prog.rep]
      simp [Prog.memSem, attemptsLaw, PMF.pure_map]
  | succ count ih =>
      rw [Prog.rep]
      simp only [Prog.memSem, attemptsLaw]
      rw [← ih, PMF.bind_map, PMF.map_bind]
      apply PMF.bind_congr
      intro result member
      cases result with
      | none => simp [kleisli, PMF.pure_map]
      | some reached =>
          simp only [Function.comp_apply, Option.map_some, kleisli, attemptStep]
          obtain ⟨reachedGuard, flag, flagged⟩ := rep_attempt_keeps width small test accept junk guard
            guardValue isTest guardAcc guardBit guardOut guardFlag guardScratch keepOut keepFlag
            keepAcc memory bit guarded count (some reached)
            ((PMF.mem_support_iff _ _).mpr member) reached rfl
          rw [attempt_law_at width small test accept junk guard guardValue isTest guardAcc guardBit
            keepOut keepFlag keepAcc reached flag flagged reachedGuard]
          congr 1
          funext value
          rw [clearRegs_keepMem accept reached value.val _ outOut flagOut]

/-! ### Word arithmetic -/

omit [FieldCertificate] in
theorem word_and_mask (value : Nat) (small : value < 2 ^ 256) :
    Arithmetic.and.eval (word value) (word mask128) = word (value % 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  have maskSmall : mask128 < 2 ^ 256 := by decide
  rw [show Arithmetic.and.eval (word value) (word mask128) = word value &&& word mask128 from rfl,
    BitVec.toNat_and, word_small small, word_small maskSmall, word_small (by omega),
    show mask128 = 2 ^ 128 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

omit [FieldCertificate] in
theorem word_shr (value : Nat) (small : value < 2 ^ 256) :
    Arithmetic.shiftRight.eval (word value) (word 128) = word (value / 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [show Arithmetic.shiftRight.eval (word value) (word 128) =
      word value >>> (word 128).toNat from rfl, BitVec.toNat_ushiftRight, word_small small,
    word_small (show 128 < 2 ^ 256 by norm_num), Nat.shiftRight_eq_div_pow, word_small (by omega)]

omit [FieldCertificate] in
theorem word_mul (first second : Nat) (firstSmall : first < 2 ^ 256) (secondSmall : second < 2 ^ 256)
    (small : first * second < 2 ^ 256) :
    Arithmetic.mul.eval (word first) (word second) = word (first * second) := by
  apply BitVec.eq_of_toNat_eq
  rw [eval_mul, BitVec.toNat_mul, word_small firstSmall, word_small secondSmall, word_small small,
    Nat.mod_eq_of_lt small]

omit [FieldCertificate] in
theorem word_add (first second : Nat) (small : first + second < 2 ^ 256) :
    Arithmetic.add.eval (word first) (word second) = word (first + second) := by
  apply BitVec.eq_of_toNat_eq
  rw [eval_add, BitVec.toNat_add, word_small (by omega : first < 2 ^ 256),
    word_small (by omega : second < 2 ^ 256), word_small small, Nat.mod_eq_of_lt small]

theorem memSem_shr128_seq (target source : Register) (rest : Prog) (memory : Memory) (value : Nat)
    (holds : memory.registers source = word value) (small : value < 2 ^ 256)
    (notAddr : source ≠ rAddr) :
    (Prog.seq (Opening.shr128 target source) rest).memSem memory =
      rest.memSem (setReg (setReg memory rAddr (word 128)) target (word (value / 2 ^ 128))) := by
  unfold Opening.shr128
  rw [memSem_pure_seq (after := setReg (setReg memory rAddr (word 128)) target
    (word (value / 2 ^ 128))) (by
      rw [memSem_cst_seq, memSem_ar _ _ _ _ _ (word value) (word 128)
        (by rw [reg_ne _ _ _ _ notAddr, holds]) (reg_same _ _ _), word_shr value small])]

/-! ### The limbs of `y + p · m` -/

omit [FieldCertificate] in
/-- **Two carries**: the machine's limb sums of `y + t0 + 2^128 (t1 + t2) + 2^256 t3`. -/
theorem carry_limbs (y t0 t1 t2 t3 : Nat) :
    (y % 2 ^ 128 + t0 % 2 ^ 128) % 2 ^ 128 =
        (y + t0 + 2 ^ 128 * t1 + 2 ^ 128 * t2 + 2 ^ 256 * t3) % 2 ^ 128 ∧
      ((y % 2 ^ 128 + t0 % 2 ^ 128) / 2 ^ 128 + y / 2 ^ 128 + t0 / 2 ^ 128 + t1 % 2 ^ 128 +
          t2 % 2 ^ 128) % 2 ^ 128 =
        (y + t0 + 2 ^ 128 * t1 + 2 ^ 128 * t2 + 2 ^ 256 * t3) / 2 ^ 128 % 2 ^ 128 ∧
      ((y % 2 ^ 128 + t0 % 2 ^ 128) / 2 ^ 128 + y / 2 ^ 128 + t0 / 2 ^ 128 + t1 % 2 ^ 128 +
          t2 % 2 ^ 128) / 2 ^ 128 + t1 / 2 ^ 128 + t2 / 2 ^ 128 + t3 =
        (y + t0 + 2 ^ 128 * t1 + 2 ^ 128 * t2 + 2 ^ 256 * t3) / 2 ^ 256 := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

omit [FieldCertificate] in
/-- `p · m` in the machine's four sub-products. -/
theorem product_split (mult : Nat) :
    pNat * mult = pLow * (mult % 2 ^ 128) + 2 ^ 128 * (pLow * (mult / 2 ^ 128)) +
      2 ^ 128 * (pHigh * (mult % 2 ^ 128)) + 2 ^ 256 * (pHigh * (mult / 2 ^ 128)) := by
  have hp : pNat = pLow + 2 ^ 128 * pHigh := by unfold pLow pHigh; omega
  have hmult : mult = mult % 2 ^ 128 + 2 ^ 128 * (mult / 2 ^ 128) := by omega
  conv_lhs => rw [hp, hmult]
  ring

/-- The three limb words of `n` as the machine stores them (limb `2` unreduced). -/
def limbWords (value : Nat) : Word × Word × Word :=
  (word (value % 2 ^ 128), word (value / 2 ^ 128 % 2 ^ 128), word (value / 2 ^ 256))

omit [FieldCertificate] in
/-- The registers the limbs clear. -/
def limbScratch : List Register := [rAcc, rOut, rFlag, rBit, rAddr, rSel, rA, rB, rC, rD, rE, rF]

omit [FieldCertificate] in
theorem openLimb_shift (digit collector block : Nat) :
    openLimb digit collector 0 + block = openLimb digit collector block := by
  unfold openLimb; omega

/-- **The limbs** of `y + p · m` at `openLimb d c 0 … 2`, read from `tmpM` and the target (exact). -/
theorem memSem_limbsOf (digit collector : Nat) (memory : Memory) (y : BaseField) (mult : Nat)
    (small : mult < 2 ^ 131) (multCell : memory.ram (word tmpM) = word mult)
    (targetCell : memory.ram (word (openTarget digit collector)) = fieldWord y) :
    (Opening.limbsOf digit collector).memSem memory =
      PMF.pure (some (clearRegs (withRam memory (putPoint memory.ram (openLimb digit collector 0)
        (limbWords (y.val + pNat * mult)))) limbScratch)) := by
  have yWord : fieldWord y = word y.val := rfl
  have ySmall : y.val < 2 ^ 254 := lt_trans y.val_lt (by unfold baseFieldModulus; norm_num)
  have pSmall : pNat < 2 ^ 254 := by decide
  have pLowSmall : pLow < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have pHighSmall : pHigh < 2 ^ 126 := by unfold pHigh; omega
  have mLoSmall : mult % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have mHiSmall : mult / 2 ^ 128 < 8 := by omega
  have t0Small : pLow * (mult % 2 ^ 128) < 2 ^ 256 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' pLowSmall mLoSmall) (by norm_num)
  have t1Small : pLow * (mult / 2 ^ 128) < 2 ^ 131 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' pLowSmall mHiSmall) (by norm_num)
  have t2Small : pHigh * (mult % 2 ^ 128) < 2 ^ 254 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' pHighSmall mLoSmall) (by norm_num)
  have t3Small : pHigh * (mult / 2 ^ 128) < 2 ^ 129 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' pHighSmall mHiSmall) (by norm_num)
  have hn : y.val + pNat * mult = y.val + pLow * (mult % 2 ^ 128) +
      2 ^ 128 * (pLow * (mult / 2 ^ 128)) + 2 ^ 128 * (pHigh * (mult % 2 ^ 128)) +
      2 ^ 256 * (pHigh * (mult / 2 ^ 128)) := by
    rw [product_split]; ring
  obtain ⟨carry0, carry1, carry2⟩ := carry_limbs y.val (pLow * (mult % 2 ^ 128))
    (pLow * (mult / 2 ^ 128)) (pHigh * (mult % 2 ^ 128)) (pHigh * (mult / 2 ^ 128))
  rw [hn]
  unfold Opening.limbsOf
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq, memSem_loadAt_seq]
  simp only [setReg_ram]
  rw [multCell, targetCell, yWord, memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (word mult) (word mask128) (by regv) (by regv),
    word_and_mask mult (by omega),
    memSem_shr128_seq _ _ _ _ mult (by regv) (by omega) (by decide),
    memSem_cst_seq, memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (word pLow) (word (mult % 2 ^ 128)) (by regv) (by regv),
    word_mul _ _ (by omega) (by omega) t0Small,
    memSem_ar_val _ _ _ _ _ _ (word pLow) (word (mult / 2 ^ 128)) (by regv) (by regv),
    word_mul _ _ (by omega) (by omega) (by omega),
    memSem_ar_val _ _ _ _ _ _ (word pHigh) (word (mult % 2 ^ 128)) (by regv) (by regv),
    word_mul _ _ (by omega) (by omega) (by omega),
    memSem_ar_val _ _ _ _ _ _ (word pHigh) (word (mult / 2 ^ 128)) (by regv) (by regv),
    word_mul _ _ (by omega) (by omega) (by omega),
    memSem_ar_val _ _ _ _ _ _ (word y.val) (word mask128) (by regv) (by regv),
    word_and_mask _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (pLow * (mult % 2 ^ 128))) (word mask128) (by regv) (by regv),
    word_and_mask _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (y.val % 2 ^ 128)) (word (pLow * (mult % 2 ^ 128) % 2 ^ 128))
      (by regv) (by regv), word_add _ _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128))
      (word mask128) (by regv) (by regv), word_and_mask _ (by omega),
    memSem_storeAt_seq _ _ _ _ (by decide),
    memSem_shr128_seq _ _ _ _ (y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) (by regv)
      (by omega) (by decide),
    memSem_shr128_seq _ _ _ _ y.val (by regv) (by omega) (by decide),
    memSem_ar_val _ _ _ _ _ _
      (word ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128))
      (word (y.val / 2 ^ 128)) (by regv) (by regv), word_add _ _ (by omega),
    memSem_shr128_seq _ _ _ _ (pLow * (mult % 2 ^ 128)) (by regv) (by omega) (by decide),
    memSem_ar_val _ _ _ _ _ _
      (word ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128))
      (word (pLow * (mult % 2 ^ 128) / 2 ^ 128)) (by regv) (by regv), word_add _ _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (pLow * (mult / 2 ^ 128))) (word mask128) (by regv) (by regv),
    word_and_mask _ (by omega),
    memSem_ar_val _ _ _ _ _ _
      (word ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 +
        pLow * (mult % 2 ^ 128) / 2 ^ 128))
      (word (pLow * (mult / 2 ^ 128) % 2 ^ 128)) (by regv) (by regv), word_add _ _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (pHigh * (mult % 2 ^ 128))) (word mask128) (by regv) (by regv),
    word_and_mask _ (by omega),
    memSem_ar_val _ _ _ _ _ _
      (word ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 +
        pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128))
      (word (pHigh * (mult % 2 ^ 128) % 2 ^ 128)) (by regv) (by regv), word_add _ _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 + pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128 + pHigh * (mult % 2 ^ 128) % 2 ^ 128)) (word mask128) (by regv) (by regv),
    word_and_mask _ (by omega),
    memSem_storeAt_seq _ _ _ _ (by decide),
    memSem_shr128_seq _ _ _ _ ((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 + pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128 + pHigh * (mult % 2 ^ 128) % 2 ^ 128) (by regv) (by omega) (by decide),
    memSem_shr128_seq _ _ _ _ (pLow * (mult / 2 ^ 128)) (by regv) (by omega) (by decide),
    memSem_ar_val _ _ _ _ _ _ (word (((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 + pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128 + pHigh * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128)) (word (pLow * (mult / 2 ^ 128) / 2 ^ 128))
      (by regv) (by regv), word_add _ _ (by omega),
    memSem_shr128_seq _ _ _ _ (pHigh * (mult % 2 ^ 128)) (by regv) (by omega) (by decide),
    memSem_ar_val _ _ _ _ _ _ (word (((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 + pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128 + pHigh * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) / 2 ^ 128))
      (word (pHigh * (mult % 2 ^ 128) / 2 ^ 128)) (by regv) (by regv), word_add _ _ (by omega),
    memSem_ar_val _ _ _ _ _ _ (word (((y.val % 2 ^ 128 + pLow * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + y.val / 2 ^ 128 + pLow * (mult % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) % 2 ^ 128 + pHigh * (mult % 2 ^ 128) % 2 ^ 128) / 2 ^ 128 + pLow * (mult / 2 ^ 128) / 2 ^ 128 +
        pHigh * (mult % 2 ^ 128) / 2 ^ 128))
      (word (pHigh * (mult / 2 ^ 128))) (by regv) (by regv), word_add _ _ (by omega),
    memSem_storeAt_seq _ _ _ _ (by decide), memSem_zeroRegs_seq, memSem_skip]
  refine congrArg (fun final => PMF.pure (some final)) ?_
  apply clearRegs_withRam_eq
  · simp only [storeRam_ram, setReg_ram, storeRam_registers, setReg_registers]
    simp (config := { decide := true }) only [if_true, if_false]
    unfold putPoint limbWords
    rw [openLimb_shift, openLimb_shift, ← carry0, ← carry1, ← carry2]
  · simp only [storeRam_bits, setReg_bits]
  · intro index outside
    simp only [limbScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := outside
    simp only [storeRam_registers, setReg_registers, if_neg n0, if_neg n1, if_neg n2, if_neg n3,
      if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_neg n8, if_neg n9, if_neg n10, if_neg n11]

/-! ### The multiplier draw -/

/-- The test `rAcc < R[rB]` on a memory whose `rB` holds `bound`. -/
theorem isTest_testBelowRegister (bound : Nat) (small : bound < 2 ^ 256) :
    IsTestAt (testBelowRegister rB) (fun value => decide (value < bound)) [rAddr] rB (word bound) := by
  intro memory guarded
  refine ⟨memory, ?_, rfl⟩
  unfold testBelowRegister
  rw [memSem_ar _ _ _ _ _ (memory.registers rAcc) (word bound) rfl guarded, less_word,
    word_small small]

theorem memSem_seq_assoc (first second third : Prog) (memory : Memory) :
    (Prog.seq (Prog.seq first second) third).memSem memory =
      (Prog.seq first (Prog.seq second third)).memSem memory := by
  rw [memSem_seq, memSem_seq, memSem_seq, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun result => ?_)
  rw [kleisli_bind]
  refine congrArg (kleisli · result) (funext fun final => ?_)
  rw [memSem_seq]

/-- **The multiplier cell**: `m < bound` by bounded rejection over `131` coins, at `tmpM`. -/
theorem memSem_multiplierCell (memory : Memory) (bound : Nat) (boundSmall : bound < 2 ^ 256)
    (guarded : memory.registers rB = word bound) :
    (Prog.seq (bounded multiplierWidth (testBelowRegister rB) attempts (storeAt tmpM rOut))
        (zeroRegs samplerScratch)).memSem memory =
      (rejectLaw multiplierWidth (fun value => decide (value < bound)) attempts).map fun kept =>
        kept.map fun value => clearRegs (storeRam memory (word tmpM) (BitVec.ofNat 256 value))
          samplerScratch := by
  have scratchJunk : attemptScratch [rAddr] = [rAcc, rBit, rAddr, rSel, rAddr] := rfl
  have outOut : rOut ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  have flagOut : rFlag ∉ attemptScratch [rAddr] := by rw [scratchJunk]; decide
  set start := setReg (setReg memory rOut (word 0)) rFlag (word 0) with startDef
  have startFlag : start.registers rFlag = bitWord false := by
    rw [startDef, setReg_registers, if_pos rfl]; rfl
  have startGuard : start.registers rB = word bound := by
    rw [startDef, reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), guarded]
  have shape : (Prog.seq (bounded multiplierWidth (testBelowRegister rB) attempts (storeAt tmpM rOut))
      (zeroRegs samplerScratch)).memSem memory =
      ((Prog.rep attempts fun _ => attempt multiplierWidth (testBelowRegister rB)).memSem start).bind
        (kleisli (cellTail tmpM)) := by
    unfold bounded rejection
    rw [memSem_seq, memSem_seq, PMF.bind_bind, memSem_cst_seq, memSem_cst_seq]
    have tailIs : cellTail tmpM = (Prog.seq (.ite rFlag (storeAt tmpM rOut) (.abort rSel))
        (zeroRegs samplerScratch)).memSem :=
      funext fun final => (memSem_cellContinuation tmpM final).symm
    rw [tailIs]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    rw [kleisli_bind]
    refine congrArg (kleisli · result) (funext fun final => ?_)
    rw [memSem_seq]
  rw [shape]
  have tailClear : ((Prog.rep attempts fun _ => attempt multiplierWidth (testBelowRegister rB)).memSem
      start).bind (kleisli (cellTail tmpM)) =
      (((Prog.rep attempts fun _ => attempt multiplierWidth (testBelowRegister rB)).memSem start).map
        (Option.map fun final => clearRegs final (attemptScratch [rAddr]))).bind
        (kleisli (cellTail tmpM)) := by
    rw [PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun result => ?_)
    cases result with
    | none => rfl
    | some final => exact (cellTail_clear tmpM final).symm
  rw [tailClear, rep_attempt_law_at multiplierWidth (by unfold multiplierWidth; omega)
      (testBelowRegister rB) (fun value => decide (value < bound)) [rAddr] rB (word bound)
      (isTest_testBelowRegister bound boundSmall) (by decide) (by decide) (by decide) (by decide)
      (by rw [scratchJunk]; decide) (by decide) (by decide) (by decide) attempts start
      ⟨false, startFlag⟩ startGuard,
    attemptsLaw_eq_rejectLaw multiplierWidth _ (attemptScratch [rAddr]) outOut flagOut attempts _
      (clearRegs_idem _ _) (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl),
    PMF.bind_map]
  rw [PMF.map]
  refine congrArg (PMF.bind _) (funext fun kept => ?_)
  cases kept with
  | none =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      rw [if_pos (by rw [clearRegs_registers, if_neg flagOut, startFlag]; rfl)]
      rfl
  | some value =>
      simp only [Function.comp_apply, kleisli, keptMem, cellTail]
      have flagOne : (clearRegs (setReg (setReg (clearRegs start (attemptScratch [rAddr])) rOut
          (BitVec.ofNat 256 value)) rFlag 1) (attemptScratch [rAddr])).registers rFlag = 1 := by
        rw [clearRegs_registers, if_neg flagOut, setReg_registers, if_pos rfl]
      rw [if_neg (by rw [flagOne]; decide)]
      simp only [Option.map_some]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [storeRam, setReg, (clearRegs_other _ _).1, clearRegs_registers, if_neg outOut,
          Function.update_of_ne (show rOut ≠ rFlag by decide), Function.update_self]
        rw [startDef]
        rfl
      · simp only [storeRam, setReg, (clearRegs_other _ _).2]
        rw [startDef]
        rfl
      · have notOut : index ≠ rOut := fun same => outside (by rw [same]; decide)
        have notFlag : index ≠ rFlag := fun same => outside (by rw [same]; decide)
        have notScratch : index ∉ attemptScratch [rAddr] := by
          intro inside
          apply outside
          rw [scratchJunk] at inside
          simp only [samplerScratch, List.mem_cons] at inside ⊢
          rcases inside with h | h | h | h | h | h <;> simp [h]
        have notAddr : index ≠ rAddr := fun same => notScratch (by rw [same, scratchJunk]; decide)
        simp only [storeRam, setReg_registers, clearRegs_registers, notAddr, notOut, notFlag,
          notScratch, if_false, startDef]

/-! ### One preimage -/

omit [FieldCertificate] in
/-- The multiplier bound `q + [y < ρ]` (the count of `sampleFp`-preimages of `y`). -/
def multBound (value : BaseField) : Nat :=
  preimageQuotient + (if value.val < preimageRemainder then 1 else 0)

/-- The memory one preimage leaves: `m` at `tmpM`, the limbs of `y + p · m` at `openLimb d c`. -/
def preMem (digit collector : Nat) (value : BaseField) (memory : Memory) (mult : Nat) : Memory :=
  clearRegs (withRam memory (putPoint (Function.update memory.ram (word tmpM) (word mult))
    (openLimb digit collector 0) (limbWords (value.val + pNat * mult)))) limbScratch

omit [FieldCertificate] in
theorem multBound_small (value : BaseField) : multBound value < 2 ^ 256 := by
  have : preimageQuotient < 2 ^ 255 := by decide
  unfold multBound
  split <;> omega

omit [FieldCertificate] in
theorem bound_word (value : BaseField) :
    Arithmetic.add.eval (bitWord (decide (value.val < preimageRemainder))) (word preimageQuotient) =
      word (multBound value) := by
  have quotientSmall : preimageQuotient < 2 ^ 255 := by decide
  have bitIs : bitWord (decide (value.val < preimageRemainder)) =
      word (if value.val < preimageRemainder then 1 else 0) := by
    by_cases below : value.val < preimageRemainder <;> simp [below, bitWord]
  rw [bitIs, word_add _ _ (by split <;> omega), multBound, Nat.add_comm]

/-- **One preimage**: the multiplier draw, then the limbs of `y + p · m` (exact). -/
theorem memSem_preimageOne (digit collector : Nat) (digitSmall : digit < 91)
    (collectorSmall : collector < 3) (memory : Memory) (value : BaseField)
    (targetCell : memory.ram (word (openTarget digit collector)) = fieldWord value) :
    (Opening.preimageOne digit collector).memSem memory =
      (rejectLaw multiplierWidth (fun candidate => decide (candidate < multBound value)) attempts).map
        (Option.map (preMem digit collector value memory)) := by
  have remainderSmall : preimageRemainder < 2 ^ 256 := by decide
  have quotientSmall : preimageQuotient < 2 ^ 256 := by decide
  unfold Opening.preimageOne
  simp only [Prog.seqList]
  rw [memSem_loadAt_seq, memSem_cst_seq]
  rw [targetCell,
    memSem_ar_val _ _ _ _ _ _ (fieldWord value) (word preimageRemainder) (by regv) (by regv),
    less_word, fieldWord_toNat, word_small remainderSmall, memSem_cst_seq,
    memSem_ar_val _ _ _ _ _ _ (bitWord (decide (value.val < preimageRemainder)))
      (word preimageQuotient) (by regv) (by regv), bound_word,
    ← memSem_seq_assoc, memSem_seq, memSem_multiplierCell _ (multBound value) (multBound_small value)
      (by regv), PMF.bind_map, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro kept member
  cases kept with
  | none => rfl
  | some mult =>
      have good := rejectLaw_support _ _ _ _ ((PMF.mem_support_iff _ _).mpr member)
      simp only [Function.comp_apply, Option.map_some, kleisli]
      set loaded := setReg (setReg (setReg (setReg (setReg (setReg memory rAddr
        (word (openTarget digit collector))) rC (fieldWord value)) rAddr (word preimageRemainder)) rD
        (bitWord (decide (value.val < preimageRemainder)))) rAddr (word preimageQuotient)) rB
        (word (multBound value)) with loadedDef
      have loadedRam : loaded.ram = memory.ram := by rw [loadedDef]; rfl
      rw [memSem_seq, memSem_limbsOf digit collector _ value mult (by unfold multiplierWidth at good; exact good.2)
        (by rw [(clearRegs_other _ _).1]; simp only [storeRam_ram, Function.update_self])
        (by
          rw [(clearRegs_other _ _).1]
          simp only [storeRam_ram]
          rw [Function.update_of_ne (by addr_ne), loadedRam, targetCell]),
        PMF.pure_bind]
      simp only [kleisli]
      rw [memSem_skip]
      refine congrArg (fun final => PMF.pure (some final)) ?_
      unfold preMem
      rw [clearRegs_eq_iff]
      refine ⟨?_, ?_, fun index outside => ?_⟩
      · simp only [withRam_ram, (clearRegs_other _ _).1, storeRam_ram, loadedRam]
      · simp only [withRam_bits, (clearRegs_other _ _).2, storeRam_bits, loadedDef, setReg_bits]
      · simp only [withRam_registers]
        simp only [limbScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
        obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := outside
        rw [clearRegs_registers, if_neg (by simp [samplerScratch, n0, n1, n2, n3, n4, n5]),
          storeRam_registers, loadedDef]
        simp only [setReg_registers, if_neg n4, if_neg n7, if_neg n8, if_neg n9]

/-! ### Reps: splitting, nesting, index-dependent draws -/

omit [FieldCertificate] in
theorem rep_congr (count : Nat) (body body' : Nat → Prog) (same : ∀ index, index < count → body index = body' index) :
    Prog.rep count body = Prog.rep count body' := by
  induction count with
  | zero => rw [Prog.rep, Prog.rep]
  | succ count ih =>
      rw [Prog.rep, Prog.rep, ih fun index bound => same index (by omega), same count (by omega)]

/-- A `rep` split after `first` bodies. -/
theorem memSem_rep_add (first : Nat) (body : Nat → Prog) :
    ∀ (second : Nat) (memory : Memory), (Prog.rep (first + second) body).memSem memory =
      ((Prog.rep first body).memSem memory).bind
        (kleisli (Prog.rep second fun index => body (first + index)).memSem)
  | 0, memory => by
      rw [Nat.add_zero]
      conv_lhs => rw [← PMF.bind_pure ((Prog.rep first body).memSem memory)]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      cases result <;> (rw [Prog.rep]; rfl)
  | second + 1, memory => by
      rw [← Nat.add_assoc, memSem_rep_succ, memSem_rep_add first body second memory, PMF.bind_bind]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      rw [kleisli_bind]
      refine congrArg (kleisli · result) (funext fun final => ?_)
      rw [memSem_rep_succ]

/-- **A nested `rep` is a flat one**, index `i ↦ (i / inner, i % inner)`. -/
theorem memSem_rep_nest (inner : Nat) (body : Nat → Nat → Prog) (innerPos : 0 < inner) :
    ∀ (outer : Nat) (memory : Memory),
      (Prog.rep outer fun digit => Prog.rep inner (body digit)).memSem memory =
        (Prog.rep (outer * inner) fun index => body (index / inner) (index % inner)).memSem memory
  | 0, memory => by rw [Nat.zero_mul, Prog.rep, Prog.rep]
  | outer + 1, memory => by
      rw [Nat.succ_mul, memSem_rep_succ, memSem_rep_add (outer * inner) _ inner,
        memSem_rep_nest inner body innerPos outer memory]
      refine congrArg (PMF.bind _) (funext fun result => ?_)
      rw [rep_congr inner (body outer) (fun index => body ((outer * inner + index) / inner)
        ((outer * inner + index) % inner)) (fun index bound => by
          congr 1
          · rw [Nat.add_comm, Nat.add_mul_div_right _ _ innerPos, Nat.div_eq_of_lt bound, Nat.zero_add]
          · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt bound])]

/-- **A `rep` of independent, index-dependent draws** under an invariant the stores keep. -/
theorem memSem_rep_law_idx {α : Type} (holds : Memory → Prop) :
    ∀ (count : Nat) (law : Nat → PMF (Option α)) (body : Nat → Prog)
      (step : Nat → Memory → α → Memory),
      (∀ index, index < count → ∀ memory, holds memory →
        (body index).memSem memory = (law index).map (Option.map (step index memory))) →
      (∀ index, index < count → ∀ memory value, holds memory → holds (step index memory value)) →
      ∀ memory, holds memory → (Prog.rep count body).memSem memory =
        (optionProduct count fun index => law index.val).map
          (Option.map (foldStore step count memory))
  | 0, law, body, step, _, _, memory, _ => by
      rw [Prog.rep]
      simp only [Prog.memSem, optionProduct, PMF.pure_map, Option.map_some]
      rw [foldStore]
  | count + 1, law, body, step, each, keeps, memory, start => by
      rw [memSem_rep_front, each 0 (by omega) memory start, PMF.bind_map]
      simp only [optionProduct]
      rw [PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun drawn => ?_)
      cases drawn with
      | none => simp [kleisli, PMF.pure_map]
      | some value =>
          simp only [Function.comp_apply, Option.map_some, kleisli]
          rw [memSem_rep_law_idx holds count (fun index => law (index + 1))
            (fun index => body (index + 1)) (fun index => step (index + 1))
            (fun index bound memory hm => each (index + 1) (by omega) memory hm)
            (fun index bound memory value hm => keeps (index + 1) (by omega) memory value hm)
            (step 0 memory value) (keeps 0 (by omega) memory value start), PMF.map_comp]
          refine congrArg (PMF.map · _) (funext fun values => ?_)
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some]
              rw [foldStore]
              simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ]

omit [FieldCertificate] in
/-- A family of mapped draws is the product of the draws, mapped. -/
theorem optionProduct_map_idx {α β : Type} :
    ∀ (count : Nat) (law : Fin count → PMF (Option α)) (map : Fin count → α → β),
      optionProduct count (fun index => (law index).map (Option.map (map index))) =
        (optionProduct count law).map (Option.map fun values index => map index (values index))
  | 0, law, map => by
      simp only [optionProduct, PMF.pure_map, Option.map_some]
      congr 2
      funext index
      exact index.elim0
  | count + 1, law, map => by
      simp only [optionProduct]
      rw [PMF.bind_map, PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun drawn => ?_)
      cases drawn with
      | none => simp [PMF.pure_map]
      | some head =>
          simp only [Function.comp_apply, Option.map_some]
          rw [optionProduct_map_idx count (fun index => law index.succ) (fun index => map index.succ),
            PMF.map_comp, PMF.map_comp]
          refine congrArg (PMF.map · _) (funext fun values => ?_)
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some]
              congr 1
              funext index
              cases index using Fin.cases with
              | zero => rfl
              | succ index => rfl

end

end Kriterion.ArgoMAC.PlanB.SimMachine
