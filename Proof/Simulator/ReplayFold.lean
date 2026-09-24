/-
**The replay, one chunk's fold** (`chunkPrefix` against the evaluator's two-level `evalFoldM`).

The chunk value `α = (coord >> 2c) & 3` and its bit `0` are stored; the level-1 labels are the
bit-`0` label twice (step `0` is free); step `1` hashes the one inactive entry (`foldPair`) and
recovers the active one from the published join; the four one-hot labels are stored at
`hotLabelBase .. + 3`.
-/

import Proof.Simulator.ReplaySwitch

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

theorem rtree_seq_assoc (first second third : Prog) (memory : Memory) :
    rtree (.seq (.seq first second) third) memory = rtree (.seq first (.seq second third)) memory := by
  simp only [rtree_seq]
  exact bindOpt_assoc _ _ _

omit [FieldCertificate] in
theorem hotIdx_eq (lane : Lane) (chunk : Fin chunkCount) (entry : Nat) (half : Bool) :
    Replay.hotIdx lane chunk.val entry half = hotIndexNat lane chunk 1 entry half := by
  unfold Replay.hotIdx
  rw [show Replay.chunkFin chunk.val = chunk from Fin.ext (Nat.mod_eq_of_lt chunk.isLt)]

/-- What the fold pair leaves: `rC` holds the step material. -/
def PairPost (memory : Memory) (mask : Block) (after : Memory) : Prop :=
  after.ram = memory.ram ∧ after.bits = memory.bits ∧
    after.registers rInput = memory.registers rInput ∧ after.registers rC = blockWord mask

/-- **The fold pair**: two hashes of the held label, `rC` = their sum. -/
theorem agree_foldPair (spec : Replay.LaneSpec) (chunk : Fin chunkCount) (entry : Nat)
    (memory : Memory) (label : Block) (input : memory.registers rInput = blockWord label) :
    Agree (PairPost memory) (rtree (Replay.foldPair ordF0 spec chunk.val entry) memory)
      (Programs.foldMaskM spec.lane chunk 1 entry label) := by
  unfold Replay.foldPair Programs.foldMaskM
  simp only [hotIdx_eq, TreeLaws.monad_bind, TreeLaws.monad_pure]
  refine agree_hashStep _ rC _ memory label input _ fun first => ?_
  set m1 := hashMem memory (ordF0 (hotIndexNat spec.lane chunk 1 entry false)) rC first label
    with m1Def
  have input1 : m1.registers rInput = blockWord label := by
    rw [m1Def, hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide), input]
  refine agree_hashStep _ rFirst _ m1 label input1 _ fun second => ?_
  rw [rtree_ar]
  refine .leaf ⟨rfl, rfl, ?_, ?_⟩
  · rw [reg_ne _ _ _ _ (by decide), hashMem_other _ _ _ _ _ _ (by decide) (by decide) (by decide)
      (by decide), input1, input]
  · rw [reg_same, eval_xor, hashMem_target, hashMem_other _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide), m1Def, hashMem_target, blockWord_xor]

/-! ### The fold is clean -/

omit [FieldCertificate] in
theorem not_designated_hot (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (half : Bool) : ¬ IsDesignated bits (hotIndexNat lane chunk step entry half) := by
  rintro ⟨digit, collector, block, same⟩
  simp [designatedIndex, scaleIndexOf, scaleIndexNat, hotIndexNat] at same

omit [FieldCertificate] in
theorem clean_foldMaskM (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) : Clean bits (Programs.foldMaskM lane chunk step entry label) :=
  (clean_hashM bits _ label (not_designated_hot bits lane chunk step entry false)).bind fun _ =>
    (clean_hashM bits _ label (not_designated_hot bits lane chunk step entry true)).bind fun _ =>
      .pure _

omit [FieldCertificate] in
theorem clean_evalFoldM (bits : BitInput) (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ steps,
      Clean bits (Programs.evalFoldM lane chunk value bitLabel join steps)
  | 0 => .pure _
  | steps + 1 => (clean_evalFoldM bits lane chunk value bitLabel join steps).bind fun previous =>
      ((Clean.vector _ fun entry => by
        by_cases active : entry = activeAt value steps
        · simp only [if_pos active]; exact .pure _
        · simp only [if_neg active]; exact clean_foldMaskM bits lane chunk steps entry.val _).bind
          fun _ => .pure _).bind fun _ => .pure _

/-! ### The two-level fold, unfolded -/

omit [FieldCertificate] in
theorem vector_pow_zero {spec : OracleSpec.{0, 0}} {α : Type} (f : Fin (2 ^ 0) → FreeQuery spec α) :
    FreeQuery.vector (2 ^ 0) f = FreeQuery.bind (f 0) fun v => .pure #v[v] := rfl

omit [FieldCertificate] in
theorem vector_pow_one {spec : OracleSpec.{0, 0}} {α : Type} (f : Fin (2 ^ 1) → FreeQuery spec α) :
    FreeQuery.vector (2 ^ 1) f =
      FreeQuery.bind (f 0) fun v0 => FreeQuery.bind (f 1) fun v1 => .pure #v[v0, v1] := by
  show FreeQuery.vector 2 f = _
  simp only [FreeQuery.vector, TreeLaws.monad_bind, TreeLaws.monad_pure, TreeLaws.bind_assoc,
    TreeLaws.bind_pure_left]
  rfl

omit [FieldCertificate] in
theorem activeAt_zero (value : Nat) : activeAt value 0 = 0 := Fin.ext (by simp [activeAt])

omit [FieldCertificate] in
theorem activeAt_one (value : Nat) : (activeAt value 1).val = value % 2 := by simp [activeAt]

omit [FieldCertificate] in
/-- The level-1 labels: the bit-`0` label twice (step `0` is free). -/
theorem levelOne (value : Nat) (bitLabel join : Nat → Block) (free : join 0 = 0) :
    extendLevel 0 (fun _ => 0) (fun entry => if entry = activeAt value 0 then
      join 0 ^^^ bitLabel 0 ^^^ xorFoldExcept (activeAt value 0) (#v[(0 : Block)] : Vector Block (2 ^ 0)).get
      else (#v[(0 : Block)] : Vector Block (2 ^ 0)).get entry) = fun _ => bitLabel 0 := by
  funext entry
  have entryZero : ∀ other : Fin (2 ^ 0), other = activeAt value 0 := fun other =>
    Fin.ext (by have := other.isLt; simp [activeAt] at this ⊢ <;> omega)
  unfold extendLevel xorFoldExcept
  dsimp only
  have foldOne : ∀ start : Block, Fin.foldl 1 (fun (acc : Block) (_ : Fin 1) => acc) start = start :=
    fun start => by
      show Fin.foldl (0 + 1) _ start = start
      rw [Fin.foldl_succ, Fin.foldl_zero]
  split <;> (rw [if_pos (entryZero _), free]; simp [entryZero, foldOne])

omit [FieldCertificate] in
theorem xorFoldExcept_zero (f : Fin (2 ^ 1) → Block) : xorFoldExcept 0 f = f 1 := by
  unfold xorFoldExcept
  show Fin.foldl (0 + 1 + 1) _ 0 = _
  rw [Fin.foldl_succ, Fin.foldl_succ, Fin.foldl_zero]
  simp

omit [FieldCertificate] in
theorem xorFoldExcept_one (f : Fin (2 ^ 1) → Block) : xorFoldExcept 1 f = f 0 := by
  unfold xorFoldExcept
  show Fin.foldl (0 + 1 + 1) _ 0 = _
  rw [Fin.foldl_succ, Fin.foldl_succ, Fin.foldl_zero]
  simp

/-- The step-1 material: the active entry is recovered from the join. -/
def foldRight (L1 J M : Block) (active entry : Nat) : Block := if entry = active then J ^^^ L1 ^^^ M else M

/-- The four one-hot labels of a chunk. -/
def foldHot (L0 L1 J M : Block) (active : Nat) (entry : Fin (2 ^ 2)) : Block :=
  if entry.val < 2 then L0 ^^^ foldRight L1 J M active entry.val
  else foldRight L1 J M active (entry.val - 2)

omit [FieldCertificate] in
/-- **The two-level fold, unfolded**: one step-1 entry is hashed (the inactive one,
`1 − (value mod 2)`), and the labels are `foldHot`. -/
theorem evalFold_two (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block)
    (free : join 0 = 0) :
    Programs.evalFoldM lane chunk value bitLabel join 2 =
      FreeQuery.bind (Programs.foldMaskM lane chunk 1 (1 - value % 2) (bitLabel 0)) fun mask =>
        .pure (foldHot (bitLabel 0) (bitLabel 1) (join 1) mask (value % 2)) := by
  have zeroActive : ∀ other : Fin (2 ^ 0), other = activeAt value 0 := fun other =>
    Fin.ext (by have := other.isLt; simp [activeAt] at this ⊢ <;> omega)
  simp only [Programs.evalFoldM, Programs.evalStepM, vector_pow_zero, vector_pow_one,
    TreeLaws.monad_bind, TreeLaws.monad_pure, TreeLaws.bind_assoc, TreeLaws.bind_pure_left,
    if_pos (zeroActive 0)]
  rw [levelOne value bitLabel join free]
  rcases Nat.mod_two_eq_zero_or_one value with even | odd
  · have active : activeAt value 1 = 0 := Fin.ext (by rw [activeAt_one, even]; rfl)
    rw [if_pos active.symm, if_neg (by rw [active]; decide), even]
    simp only [TreeLaws.bind_pure_left]
    congr 1
    funext mask
    congr 1
    funext entry
    rw [active]
    fin_cases entry <;> simp [extendLevel, foldHot, foldRight, xorFoldExcept_zero]
  · have active : activeAt value 1 = 1 := Fin.ext (by rw [activeAt_one, odd]; rfl)
    rw [if_neg (by rw [active]; decide), if_pos active.symm, odd]
    simp only [TreeLaws.bind_pure_left]
    congr 1
    funext mask
    congr 1
    funext entry
    rw [active]
    fin_cases entry <;> simp [extendLevel, foldHot, foldRight, xorFoldExcept_one]

/-! ### Words of the chunk prefix -/

theorem word_chunkValue (coord chunk : Nat) (small : coord < 2 ^ 256) (chunkSmall : 2 * chunk < 2 ^ 256) :
    Arithmetic.and.eval (Arithmetic.shiftRight.eval (word coord) (word (2 * chunk))) (word 3) =
      word ((coord >>> (2 * chunk)) % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_and, BitVec.toNat_ushiftRight, word_small small,
    word_small chunkSmall, word_small (show 3 < 2 ^ 256 by norm_num)]
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    word_small (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))]

theorem word_bitZero (value : Nat) (small : value < 4) :
    Arithmetic.and.eval (word value) (word 1) = word (value % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_and, word_small (show value < 2 ^ 256 by omega),
    word_small (show 1 < 2 ^ 256 by norm_num)]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    word_small (show value % 2 < 2 ^ 256 by omega)]

theorem hotLabel_ne (first second : Nat) (firstSmall : first < 5) (secondSmall : second < 5)
    (different : first ≠ second) : word (hotLabelBase + first) ≠ word (hotLabelBase + second) :=
  word_ne (by unfold hotLabelBase; omega) (by unfold hotLabelBase; omega) (by omega)

theorem hotLabel_ne_tmp (first second : Nat) (firstSmall : first < 5) (secondSmall : second < 16) :
    word (hotLabelBase + first) ≠ word (tmpBase + second) :=
  word_ne (by unfold hotLabelBase; omega) (by unfold tmpBase; omega)
    (by unfold hotLabelBase tmpBase; omega)

theorem tmp_ne (first second : Nat) (firstSmall : first < 16) (secondSmall : second < 16)
    (different : first ≠ second) : word (tmpBase + first) ≠ word (tmpBase + second) :=
  word_ne (by unfold tmpBase; omega) (by unfold tmpBase; omega) (by omega)

end

end Kriterion.ArgoMAC.PlanB.SimMachine