/-
**Phase 3, P1f — stage 1, fixed-key hits: at most `2^-128` each, given the stage-1 view.**

For every fixed-key index `i` a one-parameter family of join-keeping tape shifts moves the garbler's
point and output at `i` by `c` (`familyAt`): a fold gate of step `0` by the coordinate's `Δ`; a fold
gate of step `1` by the zero label of its chunk's low bit; a scale switch by the zero label of its
chunk's high bit, compensated in the fold material of the switch's parent; a gadget position by
its zero label. None of these touches the published value or the EncPRF entries, so by
`event_le_of_symmetry`:

* `inputHit_le`:  `μ{view₁ = v ∧ the garbler asks i at x}  ≤ 2^-128 · μ{view₁ = v}`;
* `outputHit_le`: `μ{view₁ = v ∧ the garbler's answer at i is y} ≤ 2^-128 · μ{view₁ = v}`.
-/

import Proof.Privacy.Phase3.Hidden.Views

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-! ### The families -/

/-- Shift one coordinate's `Δ`. -/
def familyDelta (κ : Coord) (c : Block) : TapeShift :=
  ⟨fun κ' => if κ' = κ then c else 0, fun _ _ => 0, 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0⟩

/-- Shift one zero label; when it is a chunk's high bit, compensate in the material of `parity`. -/
def familyZero (κ : Coord) (position : Fin PlanB.coordinateBits) (c : Block) (parity : Nat) : TapeShift :=
  ⟨fun _ => 0, fun κ' p => if κ' = κ ∧ p = position then c else 0, 0,
    fun ℓ ch n r => if ℓ.coord = κ ∧ n = 1 ∧ chunkOffset ch + 1 = position.val ∧ r = parity then c else 0,
    fun _ _ _ _ => 0⟩

theorem xorFold_two (f : Fin (2 ^ 1) → Block) : xorFold f = f 0 ^^^ f 1 := by
  show Fin.foldl 2 (fun acc e => acc ^^^ f e) 0 = _
  rw [Fin.foldl_succ_last, Fin.foldl_succ_last, Fin.foldl_zero]
  show ((0 : Block) ^^^ f 0) ^^^ f 1 = f 0 ^^^ f 1
  exact congrArg (· ^^^ f 1) BitVec.zero_xor

theorem chunkWidth_two (c : Fin chunkCount) : chunkWidth c = 2 := by
  unfold chunkWidth chunkWidthNat
  split <;> rfl

theorem chunkOffset_lt (ch : Fin chunkCount) : chunkOffset ch + 1 < PlanB.coordinateBits := by
  have inside := chunkOffset_add_width_le ch
  rw [chunkWidth_two] at inside
  omega

/-- The step-`1` zero label of a lane's chunk is the zero label of the chunk's high bit. -/
theorem fold_zero_one (T : TapeShift) (ℓ : Lane) (ch : Fin chunkCount) :
    ((T.lane ℓ).fold ch).zero 1 =
      T.zero ℓ.coord ⟨chunkOffset ch + 1, chunkOffset_lt ch⟩ ^^^ (if laneIsPoint ℓ then T.key2 else 0) := by
  simp only [LaneShift.fold, TapeShift.lane]
  unfold labelAt
  rw [dif_pos (by rw [chunkWidth_two]; omega)]
  rfl

theorem fold_zero_zero (T : TapeShift) (ℓ : Lane) (ch : Fin chunkCount) :
    ((T.lane ℓ).fold ch).zero 0 =
      T.zero ℓ.coord ⟨chunkOffset ch, by have := chunkOffset_lt ch; omega⟩ ^^^
        (if laneIsPoint ℓ then T.key2 else 0) := by
  simp only [LaneShift.fold, TapeShift.lane]
  unfold labelAt
  rw [dif_pos (by rw [chunkWidth_two]; omega)]
  rfl

/-- A shift is valid when, at every lane and chunk, the step-`1` materials XOR to the high bit's
zero-label shift. -/
theorem valid_of_step (T : TapeShift)
    (step : ∀ ℓ ch, T.m ℓ ch 1 0 ^^^ T.m ℓ ch 1 1 =
      T.zero ℓ.coord ⟨chunkOffset ch + 1, chunkOffset_lt ch⟩ ^^^ (if laneIsPoint ℓ then T.key2 else 0)) :
    T.Valid := by
  intro ℓ ch n one small
  rw [chunkWidth_two] at small
  obtain rfl : n = 1 := by omega
  rw [xorFold_two, fold_zero_one]
  exact step ℓ ch

theorem familyDelta_valid (κ : Coord) (c : Block) : (familyDelta κ c).Valid :=
  valid_of_step _ fun ℓ ch => by simp only [familyDelta, ite_self, BitVec.xor_zero]

theorem familyZero_valid (κ : Coord) (position : Fin PlanB.coordinateBits) (c : Block) (parity : Nat)
    (small : parity < 2) : (familyZero κ position c parity).Valid := by
  refine valid_of_step _ fun ℓ ch => ?_
  simp only [familyZero, ite_self, BitVec.xor_zero]
  by_cases hit : ℓ.coord = κ ∧ chunkOffset ch + 1 = position.val
  · have fin : (⟨chunkOffset ch + 1, chunkOffset_lt ch⟩ : Fin PlanB.coordinateBits) = position :=
      Fin.ext hit.2
    interval_cases parity <;> simp [hit.1, hit.2, fin]
  · have fin : ¬ (ℓ.coord = κ ∧ (⟨chunkOffset ch + 1, chunkOffset_lt ch⟩ : Fin PlanB.coordinateBits) =
        position) := fun both => hit ⟨both.1, congrArg Fin.val both.2⟩
    have left : ¬ (ℓ.coord = κ ∧ chunkOffset ch + 1 = position.val ∧ 0 = parity) :=
      fun all => hit ⟨all.1, all.2.1⟩
    have right : ¬ (ℓ.coord = κ ∧ chunkOffset ch + 1 = position.val ∧ 1 = parity) :=
      fun all => hit ⟨all.1, all.2.1⟩
    simp only [true_and, left, right, fin, if_false, BitVec.xor_self]

theorem labelAt_zero_chunk (ch : Fin chunkCount) (f : Fin (chunkWidth ch) → Block) :
    labelAt f 0 = f ⟨0, by rw [chunkWidth_two]; omega⟩ := by
  unfold labelAt
  rw [dif_pos (by rw [chunkWidth_two]; omega)]

theorem chunkBitIndex_zero (ch : Fin chunkCount) (h : 0 < chunkWidth ch) :
    chunkBitIndex ch ⟨0, h⟩ = ⟨chunkOffset ch, by have := chunkOffset_lt ch; omega⟩ :=
  Fin.ext rfl

theorem shiftEntry_fst_hash [FieldCertificate] [GroupCertificate] (T : TapeShift) (scalar : NonZeroScalar)
    (coins : Coins) (value : BaseField) (answer : (PublicQuery.hash (FixedIndex := FixedIndex)
      (EncIndex := EncPRF.PermutationIndex) value).Answer) :
    (shiftEntry T scalar coins ⟨.hash value, answer⟩).1 = .hash value := by
  by_cases h : value = coins.bridgeKey <;> simp [shiftEntry, h]

/-- **The family moving index `i` by `c`.** -/
def familyAt : FixedIndex → Block → TapeShift
  | .hot ℓ ch fold _ _, c =>
      if fold.val = 0 then familyDelta ℓ.coord c
      else familyZero ℓ.coord ⟨chunkOffset ch, by have := chunkOffset_lt ch; omega⟩ c 0
  | .scale ℓ ch switch _ _, c =>
      familyZero ℓ.coord ⟨chunkOffset ch + 1, chunkOffset_lt ch⟩ c (switch.val % 2)
  | .gadget _ κ position, c => familyZero κ position c 0

theorem familyAt_valid (index : FixedIndex) (c : Block) : (familyAt index c).Valid := by
  cases index with
  | hot ℓ ch fold entry half =>
      by_cases h : fold.val = 0
      · simp only [familyAt, h, if_true]
        exact familyDelta_valid _ _
      · simp only [familyAt, h, if_false]
        exact familyZero_valid _ _ _ _ (by omega)
  | scale ℓ ch switch element block => exact familyZero_valid _ _ _ _ (Nat.mod_lt _ (by omega))
  | gadget o κ position => exact familyZero_valid _ _ _ _ (by omega)

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **The family moves its index's point and output by `c`.** -/
theorem familyAt_moves (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) (c : Block) :
    indexShift (familyAt index c) scalar coins index = (c, c) := by
  cases index with
  | hot ℓ ch fold entry half =>
      obtain ⟨f, hf⟩ := fold
      have two : chunkBits = 2 := rfl
      rw [two] at hf
      interval_cases f
      · simp [familyAt, indexShift, FoldShift.hot, FoldShift.level, LaneShift.fold, TapeShift.lane,
          familyDelta]
      · have ne : chunkOffset ch + 1 ≠ chunkOffset ch := by omega
        simp [familyAt, indexShift, FoldShift.hot, FoldShift.level, FoldShift.stepShift,
          labelAt_zero_chunk, chunkBitIndex_zero, familyZero, ne, TapeShift.lane, LaneShift.fold]
  | scale ℓ ch switch element block =>
      obtain ⟨sw, hsw⟩ := switch
      have two : 2 ^ chunkBits = 4 := rfl
      rw [two] at hsw
      have ne : chunkOffset ch ≠ chunkOffset ch + 1 := by omega
      have fin : ¬ ((⟨chunkOffset ch, by have := chunkOffset_lt ch; omega⟩ : Fin PlanB.coordinateBits) =
          ⟨chunkOffset ch + 1, chunkOffset_lt ch⟩) := fun same => ne (congrArg Fin.val same)
      interval_cases sw <;>
        simp [familyAt, indexShift, FoldShift.level, FoldShift.stepShift, chunkWidth_two,
          labelAt_zero_chunk, chunkBitIndex_zero, familyZero, fin, TapeShift.lane, LaneShift.fold]
  | gadget o κ position =>
      simp [familyAt, indexShift, gadgetShift, familyZero]

theorem inputHit_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (x : Block)
    (hit : InputHit scalar index x (shiftTape T scalar tape)) :
    garblerPointOf scalar tape index ^^^ (indexShift T scalar tape.1 index).1 = x := by
  obtain ⟨y, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have good := garblerTranscript_good scalar tape e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input =>
      simp only [shiftEntry, Sigma.mk.inj_iff, PublicQuery.fixedForward.injEq] at same
      obtain ⟨⟨rfl, rfl⟩, _⟩ := same
      rw [show input = garblerPointOf scalar tape index from good]
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      have fst := congrArg Sigma.fst same
      rw [shiftEntry_fst_hash] at fst
      cases fst

theorem outputHit_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (index : FixedIndex) (y : Block)
    (hit : OutputHit scalar index y (shiftTape T scalar tape)) :
    tape.2.1.permutation index (garblerPointOf scalar tape index) ^^^
      (indexShift T scalar tape.1 index).2 = y := by
  obtain ⟨x, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have good := garblerTranscript_good scalar tape e eMember
  have consistent := transcript_consistent tape.2 (Programs.garbleM scalar tape.1) e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input =>
      simp only [shiftEntry, Sigma.mk.inj_iff, PublicQuery.fixedForward.injEq] at same
      obtain ⟨⟨rfl, _⟩, answerSame⟩ := same
      have answerEq : answer = tape.2.1.permutation index input := consistent
      rw [← show input = garblerPointOf scalar tape index from good, ← answerEq]
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      have fst := congrArg Sigma.fst same
      rw [shiftEntry_fst_hash] at fst
      cases fst

theorem card_block' : Fintype.card Block = 2 ^ 128 := Kriterion.ArgoMAC.Security.PGS.card_block

/-- **Stage 1: an input hit, at most `2^-128` given the view.** -/
theorem inputHit_le (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (x : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ InputHit scalar index x tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageOneView parameter scalar)
    (InputHit scalar index x) (fun c tape => shiftTape (familyAt index c) scalar tape)
    (fun c => swapped_shift_invariant _ (familyAt_valid index c) scalar)
    (fun c tape => stageOneView_shift _ (familyAt_valid index c) parameter scalar tape)
    (fun tape c c' first second => by
      have one := inputHit_shift _ (familyAt_valid index c) scalar tape index x first
      have two := inputHit_shift _ (familyAt_valid index c') scalar tape index x second
      rw [familyAt_moves] at one two
      have := one.trans two.symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

/-- **Stage 1: an output hit, at most `2^-128` given the view.** -/
theorem outputHit_le (parameter : ℕ) (scalar : NonZeroScalar)
    (view : Public × List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (y : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageOneView parameter scalar tape = view ∧ OutputHit scalar index y tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ *
        swappedChallengeTape.toOuterMeasure {tape | stageOneView parameter scalar tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageOneView parameter scalar)
    (OutputHit scalar index y) (fun c tape => shiftTape (familyAt index c) scalar tape)
    (fun c => swapped_shift_invariant _ (familyAt_valid index c) scalar)
    (fun c tape => stageOneView_shift _ (familyAt_valid index c) parameter scalar tape)
    (fun tape c c' first second => by
      have one := outputHit_shift _ (familyAt_valid index c) scalar tape index y first
      have two := outputHit_shift _ (familyAt_valid index c') scalar tape index y second
      rw [familyAt_moves] at one two
      have := one.trans two.symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
