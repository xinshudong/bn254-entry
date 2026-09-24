/-
**Phase 3, P1h — the stage-2 tape shifts.**

Three join-keeping `TapeShift` families, each parametrised by `c : Block`:

* **`familyDeltaU κ u c`** (the Δ-family of coordinate `κ` at the input `u`): `Δ_κ += c`, the zero
  label of every bit of `κ` that `u` sets `+= c` (so every label of `u` is kept:
  `zero ⊕ u·(Δ ⊕ c) ⊕ c·u = zero ⊕ u·Δ`), and per chunk the step material of the active parent
  `+= c` exactly when the chunk's high bit is set. Every **inactive** fold gate of step `1` and every
  **inactive** switch keeps its point and output (`deltaU_hot_off`, `deltaU_level_off`); the active
  parent's point and the active switch move by `c` (`deltaU_hot_on`, `deltaU_level_on`); a gadget
  position moves by `c` iff `u`'s bit differs from the exceptional input's (`deltaU_gadget`).
* **`familyKey2 z c`** (off the curve): `k₂ += c`; per point-lane chunk the step material of every
  parent but `z` `+= c`. The curve lanes are untouched (`key2_curve_*`); every point-lane fold gate
  of step `1` moves its point by `c`, the switches `z` and `≠ z + 2` move by `c`
  (`key2_level_point`), every gadget position by `c`.
* **`familyHotOut ℓ k r c`**: both outputs of the fold gate `(ℓ, k, 1, r)` move by `c`, nothing
  else moves (`hotOut_hot`, `hotOut_level`).
-/

import Proof.Privacy.Phase3.Hidden.GarblerAsk

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-! ### Two levels of a width-2 fold -/

theorem FoldShift.level_one (F : FoldShift) (j : Nat) :
    F.level 1 j = if j = 0 then F.delta ^^^ F.zero 0 else F.zero 0 := by
  show (if j < 2 ^ 0 then F.level 0 j ^^^ F.stepShift 0 j else F.stepShift 0 (j - 2 ^ 0)) = _
  by_cases h : j = 0
  · subst h
    rfl
  · rw [if_neg (by rw [pow_zero]; omega), if_neg h]
    rfl

theorem FoldShift.level_two (F : FoldShift) (j : Nat) :
    F.level 2 j = if j < 2 then F.level 1 j ^^^ F.m 1 j else F.m 1 (j - 2) := by
  show (if j < 2 ^ 1 then F.level 1 j ^^^ F.stepShift 1 j else F.stepShift 1 (j - 2 ^ 1)) = _
  rfl

theorem fold_level_width (F : FoldShift) (c : Fin chunkCount) (j : Nat) :
    F.level (chunkWidth c) j = F.level 2 j := by
  rw [chunkWidth_two]

/-! ### Chunk bits -/

theorem chunkOf_lt_four (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) :
    (chunkOf bits k).val < 4 := by
  have small := (chunkOf bits k).isLt
  have four : 2 ^ chunkWidth k = 4 := by rw [chunkWidth_two]; rfl
  omega

theorem chunkOf_val (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) :
    (chunkOf bits k).val = bits.toNat / 2 ^ chunkOffset k % 4 := by
  show bits.toNat >>> chunkOffset k % 2 ^ chunkWidth k = _
  rw [chunkWidth_two, Nat.shiftRight_eq_div_pow]
  rfl

/-- The low bit of a chunk is the chunk value's parity. -/
theorem getLsb_chunk_low (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) :
    bits.getLsb ⟨chunkOffset k, by have := chunkOffset_lt k; omega⟩ =
      decide ((chunkOf bits k).val % 2 = 1) := by
  show bits.toNat.testBit (chunkOffset k) = _
  rw [Nat.testBit_eq_decide_div_mod_eq, chunkOf_val]
  generalize bits.toNat / 2 ^ chunkOffset k = m
  have : m % 4 % 2 = m % 2 := by omega
  rw [this]

/-- The high bit of a chunk is the chunk value's half. -/
theorem getLsb_chunk_high (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) :
    bits.getLsb ⟨chunkOffset k + 1, chunkOffset_lt k⟩ = decide ((chunkOf bits k).val / 2 = 1) := by
  show bits.toNat.testBit (chunkOffset k + 1) = _
  rw [Nat.testBit_eq_decide_div_mod_eq, chunkOf_val, pow_succ, ← Nat.div_div_eq_div_mul]
  generalize bits.toNat / 2 ^ chunkOffset k = m
  have : m % 4 / 2 = m / 2 % 2 := by omega
  rw [this]

theorem chunkBitIndex_zero' (k : Fin chunkCount) (h : 0 < chunkWidth k) :
    chunkBitIndex k ⟨0, h⟩ = ⟨chunkOffset k, by have := chunkOffset_lt k; omega⟩ := Fin.ext rfl

theorem chunkBitIndex_one' (k : Fin chunkCount) (h : 1 < chunkWidth k) :
    chunkBitIndex k ⟨1, h⟩ = ⟨chunkOffset k + 1, chunkOffset_lt k⟩ := Fin.ext rfl

theorem lane_fold_zero_zero (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).zero 0 =
      T.zero ℓ.coord ⟨chunkOffset k, by have := chunkOffset_lt k; omega⟩ ^^^
        (if laneIsPoint ℓ then T.key2 else 0) := fold_zero_zero T ℓ k

theorem lane_fold_zero_one (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).zero 1 =
      T.zero ℓ.coord ⟨chunkOffset k + 1, chunkOffset_lt k⟩ ^^^ (if laneIsPoint ℓ then T.key2 else 0) :=
  fold_zero_one T ℓ k

theorem lane_fold_delta (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).delta = T.delta ℓ.coord := rfl

theorem lane_fold_m (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).m = T.m ℓ k := rfl

theorem lane_fold_o (T : TapeShift) (ℓ : Lane) (k : Fin chunkCount) :
    ((T.lane ℓ).fold k).o = T.o ℓ k := rfl

/-! ### The Δ-family -/

/-- The active parent at step `1`: the chunk's low bit. -/
def lowOf (input : AffineInput) (κ : Coord) (k : Fin chunkCount) : Nat :=
  (chunkOf (inputBits input κ) k).val % 2

/-- The chunk's high bit. -/
def highOf (input : AffineInput) (κ : Coord) (k : Fin chunkCount) : Nat :=
  (chunkOf (inputBits input κ) k).val / 2

/-- **The Δ-family of coordinate `κ` at the input.** -/
def familyDeltaU (κ : Coord) (input : AffineInput) (c : Block) : TapeShift where
  delta κ' := if κ' = κ then c else 0
  zero κ' p := if κ' = κ ∧ (inputBits input κ).getLsb p = true then c else 0
  key2 := 0
  m ℓ k n r := if ℓ.coord = κ ∧ n = 1 ∧ r = lowOf input κ k ∧ highOf input κ k = 1 then c else 0
  o _ _ _ _ := 0

theorem block_xor_self (c : Block) : c ^^^ c = 0 := BitVec.xor_self

theorem bxor_zero (c : Block) : c ^^^ (0 : Block) = c := BitVec.xor_zero

theorem bzero_xor (c : Block) : (0 : Block) ^^^ c = c := BitVec.zero_xor

theorem ite_xor_zero (P : Prop) [Decidable P] (c : Block) : (if P then c else 0) ^^^ (0 : Block) =
    if P then c else 0 := BitVec.xor_zero

theorem familyDeltaU_valid (κ : Coord) (input : AffineInput) (c : Block) :
    (familyDeltaU κ input c).Valid := by
  refine valid_of_step _ fun ℓ k => ?_
  have high := getLsb_chunk_high (inputBits input κ) k
  have small := chunkOf_lt_four (inputBits input κ) k
  simp only [familyDeltaU, true_and, lowOf, highOf, ite_self, BitVec.xor_zero]
  by_cases hκ : ℓ.coord = κ
  · simp only [hκ, true_and, high]
    generalize (chunkOf (inputBits input κ) k).val = α at small ⊢
    interval_cases α <;> simp [block_xor_self]
  · simp [hκ]

/-- The Δ-family's fold shift of lane `ℓ`, chunk `k`, at a lane of coordinate `κ`: the four
parameters. -/
theorem deltaU_fold (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (hκ : ℓ.coord = κ) :
    (((familyDeltaU κ input c).lane ℓ).fold k).delta = c ∧
    (((familyDeltaU κ input c).lane ℓ).fold k).zero 0 = (if lowOf input κ k = 1 then c else 0) ∧
    (∀ r, (((familyDeltaU κ input c).lane ℓ).fold k).m 1 r =
      if r = lowOf input κ k ∧ highOf input κ k = 1 then c else 0) ∧
    (∀ n r, (((familyDeltaU κ input c).lane ℓ).fold k).o n r = 0) := by
  have low := getLsb_chunk_low (inputBits input κ) k
  refine ⟨?_, ?_, fun r => ?_, fun n r => rfl⟩
  · simp [lane_fold_delta, familyDeltaU, hκ]
  · rw [lane_fold_zero_zero]
    simp only [familyDeltaU, hκ, true_and, low, ite_self, bxor_zero, lowOf, decide_eq_true_eq]
    split_ifs <;> simp_all
  · rw [lane_fold_m]
    simp [familyDeltaU, hκ]

/-- At a lane of another coordinate, the Δ-family moves nothing. -/
theorem deltaU_fold_other (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (hκ : ℓ.coord ≠ κ) :
    (((familyDeltaU κ input c).lane ℓ).fold k).delta = 0 ∧
    (((familyDeltaU κ input c).lane ℓ).fold k).zero 0 = 0 ∧
    (∀ n r, (((familyDeltaU κ input c).lane ℓ).fold k).m n r = 0) ∧
    (∀ n r, (((familyDeltaU κ input c).lane ℓ).fold k).o n r = 0) := by
  refine ⟨?_, ?_, fun n r => ?_, fun n r => rfl⟩
  · simp [lane_fold_delta, familyDeltaU, hκ]
  · rw [lane_fold_zero_zero]
    simp [familyDeltaU, hκ]
  · rw [lane_fold_m]
    simp [familyDeltaU, hκ]

theorem fold_hot_zero (F : FoldShift) (r : Nat) (half : Bool) :
    F.hot 0 r half = (F.delta, F.delta ^^^ F.o 0 r ^^^ (if half then 0 else F.m 0 r)) := rfl

/-- The fold-gate shifts of a width-2 fold at step `1`, from its four parameters. -/
theorem fold_hot_one (F : FoldShift) (r : Nat) (half : Bool) :
    F.hot 1 r half = (F.level 1 r, F.level 1 r ^^^ F.o 1 r ^^^ (if half then 0 else F.m 1 r)) := rfl

/-- **The Δ-family keeps every inactive fold gate of step `1`.** -/
theorem deltaU_hot_off (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (r : Nat) (half : Bool) (small : r < 2) (off : r ≠ (chunkOf (inputBits input ℓ.coord) k).val % 2) :
    (((familyDeltaU κ input c).lane ℓ).fold k).hot 1 r half = (0, 0) := by
  rw [fold_hot_one, FoldShift.level_one]
  by_cases hκ : ℓ.coord = κ
  · obtain ⟨d, z, m, o⟩ := deltaU_fold κ input c ℓ k hκ
    rw [d, z, m, o]
    subst hκ
    have lowSmall : lowOf input ℓ.coord k < 2 := Nat.mod_lt _ (by omega)
    have ne : r ≠ lowOf input ℓ.coord k := off
    generalize lowOf input ℓ.coord k = lo at lowSmall ne
    interval_cases r <;> interval_cases lo <;> simp_all [block_xor_self]
  · obtain ⟨d, z, m, o⟩ := deltaU_fold_other κ input c ℓ k hκ
    rw [d, z, m, o]
    simp

/-- **The Δ-family moves the active parent's point by `c`.** -/
theorem deltaU_hot_on (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (half : Bool) (hκ : ℓ.coord = κ) :
    ((((familyDeltaU κ input c).lane ℓ).fold k).hot 1 (lowOf input κ k) half).1 = c := by
  rw [fold_hot_one, FoldShift.level_one]
  obtain ⟨d, z, m, o⟩ := deltaU_fold κ input c ℓ k hκ
  rw [d, z]
  have lowSmall : lowOf input κ k < 2 := Nat.mod_lt _ (by omega)
  generalize lowOf input κ k = lo at lowSmall
  interval_cases lo <;> simp

theorem level_off_calc (c : Block) (α j : Nat) (hα : α < 4) (hj : j < 4) (off : j ≠ α) :
    (if j < 2 then (if j = 0 then c ^^^ (if α % 2 = 1 then c else 0) else (if α % 2 = 1 then c else 0)) ^^^
        (if j = α % 2 ∧ α / 2 = 1 then c else 0)
      else if j - 2 = α % 2 ∧ α / 2 = 1 then c else 0) = 0 := by
  interval_cases j <;> interval_cases α <;> simp_all [block_xor_self]

theorem level_on_calc (c : Block) (α : Nat) (hα : α < 4) :
    (if α < 2 then (if α = 0 then c ^^^ (if α % 2 = 1 then c else 0) else (if α % 2 = 1 then c else 0)) ^^^
        (if α = α % 2 ∧ α / 2 = 1 then c else 0)
      else if α - 2 = α % 2 ∧ α / 2 = 1 then c else 0) = c := by
  interval_cases α <;> simp [block_xor_self]

/-- **The Δ-family keeps every inactive switch.** -/
theorem deltaU_level_off (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (j : Nat) (small : j < 4) (off : j ≠ (chunkOf (inputBits input ℓ.coord) k).val) :
    (((familyDeltaU κ input c).lane ℓ).fold k).level 2 j = 0 := by
  rw [FoldShift.level_two, FoldShift.level_one]
  by_cases hκ : ℓ.coord = κ
  · obtain ⟨d, z, m, o⟩ := deltaU_fold κ input c ℓ k hκ
    rw [d, z, m, m]
    clear d z m o
    subst hκ
    exact level_off_calc c _ j (chunkOf_lt_four _ k) small off
  · obtain ⟨d, z, m, o⟩ := deltaU_fold_other κ input c ℓ k hκ
    rw [d, z, m, m]
    simp

/-- **The Δ-family moves the active switch by `c`.** -/
theorem deltaU_level_on (κ : Coord) (input : AffineInput) (c : Block) (ℓ : Lane) (k : Fin chunkCount)
    (hκ : ℓ.coord = κ) :
    (((familyDeltaU κ input c).lane ℓ).fold k).level 2 (chunkOf (inputBits input κ) k).val = c := by
  rw [FoldShift.level_two, FoldShift.level_one]
  obtain ⟨d, z, m, o⟩ := deltaU_fold κ input c ℓ k hκ
  rw [d, z, m, m]
  exact level_on_calc c _ (chunkOf_lt_four _ k)

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **The Δ-family at a gadget position**: `c` iff the position is `κ`'s and `u`'s bit differs from
the exceptional input's. -/
theorem deltaU_gadget (κ : Coord) (input : AffineInput) (c : Block) (scalar : NonZeroScalar)
    (coins : Coins) (o : Fin digitCount) (κ' : Coord) (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyDeltaU κ input c) scalar coins o κ' position =
      if κ' = κ ∧ (inputBits input κ').getLsb position ≠ exceptionalBit scalar coins.offsets o κ' position
      then c else 0 := by
  unfold gadgetShift
  simp only [familyDeltaU, BitVec.zero_xor]
  by_cases hκ : κ' = κ
  · subst hκ
    simp only [true_and, if_true]
    cases (inputBits input κ').getLsb position <;>
      cases exceptionalBit scalar coins.offsets o κ' position <;> simp [block_xor_self]
  · simp [hκ]

theorem scheme_encode (key : InputMacKey) (input : AffineInput) :
    Scheme.scheme.encode key input = Lamport.selectedLabels (key.encode (BitInput.ofAffine input)) := rfl

theorem encode_x_get (key : InputMacKey) (input : BitInput) (i : Nat) (h : i < 254) :
    (key.encode input).x[i] = BitAdaptor.encode key.x[i] (input.xBits.getLsb ⟨i, h⟩) := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.getElem_ofFn]

theorem encode_y_get (key : InputMacKey) (input : BitInput) (i : Nat) (h : i < 254) :
    (key.encode input).y[i] = BitAdaptor.encode key.y[i] (input.yBits.getLsb ⟨i, h⟩) := by
  simp only [InputMacKey.encode, encodeCoordinate, Vector.getElem_ofFn]

theorem inputMacKey_x_get (coins : Coins) (i : Nat) (h : i < 254) :
    coins.inputMacKey.x[i] = BitAdaptor.Key.mk (coins.inputZero .x ⟨i, h⟩)
      (coins.inputZero .x ⟨i, h⟩ ^^^ coins.inputDelta .x) := by
  simp only [Coins.inputMacKey, Vector.getElem_ofFn]

theorem inputMacKey_y_get (coins : Coins) (i : Nat) (h : i < 254) :
    coins.inputMacKey.y[i] = BitAdaptor.Key.mk (coins.inputZero .y ⟨i, h⟩)
      (coins.inputZero .y ⟨i, h⟩ ^^^ coins.inputDelta .y) := by
  simp only [Coins.inputMacKey, Vector.getElem_ofFn]

/-- A selected label is kept when its shift vanishes. -/
theorem select_shift (b : Bool) (z Δ sz sΔ : Block) (h : (if b then sz ^^^ sΔ else sz) = 0) :
    BitAdaptor.encode (BitAdaptor.Key.mk (z ^^^ sz) (z ^^^ sz ^^^ (Δ ^^^ sΔ))) b =
      BitAdaptor.encode (BitAdaptor.Key.mk z (z ^^^ Δ)) b := by
  cases b
  · simp only [BitAdaptor.encode, Bool.false_eq_true, if_false] at h ⊢
    rw [h, bxor_zero]
  · simp only [BitAdaptor.encode, if_true] at h ⊢
    have : z ^^^ sz ^^^ (Δ ^^^ sΔ) = z ^^^ Δ ^^^ (sz ^^^ sΔ) := by ac_rfl
    rw [this, h, bxor_zero]

/-- **The Δ-family keeps the labels of `u`.** -/
theorem deltaU_encode (κ : Coord) (input : AffineInput) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (familyDeltaU κ input c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  rw [scheme_encode, scheme_encode]
  refine congrArg Lamport.selectedLabels ?_
  apply InputMac.ext
  · apply Vector.ext
    intro i h
    rw [encode_x_get, encode_x_get, inputMacKey_x_get, inputMacKey_x_get]
    refine select_shift _ _ _ _ _ ?_
    show (if (coordinateBits input.x).getLsb ⟨i, h⟩ then
        (if Coord.x = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) ^^^
          (if Coord.x = κ then c else 0)
      else if Coord.x = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) = 0
    by_cases hκ : Coord.x = κ
    · subst hκ
      show (if (inputBits input .x).getLsb ⟨i, h⟩ then _ else _) = 0
      cases (inputBits input .x).getLsb ⟨i, h⟩ <;> simp [block_xor_self]
    · simp [hκ]
  · apply Vector.ext
    intro i h
    rw [encode_y_get, encode_y_get, inputMacKey_y_get, inputMacKey_y_get]
    refine select_shift _ _ _ _ _ ?_
    show (if (coordinateBits input.y).getLsb ⟨i, h⟩ then
        (if Coord.y = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) ^^^
          (if Coord.y = κ then c else 0)
      else if Coord.y = κ ∧ (inputBits input κ).getLsb ⟨i, h⟩ = true then c else 0) = 0
    by_cases hκ : Coord.y = κ
    · subst hκ
      show (if (inputBits input .y).getLsb ⟨i, h⟩ then _ else _) = 0
      cases (inputBits input .y).getLsb ⟨i, h⟩ <;> simp [block_xor_self]
    · simp [hκ]

end Instances

/-! ### The `k₂`-family -/

/-- **The `k₂`-family**: `k₂ += c`; per point-lane chunk every step-1 parent but `z` `+= c`. -/
def familyKey2 (z : Nat) (c : Block) : TapeShift where
  delta _ := 0
  zero _ _ := 0
  key2 := c
  m ℓ _ n r := if laneIsPoint ℓ = true ∧ n = 1 ∧ r ≠ z then c else 0
  o _ _ _ _ := 0

theorem familyKey2_valid (z : Nat) (small : z < 2) (c : Block) : (familyKey2 z c).Valid := by
  refine valid_of_step _ fun ℓ k => ?_
  simp only [familyKey2, BitVec.zero_xor]
  cases ℓ <;> simp only [laneIsPoint, true_and, if_true, Bool.false_eq_true, false_and, if_false,
    BitVec.xor_zero] <;> interval_cases z <;> simp

/-- The `k₂`-family leaves the curve lanes alone. -/
theorem key2_fold_curve (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (curve : laneIsPoint ℓ = false) :
    (((familyKey2 z c).lane ℓ).fold k).delta = 0 ∧ (((familyKey2 z c).lane ℓ).fold k).zero 0 = 0 ∧
    (∀ n r, (((familyKey2 z c).lane ℓ).fold k).m n r = 0) ∧
    (∀ n r, (((familyKey2 z c).lane ℓ).fold k).o n r = 0) := by
  refine ⟨rfl, ?_, fun n r => ?_, fun n r => rfl⟩
  · rw [lane_fold_zero_zero]
    simp [familyKey2, curve]
  · rw [lane_fold_m]
    simp [familyKey2, curve]

theorem key2_hot_curve (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (curve : laneIsPoint ℓ = false)
    (n r : Nat) (half : Bool) (small : n ≤ 1) :
    (((familyKey2 z c).lane ℓ).fold k).hot n r half = (0, 0) := by
  obtain ⟨d, z0, m, o⟩ := key2_fold_curve z c ℓ k curve
  interval_cases n
  · rw [fold_hot_zero, d, m, o]
    simp
  · rw [fold_hot_one, FoldShift.level_one, d, z0, m, o]
    simp

theorem key2_level_curve (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (curve : laneIsPoint ℓ = false)
    (j : Nat) : (((familyKey2 z c).lane ℓ).fold k).level 2 j = 0 := by
  obtain ⟨d, z0, m, o⟩ := key2_fold_curve z c ℓ k curve
  rw [FoldShift.level_two, FoldShift.level_one, d, z0, m, m]
  simp

theorem key2_fold_point (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (point : laneIsPoint ℓ = true) :
    (((familyKey2 z c).lane ℓ).fold k).delta = 0 ∧ (((familyKey2 z c).lane ℓ).fold k).zero 0 = c ∧
    (∀ r, (((familyKey2 z c).lane ℓ).fold k).m 1 r = if r ≠ z then c else 0) := by
  refine ⟨rfl, ?_, fun r => ?_⟩
  · rw [lane_fold_zero_zero]
    simp [familyKey2, point]
  · rw [lane_fold_m]
    simp [familyKey2, point]

/-- **The `k₂`-family moves every point-lane fold gate of step `1`.** -/
theorem key2_hot_point (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (point : laneIsPoint ℓ = true)
    (r : Nat) (half : Bool) : ((((familyKey2 z c).lane ℓ).fold k).hot 1 r half).1 = c := by
  obtain ⟨d, z0, m⟩ := key2_fold_point z c ℓ k point
  rw [fold_hot_one, FoldShift.level_one, d, z0]
  split <;> simp

/-- **The `k₂`-family at a point-lane switch.** -/
theorem key2_level_point (z : Nat) (c : Block) (ℓ : Lane) (k : Fin chunkCount) (point : laneIsPoint ℓ = true)
    (j : Nat) (small : j < 4) (hz : z = if j < 2 then j else 3 - j) :
    (((familyKey2 z c).lane ℓ).fold k).level 2 j = c := by
  obtain ⟨d, z0, m⟩ := key2_fold_point z c ℓ k point
  rw [FoldShift.level_two, FoldShift.level_one, d, z0, m, m]
  subst hz
  interval_cases j <;> simp [block_xor_self]

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem key2_gadget (z : Nat) (c : Block) (scalar : NonZeroScalar) (coins : Coins) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyKey2 z c) scalar coins o κ position = c := by
  unfold gadgetShift
  simp [familyKey2]

theorem shiftCoins_of_zero (T : TapeShift) (delta : ∀ κ, T.delta κ = 0) (zero : ∀ κ p, T.zero κ p = 0)
    (coins : Coins) : shiftCoins T coins = coins := by
  apply Scheme.Coins.data_injective
  have z : (fun κ (position : Fin coordinateBitCount) => coins.inputZero κ position ^^^ T.zero κ position) =
      coins.inputZero := funext fun κ => funext fun p => by rw [zero κ p, bxor_zero]
  have d : (fun κ => coins.inputDelta κ ^^^ T.delta κ) = coins.inputDelta :=
    funext fun κ => by rw [delta κ, bxor_zero]
  simp only [Scheme.Coins.data, shiftCoins, z, d]

theorem key2_coins (z : Nat) (c : Block) (coins : Coins) : shiftCoins (familyKey2 z c) coins = coins :=
  shiftCoins_of_zero _ (fun _ => rfl) (fun _ _ => rfl) coins

end Instances

/-! ### The hot-output family -/

/-- **Both outputs of the fold gate `(ℓ, k, 1, r)` move by `c`.** -/
def familyHotOut (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) : TapeShift where
  delta _ := 0
  zero _ _ := 0
  key2 := 0
  m _ _ _ _ := 0
  o ℓ' k' n r' := if ℓ' = ℓ ∧ k' = k ∧ n = 1 ∧ r' = r then c else 0

theorem familyHotOut_valid (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) :
    (familyHotOut ℓ k r c).Valid :=
  valid_of_step _ fun ℓ' k' => by simp [familyHotOut]

theorem hotOut_fold (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (ℓ' : Lane) (k' : Fin chunkCount) :
    (((familyHotOut ℓ k r c).lane ℓ').fold k').delta = 0 ∧
    (((familyHotOut ℓ k r c).lane ℓ').fold k').zero 0 = 0 ∧
    (∀ n r', (((familyHotOut ℓ k r c).lane ℓ').fold k').m n r' = 0) := by
  refine ⟨rfl, ?_, fun n r' => rfl⟩
  rw [lane_fold_zero_zero]
  simp [familyHotOut]

theorem hotOut_hot (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (ℓ' : Lane) (k' : Fin chunkCount)
    (n r' : Nat) (half : Bool) (small : n ≤ 1) :
    (((familyHotOut ℓ k r c).lane ℓ').fold k').hot n r' half =
      (0, if ℓ' = ℓ ∧ k' = k ∧ n = 1 ∧ r' = r then c else 0) := by
  obtain ⟨d, z0, m⟩ := hotOut_fold ℓ k r c ℓ' k'
  interval_cases n
  · rw [fold_hot_zero, d, m, lane_fold_o]
    simp [familyHotOut]
  · rw [fold_hot_one, FoldShift.level_one, d, z0, m, lane_fold_o]
    simp [familyHotOut]

theorem hotOut_level (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (ℓ' : Lane) (k' : Fin chunkCount)
    (j : Nat) : (((familyHotOut ℓ k r c).lane ℓ').fold k').level 2 j = 0 := by
  obtain ⟨d, z0, m⟩ := hotOut_fold ℓ k r c ℓ' k'
  rw [FoldShift.level_two, FoldShift.level_one, d, z0, m, m]
  simp

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem hotOut_gadget (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (scalar : NonZeroScalar)
    (coins : Coins) (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    gadgetShift (familyHotOut ℓ k r c) scalar coins o κ position = 0 := by
  unfold gadgetShift
  simp [familyHotOut]

theorem hotOut_coins (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (coins : Coins) :
    shiftCoins (familyHotOut ℓ k r c) coins = coins :=
  shiftCoins_of_zero _ (fun _ => rfl) (fun _ _ => rfl) coins

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
