/-
This file defines the frozen Plan B parameters of the projectivized garbling scheme.
The plan source is `2026-09-17-planB.md`, section D.1 and D.5.

**The query-gated profile.** The pinned challenge bounds the oracle queries of garbling
(`≤ 1,759,967`) and evaluation (`≤ 1,055,879`). The `scale-hot` layer costs `3 · 824` queries per
switch and `Σ_c 2 ^ b_c ≥ 508` for any chunking of 254 bits, so the chunks must be narrow: at
`chunkBits = 2` garbling makes `1,305,053` queries and evaluation `990,093`, both at least 5%
below their gates (`Programs.garbleBudget_eq` and `Programs.evaluateBudget_eq` in
`Construction/OraclePrograms.lean` count every term).
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import ScalarMultiplication

namespace Kriterion.ArgoMAC.PlanB

/-- The number of chunks one 254-bit coordinate is cut into. -/
def chunkCount : Nat := 127

/-- The width of every chunk but the last. -/
def chunkBits : Nat := 2

/-- The width of the last chunk: `254 - 126 * 2`. -/
def lastChunkBits : Nat := 2

/-- The number of paid `bin-to-hot` fold steps of one coordinate: `254 - chunkCount = 127 * 1`. -/
def foldStepCount : Nat := 127

/-- The number of x-type elements: `91 * 5 + 3`. -/
def elementCountX : Nat := 458

/-- The number of y-type elements: `91 * 4 + 2`. -/
def elementCountY : Nat := 366

/-- The x-type elements of the point rows, delivered by switch system B: `91 * 5`. -/
def pointElementCountX : Nat := 455

/-- The y-type elements of the point rows, delivered by switch system B: `91 * 4`. -/
def pointElementCountY : Nat := 364

/-- The x-type elements of the curve check, delivered by switch system A. -/
def curveElementCountX : Nat := 3

/-- The y-type elements of the curve check, delivered by switch system A. -/
def curveElementCountY : Nat := 2

/-- The `819` point-row elements are `91 * 9`. -/
def pointElementCount : Nat := 819

/-- The total number of IT-GS elements `S`. -/
def elementCount : Nat := 824

/-- The width in bits of one chunk's published `scale-hot` join word: `824 * 254`. -/
def chunkJoinBits : Nat := 209296

/-- The width in bytes of one chunk's published `scale-hot` join word. -/
def chunkJoinBytes : Nat := 26162

/-- The number of bits of one coordinate. -/
def coordinateBits : Nat := 254

/-- The number of recoded digits, one per output MAC. -/
def digitCount : Nat := 91

/-- A coordinate of the affine input. Each one carries its own switch system. -/
inductive Coord
  | x
  | y
deriving DecidableEq

instance : Fintype Coord := ⟨{.x, .y}, fun value => by cases value <;> simp⟩

theorem card_coord : Fintype.card Coord = 2 := rfl

/-- A *lane*: one switch system on one coordinate.

Plan B runs **two** switch systems per coordinate, not one. System A (`curveX`, `curveY`) is
keyed on the raw 508 Lamport labels and delivers the five curve-check elements; its output is
the bridge key `t`. System B (`pointX`, `pointY`) is keyed on the *EncPRF-whitened* labels,
whose one-time pads are derived from `t`, and delivers the 819 point-row elements. An
evaluator who cannot produce `t` -- an off-curve input -- holds only garbage labels for system
B and can compute none of the point rows. The lane is part of every `bin-to-hot` and
`scale-hot` index, so the two systems never share a gate. -/
inductive Lane
  | curveX
  | curveY
  | pointX
  | pointY
deriving DecidableEq

instance : Fintype Lane :=
  ⟨{.curveX, .curveY, .pointX, .pointY}, fun value => by cases value <;> simp⟩

theorem card_lane : Fintype.card Lane = 4 := rfl

/-- The coordinate a lane reads. -/
def Lane.coord : Lane → Coord
  | .curveX => .x
  | .curveY => .y
  | .pointX => .x
  | .pointY => .y

/-- The width of chunk `c`, as a total function of a natural number.
Every chunk but the last is `chunkBits` wide; the last one is `lastChunkBits` wide. -/
def chunkWidthNat (c : Nat) : Nat :=
  if c + 1 = chunkCount then lastChunkBits else chunkBits

/-- The width `b_c` of chunk `c`. -/
def chunkWidth (c : Fin chunkCount) : Nat := chunkWidthNat c.val

/-- The offset of chunk `c`'s fold joins inside the coordinate's flat
`Vector Block foldStepCount`. -/
def foldBase (c : Fin chunkCount) : Nat :=
  ∑ i ∈ Finset.range c.val, (chunkWidthNat i - 1)

theorem elementCount_eq : elementCount = elementCountX + elementCountY := by
  rfl

theorem elementCountX_eq : elementCountX = pointElementCountX + curveElementCountX := by
  rfl

theorem elementCountY_eq : elementCountY = pointElementCountY + curveElementCountY := by
  rfl

theorem pointElementCount_eq : pointElementCount = pointElementCountX + pointElementCountY := by
  rfl

theorem chunkJoinBits_eq : chunkJoinBits = 8 * chunkJoinBytes := by
  rfl

theorem chunkBits_pos : 0 < chunkBits := by unfold chunkBits; omega

theorem chunkCount_pos : 0 < chunkCount := by unfold chunkCount; omega

theorem twoPowChunkBits_pos : 0 < 2 ^ chunkBits := Nat.two_pow_pos chunkBits

theorem chunkWidthNat_pos (c : Nat) : 0 < chunkWidthNat c := by
  unfold chunkWidthNat lastChunkBits chunkBits
  split <;> omega

theorem chunkWidthNat_le (c : Nat) : chunkWidthNat c ≤ chunkBits := by
  unfold chunkWidthNat lastChunkBits chunkBits
  split <;> omega

theorem chunkWidth_pos (c : Fin chunkCount) : 0 < chunkWidth c :=
  chunkWidthNat_pos c.val

theorem chunkWidth_le (c : Fin chunkCount) : chunkWidth c ≤ chunkBits :=
  chunkWidthNat_le c.val

/-- Every chunk before the last is `chunkBits` wide. -/
theorem chunkWidthNat_of_lt (c : Nat) (before : c + 1 < chunkCount) :
    chunkWidthNat c = chunkBits := by
  unfold chunkWidthNat
  rw [if_neg (Nat.ne_of_lt before)]

/-- The last chunk is `lastChunkBits` wide. -/
theorem chunkWidthNat_last : chunkWidthNat (chunkCount - 1) = lastChunkBits := by
  unfold chunkWidthNat
  rw [if_pos (Nat.sub_add_cancel chunkCount_pos)]

/-- A sum over the chunks strictly before the last is `chunkBits`-uniform. It is proved by
induction on the number of chunks, never by evaluating the sum (Rule O). -/
theorem sum_range_before_last (g : Nat → Nat) (count : Nat) (before : count < chunkCount) :
    (∑ i ∈ Finset.range count, g (chunkWidthNat i)) = count * g chunkBits := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Finset.sum_range_succ, ih (by omega), chunkWidthNat_of_lt count before, Nat.succ_mul]

/-- A sum over all chunks: `chunkCount - 1` uniform chunks and the ragged last one. -/
theorem sum_chunkWidth (g : Nat → Nat) :
    (∑ c : Fin chunkCount, g (chunkWidth c)) = (chunkCount - 1) * g chunkBits + g lastChunkBits := by
  have toRange : (∑ c : Fin chunkCount, g (chunkWidth c))
      = ∑ i ∈ Finset.range chunkCount, g (chunkWidthNat i) :=
    Fin.sum_univ_eq_sum_range (fun i => g (chunkWidthNat i)) chunkCount
  have split : Finset.range chunkCount = Finset.range (chunkCount - 1 + 1) := by
    rw [Nat.sub_add_cancel chunkCount_pos]
  rw [toRange, split, Finset.sum_range_succ, sum_range_before_last g _ (by unfold chunkCount; omega),
    chunkWidthNat_last]

/-- The chunk widths of one coordinate add up to its 254 bits. -/
theorem chunkWidth_sum : (∑ c : Fin chunkCount, chunkWidth c) = coordinateBits := by
  have uniform := sum_chunkWidth id
  simp only [id] at uniform
  rw [uniform]
  rfl

/-- The paid fold steps of one coordinate add up to `foldStepCount`. -/
theorem foldStep_sum : (∑ c : Fin chunkCount, (chunkWidth c - 1)) = foldStepCount := by
  rw [sum_chunkWidth (fun width => width - 1)]
  rfl

/-- The fold bases are the uniform multiples of `chunkBits - 1`: every chunk before `c` is a
full chunk. -/
theorem foldBase_eq_mul (c : Fin chunkCount) : foldBase c = c.val * (chunkBits - 1) :=
  sum_range_before_last (fun width => width - 1) c.val c.isLt

/-- The fold joins of every chunk fit inside the flat `foldStepCount`-block vector. -/
theorem foldBase_add_le (c : Fin chunkCount) :
    foldBase c + (chunkWidth c - 1) ≤ foldStepCount := by
  rw [foldBase_eq_mul]
  have bound := c.isLt
  have width := chunkWidthNat_le c.val
  change c.val * (chunkBits - 1) + (chunkWidthNat c.val - 1) ≤ foldStepCount
  unfold chunkCount at bound
  unfold chunkBits at width ⊢
  unfold foldStepCount
  omega

theorem foldBase_zero : foldBase ⟨0, chunkCount_pos⟩ = 0 := by
  rw [foldBase_eq_mul, Nat.zero_mul]

/-! ### Chunking a coordinate

The construction cuts the 254 bits of a coordinate into `chunkCount` chunks, all of width
`chunkBits` but the last, which carries the ragged remainder `lastChunkBits`. These are the
plan's `chunkOf` (section D.9) and the chunk value the switch system's evaluator holds in the
clear. Both are total functions of the whole coordinate word; nothing here mentions a tape. -/

/-- The bit offset of chunk `c` inside the coordinate. -/
def chunkOffset (c : Fin chunkCount) : Nat := chunkBits * c.val

/-- Every chunk lies inside the coordinate. -/
theorem chunkOffset_add_width_le (c : Fin chunkCount) :
    chunkOffset c + chunkWidth c ≤ coordinateBits := by
  have bound := c.isLt
  have width := chunkWidthNat_le c.val
  change chunkBits * c.val + chunkWidthNat c.val ≤ coordinateBits
  unfold chunkCount at bound
  unfold chunkBits at width ⊢
  unfold coordinateBits
  omega

/-- Chunk `c` of a natural number, as the switch index of that chunk's `scale-hot` system. -/
def chunkOfNat (bits : Nat) (c : Fin chunkCount) : Fin (2 ^ chunkWidth c) :=
  ⟨bits >>> chunkOffset c % 2 ^ chunkWidth c, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Chunk `c` of a coordinate word, as a switch index. -/
def chunkOf (bits : BitVec coordinateBits) (c : Fin chunkCount) : Fin (2 ^ chunkWidth c) :=
  chunkOfNat bits.toNat c

/-- Chunk `c` of a coordinate word, as a bit vector of that chunk's width. -/
def chunkValue (bits : BitVec coordinateBits) (c : Fin chunkCount) : BitVec (chunkWidth c) :=
  BitVec.ofNat (chunkWidth c) (bits.toNat >>> chunkOffset c)

/-- The two readings of a chunk agree. -/
theorem chunkValue_toNat (bits : BitVec coordinateBits) (c : Fin chunkCount) :
    (chunkValue bits c).toNat = (chunkOf bits c).val := by
  rw [chunkValue, BitVec.toNat_ofNat]
  rfl

/-- The canonical little-endian 254-bit encoding of a coordinate. This is definitionally the
baseline's `Kriterion.ArgoMAC.coordinateBits`. -/
def coordWord (value : BN254.BaseField) : BitVec coordinateBits :=
  BitVec.ofNat coordinateBits value.val

/-- The modulus fits in 254 bits, so the canonical encoding loses nothing. -/
theorem baseFieldModulus_lt_two_pow : BN254.baseFieldModulus < 2 ^ coordinateBits := by
  unfold BN254.baseFieldModulus coordinateBits
  norm_num

theorem coordWord_toNat (value : BN254.BaseField) : (coordWord value).toNat = value.val := by
  rw [coordWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (ZMod.val_lt value) baseFieldModulus_lt_two_pow

end Kriterion.ArgoMAC.PlanB
