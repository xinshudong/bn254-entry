/-
This file proves the two premises plan B's affine encoding rests on (plan
`2026-09-17-planB.md`, section D.9 and Task 13).

The construction reads the 508 Lamport bits, interprets bits `0 .. 253` as the `chunkCount` chunks of
`x` and bits `254 .. 507` as the chunks of `y`, and claims

```
  sum_(c < C) 2 ^ (b * c) * iota (chunk c) = x       in F_p                     (dagger)
```

`(dagger)` is not an identity about bit strings: it holds only because the bits are the
*canonical* little-endian digits of `x.val`. Two premises carry it, neither of them visible at
the point of use:

* **P-bits** (`ScalarMultiplication.lean`): `affineLamportBits input` is
  `BitVec.ofNat 508 (input.x.val + input.y.val * 2 ^ 254)`, so the low 254 bits are the bits of
  `x.val` -- adding a multiple of `2 ^ 254` cannot disturb a bit below position 254;
* **P-range** (`BN254.lean`): `AffineInput` carries `x y : BaseField`, so `x.val < p < 2 ^ 254`
  and the 254-bit recomposition is *not* reduced.

With arbitrary 508 bits the recomposed sum could reach `2 ^ 254 > p`, and `(dagger)` would
deliver `a * (sum 2 ^ j x_j mod p)`, not `a * x`.
-/

import Construction.PGS.ScaleHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-! ### (A) The low 254 Lamport bits are the bits of `x.val` -/

/-- Adding a multiple of `2 ^ high` leaves every bit below position `high` alone. -/
private theorem testBit_add_mul_high (first second high position : Nat) (low : position < high) :
    (first + second * 2 ^ high).testBit position = first.testBit position := by
  have positive : 0 < 2 ^ position := Nat.two_pow_pos position
  have power : (2 : Nat) ^ high = 2 ^ (high - position - 1) * 2 * 2 ^ position := by
    rw [mul_comm ((2 : Nat) ^ (high - position - 1)) 2, ← pow_succ', ← pow_add]
    congr 1
    omega
  have expand : first + second * 2 ^ high
      = first + second * 2 ^ (high - position - 1) * 2 * 2 ^ position := by
    rw [power]
    ring
  have reduce : (first / 2 ^ position + second * 2 ^ (high - position - 1) * 2) % 2
      = first / 2 ^ position % 2 := by omega
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, expand,
    Nat.add_mul_div_right _ _ positive, reduce]

/-- **(A)** The low 254 bits of the 508-bit Lamport string are the bits of `x.val`: the `y`
coordinate contributes only above position 254. -/
theorem lamportBits_low (input : AffineInput) (position : Nat)
    (low : position < coordinateBits) :
    (affineLamportBits input).getLsbD position = (coordWord input.x).getLsbD position := by
  have wide : position < 508 := by unfold coordinateBits at low; omega
  rw [affineLamportBits, coordWord, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
    decide_eq_true wide, decide_eq_true low, Bool.true_and, Bool.true_and]
  exact testBit_add_mul_high _ _ _ _ low

/-- Above position `high`, a sum whose low summand is below `2 ^ high` shows only the high
summand's bits. -/
private theorem testBit_add_mul_low (first second high position : Nat)
    (small : first < 2 ^ high) :
    (first + second * 2 ^ high).testBit (high + position) = second.testBit position := by
  have positive : 0 < 2 ^ high := Nat.two_pow_pos high
  have shift : (first + second * 2 ^ high) >>> high = second := by
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ positive,
      Nat.div_eq_of_lt small, Nat.zero_add]
  rw [← Nat.testBit_shiftRight, shift]

/-- **(A\')** The high 254 bits of the 508-bit Lamport string are the bits of `y.val`: the `x`
coordinate is below `2 ^ 254` and so contributes nothing above position 253. This is what lets
the `y` coordinate's switch system quote `evalCoord_garbleCoord` at the Lamport labels. -/
theorem lamportBits_high (input : AffineInput) (position : Nat)
    (low : position < coordinateBits) :
    (affineLamportBits input).getLsbD (coordinateBits + position)
      = (coordWord input.y).getLsbD position := by
  have wide : coordinateBits + position < 508 := by unfold coordinateBits at low ⊢; omega
  have small : input.x.val < 2 ^ coordinateBits :=
    lt_trans (ZMod.val_lt input.x) baseFieldModulus_lt_two_pow
  rw [affineLamportBits, coordWord, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
    decide_eq_true wide, decide_eq_true low, Bool.true_and, Bool.true_and]
  exact testBit_add_mul_low _ _ _ _ small

/-! ### (B) Canonical recomposition of a coordinate from its `chunkCount` chunks -/

/-- The uniform-width digit recomposition: every number below `2 ^ (width * count)` is the
weighted sum of its `count` base-`2 ^ width` digits. Proved by induction on the digit count,
peeling the *lowest* digit, so no numeral of the size of `2 ^ 254` is ever evaluated. -/
private theorem uniform_recomposition (width : Nat) :
    ∀ (count value : Nat), value < 2 ^ (width * count) →
      (∑ slot ∈ Finset.range count, 2 ^ (width * slot) * (value >>> (width * slot) % 2 ^ width))
        = value := by
  intro count
  induction count with
  | zero =>
    intro value bound
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at bound
    simp [bound]
  | succ steps ih =>
    intro value bound
    have split : (2 : Nat) ^ (width * (steps + 1)) = 2 ^ width * 2 ^ (width * steps) := by
      rw [← pow_add]
      congr 1
      ring
    have tail : value >>> width < 2 ^ (width * steps) := by
      rw [Nat.shiftRight_eq_div_pow]
      refine Nat.div_lt_of_lt_mul ?_
      rw [← split]
      exact bound
    have shifted := ih (value >>> width) tail
    rw [Finset.sum_range_succ']
    have body : ∀ slot ∈ Finset.range steps,
        2 ^ (width * (slot + 1)) * (value >>> (width * (slot + 1)) % 2 ^ width)
          = 2 ^ width *
            (2 ^ (width * slot) * ((value >>> width) >>> (width * slot) % 2 ^ width)) := by
      intro slot _
      have index : width * (slot + 1) = width + width * slot := by ring
      rw [index, pow_add, Nat.shiftRight_add, mul_assoc]
    rw [Finset.sum_congr rfl body, ← Finset.mul_sum, shifted]
    simp only [Nat.mul_zero, pow_zero, Nat.shiftRight_zero, one_mul]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_add_mod value (2 ^ width)

/-- **(B)** The `chunkCount` chunks of a 254-bit number recompose it. The last chunk is only
`lastChunkBits` wide (at most `chunkBits`), and that is exactly enough: the number is below
`2 ^ 254`, so its top chunk is already below `2 ^ lastChunkBits` and the reduction is the
identity. -/
theorem chunk_recomposition_nat (value : Nat) (bound : value < 2 ^ coordinateBits) :
    (∑ c : Fin chunkCount, 2 ^ chunkOffset c * (chunkOfNat value c).val) = value := by
  have uniform : (∑ slot ∈ Finset.range chunkCount,
      2 ^ (chunkBits * slot) * (value >>> (chunkBits * slot) % 2 ^ chunkBits)) = value := by
    refine uniform_recomposition chunkBits chunkCount value (lt_of_lt_of_le bound ?_)
    exact Nat.pow_le_pow_right (by omega)
      (by unfold chunkBits chunkCount coordinateBits; omega)
  have ragged : ∀ slot ∈ Finset.range chunkCount,
      2 ^ (chunkBits * slot) * (value >>> (chunkBits * slot) % 2 ^ chunkWidthNat slot)
        = 2 ^ (chunkBits * slot) * (value >>> (chunkBits * slot) % 2 ^ chunkBits) := by
    intro slot inRange
    rw [Finset.mem_range] at inRange
    by_cases last : slot + 1 = chunkCount
    · have position : chunkBits * slot = 252 := by
        unfold chunkCount at last
        unfold chunkBits
        omega
      have small : value >>> (chunkBits * slot) < 2 ^ lastChunkBits := by
        rw [position, Nat.shiftRight_eq_div_pow]
        refine Nat.div_lt_of_lt_mul ?_
        refine lt_of_lt_of_le bound (le_of_eq ?_)
        unfold coordinateBits lastChunkBits
        rw [← pow_add]
      have width : chunkWidthNat slot = lastChunkBits := by
        unfold chunkWidthNat
        rw [if_pos last]
      rw [width, Nat.mod_eq_of_lt small,
        Nat.mod_eq_of_lt (lt_of_lt_of_le small (Nat.pow_le_pow_right (by omega)
          (by unfold lastChunkBits chunkBits; omega)))]
    · have width : chunkWidthNat slot = chunkBits := by
        unfold chunkWidthNat
        rw [if_neg last]
      rw [width]
  have toRange : (∑ c : Fin chunkCount, 2 ^ chunkOffset c * (chunkOfNat value c).val)
      = ∑ slot ∈ Finset.range chunkCount,
          2 ^ (chunkBits * slot) * (value >>> (chunkBits * slot) % 2 ^ chunkWidthNat slot) :=
    Fin.sum_univ_eq_sum_range
      (fun slot => 2 ^ (chunkBits * slot) * (value >>> (chunkBits * slot) % 2 ^ chunkWidthNat slot))
      chunkCount
  rw [toRange, Finset.sum_congr rfl ragged, uniform]

/-- **(B) + (C)** Canonical recomposition inside the field. The chunks of the canonical
254-bit encoding of a coordinate, weighted by `2 ^ (chunkBits * c)` and read through `iota`, sum to the
coordinate itself -- with no reduction, because `p < 2 ^ 254` (P-range). -/
theorem chunk_recomposition (value : BaseField) :
    (∑ c : Fin chunkCount,
        (2 : BaseField) ^ chunkOffset c * iota _ (chunkOf (coordWord value) c)) = value := by
  have chunks : ∀ c : Fin chunkCount, chunkOf (coordWord value) c = chunkOfNat value.val c := by
    intro c
    rw [chunkOf, coordWord_toNat]
  have digits := chunk_recomposition_nat value.val
    (lt_trans (ZMod.val_lt value) baseFieldModulus_lt_two_pow)
  calc (∑ c : Fin chunkCount,
          (2 : BaseField) ^ chunkOffset c * iota _ (chunkOf (coordWord value) c))
      = ((∑ c : Fin chunkCount, 2 ^ chunkOffset c * (chunkOfNat value.val c).val : Nat)
          : BaseField) := by
        push_cast
        refine Finset.sum_congr rfl ?_
        intro c _
        rw [chunks c, iota]
    _ = ((value.val : Nat) : BaseField) := by rw [digits]
    _ = value := ZMod.natCast_zmod_val value

end Kriterion.ArgoMAC.PlanB
