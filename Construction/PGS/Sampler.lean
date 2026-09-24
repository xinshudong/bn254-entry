/-
This file defines the Plan B field sampler.
Rule S: every `F_p` sampler is a total function of three blocks of the shape
`fun blocks => ((toNat blocks : Nat) : ZMod p)`. Reduction, never rejection --
`PerfectCorrectness` quantifies over every tape, and a rejection loop is tape-dependent.
The plan source is `2026-09-17-planB.md`, section D.3 and Rule S.
-/

import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- The Plan B hash: Davies--Meyer at the permutation the index names.

No tweak is applied. The index already names the gate uniquely, which is what makes
"one construction query per `FixedIndex`" hold. -/
def hash (oracle : PermutationOracle FixedIndex Block) (index : FixedIndex)
    (label : Block) : Block :=
  daviesMeyer (oracle.permutation index) label

/-- The little-endian natural number carried by three blocks. -/
def blocksToNat (first second third : Block) : Nat :=
  first.toNat + 2 ^ 128 * second.toNat + 2 ^ 256 * third.toNat

/-- The Rule S field sampler: three blocks, reduced.

Two blocks would leave a reduction bias of `p / 2 ^ 256`, which is a catastrophe rather than
a bound; three blocks give `p / 2 ^ 384`, the budget's term `T3`. -/
def sampleFp (first second third : Block) : BaseField :=
  ((blocksToNat first second third : Nat) : BaseField)

/-- One switch mask vector: three blocks per element, all hashed at the same label. -/
def sampleVector {count : Nat} (oracle : PermutationOracle FixedIndex Block)
    (index : Fin count → Fin 3 → FixedIndex) (label : Block) : Fin count → BaseField :=
  fun element =>
    sampleFp (hash oracle (index element 0) label) (hash oracle (index element 1) label)
      (hash oracle (index element 2) label)

/-- `sampleFp` is total: it is a function, so it answers on every triple of blocks.
Stated for the record -- Rule S forbids any non-total or rejection-based sampler. -/
theorem sampleFp_total (first second third : Block) :
    ∃ value : BaseField, sampleFp first second third = value :=
  ⟨_, rfl⟩

/-- The modulus fits in 254 bits. -/
theorem baseFieldModulus_lt : baseFieldModulus < 2 ^ 254 := by
  unfold baseFieldModulus
  norm_num

/-- Every residue is reachable: `p < 2 ^ 384`, so reduction is surjective.
This is what the bias term of the privacy budget is measured against. -/
theorem sampleFp_surjective :
    Function.Surjective fun blocks : Block × Block × Block =>
      sampleFp blocks.1 blocks.2.1 blocks.2.2 := by
  intro value
  refine ⟨(BitVec.ofNat 128 value.val, BitVec.ofNat 128 (value.val / 2 ^ 128), 0), ?_⟩
  have range : value.val < 2 ^ 254 := lt_trans (ZMod.val_lt value) baseFieldModulus_lt
  have high : value.val / 2 ^ 128 < 2 ^ 128 := by
    have : (2 : Nat) ^ 254 = 2 ^ 128 * 2 ^ 126 := by
      rw [← pow_add]
    omega
  have recompose : blocksToNat (BitVec.ofNat 128 value.val)
      (BitVec.ofNat 128 (value.val / 2 ^ 128)) 0 = value.val := by
    have zero : (0 : Block).toNat = 0 := rfl
    simp only [blocksToNat, BitVec.toNat_ofNat, zero, Nat.mod_eq_of_lt high, Nat.mul_zero,
      Nat.add_zero]
    omega
  show sampleFp _ _ _ = value
  simp only [sampleFp, recompose]
  exact ZMod.natCast_zmod_val value

end Kriterion.ArgoMAC.PlanB
