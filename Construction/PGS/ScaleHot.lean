/-
This file defines the Plan B `scale-hot` join: the per-(coordinate, chunk) switch system that
delivers all `S_k` affine encodings over the *plain* group `F_p ^ S_k`.

The plan source is `2026-09-17-planB.md`, section D.3; the reference
implementation is the internal `pgs.py` (`_switch_masks`, `scale_hot_masks`,
`scale_hot_garble`, `scale_hot_evaluate`).

The load-bearing cost fact: the switch constraints contribute nothing to the join width, so a
chunk publishes exactly one `F_p ^ S_k` value -- `S_k * 254` bits, independently of the one-hot
length `2 ^ b_c`. The `2 ^ b_c` factor appears only in the hash count.

Every sum below is a `Finset.sum` over `Finset.univ : Finset (Fin (2 ^ width))`; it is never
unfolded, enumerated or decided (Rule O).
-/

import Construction.PGS.OneHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

/-- There is at least one x-type element slot. -/
theorem elementCountX_pos : 0 < elementCountX := by
  unfold elementCountX; omega

/-- `2 ^ chunkBits` is far below the modulus, which is what makes `iota` injective. -/
theorem twoPowChunkBits_lt_modulus : 2 ^ chunkBits < baseFieldModulus := by
  unfold chunkBits baseFieldModulus
  norm_num

/-- The `scale` index of one (chunk, switch, element, block) gate.

The element slot is reduced into `Fin elementCountX`; the `y` coordinate uses only
`elementCountY` of the `elementCountX` slots, and the reduction is the identity there because
`elementCountY < elementCountX`. The coordinate is part of the index, so the two coordinates
never share a gate. -/
def scaleIndexOf {count : Nat} (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (element : Fin count) (block : Fin 3) : FixedIndex :=
  scaleIndexNat lane chunk switch
    ⟨element.val % elementCountX, Nat.mod_lt _ elementCountX_pos⟩ block

/-- The reduction of the element slot is the identity in range. -/
theorem scaleIndexOf_eq {count : Nat} (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (element : Fin count) (block : Fin 3) (inRange : element.val < elementCountX)
    (hswitch : switch < 2 ^ chunkBits) :
    scaleIndexOf lane chunk switch element block
      = .scale lane chunk ⟨switch, hswitch⟩ ⟨element.val, inRange⟩ block := by
  simp only [scaleIndexOf, Nat.mod_eq_of_lt inRange]
  exact scaleIndexNat_eq lane chunk switch _ block hswitch

/-- `iota`: the switch index seen inside the field. It is the free fold's coefficient. -/
def iota (size : Nat) (switch : Fin size) : BaseField := (switch.val : BaseField)

/-- `iota` is injective on any switch range below `2 ^ chunkBits`: distinct switch indices give
distinct field elements, because `2 ^ 14` is far below the modulus. This is the step that keeps
the `2`-bit last chunk sound as well. -/
theorem iota_injective {size : Nat} (bound : size ≤ 2 ^ chunkBits) :
    Function.Injective (iota size) := by
  intro first second equal
  have small : ∀ switch : Fin size, switch.val < baseFieldModulus := fun switch =>
    lt_of_lt_of_le (lt_of_lt_of_le switch.isLt bound) (le_of_lt twoPowChunkBits_lt_modulus)
  have firstVal : ((first.val : BaseField)).val = first.val :=
    ZMod.val_cast_of_lt (small first)
  have secondVal : ((second.val : BaseField)).val = second.val :=
    ZMod.val_cast_of_lt (small second)
  apply Fin.ext
  rw [← firstVal, ← secondVal]
  exact congrArg ZMod.val equal

/-- One switch's mask vector `Y_{c,j}[e]`: three blocks per element, hashed at the one-hot
label of that switch, reduced by Rule S. -/
def switchMask {count : Nat} (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (switch : Nat) (label : Block) : Fin count → BaseField :=
  sampleVector oracle (fun element block => scaleIndexOf lane chunk switch element block) label

/-- `Σ_j Y_{c,j}[e]`, the aggregate that the published join carries. -/
def maskTotal {count : Nat} (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width) : Fin count → BaseField :=
  fun element =>
    ∑ switch : Fin (2 ^ width),
      switchMask oracle lane chunk switch.val (hot switch) element

/-- `O_c[e] = Σ_j ι(j) * Y_{c,j}[e]`, this chunk's share of the element's output mask.

It does not mention the slopes, which is what lets the garbler run plan D.4's order: sample
every `Y`, compute `O`, derive the slopes from `O`, and only then publish `J_c`. -/
def outputMask {count : Nat} (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width) : Fin count → BaseField :=
  fun element =>
    ∑ switch : Fin (2 ^ width),
      iota _ switch * switchMask oracle lane chunk switch.val (hot switch) element

/-- **`scale-hot`, garbler side.** The published join `J_c = (Σ_j Y_{c,j}) + s_c`.

The garbler masks constants by their negation, so the constant-`0` wire carries mask `0` and
the switch output mask is `Y_{c,j}`; the scalar wire carries mask `-s_c`, and the join material
is `Σ_j (output masks) - (input mask)`. -/
def garbleScale {count : Nat} (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width)
    (scalar : Fin count → BaseField) : Fin count → BaseField :=
  fun element => maskTotal oracle lane chunk width hot element + scalar element

/-- **`scale-hot`, evaluator side.** The free fold `Σ_j ι(j) * L_{c,j}` of Lemma 6.1.

At the active switch the evaluator cannot compute the mask; it recovers the open wire's label
from the published join as `J_c - Σ_{j ≠ α} Y_{c,j}`. Everywhere else the held label is the
mask itself. -/
def evalScale {count : Nat} (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width) (alpha : Fin (2 ^ width))
    (join : Fin count → BaseField) : Fin count → BaseField :=
  fun element =>
    ∑ switch : Fin (2 ^ width), iota _ switch *
      (if switch = alpha then
          join element - ∑ other ∈ Finset.univ.erase alpha,
            switchMask oracle lane chunk other.val (hot other) element
        else switchMask oracle lane chunk switch.val (hot switch) element)

end Kriterion.ArgoMAC.PlanB
