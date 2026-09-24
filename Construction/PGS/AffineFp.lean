/-
This file assembles the Plan B chunked affine encoding over `F_p`: one coordinate's whole
switch system, garbler and evaluator side.

The plan source is `2026-09-17-planB.md`, sections D.2--D.4 and Task 14;
the internal Python reference implementation is `pgs.py` (`coordinate_mask_pass`,
`scale_joins_from_slopes`, `coordinate_garble`, `coordinate_evaluate`).

Plan D.4's ordering is what the split into `offsets` and `garbleCoord` buys:

1. sample every switch mask `Y_{c,j}` from the tape,
2. compute `O[e] = sum_c sum_j iota(j) * Y_{c,j}[e]` -- this is `offsets`, and it does **not**
   mention the slopes,
3. the row layer computes the slopes from `O` (the element offset is `b_e := O[e]`, the
   output-mask absorption that costs 0 bytes),
4. `s_c := (a_e * 2 ^ (chunkBits * c))_e` -- this is `chunkScalar`,
5. publish `J_c = sum_j Y_{c,j} + s_c` -- this is `scaleJoins`.

The coordinate's `Σ_c (b_c - 1) = 127` fold joins are flattened into one
`Vector Block foldStepCount`; every chunk but the last pays `chunkBits - 1 = 1` step, so slot
`s` belongs to chunk `s / 1` at position `s % 1` and the last chunk's single join lands at
slot 126. `hotSlice` reads the flat vector back, and `hotSlice_flattenHot` says the round trip
is the identity.
-/

import Construction.PGS.ScaleHot

namespace Kriterion.ArgoMAC.PlanB

open BN254 Cryptography

variable {count : Nat}

/-! ### Chunk-local views of the coordinate's bits -/

/-- The position inside the coordinate of bit `position` of chunk `c`. -/
def chunkBitIndex (c : Fin chunkCount) (position : Fin (chunkWidth c)) : Fin coordinateBits :=
  ⟨chunkOffset c + position.val, by
    have inside := chunkOffset_add_width_le c
    have small := position.isLt
    omega⟩

/-- The garbler's label pairs of chunk `c`. -/
def chunkKey (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    Fin (chunkWidth c) → Block × Block :=
  fun position => bitKey (chunkBitIndex c position)

/-- The evaluator's held labels of chunk `c`. -/
def chunkLabels (labels : Fin coordinateBits → Block) (c : Fin chunkCount) :
    Fin (chunkWidth c) → Block :=
  fun position => labels (chunkBitIndex c position)

/-! ### The flat layout of the fold joins -/

/-- The chunk a flat fold-join slot belongs to. Every chunk but the last pays
`chunkBits - 1` steps, and the last chunk's single join lands exactly at the next slot. -/
def slotChunk (slot : Fin foldStepCount) : Fin chunkCount :=
  ⟨slot.val / (chunkBits - 1), by
    have bound := slot.isLt
    unfold foldStepCount at bound
    unfold chunkBits chunkCount
    omega⟩

/-- The position of a flat fold-join slot inside its chunk. -/
def slotOffset (slot : Fin foldStepCount) : Nat := slot.val % (chunkBits - 1)

/-- The flat slot of fold step `position` of chunk `c`. -/
def flatSlot (c : Fin chunkCount) (position : Fin (chunkWidth c - 1)) : Fin foldStepCount :=
  ⟨foldBase c + position.val, by
    have inside := foldBase_add_le c
    have small := position.isLt
    omega⟩

/-- The fold bases are the uniform multiples of `chunkBits - 1`: the last chunk is narrower,
but it is also last, so nothing after it shifts. -/
theorem foldBase_eq (c : Fin chunkCount) : foldBase c = (chunkBits - 1) * c.val := by
  rw [foldBase_eq_mul, Nat.mul_comm]

/-- Any flat slot whose value is `foldBase c + position` belongs to chunk `c`. -/
theorem slotChunk_eq (slot : Fin foldStepCount) (c : Fin chunkCount) (position : Nat)
    (small : position < chunkWidth c - 1) (value : slot.val = foldBase c + position) :
    slotChunk slot = c := by
  have width := chunkWidth_le c
  have chunks := c.isLt
  apply Fin.ext
  show slot.val / (chunkBits - 1) = c.val
  rw [value, foldBase_eq]
  unfold chunkBits at width ⊢
  unfold chunkCount at chunks
  omega

/-- ... at position `position` inside it. -/
theorem slotOffset_eq (slot : Fin foldStepCount) (c : Fin chunkCount) (position : Nat)
    (small : position < chunkWidth c - 1) (value : slot.val = foldBase c + position) :
    slotOffset slot = position := by
  have width := chunkWidth_le c
  have chunks := c.isLt
  show slot.val % (chunkBits - 1) = position
  rw [value, foldBase_eq]
  unfold chunkBits at width ⊢
  unfold chunkCount at chunks
  omega

/-- Flatten one block per (chunk, fold step) into the coordinate's published join vector. -/
def flattenHot (blockAt : Fin chunkCount → Nat → Block) : Vector Block foldStepCount :=
  Vector.ofFn fun slot => blockAt (slotChunk slot) (slotOffset slot)

/-- Read chunk `c`'s fold joins back out of the flat vector. -/
def hotSlice (joins : Vector Block foldStepCount) (c : Fin chunkCount) :
    Vector Block (chunkWidth c - 1) :=
  Vector.ofFn fun position => joins.get (flatSlot c position)

/-- Flattening and slicing are inverse. -/
theorem hotSlice_flattenHot (blockAt : Fin chunkCount → Nat → Block) (c : Fin chunkCount)
    (position : Nat) (inRange : position < chunkWidth c - 1) :
    (hotSlice (flattenHot blockAt) c)[position] = blockAt c position := by
  have slice : (hotSlice (flattenHot blockAt) c)[position]
      = (flattenHot blockAt).get (flatSlot c ⟨position, inRange⟩) := by
    simp only [hotSlice]
    exact Vector.getElem_ofFn inRange
  rw [slice]
  have flat : (flattenHot blockAt).get (flatSlot c ⟨position, inRange⟩)
      = blockAt (slotChunk (flatSlot c ⟨position, inRange⟩))
          (slotOffset (flatSlot c ⟨position, inRange⟩)) := by
    simp only [flattenHot]
    exact Vector.getElem_ofFn (flatSlot c ⟨position, inRange⟩).isLt
  rw [flat, slotChunk_eq _ c position inRange rfl, slotOffset_eq _ c position inRange rfl]

/-! ### One coordinate, garbler side -/

/-- `bin-to-hot` for chunk `c`: the one-hot masks and this chunk's fold joins. -/
def garbleChunk (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1) :=
  garbleHot oracle lane c (chunkWidth c) delta fun position => (chunkKey bitKey c position).1

/-- The block published at fold step `position` of chunk `c`. -/
def chunkJoinBlock (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) (position : Nat) :
    Block :=
  if inRange : position < chunkWidth c - 1 then
    (garbleChunk oracle lane delta bitKey c).2.get ⟨position, inRange⟩
  else 0

/-- The coordinate's `foldStepCount` published fold-join blocks. -/
def hotJoins (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) : Vector Block foldStepCount :=
  flattenHot (chunkJoinBlock oracle lane delta bitKey)

/-- The round trip: chunk `c` reads back exactly its own fold joins. -/
theorem hotSlice_hotJoins (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (delta : Block) (bitKey : Fin coordinateBits → Block × Block) (c : Fin chunkCount) :
    hotSlice (hotJoins oracle lane delta bitKey) c
      = (garbleChunk oracle lane delta bitKey c).2 := by
  refine Vector.ext ?_
  intro position inRange
  rw [hotJoins, hotSlice_flattenHot _ c position inRange, chunkJoinBlock, dif_pos inRange]
  rfl

/-- **Step (4) of plan D.4.** The scalar of chunk `c`: the element's slope, weighted by this
chunk's place value. -/
def chunkScalar (slopes : Fin count → BaseField) (c : Fin chunkCount) : Fin count → BaseField :=
  fun element => slopes element * (2 : BaseField) ^ chunkOffset c

/-- **Step (5) of plan D.4.** The `chunkCount` published `scale-hot` joins of one coordinate. -/
def scaleJoins (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (slopes : Fin count → BaseField) :
    Fin chunkCount → Fin count → BaseField :=
  fun c =>
    garbleScale oracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).1
      (chunkScalar slopes c)

/-- **`Garb`/`Enc` for one coordinate.** The published fold joins and the `chunkCount` published
`scale-hot` joins. -/
def garbleCoord (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) (slopes : Fin count → BaseField) :
    Vector Block foldStepCount × (Fin chunkCount → Fin count → BaseField) :=
  (hotJoins oracle lane delta bitKey, scaleJoins oracle lane delta bitKey slopes)

/-- **Step (2) of plan D.4: mask absorption, 0 bytes.** The element offsets
`O[e] = sum_c sum_j iota(j) * Y_{c,j}[e]`.

`offsets` depends only on `(oracle, lane, delta, bitKey)` -- never on the slopes -- which is
what lets the row layer take `b_e := O[e]` as the IT-GS element offset and then derive the
slopes from it in one pass. -/
def offsets (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBits → Block × Block) : Fin count → BaseField :=
  fun element =>
    ∑ c : Fin chunkCount,
      outputMask oracle lane c (chunkWidth c) (garbleChunk oracle lane delta bitKey c).1 element

/-! ### One coordinate, evaluator side -/

/-- **`Eval` for one coordinate.** Per chunk: rebuild the one-hot labels from the published
fold joins, fold them against the chunk index (Lemma 6.1), then sum over the 127 chunks. -/
def evalCoord (oracle : PermutationOracle FixedIndex Block) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBits) (labels : Fin coordinateBits → Block) :
    Fin count → BaseField :=
  fun element =>
    ∑ c : Fin chunkCount,
      evalScale oracle lane c (chunkWidth c)
        (evalHot oracle lane c (chunkWidth c) (hotSlice joins c) (chunkLabels labels c)
          (chunkValue bits c))
        (chunkOf bits c) (scale c) element

end Kriterion.ArgoMAC.PlanB
