/-
**Phase 3, P1f — shifting the whole tape.**

A `TapeShift` fixes the shift of each coordinate's `Δ` and zero labels, of the second block of
`hash(t)` (the whitening key `k₂`), and per lane and chunk of the fold's step materials and gate
outputs. `shiftTape T scalar` applies it to a tape:

* the coins: `Δ` and the zero labels XOR the shift;
* the fixed-key permutations: `shiftPerm` at the index's shift (`indexShift`): the fold gates by
  `FoldShift.hot`, the scale permutations conjugated by their switch's level shift, the gadget
  permutations conjugated by the shift of the label the garbler reads there (which depends on the
  digit's exceptional input, hence on the scalar);
* the hash: `k₂` at the bridge key moves by `T.key2`; EncPRF is untouched.

`shiftEntry` is the matching map on transcript entries. `Good` is the shape of every garbler entry:
a fixed-key query at index `i` asks at `garblerPointOf i`, the hash is asked at `t`.
-/

import Proof.Privacy.Phase3.Hidden.Lane

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-- A point lane (system B), whose labels are whitened by `hash(t)`. -/
def laneIsPoint : Lane → Bool
  | .pointX | .pointY => true
  | _ => false

/-- The shift of the whole tape. -/
structure TapeShift where
  /-- The shift of each coordinate's `Δ`. -/
  delta : Coord → Block
  /-- The shift of each raw zero label. -/
  zero : Coord → Fin PlanB.coordinateBits → Block
  /-- The shift of `k₂ = hash(t).2`. -/
  key2 : Block
  /-- Per lane and chunk, the shift of each paid step material. -/
  m : Lane → Fin chunkCount → Nat → Nat → Block
  /-- Per lane and chunk, the shift of both outputs of each fold gate. -/
  o : Lane → Fin chunkCount → Nat → Nat → Block

namespace TapeShift

/-- The shift of one lane: system B's zero labels also move with `k₂`. -/
def lane (T : TapeShift) (ℓ : Lane) : LaneShift where
  delta := T.delta ℓ.coord
  zero position := T.zero ℓ.coord position ^^^ (if laneIsPoint ℓ then T.key2 else 0)
  m := T.m ℓ
  o := T.o ℓ

/-- Every lane keeps its joins. -/
def Valid (T : TapeShift) : Prop := ∀ ℓ, (T.lane ℓ).Valid

end TapeShift

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The output key of digit `o`. -/
def digitKey (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets) (o : Fin digitCount) :
    FieldMacToECMac.OutputKey :=
  (FieldMacToECMac.outputKeys construction scalar.value offsets).get o

/-- One coordinate of an affine input. -/
def coordValue' : Coord → AffineInput → BaseField
  | .x, input => input.x
  | .y, input => input.y

/-- The bit of digit `o`'s exceptional input at `(κ, position)` (`false` for a digit without
exception, whose gadget asks nothing). -/
def exceptionalBit (scalar : NonZeroScalar) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) : Bool :=
  match digitEndomorphismBase (digitKey scalar offsets o).digit with
  | none => false
  | some phi => (coordinateBits (coordValue' κ
      (Exception.exceptionalInput phi (digitKey scalar offsets o).offset.coordinates))).getLsb position

/-- The shift of the label the gadget reads at `(o, κ, position)`. -/
def gadgetShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (o : Fin digitCount)
    (κ : Coord) (position : Fin PlanB.coordinateBits) : Block :=
  T.key2 ^^^ T.zero κ position ^^^
    (if exceptionalBit scalar coins.offsets o κ position then T.delta κ else 0)

/-- **The shift of every fixed-key permutation.** -/
def indexShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) : FixedIndex → Block × Block
  | .hot ℓ c fold entry half => ((T.lane ℓ).fold c).hot fold.val entry.val half
  | .scale ℓ c switch _ _ =>
      (((T.lane ℓ).fold c).level (chunkWidth c) switch.val,
        ((T.lane ℓ).fold c).level (chunkWidth c) switch.val)
  | .gadget o κ position => (gadgetShift T scalar coins o κ position, gadgetShift T scalar coins o κ position)

/-- The shifted coins. -/
def shiftCoins (T : TapeShift) (coins : Coins) : Coins :=
  { coins with
    inputZero := fun κ position => coins.inputZero κ position ^^^ T.zero κ position
    inputDelta := fun κ => coins.inputDelta κ ^^^ T.delta κ }

/-- The shifted hash: `k₂` at the bridge key. -/
def shiftHash (T : TapeShift) (key : BaseField) (hash : EncPRF.HashOracle) : EncPRF.HashOracle :=
  fun value => if value = key then ((hash value).1, (hash value).2 ^^^ T.key2) else hash value

/-- The shifted oracle. -/
def shiftOracle (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (oracle : Oracle) : Oracle :=
  (⟨fun index => shiftPerm (indexShift T scalar coins index).1 (indexShift T scalar coins index).2
      (oracle.1.permutation index)⟩, oracle.2.1, shiftHash T coins.bridgeKey oracle.2.2)

/-- **The shifted tape.** -/
def shiftTape (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) : Coins × Oracle :=
  (shiftCoins T tape.1, shiftOracle T scalar tape.1 tape.2)

/-- The matching map on transcript entries. -/
def shiftEntry (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    Asked FixedIndex EncPRF.PermutationIndex → Asked FixedIndex EncPRF.PermutationIndex
  | ⟨.fixedForward index input, answer⟩ =>
      ⟨.fixedForward index (input ^^^ (indexShift T scalar coins index).1),
        (show Block from answer) ^^^ (indexShift T scalar coins index).2⟩
  | ⟨.fixedInverse index output, answer⟩ =>
      ⟨.fixedInverse index (output ^^^ (indexShift T scalar coins index).2),
        (show Block from answer) ^^^ (indexShift T scalar coins index).1⟩
  | ⟨.encForward index input, answer⟩ => ⟨.encForward index input, answer⟩
  | ⟨.encInverse index output, answer⟩ => ⟨.encInverse index output, answer⟩
  | ⟨.hash value, answer⟩ =>
      if value = coins.bridgeKey then
        ⟨.hash value, ((show Block × Block from answer).1, (show Block × Block from answer).2 ^^^ T.key2)⟩
      else ⟨.hash value, answer⟩

/-! ### The garbler's points -/

/-- Each lane's `Δ` and bit keys on a tape (`GameSwap.garblerKeys`). -/
def laneKeys (tape : Coins × Oracle) :
    (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block) :=
  garblerKeys (tape.1, tape.2.2.1, tape.2.2.2)

/-- The label the gadget of digit `o` reads at `(κ, position)`. -/
def gadgetLabel (scalar : NonZeroScalar) (tape : Coins × Oracle) (o : Fin digitCount) (κ : Coord)
    (position : Fin PlanB.coordinateBits) : Block :=
  match digitEndomorphismBase (digitKey scalar tape.1.offsets o).digit with
  | none => 0
  | some phi =>
      let mac := (EncPRF.transformKey tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey)
        tape.1.inputMacKey).encodeAffine
          (Exception.exceptionalInput phi (digitKey scalar tape.1.offsets o).offset.coordinates)
      match κ with
      | .x => mac.x.get position
      | .y => mac.y.get position

/-- **The garbler's point at each fixed-key index.** -/
def garblerPointOf (scalar : NonZeroScalar) (tape : Coins × Oracle) : FixedIndex → Block
  | .hot ℓ c fold entry _ =>
      (garbleFold tape.2.1 ℓ c ((laneKeys tape).1 ℓ)
        (labelAt fun p => (chunkKey ((laneKeys tape).2 ℓ) c p).1) fold.val).1
        ⟨entry.val % 2 ^ fold.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  | .scale ℓ c switch _ _ =>
      (garbleChunk tape.2.1 ℓ ((laneKeys tape).1 ℓ) ((laneKeys tape).2 ℓ) c).1
        ⟨switch.val % 2 ^ chunkWidth c, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  | .gadget o κ position => gadgetLabel scalar tape o κ position

/-- **The shape of a garbler entry.** -/
def Good (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Asked FixedIndex EncPRF.PermutationIndex → Prop
  | ⟨.fixedForward index input, _⟩ => input = garblerPointOf scalar tape index
  | ⟨.encForward _ _, _⟩ => True
  | ⟨.hash value, _⟩ => value = tape.1.bridgeKey
  | _ => False

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
