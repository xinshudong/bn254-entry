/-
**Stage 2, the interface of the opening** (the one open premise of `Stage2Law`).

The valid arm is `Replay.program`, then `Opening.program`, then the label emission.
`Opening.program` is the oracle-free part `openingFree` (the tail points, Horner and the head
clamp, the `91` randomisers, the lifts, the collector targets and the `273` preimages) followed by
the `819` programs and a register clear. This file states what the oracle-free part must do:

* `OpeningPre`: what it may read, as left by the prefix and the replay -- the request cells, the
  row constants, the two point lanes' (designated-free) accumulators and `κ`;
* `openingBlocks`: the abstract counterpart, the part of P3's `opening` between the replay and
  `programAll` (tail, lift, targets, preimages), for the extracted table and the replay's lanes;
* `OpeningLaw`: the law of `openingFree.memSem`, read through `openView` (the limb cells the
  programs read, the cells `tmpJStar` and `E*`, the labels and the response stack), is the law of
  `openingBlocks`, read through `blocksView` (the drawn limbs, the other four unchanged).

Everything else of `Stage2Law` (prefix, replay, programs, emission, the invalid arm) is proved
from `OpeningLaw` in `Stage2Valid.lean`.
-/

import Proof.Simulator.ReplayBase

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-- **The oracle-free part of the opening**: `Opening.program` without its `819` programs and
the final register clear. -/
def openingFree : Prog :=
  Prog.seqList [Opening.tail, Opening.horner, Opening.lambdas, Opening.lifts, Opening.solve,
    Opening.preimages]

section Spec

variable [FieldCertificate]

/-- The output cells the head clamp reads, `(tag₀, Q.x, Q.y)`: `(0, 0, 0)` for `O`. -/
def outputWords : Point → Word × Word × Word
  | .zero => (bitWord false, word 0, word 0)
  | .some (x := x) (y := y) _ => (bitWord true, fieldWord x, fieldWord y)

/-- **What the oracle-free opening may assume** about the memory it starts from (registers and
every other cell arbitrary). `bits = BitInput.ofAffine input` is the selected input. -/
structure OpeningPre (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory : Memory) : Prop where
  /-- `u.x` and `u.y`. -/
  reqXCell : memory.ram (word reqX) = fieldWord input.x
  reqYCell : memory.ram (word reqY) = fieldWord input.y
  /-- `tag₀`, `Q.x`, `Q.y` of the output `Q = f_k(u)`. -/
  outputCells : (memory.ram (word reqTag0), memory.ram (word reqQX), memory.ram (word reqQY)) =
    outputWords target
  /-- The row constants of every digit, in wire (cell) order (`rowField`: `xC0, xC1, xC2, xC4,
  yC0, yC2, yC3, yC4, yC5, zC0, zC1`). -/
  rowCells : ∀ (digit : Fin digitCount) (slot : Nat), slot < 11 →
    memory.ram (word (Opening.rowCell digit.val slot)) = fieldWord (rowField (source.rows.get digit) slot)
  /-- The `pointX` lane's (designated-free) values, slots `0 .. 454`. -/
  accXCells : ∀ element : Fin pointElementCountX,
    memory.ram (word (accBase + element.val)) = fieldWord (pointX element)
  /-- The `pointY` lane's values, slots `458 .. 821`. -/
  accYCells : ∀ element : Fin pointElementCountY,
    memory.ram (word (accBase + 458 + element.val)) = fieldWord (pointY element)
  /-- `κ = ι(j*) − ι(α₀)`. -/
  kappaCell : memory.ram (word tmpKappa) = fieldWord (kappa (BitInput.ofAffine input))

variable [GroupCertificate]

/-- **The abstract counterpart**: P3's `opening` from the replay's lanes to the drawn preimages
(the tail points with the clamp, the lifts, the collector targets, the preimages). -/
def openingBlocks (samplers : Samplers) (table : Public) (bits : BitInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField) :
    PMF (Option (Fin digitCount × Fin 3 → Block × Block × Block)) :=
  samplers.tail.bind fun tail => match tail with
    | none => PMF.pure none
    | some tail => samplers.lift.bind fun lift => match lift with
      | none => PMF.pure none
      | some lift =>
          preimages samplers (collectorTargets bits
            (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
              (Pipeline.digitValues pointX pointY) bits.toAffine)
            (targetRows target tail lift))

end Spec

/-- What the programs and the label emission read after the oracle-free opening. -/
abbrev OpenView :=
  (Fin digitCount → Fin 3 → Fin 3 → Word) × Word × Word × Vector Block 508 × List Bool

/-- The machine's view: the `819` limb cells, `tmpJStar`, `E*`, the labels, the response stack. -/
def openView (memory : Memory) : OpenView :=
  (fun digit collector block => memory.ram (word (openLimb digit.val collector.val block.val)),
    memory.ram (word tmpJStar), memory.ram (word (hotLabelBase + 4)), labelVector memory.ram,
    memory.bits 3)

/-- The abstract view: the drawn limbs, the other cells as they were. -/
def blocksView (memory : Memory) (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    OpenView :=
  (fun digit collector block => blockWord (limbAt block (blocks (digit, collector))),
    memory.ram (word tmpJStar), memory.ram (word (hotLabelBase + 4)), labelVector memory.ram,
    memory.bits 3)

/-- **The opening law** (the premise P2e proves): from every memory satisfying `OpeningPre`, the
oracle-free opening's law, read through `openView`, is `openingBlocks` of the machine's samplers,
read through `blocksView`. -/
def OpeningLaw : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
    (target : Point) (pointX : Fin pointElementCountX → BaseField)
    (pointY : Fin pointElementCountY → BaseField) (memory : Memory),
    OpeningPre source input target pointX pointY memory →
      (openingFree.memSem memory).map (Option.map openView) =
        (openingBlocks boundedSamplers source.publicValue (BitInput.ofAffine input) target pointX
          pointY).map (Option.map (blocksView memory))

end

end Kriterion.ArgoMAC.PlanB.SimMachine
