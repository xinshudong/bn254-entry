/-
**Phase 3, P1f — the designed-visibility rule `designedRule`.**

`designedRule scalar tape u entry` keeps a reached garbler entry iff its **index** is one the
evaluator is meant to hold at `u` — decided by the index and `u` alone, never by the entry's
input (the entry's input carrying a coincidence is exactly what made `D = true` false):

| index | designed at `u` |
|---|---|
| fold gate `(ℓ, c, step, r, half)` | `r ≠` the active parent `chunk_c(u) mod 2^step`, and (`ℓ` a curve lane, or `u` on the curve) |
| scale `(ℓ, c, j, e, b)` | `j ≠ chunk_c(u)`, and (`ℓ` a curve lane, or `u` on the curve) |
| gadget `(o, κ, pos)` | `u` on the curve, and `u`'s bit at `(κ, pos)` equals digit `o`'s exceptional input's |
| hash | `u` on the curve |
| EncPRF | never (`visibleEntries` has none) |

**No additive constant.** The coincidence views of P1c's trap (a reach that happens to equal a
hidden garbler point, e.g. a gadget point at a differing position when `Δ = pad₀ ⊕ pad₁`) are at
non-designed indices, so the designed view never contains them: such a coincidence is a stage-2
*touch* of a hidden entry by the adversary's own query, charged per query inside `L1`'s
`3/2^128` (the hidden point is `Δ`-uniform given the designed view). `GameUntilBad`'s error is
per-query only, and none is needed. `G1U` dominates the designed flagged law at this rule as at
every rule (`TwoStage.lateInstalled_ge`: `designedEntries ⊆ visibleEntries` by `List.filter`).

`stageOneGuess` (real): `StageOneGuess` at L1's constant. `hidden_of_stageTwo`: hop (1) from the one
remaining statement, `StageTwoGuess designedRule`.
-/

import Proof.Privacy.Phase3.Hidden.BridgeFamily

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- The input's bits on one coordinate. -/
def inputBits (input : AffineInput) : Coord → BitVec PlanB.coordinateBits
  | .x => coordinateBits input.x
  | .y => coordinateBits input.y

/-- A curve lane (system A). -/
def laneIsCurve : Lane → Bool
  | .curveX | .curveY => true
  | _ => false

/-- **The designed indices at an input.** -/
def designedIndex (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    FixedIndex → Bool
  | .hot ℓ c fold entry _ =>
      decide (entry.val ≠ (chunkOf (inputBits input ℓ.coord) c).val % 2 ^ fold.val) &&
        (laneIsCurve ℓ || validate input)
  | .scale ℓ c switch _ _ =>
      decide (switch.val ≠ (chunkOf (inputBits input ℓ.coord) c).val) && (laneIsCurve ℓ || validate input)
  | .gadget o κ position =>
      validate input &&
        decide ((inputBits input κ).getLsb position = exceptionalBit scalar tape.1.offsets o κ position)

/-- **The designed-visibility rule.** -/
def designedRule : Designed := fun scalar tape input entry =>
  match entry.1 with
  | .fixedForward index _ | .fixedInverse index _ => designedIndex scalar tape input index
  | .hash _ => validate input
  | _ => false

end Instances

/-- **`StageOneGuess` at L1's constant, real.** -/
theorem stageOneGuess : StageOneGuess (ENNReal.ofReal hiddenCharge) :=
  stageOneGuess_of_bridge stageOneBridgeGuess

/-- **Hop (1) from the stage-2 guess at `designedRule` alone.** -/
theorem hidden_of_stageTwo (two : StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of_guess designedRule stageOneGuess two

/-- **Hop (1) from the stage-1 bridge-key guess and the stage-2 guess at `designedRule`.** -/
theorem hidden_of_bridge (bridge : StageOneBridgeGuess)
    (two : StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge)) :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of_guess designedRule (stageOneGuess_of_bridge bridge) two

end

end Kriterion.ArgoMAC.Security.Phase3
