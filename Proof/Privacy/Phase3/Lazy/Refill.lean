/-
**Phase 3, P4 — `I^U`: the ideal game with every non-designated scale triple programmed uniform.**

`I` (`Glue.idealHybrid`) answers the simulator's honest evaluation from the shared lazy oracle
(`Glue.runIntercept`): a fresh forward query at a scale index is uniform on the outputs still
unused at that index. `I^U` differs in exactly one place. At the start of the opening it draws a
**mask tape** -- one block per (mask site, limb), the `N = 418,592` masks iid uniform on `F_p` and
the tape uniform on the fibre of `masksOf` (`uniformMaskTape`; the same fibre kernel as P1's
`G0 → G0U` swap) -- and a non-designated forward query at a mask-site index is answered from the
tape when it is the **first stage-2 touch of that index at a fresh input** (`consumeCell`): the
simulator *programs* `input ↦ limb xor input` (Davies–Meyer output `limb`), and a failed program
(the output already used at that index) aborts, like a failed designated program. Every other query
-- a repeated index, a known input (the cached stage-1 answer is returned, as in `I`), system A's
and B's non-site indices, EncPRF, the hash -- goes to the lazy oracle exactly as in `I`.

For the Plan B evaluator (one forward query per scale index) the first-touch rule is simply "every
non-designated scale triple is programmed from the tape". It is stated for an arbitrary query
computation, so no fact about the evaluator's query order is used anywhere in the `I^U → I` bound.

The runner `runRefill` takes the per-cell law as a parameter `draw`: `I^U` reads the tape
(`draw = pure ∘ tape`), and the proof's intermediate game draws a fresh uniform block per consumed
cell (`draw = uniform`).
-/

import Proof.Privacy.Phase3.GameSwap

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex siteIndex_injective masksOf fibreLaw)
open scoped ENNReal

noncomputable section

/-! ### Cells, tapes and the lazy state

Every definition below takes the index types' `DecidableEq` instances as arguments (as
`Glue.runIntercept` does), so that at the `Solution` instances (`Classical.decEq`, via
`atSolution`) the refill game and `I` use the same instances; the derived global instances are
never used. -/

section Definitions

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A mask site and one of its three limbs; `siteIndex` names its fixed-key index. -/
abbrev Cell := MaskSite × Fin 3

/-- One block per cell. -/
abbrev Tape := Cell → Block

/-- The lazy oracle state of Plan B. -/
abbrev LState := LazyOracle.State FixedIndex EncPRF.PermutationIndex

/-- The designated inputs recorded by the intercepting run. -/
abbrev Record := FixedIndex → Option Block

/-- A Plan B public query. -/
abbrev Request := PublicQuery FixedIndex EncPRF.PermutationIndex

open Classical in
/-- The cell whose index is the given one, if any (`siteIndex` is injective). -/
def cellOf (index : FixedIndex) : Option Cell :=
  if h : ∃ cell, siteIndex cell = index then some (Classical.choose h) else none

theorem cellOf_spec {index : FixedIndex} {cell : Cell} (found : cellOf index = some cell) :
    siteIndex cell = index := by
  unfold cellOf at found
  split at found
  · rename_i h
    cases found
    exact Classical.choose_spec h
  · cases found

theorem cellOf_siteIndex (cell : Cell) : cellOf (siteIndex cell) = some cell := by
  have exists_cell : ∃ other, siteIndex other = siteIndex cell := ⟨cell, rfl⟩
  unfold cellOf
  rw [dif_pos exists_cell]
  exact congrArg some (siteIndex_injective (Classical.choose_spec exists_cell))

/-- The fixed-key index a request touches, if any. -/
def touchedIndex : Request → Option FixedIndex
  | .fixedForward index _ => some index
  | .fixedInverse index _ => some index
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash _ => none

/-- The touched indices after a request. -/
def touch (request : Request) (touched : Set FixedIndex) : Set FixedIndex :=
  {index | index ∈ touched ∨ touchedIndex request = some index}

theorem subset_touch (request : Request) (touched : Set FixedIndex) :
    touched ⊆ touch request touched := fun _ member => Or.inl member

open Classical in
/-- **The consuming rule.** A forward query at a mask-site index that no stage-2 query has touched
yet, at an input not yet known there, reads the tape cell of that index. -/
def consumeCell (touched : Set FixedIndex) (oracle : LState) : Request → Option Cell
  | .fixedForward index input =>
      if index ∈ touched ∨ (oracle.fixed index).knownInput input.toFin then none else cellOf index
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash _ => none

/-- What a consuming request looks like. -/
theorem consumeCell_spec {touched : Set FixedIndex} {oracle : LState} {request : Request}
    {cell : Cell} (consumed : consumeCell touched oracle request = some cell) :
    ∃ index input, request = .fixedForward index input ∧ index ∉ touched ∧
      ¬ (oracle.fixed index).knownInput input.toFin ∧ siteIndex cell = index := by
  cases request with
  | fixedForward index input =>
      simp only [consumeCell] at consumed
      split_ifs at consumed with fresh
      exact ⟨index, input, rfl, fun member => fresh (Or.inl member),
        fun known => fresh (Or.inr known), cellOf_spec consumed⟩
  | fixedInverse _ _ => simp [consumeCell] at consumed
  | encForward _ _ => simp [consumeCell] at consumed
  | encInverse _ _ => simp [consumeCell] at consumed
  | hash _ => simp [consumeCell] at consumed

/-- The answer a programmed limb gives: the Davies–Meyer output is `limb`, so a forward query at
`input` returns `limb xor input`. (Only the forward case is ever consumed.) -/
def refillAnswer : (request : Request) → Block → request.Answer
  | .fixedForward _ input, limb => limb ^^^ input
  | .fixedInverse _ _, limb => limb
  | .encForward _ _, limb => limb
  | .encInverse _ _, limb => limb
  | .hash _, limb => (limb, limb)

/-! ### The refill runner -/

/-- **The `I^U` runner.** Designated queries are intercepted exactly as in `Glue.runIntercept`; a
consuming query (`consumeCell`) programs `input ↦ limb xor input` with `limb` drawn from
`draw cell`, and a failed program aborts; every other query goes to the lazy oracle. -/
def runRefill (bits : BitInput) (draw : Cell → PMF Block) {α : Type} :
    FreeQuery Programs.Spec α → LState → Record → Set FixedIndex →
      PMF (Option (α × LState × Record))
  | .pure value, oracle, record, _ => PMF.pure (some (value, oracle, record))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => runRefill bits draw (next answer) oracle (recordAfter bits request record)
          touched
      | none => match consumeCell touched oracle request with
        | some cell => (draw cell).bind fun limb =>
            match LazyOracle.program request (refillAnswer request limb) oracle with
            | none => PMF.pure none
            | some updated => runRefill bits draw (next (refillAnswer request limb)) updated
                record (touch request touched)
        | none => (LazyOracle.query request oracle).bind fun answer =>
            runRefill bits draw (next answer.1) answer.2 record (touch request touched)

/-- **`masksOf` is onto**: every mask family has a tape producing it. -/
theorem masksOf_surjective : Function.Surjective (masksOf (M := MaskSite)) := by
  intro masks
  have each : ∀ site, ∃ triple : Block × Block × Block,
      sampleFp triple.1 triple.2.1 triple.2.2 = masks site :=
    fun site => sampleFp_surjective (masks site)
  choose triple hTriple using each
  refine ⟨fun cell => ![(triple cell.1).1, (triple cell.1).2.1, (triple cell.1).2.2] cell.2, ?_⟩
  funext site
  exact hTriple site

/-- **The `I^U` mask tape**: the `N` masks iid uniform on `F_p`, then the tape uniformly among
those that produce them -- each site's three limbs are a uniform `sampleFp`-preimage of a uniform
field element, independently across sites. -/
def uniformMaskTape : PMF Tape :=
  (PMF.uniformOfFintype (MaskSite → BaseField)).bind (fibreLaw masksOf masksOf_surjective)

/-- The `I^U` run of a query computation: the tape, then the refill runner reading it. -/
def refillRun {α : Type} (bits : BitInput) (computation : FreeQuery Programs.Spec α)
    (oracle : LState) : PMF (Option (α × LState × Record)) :=
  uniformMaskTape.bind fun tape =>
    runRefill bits (fun cell => PMF.pure (tape cell)) computation oracle (fun _ => none) ∅

/-! ### `I^U` -/

/-- The opening after its honest run (`Glue.opening`, steps 2–5): tail, lifts, targets,
preimages, the 819 programs. -/
def openingCont [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature)
    (target : Point)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) : PMF (Option LState) :=
  let restored := Lamport.restore input labels
  samplers.tail.bind fun tail => match tail with
    | none => PMF.pure none
    | some tail => samplers.lift.bind fun lift => match lift with
      | none => PMF.pure none
      | some lift =>
        let evalRows := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
          (Pipeline.digitValues ran.1.1 ran.1.2) restored.input.toAffine
        let targets := collectorTargets restored.input evalRows (targetRows target tail lift)
        (preimages samplers targets).bind fun blocks => match blocks with
        | none => PMF.pure none
        | some blocks => PMF.pure (programAll (programRequests restored.input ran.2.2 blocks) ran.2.1)

/-- `Glue.opening` is its honest run followed by `openingCont`. -/
theorem opening_eq [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    opening samplers table input labels target oracle =
      (runIntercept (Lamport.restore input labels).input
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac) oracle fun _ => none).bind
        (openingCont samplers table input labels target) := rfl

/-- **The `I^U` opening**: the refill run in place of the intercepting run; an abort of the run
aborts the opening. -/
def refillOpening [FieldCertificate] [GroupCertificate] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    PMF (Option LState) :=
  let restored := Lamport.restore input labels
  (refillRun restored.input (openingQueriesM table restored.input restored.inputMac) oracle).bind
    fun ran => match ran with
    | none => PMF.pure none
    | some ran => openingCont samplers table input labels target ran

/-- The `I^U` stage 2: as `planBAbstractSimulator`, with the refill opening. -/
def refillStage2 [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (oracle : LState) :
    PMF (Option (LamportSignature × LState)) :=
  let labels := Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))
  match output with
  | none => PMF.pure (some (labels, oracle))
  | some target => (refillOpening samplers source.publicValue input labels target oracle).map
      (Option.map fun updated => (labels, updated))

/-- **The `I^U` abstract simulator**: `planBAbstractSimulator` with the refill stage 2. -/
def refillSimulator [FieldCertificate] [GroupCertificate] (samplers : Samplers) :
    LazyAbstractSimulator FixedIndex EncPRF.PermutationIndex Public :=
  { planBAbstractSimulator samplers with stage2 := refillStage2 samplers }

end Definitions

/-- **`I^U` as a chain game** (the `Hybrids.idealUniform` field): the abstract ideal game of the
refill simulator with the exact samplers. -/
def idealUniformHybrid : HybridGame := fun adversary parameter scalar =>
  abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter scalar ()

end

end Kriterion.ArgoMAC.Phase3.Lazy
