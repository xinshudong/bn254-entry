/-
Phase 3 glue, step 3 (design note B §3, review B-review; note C T09): **the output-aware Plan B
simulator at PMF level**, in the form the library's `LazySimulatorProtocol.idealGame` consumes for
its abstract half (`LazyIdeal.lean`: a pair of kernels over the shared lazy oracle).

**Stage 1** makes no oracle call. It draws a `Stage1Source` -- every published field in source
form (the curve triple, the 91 row-constant records, the gadget bytes, the four fold-join vectors,
and the `127 × 824` scale joins as *canonical* field elements) together with the Lamport key
(508 label pairs) -- and publishes `publicValue` of it: the scale joins packed by the construction's
own `pack`, never a uniform `BitVec` word (design note B, F7). With every scale mask swapped to
uniform before the game starts (P1's `G0 → G0U`), this is the construction's published law.

**Stage 2** receives the selected input `u` and `f_k(u)`:

* `none` (invalid input): return the selected labels, no oracle call (§1.7);
* `some Q`: return the selected labels after the **opening** (§1.2–§2.2):
  1. run the honest evaluator's system A, the bridge hash, the 508 whitening pads and system B
     on the lazy oracle (`openingQueriesM`), *skipping* the 819 designated queries
     `fixedForward (scale pointX 0 j* e b) E*` -- `j* = α₀ xor 1`, `e` the three unit collectors
     `rowX_x9, rowY_x9, rowZ_x9` of each digit, `b` the three blocks -- which are answered
     virtually by `E*` itself (Davies–Meyer output `0`) and recorded (`runIntercept`); the
     evaluator's rows `R_d` on these values are therefore the collectors' running sums;
  2. draw the 90 tail digit points exactly as the construction's garbler draws its mask points --
     the `free` offsets of a uniform coin (`coinOffsetsLaw`), so no group-order fact is needed --
     then the head clamp `D_0 = Q − β • H(tail)` (group law only; it is `Q + clampedFirst tail`),
     and the 91 lift randomisers `λ_d`; the target rows are `W_d = lift(D_d, λ_d)`;
  3. solve each collector, `y* = κ · (W_d.c − R_d.c)` with `κ = ι(j*) − ι(α₀) = ±1`;
  4. draw a uniform `sampleFp`-preimage `(o₀, o₁, o₂)` of each `y*` (`y*.val + p·m`, `m` uniform);
  5. program the 819 designated points `E* ↦ o_b xor E*` in order (`LazyOracle.program`); any
     failed program (a used input or output) is an abort.

The samplers are a parameter (`Samplers`), exactly as the baseline's abstract ideal
(`sharedStrictSourceDecision offlineLaw onlineLaw`) takes its sampler laws: `idealSamplers` are the
exact uniform laws; a machine realises bounded ones (rejection with a cutoff, `none` on failure).

**The interface P2's machine must match** is `MachineLaw` at the end of this file.
-/

import Proof.Privacy.Phase3.Glue.LazyIdeal

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

/-! ### Stage 1: the published value in source form -/

/-- Every published field in source form, and the Lamport key. -/
structure Stage1Source where
  /-- The curve-membership constants. -/
  curve : BaseField × BaseField × BaseField
  /-- The eleven row constants of each digit. -/
  rows : Vector RowGamma digitCount
  /-- The gadget bytes. -/
  exception : Vector Exception.Entry digitCount
  /-- System A's fold joins, `x` lane. -/
  curveXHot : Vector Block foldStepCount
  /-- System A's fold joins, `y` lane. -/
  curveYHot : Vector Block foldStepCount
  /-- System B's fold joins, `x` lane. -/
  pointXHot : Vector Block foldStepCount
  /-- System B's fold joins, `y` lane. -/
  pointYHot : Vector Block foldStepCount
  /-- The scale joins of every chunk, as canonical field elements. -/
  joins : Fin chunkCount → Fin elementCount → BaseField
  /-- The 508 Lamport label pairs; stage 2 selects one of each. -/
  key : InputMacKey

/-- The published value of a stage-1 source: the scale joins are packed by `pack`. -/
def Stage1Source.publicValue (source : Stage1Source) : Public where
  curve := source.curve
  rows := source.rows
  exception := source.exception
  curveXHot := source.curveXHot
  curveYHot := source.curveYHot
  pointXHot := source.pointXHot
  pointYHot := source.pointYHot
  scale := Vector.ofFn fun chunk => pack (source.joins chunk)

/-! ### Finiteness (no cardinality is computed) -/

/-- A vector is determined by its entries. -/
local instance vectorFinite {α : Type} [Finite α] {count : Nat} : Finite (Vector α count) :=
  Finite.of_injective (fun values : Vector α count => fun index : Fin count => values[index])
    (by
      intro first second equal
      apply Vector.ext
      intro index bound
      exact congrFun equal ⟨index, bound⟩)

instance rowGammaFinite : Finite RowGamma :=
  Finite.of_injective (fun row : RowGamma => (row.xC0, row.xC1, row.xC2, row.xC4, row.yC0,
      row.yC2, row.yC3, row.yC4, row.yC5, row.zC0, row.zC1)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance bitAdaptorKeyFinite : Finite BitAdaptor.Key :=
  Finite.of_injective (fun key : BitAdaptor.Key => (key.falseLabel, key.trueLabel)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance inputMacKeyFinite : Finite InputMacKey :=
  Finite.of_injective (fun key : InputMacKey => (key.x, key.y)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance nonZeroScalarFinite : Finite NonZeroScalar :=
  Finite.of_injective (fun value : NonZeroScalar => value.value) (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance stage1SourceFinite : Finite Stage1Source :=
  Finite.of_injective (fun source : Stage1Source => (source.curve, source.rows, source.exception,
      source.curveXHot, source.curveYHot, source.pointXHot, source.pointYHot, source.joins,
      source.key)) (by
    intro first second equal
    cases first
    cases second
    simp_all)

noncomputable instance stage1SourceFintype : Fintype Stage1Source := Fintype.ofFinite _

noncomputable instance nonZeroScalarFintype : Fintype NonZeroScalar := Fintype.ofFinite _

noncomputable instance nonZeroBaseFintype : Fintype NonZeroBase := Fintype.ofFinite _

instance stage1SourceNonempty : Nonempty Stage1Source :=
  ⟨{ curve := (0, 0, 0)
     rows := Vector.replicate _ ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
     exception := Vector.replicate _ (Vector.replicate _ 0)
     curveXHot := Vector.replicate _ 0
     curveYHot := Vector.replicate _ 0
     pointXHot := Vector.replicate _ 0
     pointYHot := Vector.replicate _ 0
     joins := fun _ _ => 0
     key := ⟨Vector.replicate _ ⟨0, 0⟩, Vector.replicate _ ⟨0, 0⟩⟩ }⟩

/-- The scalar modulus exceeds one. -/
instance scalarModulusFact : Fact (1 < scalarFieldModulus) := ⟨by unfold scalarFieldModulus; norm_num⟩

/-- The base modulus exceeds one. -/
instance baseModulusFact : Fact (1 < baseFieldModulus) := ⟨by unfold baseFieldModulus; norm_num⟩

instance nonZeroScalarNonempty : Nonempty NonZeroScalar := ⟨⟨1, one_ne_zero⟩⟩

instance nonZeroBaseNonempty : Nonempty NonZeroBase := ⟨⟨1, one_ne_zero⟩⟩

/-! ### The samplers -/

/-- The number of `sampleFp`-preimages of `value` below `2^384`, minus one: the preimages are
`value.val + p·m` for `m ≤ preimageCount value`. -/
def preimageCount (value : BaseField) : Nat := (2 ^ 384 - 1 - value.val) / baseFieldModulus

/-- The three little-endian 128-bit limbs of a natural number below `2^384`. -/
def limbs (value : Nat) : Block × Block × Block :=
  (BitVec.ofNat 128 value, BitVec.ofNat 128 (value / 2 ^ 128), BitVec.ofNat 128 (value / 2 ^ 256))

/-- A uniform `sampleFp`-preimage of a field element: the conditional law of three fresh
uniform blocks given their reduction (design note B §1.4). -/
def idealPreimage (value : BaseField) : PMF (Block × Block × Block) :=
  (PMF.uniformOfFintype (Fin (preimageCount value + 1))).map fun m =>
    limbs (value.val + baseFieldModulus * m.val)

/-- The four sampler laws of the simulator; `none` is a sampler abort. -/
structure Samplers where
  /-- Stage 1: the published source and the Lamport key. -/
  source : PMF (Option Stage1Source)
  /-- The 90 tail digit points, as the construction's free offsets. -/
  tail : PMF (Option (Vector FieldMacToECMac.AffineOffset 90))
  /-- The 91 lift randomisers `λ_d ∈ F_p^*`. -/
  lift : PMF (Option (Fin digitCount → NonZeroBase))
  /-- A `sampleFp`-preimage of a field element. -/
  preimage : BaseField → PMF (Option (Block × Block × Block))

/-- **The construction's law of its mask points**: the offsets of a uniform coin. The garbler reads
its 91 `K` points from exactly these offsets (`FieldMacToECMac.outputKeys … coins.offsets`). -/
def coinOffsetsLaw : PMF FieldMacToECMac.SuccessfulOffsets :=
  letI : Fintype Coins := Fintype.ofFinite Coins
  (PMF.uniformOfFintype Coins).map Coins.offsets

/-- The exact samplers of the abstract simulator: uniform sources, lifts and preimages, and the
tail points drawn by the construction's own offset law. -/
def idealSamplers : Samplers where
  source := (PMF.uniformOfFintype Stage1Source).map some
  tail := coinOffsetsLaw.map fun offsets => some offsets.free
  lift := (PMF.uniformOfFintype (Fin digitCount → NonZeroBase)).map some
  preimage value := (idealPreimage value).map some

/-- Independent draws from a finite family of abort-or-value samplers; any abort aborts. -/
def optionProduct {α : Type} : (count : Nat) → (Fin count → PMF (Option α)) →
    PMF (Option (Fin count → α))
  | 0, _ => PMF.pure (some Fin.elim0)
  | count + 1, sample => (sample 0).bind fun head => match head with
    | none => PMF.pure none
    | some head => (optionProduct count fun index => sample index.succ).map
        (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)

/-! ### The designated switch and the collectors -/

/-- Chunk `0`. -/
def chunkZero : Fin chunkCount := ⟨0, chunkCount_pos⟩

/-- The active switch `α₀` of chunk `0` of lane `pointX` (the low bits of `x`). -/
def activeSwitch (bits : BitInput) : Fin (2 ^ chunkWidth chunkZero) :=
  chunkOf (Pipeline.coordBits bits .x) chunkZero

/-- The designated switch `j* = α₀ xor 1`: inactive, queried by the evaluator, and with an
inactive last-step fold parent (B-review (2)). -/
def designatedSwitch (bits : BitInput) : Fin (2 ^ chunkWidth chunkZero) :=
  ⟨(activeSwitch bits).val ^^^ 1, by
    have := chunkWidth_pos chunkZero
    exact Nat.xor_lt_two_pow (activeSwitch bits).isLt (Nat.one_lt_two_pow (by omega))⟩

/-- `κ = ι(j*) − ι(α₀)`, the designated mask's coefficient in the evaluator's free fold (`±1`). -/
def kappa (bits : BitInput) : BaseField :=
  iota _ (designatedSwitch bits) - iota _ (activeSwitch bits)

/-- The three unit collectors of a digit, one per row: `rowX_x9`, `rowY_x9`, `rowZ_x9`. -/
def collectorElement : Fin 3 → XElement := ![.rowX_x9, .rowY_x9, .rowZ_x9]

/-- The row coordinate each collector controls. -/
def collectorComponent : Fin 3 → FieldMacToECMac.HomogeneousValue → BaseField :=
  ![fun value => value.x, fun value => value.y, fun value => value.z]

/-- The designated fixed index of (digit, collector, block). -/
def designatedIndex (bits : BitInput) (digit : Fin digitCount) (collector block : Fin 3) :
    FixedIndex :=
  scaleIndexOf (count := pointElementCountX) .pointX chunkZero (designatedSwitch bits).val
    (xElementIndex digit (collectorElement collector)) block

/-- The 819 designated indices of an input. -/
def IsDesignated (bits : BitInput) (index : FixedIndex) : Prop :=
  ∃ digit collector block, designatedIndex bits digit collector block = index

/-- A candidate designated site: a (digit, collector, block) slot and a candidate switch of chunk
`0`. The input selects one switch per slot (`j* = α₀ xor 1` ranges over all four switches). -/
abbrev CandidateSite := Fin digitCount × Fin 3 × Fin 3 × Fin (2 ^ chunkWidth chunkZero)

/-- The fixed index of a candidate site: the scale index of that slot at that switch. -/
def candidateIndex (site : CandidateSite) : FixedIndex :=
  scaleIndexOf (count := pointElementCountX) .pointX chunkZero site.2.2.2.val
    (xElementIndex site.1 (collectorElement site.2.1)) site.2.2.1

/-- A designated index is the candidate index of its slot at the selected switch. -/
theorem designatedIndex_eq_candidateIndex (bits : BitInput) (digit : Fin digitCount)
    (collector block : Fin 3) :
    designatedIndex bits digit collector block =
      candidateIndex (digit, collector, block, designatedSwitch bits) := rfl

/-- The three collectors are distinct elements. -/
theorem collectorElement_injective : Function.Injective collectorElement := by decide

/-- **The candidate indices are pairwise distinct**: an index names its switch, so the per-switch
index sets do not overlap and a stage-1 query at one index is charged to one candidate site. -/
theorem candidateIndex_injective : Function.Injective candidateIndex := by
  rintro ⟨digit, collector, block, switch⟩ ⟨digit', collector', block', switch'⟩ equal
  have widthBound : 2 ^ chunkWidth chunkZero ≤ 2 ^ chunkBits :=
    Nat.pow_le_pow_right (by norm_num) (chunkWidth_le chunkZero)
  have elementBound (d : Fin digitCount) (c : Fin 3) :
      (xElementIndex d (collectorElement c)).val < elementCountX :=
    lt_of_lt_of_le (xElementIndex d (collectorElement c)).isLt (by
      unfold pointElementCountX elementCountX
      omega)
  simp only [candidateIndex] at equal
  rw [scaleIndexOf_eq _ _ _ _ _ (elementBound digit collector)
      (lt_of_lt_of_le switch.isLt widthBound),
    scaleIndexOf_eq _ _ _ _ _ (elementBound digit' collector')
      (lt_of_lt_of_le switch'.isLt widthBound)] at equal
  simp only [FixedIndex.scale.injEq, Fin.mk.injEq, true_and] at equal
  obtain ⟨sameSwitch, sameElement, sameBlock⟩ := equal
  have samePair := xElementIndex_injective (a₁ := (digit, collectorElement collector))
    (a₂ := (digit', collectorElement collector')) (Fin.ext sameElement)
  simp only [Prod.mk.injEq] at samePair
  obtain ⟨sameDigit, sameCollector⟩ := samePair
  subst sameDigit sameBlock
  rw [collectorElement_injective sameCollector, Fin.ext sameSwitch]

/-! ### The honest queries with the designated ones skipped -/

open Classical in
/-- A designated forward query is answered virtually by its own input (Davies–Meyer output `0`),
without touching the oracle; every other query goes to the lazy oracle. -/
def interceptAnswer (bits : BitInput) :
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex) → Option request.Answer
  | .fixedForward index input => if IsDesignated bits index then some input else none
  | .fixedInverse _ _ => none
  | .encForward _ _ => none
  | .encInverse _ _ => none
  | .hash _ => none

open Classical in
/-- The designated inputs `E*` seen so far. -/
def recordAfter [DecidableEq FixedIndex] (bits : BitInput)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (record : FixedIndex → Option Block) : FixedIndex → Option Block :=
  match request with
  | .fixedForward index input =>
      if IsDesignated bits index then Function.update record index (some input) else record
  | _ => record

/-- Run a Plan B query computation on the lazy oracle, skipping the designated queries and
recording their inputs. -/
def runIntercept [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] {α : Type}
    (bits : BitInput) :
    FreeQuery Programs.Spec α → LazyOracle.State FixedIndex EncPRF.PermutationIndex →
      (FixedIndex → Option Block) →
        PMF (α × LazyOracle.State FixedIndex EncPRF.PermutationIndex × (FixedIndex → Option Block))
  | .pure value, oracle, record => PMF.pure (value, oracle, record)
  | .query request next, oracle, record =>
      match interceptAnswer bits request with
      | some answer => runIntercept bits (next answer) oracle (recordAfter bits request record)
      | none => (LazyOracle.query request oracle).bind fun answer =>
          runIntercept bits (next answer.1) answer.2 record

/-- The bit-`false` whitening pads only: `508` EncPRF queries (design note B §1.6). -/
def whitePadsM (keys : WhiteningKeys) :
    Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .x index false) >>= fun xs =>
    FreeQuery.vector coordinateBitCount (fun index => Programs.padM keys .y index false) >>= fun ys =>
      pure fun which index => match which with
        | .x => (xs.get index, xs.get index)
        | .y => (ys.get index, ys.get index)

/-- The simulator's honest evaluation, in the evaluator's order: system A, the bridge hash, the
whitening pads, system B. It returns system B's two lane vectors. -/
def openingQueriesM [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  Programs.evalLaneM curveElementCountX .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
    Programs.evalLaneM curveElementCountY .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
      Programs.askHash (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY)) >>= fun hashed =>
        whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
          Programs.evalLaneM pointElementCountX .pointX table.pointXHot
              (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .x) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .x)
            >>= fun pointX =>
          Programs.evalLaneM pointElementCountY .pointY table.pointYHot
              (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .y) (Pipeline.macLabels (Programs.whitenMacOf pads mac) .y)
            >>= fun pointY =>
          pure (pointX, pointY)

/-! ### The output kernel: target rows from `f_k(u)` -/

/-- The BN254 point `(1, 2)`. Not used by the simulator: the tail points are the construction's
offsets, so no generator (and no `#Point = r` fact) is needed. -/
def generator [FieldCertificate] : Point := (decodePoint ⟨1, 2⟩).getD 0

/-- The Jacobian lift `(λ²X, λ³Y, λ)`, and `(λ², λ³, 0)` at the identity. -/
def liftRow [FieldCertificate] (point : Point) (scale : BaseField) :
    FieldMacToECMac.HomogeneousValue :=
  match point with
  | .zero => ⟨scale ^ 2, scale ^ 3, 0⟩
  | .some (x := x) (y := y) _ => ⟨scale ^ 2 * x, scale ^ 3 * y, scale⟩

/-- The 91 digit points: the 90 tail points are the given offsets' points, and the head is the
clamp `Q − β • H(tail)`, stated with the group law only, so that `pointHorner β (D_0 :: tail) = Q`
(design note B §1.2). -/
def digitPoints [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (digit : Fin digitCount) : Point :=
  if head : digit.val = 0 then target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints tail)
  else (tail.get ⟨digit.val - 1, by
    have bound := digit.isLt
    unfold digitCount at bound
    omega⟩).point

/-- The head digit point is the target plus the construction's own clamp of the tail. -/
theorem digitPoints_head [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90) :
    digitPoints target tail ⟨0, by unfold digitCount; omega⟩ =
      target + FieldMacToECMac.clampedFirst tail := by
  simp only [digitPoints, dif_pos, FieldMacToECMac.clampedFirst, sub_eq_add_neg]

/-- The target rows `W_d = lift(D_d, λ_d)`. -/
def targetRows [FieldCertificate] [GroupCertificate] (target : Point)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (lift : Fin digitCount → NonZeroBase)
    (digit : Fin digitCount) : FieldMacToECMac.HomogeneousValue :=
  liftRow (digitPoints target tail digit) (lift digit).value

/-- The designated mask each collector needs: `y* = κ · (W_d.c − R_d.c)`, where `R_d`
is the evaluator's row with every designated mask at `0`. -/
def collectorTargets (bits : BitInput)
    (evalRows : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount)
    (targets : Fin digitCount → FieldMacToECMac.HomogeneousValue) :
    Fin digitCount × Fin 3 → BaseField :=
  fun site => kappa bits *
    (collectorComponent site.2 (targets site.1) - collectorComponent site.2 (evalRows.get site.1))

/-- A `sampleFp`-preimage of every collector target, drawn independently. -/
def preimages (samplers : Samplers) (targets : Fin digitCount × Fin 3 → BaseField) :
    PMF (Option (Fin digitCount × Fin 3 → Block × Block × Block)) :=
  (optionProduct (digitCount * 3) fun index =>
      samplers.preimage (targets (finProdFinEquiv.symm index))).map
    (Option.map fun blocks site => blocks (finProdFinEquiv site))

/-- Block `b` of a limb triple. -/
def limbAt (block : Fin 3) (triple : Block × Block × Block) : Block :=
  if block.val = 0 then triple.1 else if block.val = 1 then triple.2.1 else triple.2.2

/-- The 819 program requests `(index, E*, o_b)`, digit by digit. -/
def programRequests (bits : BitInput) (record : FixedIndex → Option Block)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    List (FixedIndex × Option Block × Block) :=
  (List.finRange digitCount).flatMap fun digit =>
    (List.finRange 3).flatMap fun collector =>
      (List.finRange 3).map fun block =>
        let index := designatedIndex bits digit collector block
        (index, record index, limbAt block (blocks (digit, collector)))

/-- Program every request `E* ↦ o_b xor E*` (so the Davies–Meyer output is `o_b`); a missing
input or a failed program aborts. -/
def programAll [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] :
    List (FixedIndex × Option Block × Block) →
      LazyOracle.State FixedIndex EncPRF.PermutationIndex →
        Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)
  | [], oracle => some oracle
  | (index, input, output) :: rest, oracle => match input with
    | none => none
    | some input => (LazyOracle.program (.fixedForward index input) (output ^^^ input) oracle).bind
        (programAll rest)

/-- **The opening** of a valid input to `target = f_k(u)` (steps 1–5 of the header). -/
def opening [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (samplers : Samplers) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex) :
    PMF (Option (LazyOracle.State FixedIndex EncPRF.PermutationIndex)) :=
  let restored := Lamport.restore input labels
  (runIntercept restored.input (openingQueriesM table restored.input restored.inputMac) oracle
      fun _ => none).bind fun ran =>
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

/-- **The output-aware Plan B abstract simulator.** -/
def planBAbstractSimulator [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (samplers : Samplers) :
    LazyAbstractSimulator FixedIndex EncPRF.PermutationIndex Public where
  State := Stage1Source
  stage1 _ oracle := samplers.source.map (Option.map fun source => (source.publicValue, source, oracle))
  stage2 source input output oracle :=
    let labels := Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))
    match output with
    | none => PMF.pure (some (labels, oracle))
    | some target => (opening samplers source.publicValue input labels target oracle).map
        (Option.map fun updated => (labels, updated))

/-- **`I`, the abstract ideal game** of the Plan B simulator (design note B §3, `absIdeal`). -/
def planBIdealGame [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] {Aux : Type} (samplers : Samplers)
    (adversary : PlanBAdversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) : PMF Bool :=
  abstractIdealGame Scheme.scheme (planBAbstractSimulator samplers) adversary parameter scalar
    auxiliary

/-! ### The chain games at the `Solution` instances -/

/-- A game of the Plan B chain: one for every certificate pair and every choice of the index
instances, against every `Unit`-auxiliary Plan B adversary. The proof-only hybrids of P1 are
values of this type. -/
abbrev HybridGame : Type 1 :=
  ∀ [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
    [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex],
    PlanBAdversary Unit → Nat → NonZeroScalar → PMF Bool

/-- A chain game at the instances `Solution.adaptivePrivacy` installs: `Fintype.ofFinite` and
`Classical.decEq` on both index types. -/
def atSolution (game : HybridGame) (field : FieldCertificate) (group : @GroupCertificate field) :
    PlanBAdversary Unit → Nat → NonZeroScalar → PMF Bool :=
  @game field group (Fintype.ofFinite FixedIndex) (Fintype.ofFinite EncPRF.PermutationIndex)
    (Classical.decEq FixedIndex) (Classical.decEq EncPRF.PermutationIndex)

/-- `I`: the abstract ideal game of the exact samplers, as a chain game. -/
def idealHybrid : HybridGame := fun adversary parameter scalar =>
  planBIdealGame idealSamplers adversary parameter scalar ()

/-- `M`: the library's ideal game with a closed machine, as a chain game. -/
def machineHybrid (simulator : BoundedMachine.Simulator) : HybridGame :=
  fun adversary parameter scalar =>
    LazySimulatorProtocol.idealGame Scheme.scheme Wire.encoding 3363376 simulator adversary
      parameter scalar ()

/-! ### The interface P2's machine must match -/

/-- The machine's sampling-cutoff allowance, `I → M`. The planned samplers cut off at about
`2^-391.72` (273 preimages × 256 retries dominate); the allowance is relaxed to `2^-128` so a
machine has ample slack, and the budget still closes (constant ≈ `2^-110.28`). -/
def machineCutoffError : ℝ := 1 / 2 ^ 128

/-- **The machine law (P2, design note B theorems 23–27).** Against every adversary, at the
instances `Solution.adaptivePrivacy` installs, the library's ideal game with the closed machine is
within `error` of the abstract ideal game `I` of the exact samplers.

The cost bound `size + 1 + firstFuel + secondFuel ≤ 2^60` is the `within` field of
`BoundedMachine.Simulator` itself. The expected route to this law is kernel-level:
`idealGame_eq_machineAbstract` makes the library game the abstract game of the machine's
kernels, `abstractIdealGame_eq_of_simulation` identifies those kernels with
`planBAbstractSimulator bounded` for the machine's bounded samplers, and the sampler cutoffs
bound the distance to `idealSamplers`. -/
def MachineLaw (simulator : BoundedMachine.Simulator) (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : Nat) (scalar : NonZeroScalar),
    Assumptions.advantage (atSolution idealHybrid field group adversary parameter scalar)
      (atSolution (machineHybrid simulator) field group adversary parameter scalar) ≤ error

end

end Kriterion.ArgoMAC.Phase3.Glue
