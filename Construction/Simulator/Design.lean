/-
The design of the Plan B simulator machine: its phases, its exact instruction counts, and the
cost bound `code size + stage-1 fuel + stage-2 fuel ≤ 2 ^ 60` (in fact `< 2 ^ 36.3`).

The register / RAM / stack layout is `Construction/Simulator/Layout.lean`. The counts below are
closed formulas; the machine modules prove that their `Prog.size` / `Prog.cost` equal them
(`Construction/Simulator.lean`), so the numbers here are the machine's, not estimates.

**Static cost.** Every `Prog` has one cost on every non-aborting path (`ite` pads its cheaper
arm), so the fuels below are exact: a stage that does not abort halts after exactly its fuel.
The only data-dependent branch without padding is the top-level output-tag dispatch of stage 2,
whose fuel is the larger (valid) arm.

**Top-level code layout** (slot `0 .. size`):

| slots | contents |
|---|---|
| `0, 1` | pop the two protocol tag bits (`[f, f]` stage 1, `[f, t]` stage 2) |
| `2 ..` | stage 1, then `halt` |
| next | stage-2 prefix (parse, select labels), then `branch rFlag` |
| next | invalid arm (emit labels), then `halt` |
| next | valid arm (replay, opening, emit labels), then `halt` |
| last | reject `halt` |
-/

import Construction.Simulator.Layout

namespace Kriterion.ArgoMAC.PlanB.SimMachine

namespace Design

/-- The phases, in execution order. -/
inductive Phase
  /-- Pop the two protocol tag bits. -/
  | dispatch
  /-- Stage 1: `105,652` bounded-rejection field cells (curve, rows, scale joins). -/
  | fields
  /-- Stage 1: `546` exception bytes. -/
  | bytes
  /-- Stage 1: `508` fold-join blocks. -/
  | hotJoins
  /-- Stage 1: the `1016`-block Lamport key. -/
  | key
  /-- Stage 1: emit the `26,907,008` wire bits of `Wire.encoding`. -/
  | serialize
  /-- Stage 2: parse `u` and `f_k u`. -/
  | parse
  /-- Stage 2: select one key label per input bit. -/
  | selectLabels
  /-- Stage 2 valid: zero the `824` accumulators. -/
  | initAcc
  /-- Stage 2 valid: system A (`curveX`, `curveY`), `6,223` fixed queries. -/
  | systemA
  /-- Stage 2 valid: the bridge value `t` and one hash query. -/
  | bridge
  /-- Stage 2 valid: `508` EncPRF false-pad queries. -/
  | whiten
  /-- Stage 2 valid: system B (`pointX` with `819` designated skips, `pointY`). -/
  | systemB
  /-- Stage 2 valid: `90` uniform finite curve points (the construction's offset law). -/
  | tail
  /-- Stage 2 valid: Horner and the head clamp. -/
  | horner
  /-- Stage 2 valid: `91` lift randomisers. -/
  | lambdas
  /-- Stage 2 valid: `91` lifted rows. -/
  | lifts
  /-- Stage 2 valid: `273` collector targets. -/
  | solve
  /-- Stage 2 valid: `273` `sampleFp` preimages. -/
  | preimages
  /-- Stage 2 valid: `819` programs. -/
  | programs
  /-- Stage 2: emit the `508` labels. -/
  | emitLabels
deriving DecidableEq

/-- The phase list. -/
def phases : List Phase :=
  [.dispatch, .fields, .bytes, .hotJoins, .key, .serialize, .parse, .selectLabels, .initAcc,
    .systemA, .bridge, .whiten, .systemB, .tail, .horner, .lambdas, .lifts, .solve, .preimages,
    .programs, .emitLabels]

/-! ### Oracle instruction counts -/

/-- Fixed queries of one lane: `127` chunks × (`2` fold + `3` inactive switches × `3 · count`). -/
def laneQueries (count : Nat) : Nat := 127 * (2 + 3 * (3 * count))

/-- Stage 2's forward queries: systems A and B, less the `819` designated blocks. -/
def fixedQueries : Nat := laneQueries 3 + laneQueries 2 + laneQueries 455 - 819 + laneQueries 364

/-- Stage 2's oracle queries: fixed, one hash, `508` EncPRF pads. -/
def stage2Queries : Nat := fixedQueries + 1 + 508

/-- Stage 2's programs. -/
def stage2Programs : Nat := 91 * 3 * 3

theorem fixedQueries_eq : fixedQueries = 942029 := rfl
theorem stage2Queries_eq : stage2Queries = 942538 := rfl
theorem stage2Programs_eq : stage2Programs = 819 := rfl

/-- The honest evaluator's `990,093` queries are the machine's `942,538` plus the `508`
bit-`true` pads it may ask and the `46,228` gadget hashes, which the opening does not need,
plus the `819` designated blocks, which it programs instead. -/
theorem evaluator_queries : stage2Queries + stage2Programs + 508 + 46228 = 990093 := rfl

/-! ### Instruction counts -/

/-- The serializer: `2 + 3 · width` per cell. -/
def serializeCount : Nat :=
  scaleCellCount * (2 + 3 * 254) + hotBlockCount * (2 + 3 * 128) +
    exceptionByteCount * (2 + 3 * 8) + (curveCellCount + rowCellCount) * (2 + 3 * 256)

/-- Stage 1: code slots and fuel. -/
def stage1Size : Nat :=
  fieldCellCount * 457231 + exceptionByteCount * 62 + hotBlockCount * 902 +
    keyBlockCount * 902 + serializeCount + 16
def stage1Cost : Nat :=
  fieldCellCount * 327180 + exceptionByteCount * 46 + hotBlockCount * 646 +
    keyBlockCount * 646 + serializeCount + 16

/-- The stage-2 prefix (parse, select labels, tag sum). -/
def prefixSize : Nat := 9692 + (labelCount * 11 + 4) + 5
def prefixCost : Nat := 5109 + (labelCount * 11 + 4) + 5

/-- The invalid arm: emit the labels. -/
def invalidSize : Nat := labelCount * (2 + 3 * 128)

/-- The replay. -/
def replaySize : Nat :=
  (1 + 824 * 2) + 127 * (141 + 176 * 3) + 127 * (141 + 176 * 2) + 40 + (4 + 508 * 8) +
    (83 + 4 * 28411 + 8 * 455 + 126 * (141 + 176 * 455)) + 127 * (141 + 176 * 364)
def replayCost : Nat :=
  (1 + 824 * 2) + 127 * (89 + 92 * 3) + 127 * (89 + 92 * 2) + 40 + (4 + 508 * 8) +
    (59 + 4 * 11205 + 8 * 455 + 126 * (89 + 92 * 455)) + 127 * (89 + 92 * 364)

/-- The opening. -/
def openingSize : Nat :=
  90 * 589865 + (3 + 90 * 397 + 439) + 91 * 457743 + 91 * 34 + 91 * 105 + 91 * (3 * 236623) +
    91 * (3 * (3 * 34)) + 16
def openingCost : Nat :=
  90 * 459290 + (3 + 90 * 397 + 415) + 91 * 327692 + 91 * 34 + 91 * 105 + 91 * (3 * 169548) +
    91 * (3 * (3 * 30)) + 16

/-- The valid arm. -/
def validSize : Nat := replaySize + openingSize + labelCount * (2 + 3 * 128)
def validCost : Nat := replayCost + openingCost + labelCount * (2 + 3 * 128)

/-! ### The top-level layout -/

def stage1Base : Nat := 2
def stage1Halt : Nat := stage1Base + stage1Size
def stage2Base : Nat := stage1Halt + 1
def branchAt : Nat := stage2Base + prefixSize
def invalidBase : Nat := branchAt + 1
def invalidHalt : Nat := invalidBase + invalidSize
def validBase : Nat := invalidHalt + 1
def validHalt : Nat := validBase + validSize
def rejectAt : Nat := validHalt + 1

/-- The code table has `size + 1` slots. -/
def size : Nat := rejectAt

/-- Stage 1: two pops, stage 1, halt. -/
def firstFuel : Nat := 2 + stage1Cost + 1

/-- Stage 2: two pops, the prefix, the branch, the valid arm (the costlier one), halt. -/
def secondFuel : Nat := 2 + prefixCost + 1 + validCost + 1

/-- **The simulator's charge**, `size + 1 + firstFuel + secondFuel`. -/
def totalCost : Nat := size + 1 + firstFuel + secondFuel

theorem stage1Size_eq : stage1Size = 48389712564 := rfl
theorem stage1Cost_eq : stage1Cost = 34649165432 := rfl
theorem validSize_eq : validSize = 178145892 := rfl
theorem validCost_eq : validCost = 127397302 := rfl
theorem size_eq : size = 48568069839 := rfl
theorem firstFuel_eq : firstFuel = 34649165435 := rfl
theorem secondFuel_eq : secondFuel = 127408012 := rfl

theorem totalCost_eq : totalCost = 83344643287 := rfl

/-- **The cost bound**: `size + 1 + firstFuel + secondFuel ≤ 2 ^ 60`. -/
theorem totalCost_le : totalCost ≤ 2 ^ 60 := by
  rw [totalCost_eq]; decide

/-- The charge is below `2 ^ 37` (about `2 ^ 36.28`): `23` bits of margin. -/
theorem totalCost_lt_two_pow_37 : totalCost < 2 ^ 37 := by
  rw [totalCost_eq]; decide

/-- The code table's address bound. -/
theorem size_lt : size < 2 ^ 256 := by rw [size_eq]; decide

end Design

end Kriterion.ArgoMAC.PlanB.SimMachine
