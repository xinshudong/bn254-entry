# Proof map (phase 3)

This map covers the Plan B entry against the challenge library `aaf2789`. The top-level
`README.md` explains the construction and the argument. This file says **which module proves
which obligation**. Every obligation and every privacy input is proved.

- `proved`: proved, with `#print axioms` giving `propext`, `Classical.choice` and `Quot.sound`
  only. `#print axioms Submission.solution` gives exactly these three.

`Proof.lean` imports `Proof.Privacy`, the privacy root, so a bare `lake build` compiles every
module named here.

## 1. `Kriterion.Solution`, field by field

| field | module | theorem / definition | status |
|---|---|---|---|
| `FixedIndex`, `EncIndex`, `fixedFinite`, `encFinite` | `Construction/PGS/Index.lean`, `Construction/ArgoMAC/EncPRF.lean` | `PlanB.FixedIndex` (`card_fixedIndex = 2,846,324`), `EncPRF.PermutationIndex` (`card_encIndex = 508`) | proved |
| `Randomness`, `randomnessFinite`, `randomness` | `Construction/Scheme.lean` | `Scheme.Coins`, `coinsFinite`, `Scheme.witness` | proved |
| `Public`, `EncodingKey`, `encoding` | `Construction/ArgoMAC/Public.lean`, `Construction/ArgoMAC/Input.lean`, `Construction/PGS/Encoding.lean` | `PlanB.Public`, `InputMacKey`, `PlanB.Wire.encoding` | proved |
| `ciphertextBytes`, `ciphertextSize` | `Proof/CiphertextSize.lean` | `PlanB.Wire.ciphertextSize` (3,363,376) | proved |
| `scheme` | `Construction/Scheme.lean` | `Scheme.scheme` | proved |
| `garbleQueries`, `garbleProgram`, `garbleProgramCorrect` | `Construction/OraclePrograms.lean` | `Programs.garbleProgram`, `garbleBudget_eq` (1,305,053), `garbleProgram_correct` | proved |
| `evaluateQueries`, `evaluateProgram`, `evaluateProgramCorrect` | `Construction/OraclePrograms.lean` | `Programs.evaluateProgram`, `evaluateBudget_eq` (990,093), `evaluateProgram_correct` | proved |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` | `Lamport.selectedLabels_eq` (in `Submission.lamportCompatible`) | proved |
| `functionCorrect` | `Submission.lean` | `rfl` | proved |
| `perfectCorrectness` | `Proof/Correctness/JacobianMixed.lean`, `Proof/LamportCompatibility/Labels.lean` | `JacobianMixed.evaluateCorrect`, `Lamport.restore_selected` | proved |
| `adaptivePrivacy` | `Proof/Privacy/Phase3/Glue/Final.lean`, `Proof/Privacy/Phase3/PublicFirst/LawsOnEFinal.lean`, `Proof/Simulator/OpeningMachine.lean` | `planB_oracleAdaptivePrivacy_of planB_publicFirst (MachineBound.of_law machineLaw_planB)` | proved |

`Proof/Correctness/` holds the supporting correctness lemmas:
- `CanonicalBits`: chunk recomposition;
- `PGS/OneHot`, `PGS/ScaleHot` and `PGS/AffineFp`: the switch systems deliver `a_e·x + O[e]`;
- `PGS/Row`, `PGS/EncSlots` and `PGS/ExceptionalPoints`;
- `Base7Termination`.

## 2. The privacy assembly and its inputs

`planB_oracleAdaptivePrivacy simulator hybrids H_swap H_open H_joint H_machine H_abort` has
**literally** the type of the `adaptivePrivacy` field.

- It is proved in `Proof/Privacy/Phase3/Glue/Assembly.lean`. It uses:
  - `planB_lazy_real` (`Glue/LazyReal.lean`): the scored real game equals `G0`, exactly;
  - `adaptivePrivacyTransfer` through the abstract ideal game `I`;
  - the hop bounds;
  - `chainError_budget` (`Glue/Budget.lean`);
  - the free unit `size + 1` of `T`.
- `Glue/LazyIdeal.lean` proves that the library's ideal game with any closed machine **is** the
  abstract game of the machine's two kernels (`idealGame_eq_machineAbstract`).
- `Glue/AbstractSimulator.lean` defines the abstract simulator `planBAbstractSimulator`, the
  samplers `idealSamplers` and the game `I`.

### The inputs

| input | Glue statement | error | owner module | status |
|---|---|---|---|---|
| `hybrids` = `planBHybrids` | all five `HybridGame`s | — | P1, `Proof/Privacy/Phase3/Hybrids.lean` | proved |
| `simulator` = `planBSimulator` | a closed `BoundedMachine.Simulator` | — | P2, `Proof/Simulator/Machine.lean` (`planBSimulator`, `planBSimulator_within`); its code is `Construction/Simulator/` (`Top.machine`) | proved |
| `MaskSwapBound.real` (G0 → G0U) | `HopBound realHybrid maskSwapped` | `N·δ₃ = 2^-111.86` | P1, `GameSwap.lean` (`maskSwapBound_real`), from `MaskSwap.lean` (`maskSwap_bind_etvDist_le`) | proved (`planB_maskSwapBound`) |
| `MaskSwapBound.idealPerMask` (I^U → I) | per derived mask: `Σ_site (δ₃ + count·refillQueryCharge q₁)`, with `card ≤ N` and `Σ count ≤ q₁` | `N·δ₃ + q₁·(1/2^128 + 1/(2^128 − q₁))` | P4, `Proof/Privacy/Phase3/Lazy/` (`maskSwapBound_of`) | proved |
| `MaskSwapBound.ideal` | the sum of `idealPerMask` | same | `Glue/Assembly.lean` (theorem) | proved, given `idealPerMask` |
| `OpeningBound.kernel` (HW → H) | `HopBound publicFirst opened` | `364/(r−1)` | P1, `Proof/Privacy/Phase3/Opening.lean` (`digitPoints_good_law`, `rowsLaw_eq`, `bn254_doubling_real_le`) | proved (`planB_openingBound`) |
| `JointExactnessBound.hidden` (G0U → G1U) | `GameUntilBad`: flagged laws that agree when the flag is down, with the bad mass at most the error | `3q/2^128 + q/(p−1)` | P1h, `Proof/Privacy/Phase3/Hidden/Final.lean` (`planB_hidden`) | proved |
| `JointExactnessBound.publicFirst` (G1U → HW) | `GameCoreUntilBad`, which by `coreUntilBad_iff` (`UntilBadIff.lean`) is exactly the advantage bound; the proof bounds the advantage through the exact core `realCore = simCore` (F4) and a triangle through `G1U°`, charging a stage-1 hit, a doubling input and the off-curve system-A sampler bias | `4q₁/2^128 + 182/(r−1) + N·δ₃` (`stageOneHitError + exceptionalError + maskSwapError`) | P1, `Proof/Privacy/Phase3/JointExactness.lean` (`jointLaw`, `jointLaw_context`: the core); `Proof/Privacy/Phase3/PublicFirst/` (`planB_publicFirst` in `LawsOnEFinal.lean`, from `designedLaws` and `designedBounds` via `planB_publicFirst_of_laws_bounds` in `LawsGuess.lean`) | proved (`Security.Phase3.PublicFirst.planB_publicFirst`) |
| `AbortBound.perQuery` (H → I^U) | per abort site, over an existential finite site type: `Σ count·abortQueryCharge q₁`, with `Σ count ≤ q₁`. P4's instance is `Lazy.AbortSite` (the chunk-0 scale indices and level-1 fold indices of `pointX` and `curveX`). The bridges are `AbortBound.of_perQuery'` and `AbortBound.of_keyAveraged` (`Glue/AbortBridge.lean`). | `2q₁/(2^128 − q₁)` | P4, `Proof/Privacy/Phase3/Lazy/AbortPerQuery.lean` (`abortBound_perQuery'_of`); P4b, `Lazy.KeyAveragedFailBound` | proved (`AbortBound.of_keyAveraged rfl rfl Lazy.keyAveragedFailBound`) |
| `OutputFreshness` | `Glue/Budget.lean`: a limb independent of the label, with label point masses `≤ ε`, lands in an `n`-block range with mass `≤ n·ε` | the output part of the abort charge | P4, `Proof/Privacy/Phase3/Lazy/OutputFreshness.lean` (`outputFreshness`) | proved |
| `MachineBound.law` (I → M) | `MachineLaw simulator (1/2^128)` | `2^-128` | P2, `Proof/Simulator/OpeningMachine.lean` (`machineLaw_planB`). `machineLaw_of` (`Law.lean`) splits it into `Stage1Law` (`Stage1Law.lean`, `stage1Law`), `Stage2Law` (`OpeningMachine.stage2Law`, from `openingLaw` in `OpeningLaw.lean` via `Stage2Valid.lean`) and `SamplerCutoff` (`CutoffMass.samplerCutoff`) | proved |
| `MachineBound.cost` | `size + 1 + firstFuel + secondFuel ≤ 2^60` | — | `Glue/Assembly.lean` (`MachineBound.of_law`, from `Simulator.within`) | proved |
The Glue's own supporting results are all proved:
- `splitCoins` and `uniform_split` (`RandomnessSplit`);
- the ported lazy-oracle law (`OracleLaw`: `public_run`, `public_initial`, `lazy_real_uniform`,
  `public_program_fixed`);
- `UntilBad.advantage_le` and `CoreUntilBad.untilBad`;
- `candidateIndex_injective`;
- `digitPoints_head`;
- `chainError_budget`.

## 3. Query-program accounting

Both programs are `FreeQuery` programs, turned into the library's `QueryProgram` at the index
proved by `garbleBudget_eq` and `evaluateBudget_eq`. That index bounds every path.

Per lane, with `count` elements, 127 chunks of 2 bits and four switches:

| | garbling | evaluation |
|---|---|---|
| per chunk | 4 fold queries + `4 · 3 · count` mask blocks | 2 fold queries + `3 · 3 · count` mask blocks (the active switch is recovered) |
| `curveX` (3) | 5,080 | 3,683 |
| `curveY` (2) | 3,556 | 2,540 |
| `pointX` (455) | 693,928 | 520,319 |
| `pointY` (364) | 555,244 | 416,306 |
| bridge hash | 1 | 1 |
| EncPRF pads | 1,016 | 1,016 (508 whitening pads, plus the bit pads) |
| gadget | `91 · 508` = 46,228 | `91 · 508` = 46,228 |
| **total** | **1,305,053** (gate 1,759,967) | **990,093** (gate 1,055,879) |

## 4. Simulator-machine accounting

These counts are from P2's `Construction/Simulator/Design.lean`. There, `totalCost_le` proves the
bound by `decide` on the closed formulas.

| | count |
|---|---:|
| code table `size + 1` | 48,568,069,840 |
| `firstFuel` (stage 1: 105,652 field cells by bounded rejection, the gadget bytes, the fold joins, the key, serialisation) | 34,649,165,435 |
| `secondFuel` (stage 2, valid arm: parse, replay, opening, labels) | 127,408,012 |
| **total** `size + 1 + firstFuel + secondFuel` | **83,344,643,287 ≈ 2^36.28 ≤ 2^60** |

The stage-2 oracle traffic is 942,538 lazy queries and 819 programs. These reconcile with the
honest evaluator (`evaluator_queries`):

`942,538 + 819 + 508 (bit pads) + 46,228 (gadget) = 990,093`

## 5. Other modules

`Proof/Privacy/PGS/` keeps only the two lemma modules the phase-3 proof imports,
`DaviesMeyerUniform.lean` and `FibreUniformity.lean`. The earlier hybrid chain, written against
the previous library interface, has been removed. Every module under `Construction/` and `Proof/`
is in the import closure of `Submission`.
