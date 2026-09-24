# Plan B: the chunked one-hot projectivisation of ArgoMAC

This is an entry for the Kriterion `scalar-multiplication` challenge: garbled BN254 scalar
multiplication `f_k(u) = k·u`, checked in Lean against the challenge library
`Kriterion-cc/kriterion-challenge` at commit `aaf2789` (Lean `v4.33.1`).

| metric | value | rule |
|---|---|---|
| `ciphertextBytes` | **3,363,376** `= 48,930 + 26,098·127` | ranked, lower is better |
| `garbleQueries` | **1,305,053** `≤ 1,759,967` | acceptance gate |
| `evaluateQueries` | **990,093** `≤ 1,055,879` | acceptance gate |

Every field of `Kriterion.Solution` is proved, and there is no `sorry` in the tree.
`adaptivePrivacy` is the proved assembly `planB_oracleAdaptivePrivacy_of`, applied to the proved
public-first hop `planB_publicFirst` (`G1U → HW`) and the proved machine law of the closed
simulator machine. `#print axioms Submission.solution` reports exactly `propext`,
`Classical.choice` and `Quot.sound`. §7 gives the details.

---

## 1. The construction

The entry keeps everything of ArgoMAC above the affine encodings:

- the 91 base-`(2 − ω)` digit MACs;
- the three Jacobian rows per digit, with 11 published constants each;
- the curve-membership check;
- the EncPRF whitening;
- the doubling-exception gadget.

It replaces only how the **824 affine encodings** (`a_e·x + b_e` or `a_e·y + b_e`) reach the
evaluator. The original baseline sends one 254-row bit-adaptor table per encoding; Plan B sends
one field join per chunk.

### 1.1 Interface

| `Solution` field | value |
|---|---|
| `FixedIndex` | `PlanB.FixedIndex`. It has three families: `hot` (fold steps), `scale` (switch masks) and `gadget`. `#FixedIndex = 2,846,324` (`card_fixedIndex`). |
| `EncIndex` | `EncPRF.PermutationIndex`, `#EncIndex = 508` |
| `Randomness` | `Scheme.Coins`: the private coins only. The three public oracle families are supplied by the library, not by the tape. |
| `Public` | `PlanB.Public`: eight fixed-width fields, no tags |
| `EncodingKey` | `InputMacKey`: exactly the 508 Lamport label pairs `(Z_j, Z_j ⊕ Δ_coord)` |
| `encoding` | `PlanB.Wire.encoding` |
| `scheme` | `Scheme.scheme`: the Plan B garbler and evaluator on `coins.withOracle oracle` |

### 1.2 Elements, lanes, chunks

Each digit needs 9 affine encodings: 5 of `x` and 4 of `y`. Together with the 5 encodings of the
curve check, that gives `91·9 + 5 = 824` elements. They are split over **four lanes**:

- `curveX` (3 elements) and `curveY` (2 elements) form **system A**;
- `pointX` (455 elements) and `pointY` (364 elements) form **system B**.

Each 254-bit coordinate is cut into **`C = 127` chunks of `b = 2` bits** (`chunkBits = 2`,
`chunkCount = 127`, `lastChunkBits = 2`). Chunk `c` holds `α_c < 4`, and
`x = Σ_c 4^c·α_c` (`Proof/Correctness/CanonicalBits.lean`).

### 1.3 `bin-to-hot`: bit labels to one-hot labels

Per chunk, the two bit labels are folded into four one-hot labels by free XOR. Each fold step's
material is the sum of **two** fixed-key permutation images, `π_{i0}(Z) ⊕ π_{i1}(Z)`, so that no
child is a raw permutation image. Each chunk publishes one 128-bit fold join per lane.

The evaluator hashes every entry except the active one, and recovers the active entry from the
join.

### 1.4 `scale-hot`: one join per chunk over `F_p^824`

Every one-hot entry `j` of chunk `c` hashes its label into a mask vector `Y_{c,j} ∈ F_p^824`, one
field element per encoding. The garbler publishes the join

```
J_c = Σ_j Y_{c,j} + s_c,        s_c = (a_e · 4^c)_e
```

The evaluator computes `Y_{c,j}` for the three inactive `j`. It recovers the active entry as
`J_c − Σ_{j≠α_c} Y_{c,j}`, then folds against the chunk index:

```
Σ_c Σ_j ι(j)·L_{c,j}[e] = O[e] + a_e·x,        ι(j) = (j : F_p)
```

The garbler **defines** the offset `b_e := O[e]`, so offsets cost no bytes. It derives the slopes
`a_e` from them and publishes the joins last.

### 1.5 Rule S: the three-block sampler

Every mask element is `sampleFp(o₀, o₁, o₂) = (o₀ + 2^128·o₁ + 2^256·o₂ : ℕ) mod p`, where the
`o_b` are three Davies–Meyer blocks. There is no rejection, because correctness must hold on
every tape.

- The bias per element is `δ₃ = (2^384 mod p)/2^384 = 2^-130.54`.
- Over all `N = 824·508 = 418,592` garbler masks the bias is `N·δ₃ = 2^-111.86`.

### 1.6 Two switch systems

- **System A** is keyed on the raw Lamport labels. It delivers the curve check, which publishes
  `t + mask·(x³ + 3 − y²)`. On the curve this equals the bridge key `t`; off the curve it is
  uniform.
- **System B** is keyed on labels whitened by EncPRF pads under the keys `H(t)`. It delivers the
  819 point-row encodings. An evaluator that cannot produce `t` holds only garbage labels for
  system B.

### 1.7 Rows and gadget

Each digit's three Jacobian rows are affine in the delivered values, with the published `γ`
fixed. The 91 decoded points are combined by `pointHorner (2 − ω)`. The doubling case
(`T_d = K_d`, row `(0,0,0)`) is released by the exception gadget: 6 bytes per digit, unlocked by a
digest of the digit's labels.

## 2. The bytes

| field | contents | bytes |
|---|---|---|
| `curve` | 3 constants | 96 |
| `rows` | 91 × 11 constants × 32 B | 32,032 |
| `exception` | 91 × 6 B | 546 |
| `curveXHot`, `curveYHot`, `pointXHot`, `pointYHot` | 4 lanes × 127 fold joins × 16 B | 8,128 |
| `scale` | 127 chunk words × 824 elements × 254 bits (26,162 B each) | 3,322,574 |
| **total** | `48,930 + 26,098·C` at `C = 127` | **3,363,376** |

Every field has a fixed width, so every public value encodes to the same length
(`PlanB.Wire.ciphertextSize`, `Proof/CiphertextSize.lean`).

## 3. Query accounting

The two programs are written in `Construction/OraclePrograms.lean` as free query programs. Each
distinct question is asked once, and its answer is kept in a table. Each program is given the
library's indexed `QueryProgram` type at its exact budget (`garbleBudget_eq`,
`evaluateBudget_eq`). The budgets bound every path.

| family | garbling | evaluation |
|---|---|---|
| `scale-hot` masks, `3·824` blocks per switch | `3·824·508` = 1,255,776 | `3·824·381` = 941,832 (inactive switches only) |
| `bin-to-hot` fold, 2 permutations per entry at levels `≥ 1` | 2,032 | 1,016 (active entry recovered) |
| exception gadget, 508 labels per digit | `91·508` = 46,228 (zero digits skip) | `91·508` = 46,228 |
| EncPRF pads | 1,016 | ≤ 1,016 (508 whitening pads, plus one per set bit) |
| bridge hash `H(t)` | 1 | 1 |
| **total** | **1,305,053** | **990,093** |

- The garbler is 25.8% under its gate and the evaluator 6.2% under its gate.
- `b = 2` is the widest chunk that fits the evaluation gate. At `b = 3` evaluation would need
  1,510,893 queries.
- An off-curve input is refused before any query.

## 4. Correctness

Correctness is exact for every tape, oracle and input.

- Every gate is `F_p`-linear, so the one-hot fold is an identity, not an estimate.
- An off-curve input evaluates to `some none`.
- The two Jacobian degeneracies go through the gadget.

The proofs are in `Proof/Correctness/`. They reach `perfectCorrectness` through the Lamport label
adapter (`Lamport.restore_selected`).

## 5. Privacy: the argument

### 5.1 The obligation

`GarbledCircuit.OracleAdaptivePrivacy` asks for **one closed `BoundedMachine.Simulator`** with
`size + 1 + firstFuel + secondFuel ≤ 2^60`. For every adversary *machine* `M`, every parameter
and every scalar, it must satisfy

```
Adv(R, M) · 2^100 ≤ T + 1,        T = M.steps = size + 1 + firstFuel + secondFuel
```

- `R` is `lazyRealGame`: the private coins, then the garbler and both adversary stages, all
  against **one fixed, shared lazy oracle**.
- In the machine ideal game, the adversary's queries are answered by that same lazy oracle. The
  simulator can only `query`, `lookup` and `program` it.
- A permutation program needs a fresh input *and* a fresh output. A failed program aborts the
  experiment to `false`.

### 5.2 The simulator

**Stage 1** receives only `n` and the byte count, and makes **no oracle call**. It publishes a
table in which every field is drawn uniformly in its source form:

- the curve constants;
- the row constants;
- the gadget bytes;
- the fold joins;
- the 127 × 824 scale joins, as canonical field elements packed exactly as the construction
  packs them.

It also keeps a uniform Lamport key. This is the real table's law once every garbler scale mask
is uniform. Nothing is programmed in stage 1.

**Stage 2** receives `u` and `f_k(u)`.

*Off the curve* (`f_k(u) = none`), it returns the selected labels and makes no oracle call.

*On the curve* (`f_k(u) = Q`), it proceeds in five steps.

1. **Replay.** It replays the honest evaluator's path to the rows on the lazy oracle:
   - system A;
   - `H(t)`;
   - the 508 whitening pads;
   - system B.

   It **skips** the 819 designated queries. These sit at the inactive switch `j* = α₀ ⊕ 1` of
   chunk 0 in lane `pointX`, one per digit × row collector (`rowX_x9`, `rowY_x9`, `rowZ_x9`) ×
   block.
2. **Opening.** It draws the 90 tail digit points exactly as the garbler draws its mask points,
   i.e. the offsets of a uniform coin. The head is the clamp `D₀ = Q − β·H(tail)`, which uses
   only the group law, so `pointHorner β (D₀ :: tail) = Q`. It then draws 91 lift randomisers,
   giving the target rows `W_d = lift(D_d, λ_d)`.
3. **Collector solve.** Each row has a private unit-coefficient collector, so the designated
   mask it needs is `y* = κ·(W − partial)`, where `κ = ι(j*) − ι(α₀) = ±1`.
4. **Preimages.** It draws a uniform `sampleFp` preimage `(o₀, o₁, o₂)` of each `y*`.
5. **Programs.** It programs the **819 fixed-key points** `E* ↦ o_b ⊕ E*`, so that the
   evaluator's Davies–Meyer output there is `o_b` and its rows evaluate to `W`. It then returns
   the labels.

Everything else the adversary later evaluates, including every other switch and fold, the hash,
EncPRF and the gadget, is honest lazy sampling. There is no hash programming and no EncPRF
programming.

### 5.3 The hybrid chain

`q₁` and `q₂` are the adversary's stage-1 and stage-2 query budgets, and `q = q₁ + q₂`.

| hop | what changes | cost |
|---|---|---|
| `R = G0` | the lazy real game is the tape-sampled game | **0** (exact) |
| `G0 → G0U` | every garbler scale mask is swapped to uniform `F_p`, before the game, non-adaptively | `N·δ₃ = 2^-111.86` |
| `G0U → G1U` | the hidden entries (active switches, active fold parents, gadget positions; all of system B off the curve) are deleted at the input choice | `L1 = 3q/2^128 + q/(p−1)` |
| `G1U → HW` | public-first reparametrisation: the joint law of the published cells and the visible masks is exactly uniform for every selection rule (F4), off a stage-1 hit **and** off a doubling input (where `G1U`'s real gadget unlocks the true digit and `HW`'s published gadget byte is uniform), plus one sampler-bias swap: off the curve `G1U` installs the system-A masks with `G0U`'s uniform values, while in `HW` the adversary samples them by Rule S | `L2 + ε_exc + N·δ₃ = 4q₁/2^128 + 182/(r−1) + 2^-111.86` |
| `HW → H` | the real digit rows are replaced by the tail, head-clamp and lift sampler | `ε_pt = 364/(r−1) ≈ 2^-245.1` |
| `H → I^U` | the 819 lazy programs may abort (a used input or output); charged per stage-1 query at a candidate designated index | `ε_abort = 2q₁/(2^128 − q₁)` |
| `I^U → I` | the non-designated masks go back to lazily queried values | `N·δ₃ + q₁·(1/2^128 + 1/(2^128 − q₁))` |
| `I → M` | the closed machine realises `I` with bounded samplers | `ε_cut ≤ 2^-128` |

### 5.4 The budget

- **Constant part:** `3·N·δ₃ + ε_exc + ε_pt + ε_cut = 3·N·δ₃ + 182/(r−1) + 364/(r−1) + 2^-128 ≈ 2^-110.28`. There are three copies of `N·δ₃`: `G0 → G0U`, the off-curve system-A masks in `G1U → HW`, and `I^U → I`. The doubling event is charged twice, in `G1U → HW` (the gadget) and in `HW → H` (the `(0,0,0)` row against a lift): two hops, two different discrepancies on the same event.
- **Linear part:** `3 + 4 + 2 + 2 = 11` units of `q/2^128`, about `2^-124.5` per query, plus the
  negligible `q/(p−1)`.

`chainError_budget` proves `chainError q₁ q₂ · 2^100 ≤ q₁ + q₂ + 1` for `q < 2^100`. Every term is
below a thousandth of its unit. The assembly closes with

```
Adv(R,M)·2^100 ≤ chainError·2^100 ≤ q₁ + q₂ + 1 ≤ (size + 1) + q₁ + q₂ + 1 = T + 1
```

For `q ≥ 2^100` the bound holds because `Adv ≤ 1`.

### 5.5 The machine

The simulator machine `planBSimulator` costs `size + 1 + firstFuel + secondFuel = 83,344,643,287`
(about `2^36.3`) against the allowance `2^60` (`Design.totalCost_le`). Its machine law
`machineLaw_planB : MachineLaw planBSimulator 2^-128` is proved
(`Proof/Simulator/OpeningMachine.lean`).

- Stage 1 is dominated by bounded-rejection sampling of 105,652 field cells and by serialising
  the table.
- Stage 2 is dominated by the replay (about `9.4·10^5` lazy queries) and the 819 programs.
- The query and program instructions address `FixedIndex` through `Fintype.equivFin`. The machine
  embeds these ordinals as constants.
- `Construction/Simulator/` builds the machine for any two ordinal functions and is computable.
  The instance at `Fintype.equivFin` is not computable, so `planBSimulator` itself is a proof-side
  definition (`Proof/Simulator/Machine.lean`).

## 6. Proof map

| `Solution` field | where | status |
|---|---|---|
| `garbleProgram`, `evaluateProgram`, `garbleQueries`, `evaluateQueries`, `garbleProgramCorrect`, `evaluateProgramCorrect` | `Construction/OraclePrograms.lean` (`garbleProgram_correct`, `evaluateProgram_correct`, `garbleBudget_eq`, `evaluateBudget_eq`) | proved |
| `ciphertextSize` | `Proof/CiphertextSize.lean` (`PlanB.Wire.ciphertextSize`) | proved |
| `lamportCompatible` | `Proof/LamportCompatibility/Labels.lean` (`Lamport.selectedLabels_eq`) | proved |
| `functionCorrect` | `rfl` | proved |
| `perfectCorrectness` | `Proof/Correctness/JacobianMixed.lean` (`JacobianMixed.evaluateCorrect`), `Lamport.restore_selected` | proved |
| `adaptivePrivacy` | `Proof/Privacy/Phase3/Glue/Final.lean` (`planB_oracleAdaptivePrivacy_of`), `Proof/Privacy/Phase3/PublicFirst/LawsOnEFinal.lean` (`planB_publicFirst`), `Proof/Simulator/OpeningMachine.lean` (`machineLaw_planB`) | proved |

**The privacy assembly**, `Proof/Privacy/Phase3/Glue/`. All of it is proved. Namespace
`Kriterion.ArgoMAC.Phase3.Glue`.

| module | content |
|---|---|
| `RandomnessSplit` | `splitCoins : Garbling.Randomness ≃ Coins × Oracle`, and the uniform tape as a product |
| `OracleLaw` | the lazy-oracle / eager-completion law (`public_run`, `public_initial`, `lazy_real_uniform`, `public_program_fixed`), ported from the ArgoMAC baseline |
| `LazyReal` | `planB_lazy_real`: `lazyRealGame … = G0`, exactly. It consumes `garbleProgram_correct`. |
| `LazyIdeal` | `idealGame_eq_machineAbstract`: the library's ideal game **is** the abstract game of the machine's two kernels; `abstractIdealGame_eq_of_simulation` |
| `AbstractSimulator` | `planBAbstractSimulator` (§5.2), the ideal game `I`, `CandidateSite` / `candidateIndex_injective`, and `MachineLaw` |
| `Budget` | the error terms and `chainError_budget` |
| `Assembly` | the hypothesis structures, the identical-until-bad wrapping (`UntilBad`, `CoreUntilBad`; `untilBad_iff` and `coreUntilBad_iff` in `Phase3/UntilBadIff.lean` show each is exactly the advantage bound), and `planB_oracleAdaptivePrivacy`, whose type is literally that of the `adaptivePrivacy` field |
| `AbortBridge` | `AbortBound.of_perQuery'` and `AbortBound.of_keyAveraged`, the bridges from the lazy-oracle abort bounds |
| `Final` | `planB_oracleAdaptivePrivacy_of`: the assembly at `planBHybrids` with every proved input plugged in; its two arguments are `publicFirst` and the machine bound |

The hops themselves live beside the assembly: `Proof/Privacy/Phase3/` (the hybrids
`planBHybrids`, the mask swap, the opening bound, the exactness core), `Phase3/Hidden/` (the
hidden hop `planB_hidden`), `Phase3/PublicFirst/` (the public-first hop `planB_publicFirst`,
from `designedLaws` and `designedBounds` via `planB_publicFirst_of_laws_bounds`) and
`Phase3/Lazy/` (the lazy refill and the abort bound). The machine
law is in `Proof/Simulator/`: `machineLaw_of` (`Law.lean`) splits it into `Stage1Law`
(`Stage1Law.lean`), `Stage2Law` (`OpeningMachine.stage2Law`, from `openingLaw` in
`OpeningLaw.lean`) and `SamplerCutoff` (`CutoffMass.samplerCutoff`). `Proof/Privacy.lean` is the
single root that imports all of it.

## 7. Status

**Every field is proved.** `Submission.lean` sets

```lean
adaptivePrivacy := Phase3.Glue.planB_oracleAdaptivePrivacy_of
  Security.Phase3.PublicFirst.planB_publicFirst
  (Phase3.Glue.MachineBound.of_law PlanB.SimMachine.machineLaw_planB)
```

- `planB_oracleAdaptivePrivacy_of` is in `Proof/Privacy/Phase3/Glue/Final.lean`.
- `planB_publicFirst` is in `Proof/Privacy/Phase3/PublicFirst/LawsOnEFinal.lean`.
- `machineLaw_planB` is in `Proof/Simulator/OpeningMachine.lean`.
- There is no `sorry` in the tree. `#print axioms Submission.solution` reports exactly
  `propext`, `Classical.choice` and `Quot.sound`.

| input | hop(s) | status |
|---|---|---|
| `hybrids = planBHybrids` | the games `G0U`, `G1U`, `HW`, `H`, `I^U` (`Proof/Privacy/Phase3/Hybrids.lean`) | **proved** |
| `H_swap = planB_maskSwapBound` | `G0 → G0U` (`N·δ₃`); `I^U → I` (lazy refill, per derived mask and per stage-1 query) | **proved** |
| `H_open = planB_openingBound` | `HW → H`, `364/(r−1)` | **proved** |
| `H_joint.hidden = planB_hidden` | `G0U → G1U`, identical until a hidden entry is touched, `L1` | **proved** |
| `H_joint.publicFirst = planB_publicFirst` | `G1U → HW`, identical until a stage-1 hit or a doubling input, plus one `N·δ₃`: `4q₁/2^128 + 182/(r−1) + N·δ₃`; from the F4 `jointLaw` core, `designedLaws` and `designedBounds` | **proved** |
| `H_abort = AbortBound.of_keyAveraged rfl rfl Lazy.keyAveragedFailBound` | `H → I^U`, per abort site, `2/(2^128 − q₁)` per stage-1 entry | **proved** |
| `H_machine = MachineBound.of_law machineLaw_planB` | `I → M`, `MachineLaw planBSimulator 2^-128`; the cost field is `planBSimulator.within` (`83,344,643,287 ≤ 2^60`) | **proved** |

## 8. Build and verify

```sh
lake exe cache get      # Mathlib build cache
lake build              # Construction, Proof (with the whole privacy tree), Submission
```

`#print axioms Submission.solution` reports exactly `propext`, `Classical.choice` and
`Quot.sound`. So do `planB_oracleAdaptivePrivacy_of`, `planB_publicFirst` and `machineLaw_planB`.
Every declaration under `Construction/` and `Proof/` uses no other axiom.

## 9. Provenance and AI assistance

**This entry is AI-assisted.** The construction, the proofs, the design notes, this README and
`Intuition.md` were written with AI coding agents under human direction and review. That changes
nothing that is checked: the verifier builds the tree against the pinned public library, rejects
`sorry` and every axiom beyond the three above, and evaluates the three metrics. Every
obligation is proved (§7).

## 10. Layout

| path | content |
|---|---|
| `Construction/` | the executable construction: `ArgoMAC/` (rows, offsets, EncPRF, gadget, pipeline), `PGS/` (indices, fold, scale-hot, sampler, packing, encoding), `Garbling`, `Scheme`, `QueryMonad`, `OraclePrograms`; `Simulator/`, the simulator machine's code (computable, generic in the index ordinals) |
| `Proof/Correctness/`, `Proof/LamportCompatibility/`, `Proof/CiphertextSize.lean` | the proved fields |
| `Proof/Privacy.lean`, `Proof/Privacy/Phase3/` | the privacy proof: the hybrids and hops, `Hidden/`, `Lazy/` and the assembly `Glue/` (§6) |
| `Proof/Privacy/PGS/` | two lemma modules the phase-3 proof reuses (`DaviesMeyerUniform`, `FibreUniformity`) |
| `Proof/Simulator/` | the simulator machine `planBSimulator`, its semantics and its machine law `machineLaw_planB` |
| `Submission.lean` | the `Kriterion.Solution` instance |
| `Intuition.md` | the public design rationale the challenge requires |

Module headers cite internal design notes by file name: the plan `2026-09-17-planB.md`, the
phase-3 note `B-output-aware-simulator.md` and its review `B-review.md`, `phase2-dfb-design-v2.md`,
`planB-hop1-review.md`, and the Python reference implementation `pgs.py`. They are not part of
this repository; §1–§5 and `Intuition.md` summarise them.
