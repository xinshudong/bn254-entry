# Intuition: chunked one-hot projectivization of ArgoMAC

This entry garbles BN254 scalar multiplication at **3,363,376 bytes** of public ciphertext.
Garbling makes at most **1,305,053** oracle queries (gate 1,759,967) and evaluation at most
**990,093** (gate 1,055,879). Both figures are the exact bounds carried in the types of
`garbleProgram` and `evaluateProgram`.

This note explains the design, the byte count, the query count and the privacy argument.
Section 7 states what is proved: every obligation.

---

## 1. Starting point: where the ArgoMAC baseline spends its bytes

The baseline follows the BaBe/ArgoMAC paper. The evaluator holds one Lamport label for each of
the 508 input bits (254 bits of `x`, then 254 bits of `y`). The garbled circuit has to turn those
labels into 91 elliptic-curve MACs, one per base-7 digit of the secret scalar. The output point
is then rebuilt from the MACs by Horner's rule.

Each digit's MAC comes from three Jacobian rows (`X`, `Y`, `Z`). Each row is a low-degree
polynomial in `(x, y)` with published coefficients `γ`. The rows read nine *affine encodings* of
the input coordinates, values of the form `a_e · x + b_e` or `a_e · y + b_e`. With 91 digits,
plus five values for the curve-membership check, there are **824 affine encodings**: 458 of `x`
and 366 of `y`.

In the baseline, each encoding comes from its own bit-adaptor table: 254 rows, one per input
bit, each a masked field element. These per-encoding tables are almost all of the baseline's
ciphertext. The published row constants (`91 · 11` field elements), the curve check and the
doubling-exception gadget together take under 33 KB.

**Plan B keeps everything above the affine encodings unchanged.** That covers the 11 published
`γ` per digit, the Jacobian rows, the curve check, the EncPRF gate and the exception gadget.
Plan B only replaces how the 824 encodings reach the evaluator.

---

## 2. The construction: one-hot switch systems over a plain group

### 2.1 Cutting a coordinate into chunks

Each 254-bit coordinate is cut into `C` chunks of `b` bits. This entry uses `b = 2` and
`C = 127`. Chunk `c` of `x` is a number `α_c < 2^b`, and

```
x = Σ_c 2^(b·c) · α_c        (in F_p)
```

This identity holds because the Lamport bits are the canonical little-endian digits of
`x.val < p < 2^254`. `Proof/Correctness/CanonicalBits.lean` proves it. Nothing is reduced
modulo anything but `p`.

### 2.2 `bin-to-hot`: bit labels to a one-hot label vector

For each chunk, the `b` bit labels are folded into `2^b` *one-hot* labels. Entry `j` carries
the "active" label when `j = α_c` and a "zero" label otherwise. The fold doubles the vector once
per bit, and each level uses free XOR:

```
M_r        := π_{i0}(Z_r) ⊕ π_{i1}(Z_r)       two fixed-key permutations per entry
right child := M_r ,  left child := Z_r ⊕ M_r
join_j      := (⊕_r M_r) ⊕ (zero label of bit j)   one published 128-bit block per level
```

Level 0 is free, so a chunk of width `b` publishes `b − 1` blocks. The evaluator mirrors the
fold. It hashes every entry except the active one and recovers the active entry's material from
the published join.

The two-permutation step (`π_{i0} ⊕ π_{i1}` rather than one Davies–Meyer call) keeps the left
child from being a raw permutation image. A single permutation would let one inverse query
recover the free-XOR offset Δ.

### 2.3 `scale-hot`: one published join per chunk, over `F_p^824`

The key cost fact: a switch system over a **plain** group publishes a single join, whatever the
one-hot length. For chunk `c`, every one-hot entry `j` hashes its label into a mask vector
`Y_{c,j} ∈ F_p^824`, with one field element per affine encoding. The garbler publishes

```
J_c := Σ_j Y_{c,j} + s_c ,      s_c := (a_e · 2^(b·c))_e        (824 field elements)
```

The evaluator holds the labels of every inactive entry, so it can compute `Y_{c,j}` for every
`j ≠ α_c`. It recovers the active entry as `J_c − Σ_{j ≠ α_c} Y_{c,j}` and folds the one-hot
against the chunk index for free:

```
Σ_j ι(j) · L_{c,j} = Σ_j ι(j) · Y_{c,j} + α_c · s_c ,     ι(j) = (j : F_p)
```

Summing over the chunks gives, for every encoding `e`,

```
Σ_c Σ_j ι(j) · L_{c,j}[e] = O[e] + a_e · x ,     O[e] := Σ_c Σ_j ι(j) · Y_{c,j}[e]
```

`O[e]` is known to the garbler at garbling time, and in the underlying scheme the offsets `b_e`
are free garbler randomness. So the garbler *defines* `b_e := O[e]`: the offset costs no bytes.
It then derives the slopes `a_e` from these offsets and publishes the joins last.

Each mask element is a Rule-S sample: three Davies–Meyer blocks read as one 384-bit integer and
reduced mod `p`. Rejection sampling is never used, because correctness must hold on every tape.

### 2.4 Two switch systems per coordinate: the curve check gates the point rows

Each coordinate carries **two** systems, so there are four *lanes*.

* **System A** (`curveX`, `curveY`) is keyed on the raw Lamport labels. It delivers the five
  curve-check encodings. The check publishes `t + mask · (x³ + 3 − y²)`, which is the bridge key
  `t` exactly on the curve and uniform off it.
* **System B** (`pointX`, `pointY`) is keyed on EncPRF-whitened labels. Their one-time pads are
  derived from `H(t)`, and system B delivers the 819 point-row encodings. An evaluator who cannot
  produce `t` holds only garbage labels for system B.

The whitening applies one pad per (coordinate, position) to *both* labels of a pair, so it keeps
the free-XOR offset that the fold needs. The exception gadget still reads the bit-dependent
EncPRF labels, as in the baseline.

### 2.5 The input interface

The encoding key is exactly the 508 Lamport label pairs `(Z_j, Z_j ⊕ Δ_coord)`, and `Encode`
selects one label per bit. The private coins hold the offsets, row randomizers, gadget pads,
bridge key, curve mask and the free-XOR label material. The library supplies the three public
oracle families (fixed-key permutations, EncPRF permutations, and the field hash) separately.

---

## 3. Why the ciphertext is 3,363,376 bytes

| Field | Contents | Bytes |
|---|---|---|
| `curve` | 3 curve-check constants | 96 |
| `rows` | 91 digits × 11 constants × 32 B | 32,032 |
| `exception` | 91 digits × 6-byte gadget entry | 546 |
| 4 × `hot` | 4 lanes × `(254 − C)` fold joins × 16 B | 8,128 |
| `scale` | `C` chunk words × 824 elements × 254 bits = 26,162 B | 3,322,574 |
| **total** | `48,930 + 26,098 · C` at `C = 127` | **3,363,376** |

Every field has a fixed width and there are no tags. So every public value encodes to the same
length, and the byte-count theorem (`PlanB.Wire.ciphertextSize`) does not mention `garble` at
all. Each chunk word packs its 824 field elements at 254 bits each, the exact bit length, without
padding each element to 32 bytes.

**The size is dominated by the chunk count.** Each chunk publishes one `F_p^824` join, whatever
its width. So fewer, wider chunks mean fewer bytes: `C = 10` would give about 0.31 MB. The price
of a wide chunk is paid in **queries**, not bytes. Section 4 shows that the query gates are what
fix the chunk width.

---

## 4. Query counts, and why the chunks are 2 bits wide

The challenge bounds garbling at 1,759,967 queries and evaluation at 1,055,879. Each count is
exact for the construction as written. Each distinct question is asked once, and a program
reuses an answer only where it keeps that answer in a local table.

| Family | Garbling | Evaluation |
|---|---|---|
| `scale-hot` masks: `3 · 824` blocks per switch | `3·824·Σ_c 2^(b_c)` = 1,255,776 | `3·824·Σ_c (2^(b_c) − 1)` = 941,832 |
| `bin-to-hot` fold: 2 permutations per entry, level `j ≥ 1` | `4·Σ_c (2^(b_c+1) − 4)` = 2,032 | `4·Σ_c (2^(b_c+1) − 2b_c − 2)` = 1,016 |
| Exception gadget: 508 labels per nonzero digit | ≤ 91 · 508 = 46,228 | 91 · 508 = 46,228 |
| EncPRF pads: whitening shares the bit-0 pad | 1,016 | ≤ 1,016 (508 + one per set bit) |
| Bridge-key hash `H(t)` | 1 | 1 |
| **total** | **1,305,053** (25.8% under) | **990,093** (6.2% under) |

The switch masks dominate: `3 · 824` queries per switch, and `Σ_c 2^(b_c) ≥ 508` for any
chunking of 254 bits, with equality only for widths 1 and 2. The evaluator pays for every
**inactive** switch, not only the active one, because it must strip each inactive mask from
the join. At `b = 3` evaluation would need 1,510,893 queries. At `b = 2` it fits with a 6% margin.
Width 1 would also fit, but at `C = 254` it doubles the byte count. So `b = 2`, `C = 127` is the
smallest ciphertext that fits both gates.

The three-block sampler is kept. With `N = 824 · 508 = 418,592` sampled masks, the reduction
bias is `N · (2^384 mod p) / 2^384 = 2^-111.9`.

### How the programs are written

The pure definitions recompute oracle values freely. For example, `offsets`, `scaleJoins` and
`evalCoord` rerun a whole fold for each of the 824 elements. So they are not query programs.
`Construction/OraclePrograms.lean` writes the garbler and the evaluator in a small free monad
(`FreeQuery`) that:

* runs each fold level by level and stores the answers;
* asks each switch's mask vector once and reads it for the offsets, the join and the recovery;
* shares the whitening pad with the bit-0 EncPRF pad;
* asks the gadget labels once per digit.

The program then assembles the public value from these answer tables. Two facts make it valid:

* **Exact budget.** A separate predicate, `Bounded program n`, says that every path asks at most
  `n` questions. `toProgram` turns a bounded free program into the library's indexed
  `QueryProgram` at exactly that index.
* **Equal output.** Each table's *real* counterpart, built from the oracle, is the pure
  definition by `rfl`. The theorems `garbleProgram_correct` and `evaluateProgram_correct` show
  that the programs equal the scheme for every complete oracle.

An off-curve input is refused before any query is made.

---

## 5. Perfect correctness

Correctness is exact for every tape, oracle and input, and nothing in it is probabilistic.

* Every wire is an `F_p` element and every gate is `F_p`-linear. So the one-hot fold is an
  identity (`Finset.sum_eq_single`), not an estimate. There is no working modulus and no
  wraparound.
* The switch resolution order depends only on the evaluator's cleartext input.
* An off-curve input returns `some none` before the garbled program is touched.
* The two Jacobian degeneracies go through the exception gadget, whose entry is a deterministic
  function of the tape and the input.

These facts are proved in `Proof/Correctness/` and reach `Solution.perfectCorrectness` through
the Lamport label adapter (`Lamport.restore_selected`).

---

## 6. The privacy argument

### 6.1 What has to be shown

The adversary and the simulator share **one fixed lazy oracle**.

- Every adversary query is answered by that oracle.
- The simulator can only query it, look entries up, and *program* fresh points. A permutation
  program needs a fresh input and a fresh output; a failed program ends the ideal experiment
  with `false`.
- The simulator is one closed arithmetic machine. Its code size plus both stage fuels must fit
  in `2^60`.
- Its first stage sees only the byte count. Its second stage sees the chosen input `u` and the
  output `f_k(u)`.

The advantage against it must satisfy `Adv · 2^100 ≤ T + 1`, where `T` is the adversary
machine's code size plus its two fuels. Since `T + 1 ≥ q + 2`, a constant term below `2·2^-100`
and a linear term below `2^-100` per query would suffice. The entry is far inside both.

### 6.2 The simulator

**Stage 1 programs nothing and asks nothing.** It publishes a table whose every field is drawn
uniformly in source form:

- the curve and row constants and the gadget bytes;
- the fold joins;
- the `127 × 824` scale joins as canonical field elements, packed exactly as the construction
  packs them.

It also keeps a uniform Lamport key.

The table is right because of one global step. If *every* garbler switch mask is replaced by a
uniform field element before the game starts, the real table becomes exactly uniform.
- This replacement costs `N·δ₃ = 2^-111.86` with `N = 824·508`. It is affordable only because
  the 2-bit chunks keep `N` small.
- It is non-adaptive: no mask is singled out. That is what lets the published joins be exactly
  uniform *for every way the adversary later chooses its input*.

**Stage 2 opens the rows to `f_k(u)`.**

- *Off the curve*, it returns the selected labels and nothing else. The real evaluator's
  bridge value is then wrong, so every point-lane label is hidden in the real game too.
- *On the curve*, it proceeds as follows.

1. It replays the honest evaluator on the shared oracle:
   - system A;
   - the bridge hash;
   - the 508 whitening pads;
   - system B.
2. It leaves out the 819 designated queries: at the inactive switch `j* = α₀ ⊕ 1` of chunk 0
   in lane `pointX`, the three blocks of each digit's three *collector* elements.
3. It picks the digit points that the rows must reach:
   - the 90 tail points exactly as the garbler picks its mask points, i.e. the offsets of a
     uniform coin;
   - the head point by the group-law clamp `D₀ = Q − β·H(tail)`, so that Horner's rule returns
     `Q = f_k(u)`;
   - a Jacobian lift of each point with a fresh randomiser.
4. It solves for the designated masks. Each row has a private unit-coefficient collector, and
   the designated switch enters the evaluator's sum with coefficient `±1`, so the needed mask is
   a subtraction.
5. It programs each designated point with a uniform preimage of that mask under the three-block
   sampler.

The programmed switch is inactive, and that is deliberate. The evaluator never queries an
active switch: it recovers the active entry from the join. Programming an active point would
change nothing the adversary computes.

- Flipping the low bit of `α₀` keeps the programmed input on the *visible* fold material.
- The three-block sampler makes the programmed value's law exactly that of three fresh blocks
  conditioned on their reduction.

### 6.3 The chain of games

| hop | change | cost |
|---|---|---|
| `R = G0` | the scored lazy real game equals the tape-sampled real game | 0 (proved) |
| `G0 → G0U` | every garbler scale mask becomes uniform `F_p` | `N·δ₃` |
| `G0U → G1U` | the entries the evaluator cannot compute are deleted at the input choice | `3q/2^128 + q/(p−1)` |
| `G1U → HW` | public-first: the published cells and visible masks are jointly uniform for every selection rule; the gadget switches from the garbler's entries to uniform bytes; off the curve, the adversary's system-A masks go from swapped-uniform to Rule-S samples | `4q₁/2^128 + 182/(r−1) + N·δ₃` |
| `HW → H` | the real digit rows are replaced by the tail, clamp and lift sampler | `364/(r−1)` |
| `H → I^U` | the 819 programs can abort, charged per stage-1 query at its own candidate index | `2q₁/(2^128 − q₁)` |
| `I^U → I` | the other masks go back to lazily queried values | `N·δ₃ + q₁·(1/2^128 + 1/(2^128 − q₁))` |
| `I → M` | the machine's bounded samplers | `≤ 2^-128` |

Four points in this chain are worth stating.

- **The abort term.** A designated index names its switch. Each stage-1 query is therefore
  charged to at most one of the `4·819` candidate indices. Its recorded pair collides with the
  program only if the hidden label `E*` equals its domain, or equals its range shifted by the
  programmed limb. The limb is drawn independently of `E*`, so both cases cost the label's
  min-entropy, `1/(2^128 − q₁)`. The limb's own point masses are *not* small enough to use
  directly.
- **The doubling case.** If the adversary's input doubles a digit (the digit's point equals its
  mask point), the real rows are `(0,0,0)`, which a lift never produces. The real gadget then
  unlocks the true digit, while the simulator's gadget bytes are uniform. The simulator does not
  reproduce the case. It is charged twice, once in each hop where it makes a difference:
  - `182/(r−1)` in the public-first hop, where the gadget becomes uniform;
  - inside `364/(r−1)`, together with the offset restrictions, in the opening hop, where the rows
    become lifts.
- **The constant part** is `3·N·δ₃ + 182/(r−1) + 364/(r−1) + 2^-128 ≈ 2^-110.28`, more than 10 bits
  under its allowance.
- **The linear part** is 11 units of `q/2^128`, about `2^-124.5` per query.

### 6.4 The machine

The simulator's machine samples about `10^5` field cells by bounded rejection, serialises the
table, and in stage 2 replays about `9.4·10^5` lazy queries and makes 819 programs. Its designed
total is `size + 1 + fuels = 83,344,643,287 ≈ 2^36.3`, far inside `2^60`.

The machine reaches `FixedIndex` through `Fintype.equivFin`, and it embeds those ordinals as
constants. Its law, `MachineLaw planBSimulator 2^-128`, is proved: stage 1 and stage 2 of the
machine are the abstract simulator's stages run on bounded samplers, and the samplers' cutoff
mass is below `2^-128`.

---

## 7. Status

Every obligation of `Kriterion.Solution` is proved. These are:

* computable garbling, with query programs at exact budgets and their equality proofs;
* Lamport compatibility;
* perfect correctness;
* function correctness;
* the fixed byte count;
* adaptive privacy.

`#print axioms Submission.solution` reports exactly `propext`, `Classical.choice` and
`Quot.sound`.

`adaptivePrivacy` is the proved top-level assembly. It yields exactly the field's type from
these inputs, all proved:

- the mask swaps;
- the hidden hop;
- the public-first hop `G1U → HW` of §6.3, on top of its exact joint-law core;
- the opening;
- the abort mass;
- the machine law of the closed simulator machine, with its `2^60` cost bound.

Also proved are:

- the exact equality of the scored real game with the tape-sampled one;
- the exact identification of the library's ideal game with the abstract simulator of §6.2;
- the budget arithmetic.

This entry was written with AI coding agents under human direction and review.
