/-
Phase 3 glue, step 4a: **the error terms of the Plan B chain and the closing inequality.**

Each term is the formula of design note B §5, with the corrections of the review and of P1:

| hop | term | value |
|---|---|---|
| `G0 → G0U` | `maskSwapError = N·δ₃`, `N = 824·508`, `δ₃ = (2^384 mod p)/2^384` | `2^-111.86` |
| `G0U → G1U` | `hiddenPointError q = 3q/2^128 + q/(p−1)` (`L1`) | linear |
| `G1U → HW` | `stageOneHitError q₁ + exceptionalError + maskSwapError`: `L2 = 4q₁/2^128`, plus the doubling-exception mass `182/(r−1)` (the gadget goes from real to lazy in this hop; P1d, `PublicFirst.gadget_counterShape_refutes`), plus one more `N·δ₃`. The last term is needed because off the curve `G1U` installs the system-A masks with `G0U`'s uniform values while `HW` makes no call, so the adversary's own masks are `sampleFp` of fresh blocks (P1g, `not_publicFirst`). | linear + `2^-111.86` |
| `HW → H` | `outputKernelError = 364/(r−1)` (`ε_pt`; P1's lemmas give `≤ 363/#Point`) | `2^-245.1` |
| `H → I^U` | `abortError q₁ = q₁·abortQueryCharge q₁`, `abortQueryCharge q₁ = 1/(2^128−q₁) + 1/(2^128−q₁)` (per stage-1 query at a candidate designated index: input and output freshness, both through `E*`'s min-entropy; see `AbortBound`) | linear |
| `I^U → I` | `maskSwapError + idealRefillError q₁`: per derived mask `δ₃`, per stage-1 query at its indices `refillQueryCharge q₁ = 1/2^128 + 1/(2^128−q₁)` (`L3`) | `2^-111.86` + linear |
| `I → M` | `machineCutoffError = 2^-128` (`ε_cut`, relaxed from the planned `2^-391.72`) | constant |

`chainError_budget`: for `q₁ + q₂ < 2^100`, `chainError q₁ q₂ · 2^100 ≤ q₁ + q₂ + 1`. Every term
is bounded by a thousandth of its unit, so the budget closes with the constant `≤ 6/1000` (six
terms: three `N·δ₃`, `182/(r−1)`, `364/(r−1)` and the cutoff; the value is ≈ `2^-110.28`) and the
linear coefficient `≤ 4/1000` (per query, in units of `2^-100`).
-/

import Proof.Privacy.Phase3.Glue.AbstractSimulator

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254

noncomputable section

/-- `N`: the garbler's scale masks, `S · Σ_c 2^{b_c} = 824 · 508 = 418,592`. -/
def scaleMaskCount : ℕ := 824 * 508

/-- One copy of the global mask swap, `N·δ₃` with `δ₃ = (2^384 mod p)/2^384`. -/
def maskSwapError : ℝ :=
  (scaleMaskCount : ℝ) * ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) / 2 ^ 384

/-- `δ₃ = (2^384 mod p)/2^384`: the Rule-S bias of one `sampleFp` of three uniform blocks. -/
def delta3 : ℝ := ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) / 2 ^ 384

theorem delta3_nonneg : 0 ≤ delta3 := by
  unfold delta3
  positivity

/-- One mask swap is `N` copies of `δ₃`. -/
theorem maskSwapError_eq : maskSwapError = (scaleMaskCount : ℝ) * delta3 := by
  unfold maskSwapError delta3
  ring

/-- `L1`: hidden-point hits (`Δ` guesses, hidden outputs, `hash(t)` off the curve). -/
def hiddenPointError (queries : ℕ) : ℝ :=
  3 * (queries : ℝ) / 2 ^ 128 + (queries : ℝ) / ((baseFieldModulus : ℝ) - 1)

/-- `L2`: stage-1 hits on a garbler point. -/
def stageOneHitError (first : ℕ) : ℝ := 4 * (first : ℝ) / 2 ^ 128

/-- `ε_exc`: the doubling-exception mass at the adversary's input, `≤ 182/#Point ≤ 182/(r−1)`.
It is charged in `G1U → HW`, where the gadget switches from the garbler's entries (which unlock the
true digit at the exceptional input) to uniform published bytes. The adversary's input doubles a
digit with this mass under the construction's offset law, independently of its view. -/
def exceptionalError : ℝ := 182 / ((scalarFieldModulus : ℝ) - 1)

/-- `ε_pt`: the offset restriction, the doubling rows and the tail restriction of the output
kernel. P1's opening lemmas give `≤ 363/#Point`, which is `≤ 364/(r−1)` since `#Point ≥ r`. -/
def outputKernelError : ℝ := 364 / ((scalarFieldModulus : ℝ) - 1)

/-- The smallest preimage count `M(p−1) = ⌊(2^384 − p)/p⌋ + 1` of `sampleFp`. It no longer enters
the budget (the abort charge has no limb term); it is kept for P1's `LimbBound`. -/
def preimageFloor : ℕ := (2 ^ 384 - baseFieldModulus) / baseFieldModulus + 1

/-- The input part of one stage-1 query's abort charge: the designated label `E*` equals the
query's recorded domain, `≤ max_e Pr[E* = e | view] ≤ 1/(2^128 − q₁)`. -/
def abortInputCharge (first : ℕ) : ℝ := 1 / (2 ^ 128 - (first : ℝ))

/-- The output part of one stage-1 query's abort charge: the programmed output `o_b xor E*`
equals the query's recorded range `y`, i.e. `E* = y xor o_b`. The limb `o_b` is drawn from `y*`
alone, independently of `E*` given the view, so this is again `≤ max_e Pr[E* = e | view] ≤
1/(2^128 − q₁)` (`OutputFreshness`). The limb bound `max_v Pr[o_b = v] ≤ 7/M` is **not** used: it
is false (P1, `LimbBound.limbOne_counterexample`: the middle limb of `idealPreimage 0` has mass
`≥ 15/M` at `0`). -/
def abortOutputCharge (first : ℕ) : ℝ := 1 / (2 ^ 128 - (first : ℝ))

/-- The abort charge of **one stage-1 query at a candidate designated index**: its recorded pair
collides with the program at that index through the input or through the output. The index names
its switch, so the query is charged to one candidate site only; summed over the distinct
candidate indices the coefficient is `1` per part (no factor for the four candidate switches). -/
def abortQueryCharge (first : ℕ) : ℝ := abortInputCharge first + abortOutputCharge first

/-- `ε_abort`: the per-query charge over the `q₁` stage-1 queries. -/
def abortError (first : ℕ) : ℝ := (first : ℝ) * abortQueryCharge first

/-- The lazy-refill charge of **one stage-1 query at a derived mask's index**: the lazy answer at a
fresh input is uniform on the values left after that query (`1/2^128`), and the derived input
may equal the query's recorded input (`1/(2^128 − q₁)`). -/
def refillQueryCharge (first : ℕ) : ℝ := 1 / 2 ^ 128 + 1 / (2 ^ 128 - (first : ℝ))

/-- `L3`: the per-query refill charge over the `q₁` stage-1 queries. -/
def idealRefillError (first : ℕ) : ℝ := (first : ℝ) * refillQueryCharge first

/-- The whole chain `G0 → G0U → G1U → HW → H → I^U → I → M`. -/
def chainError (first second : ℕ) : ℝ :=
  maskSwapError + hiddenPointError (first + second) +
    (stageOneHitError first + exceptionalError + maskSwapError) + outputKernelError + abortError first + (maskSwapError + idealRefillError first) +
    machineCutoffError

/-! ### Each term against its unit

`norm_num` does not expand powers above `2^256`, so the two large powers are split first. -/

theorem two_pow_384_real : (2 : ℝ) ^ 384 = 2 ^ 192 * 2 ^ 192 := by rw [← pow_add]

theorem two_pow_384_nat : (2 : ℕ) ^ 384 = 2 ^ 192 * 2 ^ 192 := by rw [← pow_add]

theorem maskSwapError_nonneg : 0 ≤ maskSwapError := by
  unfold maskSwapError
  positivity

theorem maskSwapError_le : maskSwapError * 2 ^ 100 ≤ 1 / 1000 := by
  have residue : ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) ≤ 2 ^ 254 := by
    have bound : 2 ^ 384 % baseFieldModulus ≤ 2 ^ 254 :=
      ((Nat.mod_lt _ (by unfold baseFieldModulus; norm_num)).trans PlanB.baseFieldModulus_lt).le
    exact_mod_cast bound
  have split : maskSwapError * 2 ^ 100 =
      ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) * ((scaleMaskCount : ℝ) * 2 ^ 100 / 2 ^ 384) := by
    unfold maskSwapError
    ring
  rw [split]
  calc _ ≤ (2 : ℝ) ^ 254 * ((scaleMaskCount : ℝ) * 2 ^ 100 / 2 ^ 384) :=
        mul_le_mul_of_nonneg_right residue (by positivity)
    _ ≤ 1 / 1000 := by unfold scaleMaskCount; rw [two_pow_384_real]; norm_num

theorem outputKernelError_nonneg : 0 ≤ outputKernelError := by
  unfold outputKernelError scalarFieldModulus
  norm_num

theorem exceptionalError_nonneg : 0 ≤ exceptionalError := by
  unfold exceptionalError scalarFieldModulus
  norm_num

theorem exceptionalError_le : exceptionalError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold exceptionalError scalarFieldModulus
  norm_num

theorem outputKernelError_le : outputKernelError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold outputKernelError scalarFieldModulus
  norm_num

theorem machineCutoffError_le : machineCutoffError * 2 ^ 100 ≤ 1 / 1000 := by
  unfold machineCutoffError
  norm_num

theorem hiddenPointError_le (queries : ℕ) :
    hiddenPointError queries * 2 ^ 100 ≤ (queries : ℝ) / 1000 := by
  have split : hiddenPointError queries * 2 ^ 100 =
      (queries : ℝ) * ((3 / 2 ^ 128 + 1 / ((baseFieldModulus : ℝ) - 1)) * 2 ^ 100) := by
    unfold hiddenPointError
    ring
  have coefficient : (3 / 2 ^ 128 + 1 / ((baseFieldModulus : ℝ) - 1)) * 2 ^ 100 ≤ 1 / 1000 := by
    unfold baseFieldModulus
    norm_num
  rw [split, div_eq_mul_one_div (queries : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left coefficient (Nat.cast_nonneg _)

theorem stageOneHitError_le (first : ℕ) :
    stageOneHitError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  have split : stageOneHitError first * 2 ^ 100 = (first : ℝ) * (4 * 2 ^ 100 / 2 ^ 128) := by
    unfold stageOneHitError
    ring
  rw [split, div_eq_mul_one_div (first : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left (by norm_num) (Nat.cast_nonneg _)

/-- Below `2^100` queries, `2^128 − q₁ ≥ 2^127`. -/
theorem room_le (first : ℕ) (small : first < 2 ^ 100) : (2 : ℝ) ^ 127 ≤ 2 ^ 128 - (first : ℝ) := by
  have firstSmall : (first : ℝ) ≤ 2 ^ 100 := by exact_mod_cast small.le
  have : (2 : ℝ) ^ 100 ≤ 2 ^ 127 := by norm_num
  have : (2 : ℝ) ^ 128 = 2 ^ 127 + 2 ^ 127 := by norm_num
  linarith

/-- The per-query refill charge is non-negative below `2^100` queries. -/
theorem refillQueryCharge_nonneg (first : ℕ) (small : first < 2 ^ 100) :
    0 ≤ refillQueryCharge first := by
  have room := room_le first small
  unfold refillQueryCharge
  have : (0 : ℝ) < 2 ^ 128 - (first : ℝ) := lt_of_lt_of_le (by positivity) room
  positivity

/-- The per-query abort charge is non-negative below `2^100` queries. -/
theorem abortQueryCharge_nonneg (first : ℕ) (small : first < 2 ^ 100) :
    0 ≤ abortQueryCharge first := by
  have room := room_le first small
  unfold abortQueryCharge abortInputCharge abortOutputCharge
  have : (0 : ℝ) < 2 ^ 128 - (first : ℝ) := lt_of_lt_of_le (by positivity) room
  positivity

theorem idealRefillError_le (first : ℕ) (small : first < 2 ^ 100) :
    idealRefillError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  have room := room_le first small
  have fresh : 1 / (2 ^ 128 - (first : ℝ)) ≤ 1 / 2 ^ 127 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) room
  have coefficient : refillQueryCharge first * 2 ^ 100 ≤ 1 / 1000 := by
    unfold refillQueryCharge
    calc _ ≤ (1 / 2 ^ 128 + 1 / 2 ^ 127) * (2 : ℝ) ^ 100 :=
          mul_le_mul_of_nonneg_right (add_le_add le_rfl fresh) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have split : idealRefillError first * 2 ^ 100 =
      (first : ℝ) * (refillQueryCharge first * 2 ^ 100) := by
    unfold idealRefillError
    ring
  rw [split, div_eq_mul_one_div (first : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left coefficient (Nat.cast_nonneg _)

theorem abortError_le (first : ℕ) (small : first < 2 ^ 100) :
    abortError first * 2 ^ 100 ≤ (first : ℝ) / 1000 := by
  have room := room_le first small
  have fresh : 1 / (2 ^ 128 - (first : ℝ)) ≤ 1 / 2 ^ 127 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) room
  have coefficient : abortQueryCharge first * 2 ^ 100 ≤ 1 / 1000 := by
    unfold abortQueryCharge abortInputCharge abortOutputCharge
    calc _ ≤ (1 / 2 ^ 127 + 1 / 2 ^ 127) * (2 : ℝ) ^ 100 :=
          mul_le_mul_of_nonneg_right (add_le_add fresh fresh) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have split : abortError first * 2 ^ 100 = (first : ℝ) * (abortQueryCharge first * 2 ^ 100) := by
    unfold abortError
    ring
  rw [split, div_eq_mul_one_div (first : ℝ) 1000]
  exact mul_le_mul_of_nonneg_left coefficient (Nat.cast_nonneg _)

/-- **The closing inequality.** Below `2^100` queries the whole chain costs at most
`(q₁ + q₂ + 1) / 2^100`: the constant part (three mask swaps, the doubling exception, the output
kernel, the cutoff) is below one unit and the linear part below one unit per query. -/
theorem chainError_budget (first second : ℕ) (small : first + second < 2 ^ 100) :
    chainError first second * 2 ^ 100 ≤ (first : ℝ) + (second : ℝ) + 1 := by
  have swap := maskSwapError_le
  have kernel := outputKernelError_le
  have exceptional := exceptionalError_le
  have cutoff := machineCutoffError_le
  have hidden := hiddenPointError_le (first + second)
  have hit := stageOneHitError_le first
  have abort := abortError_le first (by omega)
  have refill := idealRefillError_le first (by omega)
  have firstNonneg : (0 : ℝ) ≤ first := Nat.cast_nonneg _
  have secondNonneg : (0 : ℝ) ≤ second := Nat.cast_nonneg _
  push_cast at hidden
  unfold chainError
  nlinarith

/-- **The output-freshness lemma (P4).** A programmed output `limb xor label`, with the limb drawn
independently of the label and the label's point masses at most `ε`, lands in a stage-1 range of
`n` blocks with mass at most `n·ε`. Instantiated per stage-1 query at a candidate designated index
(`range` = that query's recorded range, `labelLaw` = the law of `E*` given the view and `y*`,
`ε = 1/(2^128 − q₁)`), it is the output part `abortOutputCharge` of `AbortBound.perQuery`. -/
def OutputFreshness : Prop :=
  ∀ (labelLaw limbLaw : PMF Cryptography.Block) (range : Finset Cryptography.Block)
    (ε : ENNReal), (∀ label, labelLaw label ≤ ε) →
      (labelLaw.bind fun label => limbLaw.map fun limb => limb ^^^ label).toOuterMeasure
          (range : Set Cryptography.Block) ≤ (range.card : ENNReal) * ε

end

end Kriterion.ArgoMAC.Phase3.Glue
