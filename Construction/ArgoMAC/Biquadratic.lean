/-
This file defines the three sparse biquadratic rows of one recoded digit.

Plan B removes the 254-row `DigitAdaptor` tables: a row no longer garbles its own adaptors, it
consumes the affine element values the projectivized garbling scheme delivers. A digit
therefore publishes exactly eleven field elements (`X` four, `Y` five, `Z` two) and consumes
nine element slots -- five against the `x` coordinate and four against the `y` coordinate.
The masking algebra is the baseline's, unchanged: the row constants absorb the element offsets
exactly as they used to absorb `DigitAdaptor.bitsK`.
The plan source is `2026-09-17-planB.md`, sections D.1 and D.4.
-/

import Construction.ArgoMAC.Input
import Construction.PGS.Elements

namespace Kriterion.ArgoMAC.Biquadratic

open BN254 Kriterion.ArgoMAC.PlanB

/-- The nine element slots one digit consumes: five x-type and four y-type. -/
abbrev Element := XElement ⊕ YElement

/-- One value per element slot of a digit. The garbler uses this for the element offsets
`K e = b_e = O[e]`, the evaluator for the delivered values `a_e * coord + b_e`. -/
abbrev Values := Element → BaseField

/-- The coordinate an element slot is chunked against. -/
def coordValue (input : AffineInput) : Element → BaseField
  | .inl _ => input.x
  | .inr _ => input.y

@[simp] theorem coordValue_inl (input : AffineInput) (element : XElement) :
    coordValue input (.inl element) = input.x := rfl

@[simp] theorem coordValue_inr (input : AffineInput) (element : YElement) :
    coordValue input (.inr element) = input.y := rfl

/-- The `X` row randomizers: monomials `1, x, y, x²`. -/
structure XRandomness where
  /-- The randomizer of the `x` monomial. -/
  r1 : BaseField
  /-- The randomizer of the `y` monomial. -/
  r2 : BaseField
  /-- The randomizer of the `x²` monomial. -/
  r4 : BaseField

/-- The `Y` row randomizers: monomials `1, y, x y, x², y²`. -/
structure YRandomness where
  /-- The randomizer of the `y` monomial. -/
  r2 : BaseField
  /-- The randomizer of the `x y` monomial. -/
  r3 : BaseField
  /-- The randomizer of the `x²` monomial. -/
  r4 : BaseField
  /-- The randomizer of the `y²` monomial. -/
  r5 : BaseField

/-- The `Z` row randomizer: monomials `1, x`. -/
structure ZRandomness where
  /-- The randomizer of the `x` monomial. -/
  r1 : BaseField

/-- The four published constants of the `X` row. -/
structure XGamma where
  /-- The constant monomial. -/
  c0 : BaseField
  /-- The `x` monomial. -/
  c1 : BaseField
  /-- The `y` monomial. -/
  c2 : BaseField
  /-- The `x²` monomial. -/
  c4 : BaseField

/-- The five published constants of the `Y` row. The `x` monomial is always absent, which is
why a digit publishes eleven constants and not twelve. -/
structure YGamma where
  /-- The constant monomial. -/
  c0 : BaseField
  /-- The `y` monomial. -/
  c2 : BaseField
  /-- The `x y` monomial. -/
  c3 : BaseField
  /-- The `x²` monomial. -/
  c4 : BaseField
  /-- The `y²` monomial. -/
  c5 : BaseField

/-- The two published constants of the `Z` row. -/
structure ZGamma where
  /-- The constant monomial. -/
  c0 : BaseField
  /-- The `x` monomial. -/
  c1 : BaseField

/-! ### Slopes

The slope table is plan D.4's, verbatim. `K e` is the element offset the projectivized
garbling scheme delivers -- the PGS output mask `O[e]`, which the garbler can compute from the
tape alone before any slope exists. That is what keeps the chain `x7 → x9`, `y6, x7 → x9`,
`y8 → y10` resolvable in one pass. -/

/-- The slope of every element slot of one digit. -/
def slopes (x : XRandomness) (y : YRandomness) (z : ZRandomness) (K : Values) : Values
  | .inl .rowX_x7 => -x.r4
  | .inl .rowX_x9 => -(x.r1 + K (.inl .rowX_x7))
  | .inr .rowX_y10 => -x.r2
  | .inr .rowY_y6 => -y.r3
  | .inl .rowY_x7 => -y.r4
  | .inr .rowY_y8 => -y.r5
  | .inl .rowY_x9 => -(K (.inr .rowY_y6) + K (.inl .rowY_x7))
  | .inr .rowY_y10 => -(y.r2 + K (.inr .rowY_y8))
  | .inl .rowZ_x9 => -z.r1

/-- The value the evaluator obtains for every element slot of one digit. -/
def delivered (x : XRandomness) (y : YRandomness) (z : ZRandomness) (K : Values)
    (input : AffineInput) : Values :=
  fun element => slopes x y z K element * coordValue input element + K element

/-! ### Garbling and evaluation -/

/-- The `X` row: the three consumed elements are `x7`, `x9` and `y10`. -/
def garbleX (c0 c1 c2 c4 : BaseField) (randomness : XRandomness) (K : Values) : XGamma := {
  c0 := c0 - K (.inl .rowX_x9) - K (.inr .rowX_y10)
  c1 := c1 + randomness.r1
  c2 := c2 + randomness.r2
  c4 := c4 + randomness.r4 }

/-- The `Y` row: the five consumed elements are `y6`, `x7`, `y8`, `x9` and `y10`. -/
def garbleY (c0 c2 c3 c4 c5 : BaseField) (randomness : YRandomness) (K : Values) : YGamma := {
  c0 := c0 - K (.inl .rowY_x9) - K (.inr .rowY_y10)
  c2 := c2 + randomness.r2
  c3 := c3 + randomness.r3
  c4 := c4 + randomness.r4
  c5 := c5 + randomness.r5 }

/-- The `Z` row: the single consumed element is `x9`. -/
def garbleZ (c0 c1 : BaseField) (randomness : ZRandomness) (K : Values) : ZGamma := {
  c0 := c0 - K (.inl .rowZ_x9)
  c1 := c1 + randomness.r1 }

/-- The `X` row value: `c0 + c1 x + c2 y + c4 x² + x7 · x + x9 + y10`. -/
def evaluateX (gamma : XGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + gamma.c1 * input.x + gamma.c2 * input.y + gamma.c4 * input.x ^ 2 +
    values (.inl .rowX_x7) * input.x + values (.inl .rowX_x9) + values (.inr .rowX_y10)

/-- The `Y` row value:
`c0 + c2 y + c3 x y + c4 x² + c5 y² + y6 · x + x7 · x + y8 · y + x9 + y10`. -/
def evaluateY (gamma : YGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + gamma.c2 * input.y + gamma.c3 * input.x * input.y + gamma.c4 * input.x ^ 2 +
    gamma.c5 * input.y ^ 2 + values (.inr .rowY_y6) * input.x +
    values (.inl .rowY_x7) * input.x + values (.inr .rowY_y8) * input.y +
    values (.inl .rowY_x9) + values (.inr .rowY_y10)

/-- The `Z` row value: `c0 + c1 x + x9`. -/
def evaluateZ (gamma : ZGamma) (input : AffineInput) (values : Values) : BaseField :=
  gamma.c0 + gamma.c1 * input.x + values (.inl .rowZ_x9)

/-! ### Correctness

Each row's published constants cancel the offsets of the elements it consumes, and each
element's slope cancels the randomizer of the monomial it rides on. -/

/-- The `X` row evaluates to its three-monomial value. -/
theorem evaluateEncodedX (c0 c1 c2 c4 : BaseField) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateX (garbleX c0 c1 c2 c4 x K) input (delivered x y z K input) =
      c0 + c1 * input.x + c2 * input.y + c4 * input.x ^ 2 := by
  simp only [evaluateX, garbleX, delivered, slopes, coordValue]
  ring

/-- The `Y` row evaluates to its five-monomial value. -/
theorem evaluateEncodedY (c0 c2 c3 c4 c5 : BaseField) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateY (garbleY c0 c2 c3 c4 c5 y K) input (delivered x y z K input) =
      c0 + c2 * input.y + c3 * input.x * input.y + c4 * input.x ^ 2 + c5 * input.y ^ 2 := by
  simp only [evaluateY, garbleY, delivered, slopes, coordValue]
  ring

/-- The `Z` row evaluates to its two-monomial value. -/
theorem evaluateEncodedZ (c0 c1 : BaseField) (x : XRandomness) (y : YRandomness)
    (z : ZRandomness) (K : Values) (input : AffineInput) :
    evaluateZ (garbleZ c0 c1 z K) input (delivered x y z K input) = c0 + c1 * input.x := by
  simp only [evaluateZ, garbleZ, delivered, slopes, coordValue]
  ring

/-- The `X` row's `y10` element value at one `y` coordinate. The garbler uses it as a gadget
key in the baseline; it is kept as a named deliverable. -/
def xY10Value (x : XRandomness) (y : YRandomness) (z : ZRandomness) (K : Values)
    (input : AffineInput) : BaseField := delivered x y z K input (.inr .rowX_y10)

/-- The `Z` row's `x9` element value at one `x` coordinate. -/
def zX9Value (x : XRandomness) (y : YRandomness) (z : ZRandomness) (K : Values)
    (input : AffineInput) : BaseField := delivered x y z K input (.inl .rowZ_x9)

end Kriterion.ArgoMAC.Biquadratic
