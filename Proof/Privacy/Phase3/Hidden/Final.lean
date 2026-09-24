/-
**Phase 3, P1h — hop (1), `G0U → G1U`, real.**

`stageTwoGuess`: `StageTwoGuess designedRule (3/2^128 + 1/(p − 1))` — a stage-2 touch is a hidden
fixed-key hit (`2 · 2^-128`, `StageTwoFixed`) or, off the curve, the bridge key (`1/(p − 1)`,
`CurveView.stageTwoBridgeGuess`). With `stageOneGuess` (P1f) and the reduction (P1c):

```
hidden : GameUntilBad maskSwappedHybrid hiddenDeletedHybrid fun q₁ q₂ => hiddenPointError (q₁ + q₂)
```

per query exactly `3/2^128 + 1/(p − 1)` (L1's constant), no additive constant.
-/

import Proof.Privacy.Phase3.Hidden.CurveView

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

noncomputable section

/-- **`StageTwoGuess designedRule` at L1's constant, real.** -/
theorem stageTwoGuess : StageTwoGuess designedRule (ENNReal.ofReal hiddenCharge) :=
  stageTwoGuess_of_bridge stageTwoBridgeGuess

/-- **Hop (1), `G0U → G1U`, real**: identical until a hidden entry is touched, at
`L1 = hiddenPointError (q₁ + q₂)`, per query `3/2^128 + 1/(p − 1)`. -/
theorem hidden :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad maskSwappedHybrid hiddenDeletedHybrid
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden_of_stageTwo stageTwoGuess

/-- The same, as `planBHybrids`' field (`JointExactnessBound.hidden`). -/
theorem planB_hidden :
    Kriterion.ArgoMAC.Phase3.Glue.GameUntilBad planBHybrids.maskSwapped planBHybrids.hiddenDeleted
      fun first second => Kriterion.ArgoMAC.Phase3.Glue.hiddenPointError (first + second) :=
  hidden

end

end Kriterion.ArgoMAC.Security.Phase3
