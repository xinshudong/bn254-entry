/-
**Phase 3, P1c/P1f/P1h — hop (1), `G0U → G1U`: hidden-entry deletion, identical until touched. REAL.**

* `Hidden/Reduction.lean` (P1c): `hidden_of_guess D one two : GameUntilBad G0U G1U L1` from the two
  view-independence bounds `StageOneGuess` and `StageTwoGuess D`.
* `Hidden/Designed.lean` (P1f): the designed-visibility rule `designedRule` (index-based: no
  coincidence reaches the designed view, so no additive constant); **`stageOneGuess` is real**.
* P1h, **`StageTwoGuess designedRule` is real** (`Hidden/Final.lean`, `stageTwoGuess`):
  - `Hidden/StageTwoShift.lean`: the stage-2 tape shifts (the Δ-family at `u`, the `k₂`-family, the
    hot-output family); `Hidden/GarblerAsk.lean`: the shape of the garbler's questions;
  - `Hidden/{Reach,Containment}.lean`: **the evaluator-correctness containment** — every garbler
    entry at a designed index is asked by the adversary's own evaluation (`designed_asks`), so the
    designed entries are a filter of the garbler's transcript (`designedEntries_eq`);
  - `Hidden/{StageTwoFixed,StageTwo}.lean`: the view is kept by the shifts, a touch is a hidden hit
    (`2^-128` each) or the bridge key off the curve (`stageTwoGuess_of_bridge`);
  - `Hidden/{Split,CurveFamily,CurveDesigned,CurveView}.lean`: **the off-curve bridge key**
    (`stageTwoBridgeGuess`, `1/(p − 1)`) on the curve coordinates.
* **`hidden : GameUntilBad maskSwappedHybrid hiddenDeletedHybrid (hiddenPointError (q₁ + q₂))`**,
  per query exactly `3/2^128 + 1/(p − 1)`, axioms `[propext, Classical.choice, Quot.sound]`.
-/

import Proof.Privacy.Phase3.Hidden.Reduction
import Proof.Privacy.Phase3.Hidden.Designed
import Proof.Privacy.Phase3.Hidden.StageTwoShift
import Proof.Privacy.Phase3.Hidden.Containment
import Proof.Privacy.Phase3.Hidden.StageTwo
import Proof.Privacy.Phase3.Hidden.CurveFamily
import Proof.Privacy.Phase3.Hidden.CurveView
import Proof.Privacy.Phase3.Hidden.Final
