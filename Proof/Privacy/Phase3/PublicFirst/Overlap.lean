/-
**Phase 3, P1d — flagged games and the overlap bound.**

The exact constant of `G1U → HW` (`4q₁/2^128 + 182/(r−1)`) cannot be reached by a triangle of
advantage bounds through an intermediate game: `G1U` and `HW` each deviate from any middle game on
stage-1 touches of the *same* (coupled) stage-2 points, and a triangle charges those touches twice.
The chain is therefore run on **flagged** games, `PMF (Option Bool)` with `none` the bad event:

* `Below first flagged` — `flagged (some b) ≤ first b` for both bits: the flag-down part of
  `flagged` is below `first`;
* `Below.trans` / `FlagMono` — lower bounds compose, and raising more flags only lowers the
  flag-down part;
* `advantage_le_of_overlap` — **if one flagged game is below both games, their advantage is at most
  its flag mass.** So the two chains from `G1U` and from `HW` must meet at one flagged middle game,
  whose flag is the *union* of both sides' bad events (each stage-1 query charged once, at its
  index, against the coupled stage-2 points there).
-/

import Proof.Privacy.Phase3.UntilBadIff

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography
open scoped ENNReal

noncomputable section

/-- The flag-down part of a flagged game is below a game. -/
def Below (game : PMF Bool) (flagged : PMF (Option Bool)) : Prop :=
  ∀ b, flagged (some b) ≤ game b

/-- A flagged game is below another (more flags raised): its flag-down part is smaller. -/
def FlagMono (upper lower : PMF (Option Bool)) : Prop :=
  ∀ b, lower (some b) ≤ upper (some b)

theorem Below.trans {game : PMF Bool} {upper lower : PMF (Option Bool)} (below : Below game upper)
    (mono : FlagMono upper lower) : Below game lower :=
  fun b => (mono b).trans (below b)

/-- The three masses of a flagged game sum to one. -/
theorem flagged_total (flagged : PMF (Option Bool)) :
    flagged none + flagged (some true) + flagged (some false) = 1 := by
  have total := flagged.tsum_coe
  rw [tsum_fintype] at total
  rw [← total]
  simp only [Fintype.sum_option, Fintype.sum_bool]
  ring

/-- **The overlap bound.** A flagged game below both games bounds their advantage by its flag
mass. -/
theorem advantage_le_of_overlap {first second : PMF Bool} {flagged : PMF (Option Bool)}
    (firstBelow : Below first flagged) (secondBelow : Below second flagged) :
    Assumptions.advantage first second ≤ (flagged none).toReal := by
  have total := flagged_total flagged
  have finite (x : Option Bool) : flagged x ≠ ⊤ := PMF.apply_ne_top _ _
  have firstFalse := pmf_bool_false first
  have secondFalse := pmf_bool_false second
  have firstLe : first true ≤ 1 := PMF.coe_le_one _ _
  have secondLe : second true ≤ 1 := PMF.coe_le_one _ _
  have firstTop : first true ≠ ⊤ := PMF.apply_ne_top _ _
  have secondTop : second true ≠ ⊤ := PMF.apply_ne_top _ _
  -- real versions
  have totalReal : (flagged none).toReal + (flagged (some true)).toReal
      + (flagged (some false)).toReal = 1 := by
    rw [← ENNReal.toReal_add (finite _) (finite _),
      ← ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩) (finite _), total,
      ENNReal.toReal_one]
  have lowerTrue (game : PMF Bool) (below : Below game flagged) :
      (flagged (some true)).toReal ≤ (game true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (below true)
  have upperTrue (game : PMF Bool) (below : Below game flagged) :
      (game true).toReal ≤ 1 - (flagged (some false)).toReal := by
    have falseLe : (flagged (some false)).toReal ≤ (game false).toReal :=
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) (below false)
    have gameTotal : (game true).toReal + (game false).toReal = 1 := by
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      have sum := game.tsum_coe
      rw [tsum_fintype, Fintype.sum_bool] at sum
      rw [sum, ENNReal.toReal_one]
    linarith
  have a1 := lowerTrue first firstBelow
  have a2 := upperTrue first firstBelow
  have b1 := lowerTrue second secondBelow
  have b2 := upperTrue second secondBelow
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-- **From an overlap to the hop's identical-until-bad shape.** -/
theorem coreUntilBad_of_overlap {first second : PMF Bool} {flagged : PMF (Option Bool)}
    {error : ℝ} (firstBelow : Below first flagged) (secondBelow : Below second flagged)
    (flagMass : (flagged none).toReal ≤ error) :
    Kriterion.ArgoMAC.Phase3.Glue.CoreUntilBad first second error :=
  coreUntilBad_iff.mpr ((advantage_le_of_overlap firstBelow secondBelow).trans flagMass)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
