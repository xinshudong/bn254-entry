/-
**Phase 3, P4 — `MaskSwapBound.idealPerMask`: the lazy refill `I^U → I`, in P3's exact form.**

For every adversary (the `2^100` budget guard is only used to make `refillQueryCharge` positive):

* the sites are P1's `MaskSite` (`#MaskSite = 418,592 = scaleMaskCount`);
* `count site` is the expected number of entries the adversary's first stage leaves at the
  site's three indices (`stageOneMean` of `Σ_b used`), so `Σ count ≤ q₁` (`StageOne`);
* `advantage(I^U, I) ≤ #MaskSite · δ₃ + (Σ count)/2^128 ≤ Σ_site (δ₃ + count · refillQueryCharge q₁)`.

The per-site charge actually used is `δ₃ + count/2^128` -- the answer-exclusion term only. The
input-hit term `1/(2^128 − q₁)` of `refillQueryCharge` is **not needed**: in `I^U` a known input
at a site index is answered from the cache exactly as in `I` (`consumeCell`), so no programming
ever fails on its input.

`maskSwapBound_of` assembles P3's whole `H_swap` from P1's `G0 → G0U` and this lemma, given the two
data choices `maskSwapped := maskSwappedHybrid` (P1) and `idealUniform := idealUniformHybrid`.
-/

import Proof.Privacy.Phase3.Lazy.StageOne

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex card_maskSite advantage_eq_etvDist
  maskSwappedHybrid maskSwapBound_real)
open scoped ENNReal

noncomputable section

section Mean

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The average over `I`'s prefix** (the simulator's stage 1, then the adversary's first stage
on the lazy oracle) of a function of the oracle state it leaves. -/
def stageOneMean (adversary : PlanBAdversary Unit) (parameter : ℕ) (value : LState → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty (some first) *
    ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
      first.2.2) chosen * value chosen.2

/-- The prefix loses mass only to stage-1 aborts. -/
theorem stageOne_mass_le (parameter : ℕ) :
    (∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
      (some first)) ≤ 1 :=
  le_trans (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) _)
    (le_of_eq (PMF.tsum_coe _))

/-- A constant comes out of the average at most whole. -/
theorem stageOneMean_add_const_le (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (constant : ℝ≥0∞) (value : LState → ℝ≥0∞) :
    stageOneMean adversary parameter (fun oracle => constant + value oracle) ≤
      constant + stageOneMean adversary parameter value := by
  unfold stageOneMean
  have inner : ∀ first : Public × Stage1Source × LState,
      (∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ()) first.2.2) chosen *
        (constant + value chosen.2)) =
      constant + ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
        first.2.2) chosen * value chosen.2 := by
    intro first
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc (∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
          (some first) * ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
            first.2.2) chosen * (constant + value chosen.2))
      = ∑' first, ((planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
          (some first) * constant + (planBAbstractSimulator idealSamplers).stage1 parameter
            LazyOracle.empty (some first) * ∑' chosen, (LazyOracle.run
              (adversary.chooseInput parameter first.1 ()) first.2.2) chosen * value chosen.2) := by
        refine tsum_congr fun first => ?_
        rw [inner first, mul_add]
    _ = (∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
          (some first)) * constant + ∑' first, (planBAbstractSimulator idealSamplers).stage1
            parameter LazyOracle.empty (some first) * ∑' chosen, (LazyOracle.run
              (adversary.chooseInput parameter first.1 ()) first.2.2) chosen * value chosen.2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * constant + ∑' first, (planBAbstractSimulator idealSamplers).stage1
            parameter LazyOracle.empty (some first) * ∑' chosen, (LazyOracle.run
              (adversary.chooseInput parameter first.1 ()) first.2.2) chosen * value chosen.2 := by
        gcongr
        exact stageOne_mass_le parameter
    _ = _ := by rw [one_mul]

/-- Division by a constant commutes with the average. -/
theorem stageOneMean_div (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (value : LState → ℝ≥0∞) (scale : ℝ≥0∞) :
    stageOneMean adversary parameter (fun oracle => value oracle / scale) =
      stageOneMean adversary parameter value / scale := by
  unfold stageOneMean
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]

/-- A finite sum commutes with the average. -/
theorem stageOneMean_sum {Site : Type} [Fintype Site] (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (value : Site → LState → ℝ≥0∞) :
    stageOneMean adversary parameter (fun oracle => ∑ site, value site oracle) =
      ∑ site, stageOneMean adversary parameter (value site) := by
  unfold stageOneMean
  simp only [Finset.mul_sum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun first => ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]

/-- **The average of the site entries is at most `q₁`.** Plan B's stage 1 leaves the empty
oracle, and the adversary's first stage adds at most `q₁` site entries. -/
theorem stageOneMean_siteUse_le (adversary : PlanBAdversary Unit) (parameter : ℕ) :
    stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
  unfold stageOneMean
  calc (∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
          (some first) * ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
            first.2.2) chosen * (siteUse chosen.2 : ℝ≥0∞))
      ≤ ∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
          (some first) * (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun first => ?_
        by_cases zero : (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
            (some first) = 0
        · rw [zero, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          -- stage 1 of Plan B leaves the empty oracle
          have member : some first ∈ ((planBAbstractSimulator idealSamplers).stage1 parameter
              LazyOracle.empty).support := (PMF.mem_support_iff _ _).mpr zero
          obtain ⟨source, _, sourceEq⟩ := (PMF.mem_support_map_iff _ _ _).mp member
          have emptyOracle : first.2.2 = LazyOracle.empty := by
            cases source with
            | none => cases sourceEq
            | some source =>
                simp only [Option.map_some] at sourceEq
                rw [← Option.some.inj sourceEq]
          calc (∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
                  first.2.2) chosen * (siteUse chosen.2 : ℝ≥0∞))
              ≤ ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 ())
                  first.2.2) chosen * (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
                refine ENNReal.tsum_le_tsum fun chosen => ?_
                by_cases chosenZero : (LazyOracle.run (adversary.chooseInput parameter first.1 ())
                    first.2.2) chosen = 0
                · rw [chosenZero, zero_mul, zero_mul]
                · refine mul_le_mul_of_nonneg_left ?_ zero_le
                  have bound := run_siteUse_le (adversary.chooseInput parameter first.1 ())
                    first.2.2 chosen ((PMF.mem_support_iff _ _).mpr chosenZero)
                  rw [emptyOracle, siteUse_empty, Nat.zero_add] at bound
                  exact_mod_cast bound
            _ = (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
                rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ 1 * (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right]
        gcongr
        exact stageOne_mass_le parameter
    _ = (adversary.firstQueryBudget parameter : ℝ≥0∞) := one_mul _

/-- **`I^U` against `I`, as a distance**: `#MaskSite · δ₃` plus the average stage-1 site entries
over `2^128`. -/
theorem idealUniform_etvDist_le (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    (abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter scalar
        ()).etvDist (planBIdealGame idealSamplers adversary parameter scalar ()) ≤
      (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞)) / 2 ^ 128 := by
  have game : (abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter
      scalar ()).etvDist (planBIdealGame idealSamplers adversary parameter scalar ()) ≤
      stageOneMean adversary parameter (fun oracle => (Fintype.card MaskSite : ℝ≥0∞) *
        Kriterion.ArgoMAC.Security.Phase3.delta3 + potential ∅ oracle / 2 ^ 128) :=
    abstractIdealGame_stage2_etvDist_le Scheme.scheme
      (planBAbstractSimulator idealSamplers) (refillStage2 idealSamplers)
      (fun oracle => (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        potential ∅ oracle / 2 ^ 128)
      (refillStage2_etvDist_le idealSamplers) adversary parameter scalar ()
  have split := stageOneMean_add_const_le adversary parameter
    ((Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3)
    (fun oracle => potential ∅ oracle / 2 ^ 128)
  have divided := stageOneMean_div adversary parameter (fun oracle => potential ∅ oracle) (2 ^ 128)
  have emptyEq : (fun oracle => potential ∅ oracle) = fun oracle => (siteUse oracle : ℝ≥0∞) :=
    funext potential_empty
  rw [divided, emptyEq] at split
  exact le_trans game split

end Mean

/-! ### P3's statement -/

/-- P3's `δ₃` is P1's, as a real number. -/
theorem delta3_eq_toReal :
    delta3 = Kriterion.ArgoMAC.Security.Phase3.delta3.toReal := by
  rw [delta3, Kriterion.ArgoMAC.Security.Phase3.delta3,
    Kriterion.ArgoMAC.Security.Phase3.reductionResidue, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- P1's `δ₃` is finite. -/
theorem delta3_ne_top : Kriterion.ArgoMAC.Security.Phase3.delta3 ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)

set_option maxRecDepth 8000 in
/-- **`MaskSwapBound.idealPerMask`**, verbatim with `hybrids.idealUniform := idealUniformHybrid`:
the lazy refill `I^U → I`, charged per derived mask (`δ₃`) and per stage-1 entry at the mask's
indices. -/
theorem idealPerMask : ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ (Site : Type) (_ : Fintype Site) (count : Site → ℝ),
        Fintype.card Site ≤ scaleMaskCount ∧ (∀ site, 0 ≤ count site) ∧
        ∑ site, count site ≤ (adversary.firstQueryBudget parameter : ℝ) ∧
        Assumptions.advantage
            (atSolution idealUniformHybrid field group adversary parameter scalar)
            (atSolution idealHybrid field group adversary parameter scalar) ≤
          ∑ site, (delta3 + count site * refillQueryCharge (adversary.firstQueryBudget parameter)) := by
  intro field group adversary parameter scalar small
  let _ : DecidableEq FixedIndex := Classical.decEq _
  let _ : DecidableEq EncPRF.PermutationIndex := Classical.decEq _
  -- the per-site mean entries, and their total
  let entries : MaskSite → LState → ℝ≥0∞ := fun site oracle =>
    ∑ block : Fin 3, (((oracle.fixed (siteIndex (site, block))).used : ℕ) : ℝ≥0∞)
  let mean : MaskSite → ℝ≥0∞ := fun site => stageOneMean adversary parameter (entries site)
  have total : ∑ site, mean site =
      stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞)) := by
    rw [← stageOneMean_sum]
    refine congrArg (stageOneMean adversary parameter) (funext fun oracle => ?_)
    show (∑ site : MaskSite, ∑ block : Fin 3,
        (((oracle.fixed (siteIndex (site, block))).used : ℕ) : ℝ≥0∞)) =
      ((∑ cell : Cell, (oracle.fixed (siteIndex cell)).used : ℕ) : ℝ≥0∞)
    rw [Nat.cast_sum, Fintype.sum_prod_type]
  have totalLe := stageOneMean_siteUse_le adversary parameter
  have totalFinite : stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) totalLe
  have meanFinite : ∀ site, mean site ≠ ⊤ := by
    intro site
    refine ne_top_of_le_ne_top totalFinite ?_
    rw [← total]
    exact Finset.single_le_sum (f := mean) (fun _ _ => zero_le) (Finset.mem_univ site)
  have countSum : ∑ site, (mean site).toReal =
      (stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞))).toReal := by
    rw [← total, ENNReal.toReal_sum fun site _ => meanFinite site]
  refine ⟨MaskSite, inferInstance, fun site => (mean site).toReal, ?_, ?_, ?_, ?_⟩
  · rw [card_maskSite]
    unfold scaleMaskCount
    norm_num
  · exact fun _ => ENNReal.toReal_nonneg
  · rw [countSum]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) totalLe
    rwa [ENNReal.toReal_natCast] at this
  · -- the distance, in the challenge's currency
    have room := room_le (adversary.firstQueryBudget parameter) (by omega)
    have chargeLower : (1 : ℝ) / 2 ^ 128 ≤ refillQueryCharge (adversary.firstQueryBudget parameter) := by
      unfold refillQueryCharge
      have positive : (0 : ℝ) < 2 ^ 128 - (adversary.firstQueryBudget parameter : ℝ) := by
        have : (0 : ℝ) < 2 ^ 127 := by norm_num
        linarith
      have : (0 : ℝ) ≤ 1 / (2 ^ 128 - (adversary.firstQueryBudget parameter : ℝ)) :=
        le_of_lt (one_div_pos.mpr positive)
      linarith
    have distance := @idealUniform_etvDist_le field group (Classical.decEq _) (Classical.decEq _)
      adversary parameter scalar
    show Assumptions.advantage
        (abstractIdealGame Scheme.scheme (refillSimulator idealSamplers) adversary parameter scalar ())
        (planBIdealGame idealSamplers adversary parameter scalar ()) ≤ _
    rw [advantage_eq_etvDist]
    have finiteRight : (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        stageOneMean adversary parameter (fun oracle => (siteUse oracle : ℝ≥0∞)) / 2 ^ 128 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) delta3_ne_top,
        ENNReal.div_ne_top totalFinite (by simp)⟩
    refine le_trans (ENNReal.toReal_mono finiteRight distance) ?_
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) delta3_ne_top)
        (ENNReal.div_ne_top totalFinite (by simp)),
      ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ← delta3_eq_toReal, ← countSum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
    have countNonneg : (0 : ℝ) ≤ ∑ site, (mean site).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have perEntry : (∑ site, (mean site).toReal) / 2 ^ 128 ≤
        (∑ site, (mean site).toReal) * refillQueryCharge (adversary.firstQueryBudget parameter) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left chargeLower countNonneg
    linarith

/-- **P3's `H_swap`, whole**: P1's `G0 → G0U` (`maskSwapBound_real`) and the lazy refill
(`idealPerMask`), for any `Hybrids` whose `maskSwapped` is P1's `maskSwappedHybrid` and whose
`idealUniform` is `idealUniformHybrid`. -/
theorem maskSwapBound_of (hybrids : Hybrids)
    (swapped : @Hybrids.maskSwapped hybrids = @maskSwappedHybrid)
    (uniform : @Hybrids.idealUniform hybrids = @idealUniformHybrid) : MaskSwapBound hybrids := by
  obtain ⟨maskSwapped, hiddenDeleted, publicFirst, opened, idealUniform⟩ := hybrids
  dsimp only at swapped uniform
  subst swapped uniform
  exact ⟨maskSwapBound_real, idealPerMask⟩

end

end Kriterion.ArgoMAC.Phase3.Lazy
