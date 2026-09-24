/-
**Phase 3, P1j — the lift, part 2: the designed hop (P1i's "V2", as a separate hop), at the Glue's
constant.**

P1i found that off the curve `G1U` installs *coincidence* entries — garbler entries its reach meets
at points the adversary cannot locate (system B and the gadget whitened with the tape's
`hash(t_eval)`) — of total mass `≈ 2^-117`, and on the curve the gadget's label collisions
(`pad₀ ⊕ pad₁ = Δ`, `≈ 2^-119`). None of them fits the flag budget of `M'`, and mirroring them
exactly (P1i's "V1") needs the hidden world's conditional law. **P1j removes all of them by one
identical-until-bad hop** and lifts against the coincidence-free game:

* `G1U° := hiddenDeletedWith designedInstall` — `G1U` with the **designed** entries of the hidden
  hop (`designedRule`, index-based: inactive fold parents and switches, agreeing gadget positions,
  system B and `hash(t)` only on the curve) installed at the input choice, instead of the reach's;
* **`G1U → G1U°`** costs the mass of the coincidence event `visible ≠ designed` under `G1U`'s stage 1
  (`hop_advantage_le`, `advantage_le_of_agree`); the obligation `CoincidenceBound coincidenceError`
  asks it below `coincidenceError = 2^16/2^128` (≈ 2540 label-coincidence groups of `≤ 2^-127` each;
  grouping by label, not by reach query, is what keeps it small);
* **`G1U° → HW`** is the overlap of P1g/P1i with `M'` against `g1uLaterWith designedInstall`
  (`below_laterWith`), its flag mass from P1k's `PerPairBound`/`RevealBound` (unchanged), and a
  **refined** mask-tape distance: off the curve the designed shadow's fill reads only system A's
  `127 · 4 · 5 = 2540` masks, so the two readings of `M'` are within `2540·δ₃`
  (`offCurveSites`; proved for the designed shadow in `LiftTV.lean`), not `N·δ₃`;
* **the budget closes**: `coincidenceError + 2540·δ₃ ≤ N·δ₃ = maskSwapError`
  (`coincidence_slack`: `2^272 ≤ 416052 · (2^384 mod p)`, a `decide` on ℕ).

`planB_publicFirst_of_designed`: the Glue's `publicFirst` field, at its constant
`stageOneHitError q₁ + exceptionalError + maskSwapError`, from `ShadowObligationDesigned` (the lift
against `G1U°`, the two (B) bounds, the refined distance) and `CoincidenceBound`.
-/

import Proof.Privacy.Phase3.PublicFirst.Lift
import Proof.Privacy.Phase3.Hidden.Designed
import Proof.Privacy.Phase3.Hidden.Containment

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option exponentiation.threshold 500

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source HybridGame atSolution
  GameCoreUntilBad stageOneHitError exceptionalError maskSwapError)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape uniformMaskTape)
open scoped ENNReal

noncomputable section

/-! ### 1. Two continuations that agree off an event -/

theorem bind_le_add_bad {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) (b : Bool) :
    (μ.bind f) b ≤ (μ.bind g) b + μ.toOuterMeasure bad := by
  rw [PMF.bind_apply, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases inside : a ∈ bad
  · rw [Set.indicator_of_mem inside]
    exact le_trans (mul_le_of_le_one_right' (PMF.coe_le_one _ _)) le_add_self
  · rw [Set.indicator_of_notMem inside, add_zero, agree a inside]

/-- **Identical until bad**: two continuations of one law that agree off an event are within its
mass. -/
theorem advantage_le_of_agree {A : Type} (μ : PMF A) (f g : A → PMF Bool) (bad : Set A)
    (agree : ∀ a, a ∉ bad → f a = g a) :
    Assumptions.advantage (μ.bind f) (μ.bind g) ≤ (μ.toOuterMeasure bad).toReal := by
  have finite : μ.toOuterMeasure bad ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [PMF.toOuterMeasure_apply]
    exact le_trans (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self bad (⇑μ) a)
      (le_of_eq μ.tsum_coe)
  have one := bind_le_add_bad μ f g bad agree true
  have two := bind_le_add_bad μ g f bad (fun a outside => (agree a outside).symm) true
  have r1 : ((μ.bind f) true).toReal ≤ ((μ.bind g) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) one
  have r2 : ((μ.bind g) true).toReal ≤ ((μ.bind f) true).toReal + (μ.toOuterMeasure bad).toReal := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) finite]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, finite⟩) two
  unfold Assumptions.advantage
  rw [abs_le]
  constructor <;> linarith

/-! ### 2. `G1U°` and the hop `G1U → G1U°` -/

section Designed

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designed rule as an installation rule**: the garbler's non-EncPRF entries that
`designedRule` keeps at the input (`designedEntries_eq`: exactly the hidden hop's designed
entries). -/
def designedInstall : InstallRule := fun scalar tape _ input _ =>
  (garblerTranscript scalar tape).filter fun entry =>
    !entry.IsEnc && designedRule scalar tape input entry

/-- The reach's rule (`G1U`'s own). -/
def visibleInstall : InstallRule := fun scalar tape table input labels =>
  visibleEntries scalar tape table input labels

/-- The designed rule is the hidden hop's designed entries. -/
theorem designedInstall_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
        (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) =
      designedEntries designedRule parameter scalar tape input :=
  (designedEntries_eq parameter scalar tape input).symm

/-- `G1U`'s stage 1: the tape and the adversary's stage-1 outcome on the EncPRF entries. -/
def stageOneLaw (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    PMF ((Coins × Oracle) × ((AffineInput × adversary.State) × LState)) :=
  swappedChallengeTape.bind fun tape =>
    (LazyOracle.run (adversary.chooseInput parameter (Scheme.scheme.garble parameter scalar tape).1 ())
        (installAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty)).map
      fun selected => (tape, selected)

/-- `G1U`'s stage 2 read with a rule. -/
def stageTwoWith (installed : InstallRule) (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (x : (Coins × Oracle) × ((AffineInput × adversary.State) × LState)) :
    PMF Bool :=
  (LazyOracle.run (adversary.decide parameter (Scheme.scheme.garble parameter scalar x.1).1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) () x.2.1.2)
    (installAll (installed scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1)) x.2.2)).map
    Prod.fst

theorem hiddenDeletedWith_eq (installed : InstallRule) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar) :
    hiddenDeletedWith installed adversary parameter scalar =
      (stageOneLaw adversary parameter scalar).bind (stageTwoWith installed adversary parameter scalar) := by
  unfold hiddenDeletedWith stageOneLaw
  rw [PMF.bind_bind]
  congr 1
  funext tape
  rw [PMF.bind_map]
  rfl

/-- **The coincidence event** at an input: the reach meets a garbler entry the designed rule hides
(the reach's entries are not the designed ones). -/
def Coincide (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput) :
    Prop :=
  visibleInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) ≠
    designedInstall scalar tape (Scheme.scheme.garble parameter scalar tape).1 input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)

/-- Its mass under `G1U`'s stage 1 (the input is the adversary's). -/
def coincidenceMass (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    ℝ≥0∞ :=
  (stageOneLaw adversary parameter scalar).toOuterMeasure
    {x | Coincide parameter scalar x.1 x.2.1.1}

/-- **The hop `G1U → G1U°`**: identical until a coincidence. -/
theorem hop_advantage_le (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    Assumptions.advantage (hiddenDeletedHybrid adversary parameter scalar)
        (hiddenDeletedWith designedInstall adversary parameter scalar)
      ≤ (coincidenceMass adversary parameter scalar).toReal := by
  rw [← hiddenDeletedWith_visible, show (fun scalar tape table input labels =>
      visibleEntries scalar tape table input labels) = (visibleInstall : InstallRule) from rfl,
    hiddenDeletedWith_eq, hiddenDeletedWith_eq]
  refine advantage_le_of_agree _ _ _ _ fun x outside => ?_
  have same : visibleInstall scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) =
    designedInstall scalar x.1 (Scheme.scheme.garble parameter scalar x.1).1 x.2.1.1
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar x.1).2 x.2.1.1) := by
    by_contra different
    exact outside different
  unfold stageTwoWith
  rw [same]

end Designed

/-! ### 3. The obligations and the constant -/

/-- `G1U°` as a chain game. -/
def hiddenDesignedHybrid : HybridGame := fun adversary parameter scalar =>
  hiddenDeletedWith designedInstall adversary parameter scalar

/-- The coincidence allowance: `2^16` label-coincidence groups at `2^-128` each. -/
def coincidenceError : ℝ := 2 ^ 16 / 2 ^ 128

/-- The mask sites the designed off-curve shadow's fill may read: system A's,
`127` chunks × `4` switches × `3 + 2` curve elements (`LiftTV.card_curveSite`). -/
def offCurveSites : ℕ := 2540

/-- **The coincidence bound**: under `G1U`'s stage 1 (the adversary's input), the reach meets a
hidden garbler entry with mass at most `error`. -/
def CoincidenceBound (error : ℝ) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
       letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
       letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
       letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
       coincidenceMass adversary parameter scalar).toReal ≤ error

/-- **The lift's obligation against `G1U°`**: a shadow whose `M'` is below `g1uLater°` (the F4 lift
at the designed rule), with P1k's two (B) bounds, and whose two tape readings are within
`offCurveSites · δ₃`. -/
def ShadowObligationDesigned : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ shadow : Shadow,
        (letI := field
         letI := group
         letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
         letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
         letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
         letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
         FlagMono (g1uLaterWith designedInstall adversary parameter scalar)
             (middleGameFill uniformMaskTape shadow adversary parameter scalar) ∧
           PerPairBound shadow scalar (4 / 2 ^ 128) ∧
           RevealBound shadow scalar (ENNReal.ofReal exceptionalError) ∧
           (middleGameFill uniformMaskTape shadow adversary parameter scalar).etvDist
               (middleGameFill (PMF.uniformOfFintype Tape) shadow adversary parameter scalar)
             ≤ (offCurveSites : ℝ≥0∞) * delta3)

/-- **The budget closes**: the coincidence allowance and the refined distance fit in `N·δ₃`. -/
theorem coincidence_slack :
    coincidenceError + ((offCurveSites : ℝ≥0∞) * delta3).toReal ≤ maskSwapError := by
  have residue : (2 : ℕ) ^ 272 ≤ 416052 * (2 ^ 384 % baseFieldModulus) := by
    unfold baseFieldModulus
    decide
  have residueReal : (2 : ℝ) ^ 272 ≤ 416052 * ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) := by
    exact_mod_cast residue
  have tvEq : ((offCurveSites : ℝ≥0∞) * delta3).toReal =
      2540 * ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) / 2 ^ 384 := by
    rw [ENNReal.toReal_mul, delta3, reductionResidue, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    unfold offCurveSites
    push_cast
    ring
  rw [tvEq]
  unfold coincidenceError maskSwapError Kriterion.ArgoMAC.Phase3.Glue.scaleMaskCount
  have split : (2 : ℝ) ^ 16 / 2 ^ 128 = 2 ^ 272 / 2 ^ 384 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    norm_num
  rw [split, ← add_div, div_le_div_iff_of_pos_right (by positivity)]
  generalize ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) = residueValue at residueReal ⊢
  push_cast
  linarith

/-! ### 4. The assembly -/

/-- **The Glue's `publicFirst` at its constant, through `G1U°`.** -/
theorem planB_publicFirst_of_designed (obligation : ShadowObligationDesigned)
    (coincidence : CoincidenceBound coincidenceError) :
    GameCoreUntilBad Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        stageOneHitError first + exceptionalError + maskSwapError := by
  intro field group adversary parameter scalar small
  obtain ⟨shadow, mono, perPair, reveal, tv⟩ := obligation field group adversary parameter scalar small
  have coincidenceLe := coincidence field group adversary parameter scalar small
  letI := field
  letI := group
  letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
  letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  have hop := hop_advantage_le adversary parameter scalar
  have belowDesigned : Below (hiddenDeletedWith designedInstall adversary parameter scalar)
      (middleGameFill uniformMaskTape shadow adversary parameter scalar) :=
    (below_laterWith designedInstall adversary parameter scalar).trans mono
  have belowHW : Below (atSolution publicFirstHybrid field group adversary parameter scalar)
      (middleGameFill (PMF.uniformOfFintype Tape) shadow adversary parameter scalar) := by
    rw [middleFill_uniform_eq]
    exact middle_below shadow adversary parameter scalar
  have overlap := advantage_le_of_overlap_tv belowDesigned belowHW
  have mass := middleFill_mass_le shadow adversary parameter scalar perPair reveal
  have finite : (offCurveSites : ℝ≥0∞) * delta3 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp))
  have tvReal := ENNReal.toReal_mono finite tv
  have slack := coincidence_slack
  refine Kriterion.ArgoMAC.Security.Phase3.coreUntilBad_iff.mpr ?_
  have triangle : Assumptions.advantage
      (atSolution hiddenDeletedHybrid field group adversary parameter scalar)
      (atSolution publicFirstHybrid field group adversary parameter scalar) ≤
    Assumptions.advantage (hiddenDeletedHybrid adversary parameter scalar)
        (hiddenDeletedWith designedInstall adversary parameter scalar) +
      Assumptions.advantage (hiddenDeletedWith designedInstall adversary parameter scalar)
        (atSolution publicFirstHybrid field group adversary parameter scalar) := by
    unfold Assumptions.advantage
    exact abs_sub_le _ _ _
  refine le_trans triangle (le_trans (add_le_add (hop.trans coincidenceLe)
    (overlap.trans (add_le_add mass tvReal))) ?_)
  linarith [slack]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
