/-
**Phase 3, P4 — the `I^U` opening against `I`'s: `N·δ₃` plus `1/2^128` per stage-1 entry.**

* `runRefill_uniform_etvDist_le` — fresh uniform limbs against the lazy oracle, for any query
  computation: at most `potential touched oracle / 2^128` (the potential induction of
  `StepBound`).
* `refillRun_etvDist_le` — the `I^U` run (mask tape) against `runIntercept`:
  `#MaskSite · δ₃ + potential ∅ oracle / 2^128` (tape bias, eager = lazy, the induction).
* `refillStage2_etvDist_le` — the same bound for the two stage-2 kernels: the rest of the opening
  (tail, lifts, targets, preimages, the 819 designated programs) is a common continuation.
-/

import Proof.Privacy.Phase3.Lazy.StepBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **One consumed query, with its continuations.** Programming a fresh uniform limb (abort on a
used output) and continuing with `R`, against the lazy query continuing with `R'`: the step costs
`used / 2^128`, the continuations at most `c` on the lazy support. -/
theorem consume_bind_etvDist_le {γ : Type} (oracle : LState) (index : FixedIndex) (input : Block)
    (fresh : ¬ (oracle.fixed index).knownInput input.toFin)
    (R R' : Block → LState → PMF (Option γ)) (c : ℝ≥0∞)
    (close : ∀ answer ∈ (LazyOracle.query (.fixedForward index input) oracle).support,
      (R answer.1 answer.2).etvDist (R' answer.1 answer.2) ≤ c) :
    ((PMF.uniformOfFintype Block).bind fun limb =>
        match LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle with
        | none => PMF.pure none
        | some updated => R (limb ^^^ input) updated).etvDist
      ((LazyOracle.query (.fixedForward index input) oracle).bind fun answer =>
        R' answer.1 answer.2) ≤
      (((oracle.fixed index).used : ℕ) : ℝ≥0∞) / 2 ^ 128 + c := by
  let A : PMF (Option (Block × LState)) := (PMF.uniformOfFintype Block).map fun limb =>
    (LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle).map
      fun updated => (limb ^^^ input, updated)
  let B : PMF (Option (Block × LState)) :=
    (LazyOracle.query (.fixedForward index input) oracle).map some
  let K : Option (Block × LState) → PMF (Option γ) := fun step => match step with
    | none => PMF.pure none
    | some step => R step.1 step.2
  let K' : Option (Block × LState) → PMF (Option γ) := fun step => match step with
    | none => PMF.pure none
    | some step => R' step.1 step.2
  have leftEq : ((PMF.uniformOfFintype Block).bind fun limb =>
      match LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle with
      | none => PMF.pure none
      | some updated => R (limb ^^^ input) updated) = A.bind K := by
    rw [PMF.bind_map]
    congr 1
    funext limb
    show _ = K ((LazyOracle.program (.fixedForward index input) (limb ^^^ input)
      oracle).map fun updated => (limb ^^^ input, updated))
    cases LazyOracle.program (.fixedForward index input) (limb ^^^ input) oracle <;> rfl
  have rightEq : ((LazyOracle.query (.fixedForward index input) oracle).bind fun answer =>
      R' answer.1 answer.2) = B.bind K' :=
    (PMF.bind_map (LazyOracle.query (.fixedForward index input) oracle) some K').symm
  rw [leftEq, rightEq]
  have remaining : ∀ step ∈ B.support, (K step).etvDist (K' step) ≤ c := by
    intro step member
    obtain ⟨answer, answerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact close answer answerMember
  calc (A.bind K).etvDist (B.bind K')
      ≤ (A.bind K).etvDist (B.bind K) + (B.bind K).etvDist (B.bind K') :=
        PMF.etvDist_triangle _ _ _
    _ ≤ (((oracle.fixed index).used : ℕ) : ℝ≥0∞) / 2 ^ 128 + c :=
        add_le_add (le_trans (PMF.etvDist_bind_right_le K A B)
          (consume_step_etvDist_le oracle index input fresh))
          (etvDist_bind_le_of_support B K K' _ remaining)

/-- **Fresh uniform limbs against the lazy oracle**, for any query computation: the distance is at
most the untouched mask-site entries over `2^128`. -/
theorem runRefill_uniform_etvDist_le (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      (runRefill bits (fun _ => PMF.uniformOfFintype Block) computation oracle record
          touched).etvDist ((runIntercept bits computation oracle record).map some) ≤
        potential touched oracle / 2 ^ 128 := by
  induction computation with
  | pure value =>
      intro oracle record touched
      simp only [runRefill, runIntercept, PMF.pure_map, PMF.etvDist_self]
      exact zero_le
  | query request next ih =>
      intro oracle record touched
      simp only [runRefill, runIntercept]
      split
      · rename_i answer intercepted
        simp only [intercepted]
        exact ih _ _ _ _
      · rename_i intercepted
        simp only [intercepted]
        split
        · rename_i cell consumed
          obtain ⟨index, input, rfl, notTouched, fresh, site⟩ := consumeCell_spec consumed
          rw [PMF.map_bind]
          have usedLe : (((oracle.fixed index).used : ℕ) : ℝ≥0∞) ≤ potential touched oracle := by
            rw [potential_consume touched oracle oracle cell index input notTouched site
              fun _ _ => rfl]
            exact le_self_add
          refine le_trans (consume_bind_etvDist_le oracle index input fresh
            (fun answer updated => runRefill bits (fun _ => PMF.uniformOfFintype Block)
              (next answer) updated record (touch (.fixedForward index input) touched))
            (fun answer updated => (runIntercept bits (next answer) updated record).map some)
            ((potential touched oracle - (((oracle.fixed index).used : ℕ) : ℝ≥0∞)) / 2 ^ 128)
            ?_) (le_of_eq ?_)
          · intro answer member
            have split := potential_consume touched oracle answer.2 cell index input notTouched
              site fun other different => query_frame _ oracle answer member other
                fun same => different (Option.some.inj same).symm
            have rest : potential (touch (.fixedForward index input) touched) answer.2 =
                potential touched oracle - (((oracle.fixed index).used : ℕ) : ℝ≥0∞) := by
              rw [split, ENNReal.add_sub_cancel_left (ENNReal.natCast_ne_top _)]
            rw [← rest]
            exact ih _ _ _ _
          · rw [ENNReal.div_add_div_same, add_tsub_cancel_of_le usedLe]
        · rw [PMF.map_bind]
          refine etvDist_bind_le_of_support _ _ _ _ fun answer member => ?_
          refine le_trans (ih _ _ _ _) ?_
          exact ENNReal.div_le_div_right (potential_touch_le request touched oracle answer.2
            fun other different => query_frame request oracle answer member other different) _

/-- **The `I^U` run against `I`'s**: the tape bias `#MaskSite · δ₃` plus one `1/2^128` per
stage-1 entry at a mask-site index. -/
theorem refillRun_etvDist_le (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) (oracle : LState) :
    (refillRun bits computation oracle).etvDist
        ((runIntercept bits computation oracle fun _ => none).map some) ≤
      (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        potential ∅ oracle / 2 ^ 128 := by
  refine le_trans (PMF.etvDist_triangle _ ((PMF.uniformOfFintype Tape).bind fun tape =>
    runRefill bits (fun cell => PMF.pure (tape cell)) computation oracle (fun _ => none) ∅) _) ?_
  refine add_le_add (le_trans (PMF.etvDist_bind_right_le _ _ _) uniformMaskTape_etvDist_le) ?_
  rw [uniform_bind_runRefill]
  exact runRefill_uniform_etvDist_le bits computation oracle _ ∅

/-- **The `I^U` opening against `I`'s.** -/
theorem refillOpening_etvDist_le [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (table : Public) (input : AffineInput) (labels : LamportSignature) (target : Point)
    (oracle : LState) :
    (refillOpening samplers table input labels target oracle).etvDist
        (opening samplers table input labels target oracle) ≤
      (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        potential ∅ oracle / 2 ^ 128 := by
  let K := fun ran : Option (((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)) × LState × Record) => match ran with
    | none => PMF.pure none
    | some ran => openingCont samplers table input labels target ran
  have openingForm : opening samplers table input labels target oracle =
      ((runIntercept (Lamport.restore input labels).input
          (openingQueriesM table (Lamport.restore input labels).input
            (Lamport.restore input labels).inputMac) oracle fun _ => none).map some).bind K := by
    rw [opening_eq, PMF.bind_map]
    rfl
  rw [openingForm]
  exact le_trans (PMF.etvDist_bind_right_le K _ _) (refillRun_etvDist_le _ _ oracle)

/-- **The two stage-2 kernels.** -/
theorem refillStage2_etvDist_le [FieldCertificate] [GroupCertificate] (samplers : Samplers)
    (source : Stage1Source) (input : AffineInput) (output : Option Point) (oracle : LState) :
    (refillStage2 samplers source input output oracle).etvDist
        ((planBAbstractSimulator samplers).stage2 source input output oracle) ≤
      (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 +
        potential ∅ oracle / 2 ^ 128 := by
  cases output with
  | none =>
      simp only [refillStage2, planBAbstractSimulator, PMF.etvDist_self]
      exact zero_le
  | some target =>
      exact le_trans (PMF.etvDist_map_le _ _ _) (refillOpening_etvDist_le _ _ _ _ _ _)

end

end Kriterion.ArgoMAC.Phase3.Lazy
