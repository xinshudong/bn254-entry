/-
**Phase 3, P4 — `H → I^U` reduced to the key-averaged installation-failure mass.**

`H` (P1b's `openedHybrid`) and `I^U` (`idealUniformHybrid`, which is the opened game at
`abortInstallation`, `idealUniformHybrid_eq_opened`) differ only in the designated installation:
`H` skips a failed program, `I^U` aborts.

* `programAllSkip_of_programAll` — **`H = I^U` off the abort event**: when every program succeeds,
  skipping installs exactly the same oracle.
* `openedStage2_etvDist_le` — the two stage-2 kernels are within the **installation-failure mass**
  `failMass` (the mass of the installation inputs on which `Glue.programAll` returns `none`).
* `abstractIdealGame_stage2_etvDist_le'` — swapping stage 2 costs the prefix average of a bound
  that may depend on the retained state (the source, hence the Lamport key), the input and the
  output.
* `stageOne_key_average` — the prefix average with the key averaged separately: stage 1 publishes
  `publicValue`, which does not read the key, so the key is uniform and independent of the
  adversary's first stage.

The per-prefix analysis is the named hypothesis `KeyAveragedFailBound`. Given it,
`abortBound_perQuery'_of` proves the restated `AbortBound.perQuery`
(`AbortPerQuery'`: sites = `AbortSite`, per-query charge `Glue.abortQueryCharge q₁`).
-/

import Proof.Privacy.Phase3.Opened
import Proof.Privacy.Phase3.Lazy.IdealPerMask
import Proof.Privacy.Phase3.Lazy.FoldEntropy

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle (SparsePermutation)
open Kriterion.ArgoMAC.Security.Phase3 (openedSimulator openedCont openedOpening skipInstallation
  abortInstallation programAllSkip simulatedRows openedHybrid idealUniformHybrid_eq_opened
  RowsKernel Installation advantage_eq_etvDist)
open scoped ENNReal

noncomputable section

/-! ### The broadened abort sites -/

/-- **The indices an abort may be billed to**: the scale indices of chunk `0` of lanes `pointX`
(which contain the `4·819` candidate designated indices, and the free elements read at `E*`) and
`curveX`, and the level-1 fold indices of chunk `0` of the same two lanes. -/
def IsAbortIndex : FixedIndex → Prop
  | .scale lane chunk _ _ _ => (lane = .pointX ∨ lane = .curveX) ∧ chunk = chunkZero
  | .hot lane chunk fold _ _ => (lane = .pointX ∨ lane = .curveX) ∧ chunk = chunkZero ∧ fold.val = 1
  | .gadget _ _ _ => False

/-- **An abort site**: a fixed-key index an abort may be billed to. -/
abbrev AbortSite := {index : FixedIndex // IsAbortIndex index}

noncomputable instance abortSiteFintype : Fintype AbortSite := Fintype.ofFinite _

/-- A candidate designated index is an abort site. -/
theorem candidateIndex_isAbort (site : CandidateSite) : IsAbortIndex (candidateIndex site) := by
  simp [candidateIndex, scaleIndexOf, scaleIndexNat, IsAbortIndex]

/-- **The restated `AbortBound.perQuery`**: `H → I^U`, charged per stage-1 query at an abort site. -/
def AbortPerQuery' (opened idealUniform : HybridGame) : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∃ count : AbortSite → ℝ, (∀ site, 0 ≤ count site) ∧
        ∑ site, count site ≤ (adversary.firstQueryBudget parameter : ℝ) ∧
        Assumptions.advantage (atSolution opened field group adversary parameter scalar)
            (atSolution idealUniform field group adversary parameter scalar) ≤
          ∑ site, count site * abortQueryCharge (adversary.firstQueryBudget parameter)

/-! ### `H = I^U` off the abort event -/

section Kernels

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **When every program succeeds, skipping installs the same oracle.** -/
theorem programAllSkip_of_programAll :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (oracle updated : LState),
      programAll requests oracle = some updated → programAllSkip requests oracle = updated
  | [], oracle, updated, success => by
      simp only [programAll, Option.some.injEq] at success
      exact success
  | (index, input, output) :: rest, oracle, updated, success => by
      cases input with
      | none => simp [programAll] at success
      | some input =>
          simp only [programAll] at success
          obtain ⟨middle, programmed, rest⟩ := Option.bind_eq_some_iff.mp success
          simp only [programAllSkip, programmed, Option.getD_some]
          exact programAllSkip_of_programAll _ _ _ rest

/-- The designated requests and the oracle after the refill run, the rows and the preimages; `none`
is a run or sampler abort. -/
def installInputs [FieldCertificate] [GroupCertificate] (rows : RowsKernel) (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    PMF (Option (List (FixedIndex × Option Block × Block) × LState)) :=
  let restored := Lamport.restore input labels
  (refillRun restored.input (openingQueriesM table restored.input restored.inputMac) oracle).bind
    fun ran => match ran with
    | none => PMF.pure none
    | some ran => (rows input target).bind fun targets => match targets with
      | none => PMF.pure none
      | some targets =>
        let evalRows := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
          (Pipeline.digitValues ran.1.1 ran.1.2) restored.input.toAffine
        (preimages idealSamplers (collectorTargets restored.input evalRows targets)).bind
          fun blocks => match blocks with
          | none => PMF.pure none
          | some blocks => PMF.pure (some (programRequests restored.input ran.2.2 blocks, ran.2.1))

/-- The installation step of an opened opening. -/
def installStep (install : Installation) :
    Option (List (FixedIndex × Option Block × Block) × LState) → PMF (Option LState)
  | none => PMF.pure none
  | some inputs => PMF.pure (install inputs.1 inputs.2)

/-- **The opened opening is its installation inputs, then the installation.** -/
theorem openedOpening_eq [FieldCertificate] [GroupCertificate] (rows : RowsKernel)
    (install : Installation) (table : Public) (input : AffineInput) (labels : LamportSignature)
    (target : Point) (oracle : LState) :
    openedOpening rows install table input labels target oracle =
      (installInputs rows table input labels target oracle).bind (installStep install) := by
  unfold openedOpening installInputs
  dsimp only
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun ran => ?_)
  cases ran with
  | none => simp [installStep]
  | some ran =>
      simp only [openedCont, PMF.bind_bind]
      congr 1
      funext targets
      cases targets with
      | none => simp [installStep]
      | some targets =>
          simp only [PMF.bind_bind]
          congr 1
          funext blocks
          cases blocks with
          | none => simp [installStep]
          | some blocks => simp [installStep]

/-- The installation inputs on which `I^U`'s installation aborts. -/
def FailsInstall (inputs : Option (List (FixedIndex × Option Block × Block) × LState)) : Prop :=
  ∃ requests oracle, inputs = some (requests, oracle) ∧ programAll requests oracle = none

/-- **The installation-failure mass** of the opened opening. -/
def failMass [FieldCertificate] [GroupCertificate] (table : Public) (input : AffineInput)
    (labels : LamportSignature) (target : Point) (oracle : LState) : ℝ≥0∞ :=
  (installInputs simulatedRows table input labels target oracle).toOuterMeasure
    {inputs | FailsInstall inputs}

/-- **The two openings are within the failure mass.** -/
theorem openedOpening_etvDist_le [FieldCertificate] [GroupCertificate] (table : Public)
    (input : AffineInput) (labels : LamportSignature) (target : Point) (oracle : LState) :
    (openedOpening simulatedRows skipInstallation table input labels target oracle).etvDist
        (openedOpening simulatedRows abortInstallation table input labels target oracle) ≤
      failMass table input labels target oracle := by
  classical
  rw [openedOpening_eq, openedOpening_eq]
  refine le_trans (Kriterion.ArgoMAC.Security.Phase3.etvDist_bind_left_le _ _ _) ?_
  rw [failMass, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun inputs => ?_
  rw [mul_comm, Set.indicator_apply]
  cases inputs with
  | none => simp [installStep]
  | some inputs =>
      by_cases fails : programAll inputs.1 inputs.2 = none
      · rw [if_pos ⟨inputs.1, inputs.2, rfl, fails⟩]
        exact mul_le_of_le_one_right zero_le (PMF.etvDist_le_one _ _)
      · rw [if_neg (by rintro ⟨requests, oracle', same, failed⟩; cases same; exact fails failed)]
        obtain ⟨updated, success⟩ := Option.ne_none_iff_exists'.mp fails
        simp only [installStep, skipInstallation, abortInstallation, success,
          programAllSkip_of_programAll _ _ _ success, PMF.etvDist_self, mul_zero]
        exact le_rfl

/-- **The two stage-2 kernels are within the failure mass** (`0` without an output point). -/
theorem openedStage2_etvDist_le [FieldCertificate] [GroupCertificate] (source : Stage1Source)
    (input : AffineInput) (output : Option Point) (oracle : LState) :
    ((openedSimulator simulatedRows skipInstallation).stage2 source input output oracle).etvDist
        ((openedSimulator simulatedRows abortInstallation).stage2 source input output oracle) ≤
      match output with
      | none => 0
      | some target => failMass source.publicValue input
          (Lamport.selectedLabels (source.key.encode (BitInput.ofAffine input))) target oracle := by
  cases output with
  | none => simp [openedSimulator]
  | some target =>
      exact le_trans (PMF.etvDist_map_le _ _ _) (openedOpening_etvDist_le _ _ _ _ _)

end Kernels

/-! ### Swapping stage 2, with a state-dependent bound -/

/-- **Swapping stage 2 of an abstract simulator**, with a bound depending on the retained state,
the input and the output: the games are within its prefix average. -/
theorem abstractIdealGame_stage2_etvDist_le' [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle)
    (simulator : LazyAbstractSimulator FixedIndex EncIndex Public)
    (stage2 : simulator.State → AffineInput → Option Point →
      LazyOracle.State FixedIndex EncIndex →
        PMF (Option (LamportSignature × LazyOracle.State FixedIndex EncIndex)))
    (bound : simulator.State → AffineInput → Option Point →
      LazyOracle.State FixedIndex EncIndex → ℝ≥0∞)
    (close : ∀ state input output oracle,
      (stage2 state input output oracle).etvDist (simulator.stage2 state input output oracle) ≤
        bound state input output oracle)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    (abstractIdealGame scheme { simulator with stage2 := stage2 } adversary parameter scalar
        auxiliary).etvDist
      (abstractIdealGame scheme simulator adversary parameter scalar auxiliary) ≤
      ∑' first, simulator.stage1 parameter LazyOracle.empty (some first) *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter first.1 auxiliary)
          first.2.2) chosen *
            bound first.2.1 chosen.1.1 (scheme.function scalar chosen.1.1) chosen.2 := by
  unfold abstractIdealGame
  refine le_trans (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _) ?_
  refine le_trans (optionT_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun first => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨circuit, state, oracle⟩ := first
  refine le_trans (optionT_lift_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun chosen => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨selected, chosen⟩ := chosen
  refine le_trans (optionT_bind_mk_etvDist_le _ _ _) ?_
  exact close _ _ _ _

/-! ### The key is independent of the stage-1 view -/

/-- A source with its Lamport key replaced. -/
def withKey (source : Stage1Source) (key : InputMacKey) : Stage1Source := { source with key := key }

/-- The published value does not read the key. -/
theorem publicValue_withKey (source : Stage1Source) (key : InputMacKey) :
    (withKey source key).publicValue = source.publicValue := rfl

/-- `(s, k) ↦ (s[key := k], s.key)` is a bijection. -/
def keySwap : (Stage1Source × InputMacKey) ≃ (Stage1Source × InputMacKey) where
  toFun pair := (withKey pair.1 pair.2, pair.1.key)
  invFun pair := (withKey pair.1 pair.2, pair.1.key)
  left_inv pair := by obtain ⟨source, key⟩ := pair; rfl
  right_inv pair := by obtain ⟨source, key⟩ := pair; rfl

noncomputable instance inputMacKeyFintype : Fintype InputMacKey := Fintype.ofFinite _

instance inputMacKeyNonempty : Nonempty InputMacKey := ⟨(Classical.choice inferInstance :
  Stage1Source).key⟩

/-- **A uniform source is a uniform source with an independent uniform key written in.** -/
theorem uniform_withKey :
    (PMF.uniformOfFintype Stage1Source).bind (fun source =>
        (PMF.uniformOfFintype InputMacKey).map (withKey source)) =
      PMF.uniformOfFintype Stage1Source := by
  have product := uniform_product (A := Stage1Source) (B := InputMacKey)
  have swapped : (PMF.uniformOfFintype (Stage1Source × InputMacKey)).map
      (fun pair => withKey pair.1 pair.2) = PMF.uniformOfFintype Stage1Source := by
    have factor : (fun pair : Stage1Source × InputMacKey => withKey pair.1 pair.2) =
        Prod.fst ∘ keySwap := rfl
    rw [factor, ← PMF.map_comp, uniform_equiv keySwap, uniform_map_fst]
  calc (PMF.uniformOfFintype Stage1Source).bind (fun source =>
        (PMF.uniformOfFintype InputMacKey).map (withKey source))
      = ((PMF.uniformOfFintype Stage1Source).bind fun source =>
          (PMF.uniformOfFintype InputMacKey).map fun key => (source, key)).map
            (fun pair => withKey pair.1 pair.2) := by
        rw [PMF.map_bind]
        refine congrArg _ (funext fun source => ?_)
        rw [PMF.map_comp]
        rfl
    _ = PMF.uniformOfFintype Stage1Source := by rw [product, swapped]

/-! ### Stage-1 entries at a family of indices -/

section Budget

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The lazy entries at an injective family of fixed-key indices. -/
def indexUse {S : Type} [Fintype S] (family : S → FixedIndex) (oracle : LState) : ℕ :=
  ∑ site, (oracle.fixed (family site)).used

theorem indexUse_update_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (fixed : FixedIndex → SparsePermutation (2 ^ 128))
    (index : FixedIndex) (next : SparsePermutation (2 ^ 128))
    (grow : next.used ≤ (fixed index).used + 1) :
    ∑ site, (Function.update fixed index next (family site)).used ≤
      ∑ site, (fixed (family site)).used + 1 := by
  classical
  have termwise : ∀ site, (Function.update fixed index next (family site)).used ≤
      (fixed (family site)).used + (if family site = index then 1 else 0) := by
    intro site
    by_cases same : family site = index
    · rw [same, Function.update_self, if_pos rfl]
      exact grow
    · rw [Function.update_of_ne same, if_neg same, Nat.add_zero]
  have atMostOne : (∑ site, (if family site = index then 1 else 0 : ℕ)) ≤ 1 := by
    by_cases found : ∃ named, family named = index
    · obtain ⟨named, named_eq⟩ := found
      have reindex : ∀ site, (if family site = index then 1 else 0 : ℕ) =
          if site = named then 1 else 0 := by
        intro site
        by_cases same : site = named
        · rw [if_pos same, if_pos (same ▸ named_eq)]
        · rw [if_neg same, if_neg fun equal => same (injective (equal.trans named_eq.symm))]
      rw [Finset.sum_congr rfl fun site _ => reindex site, Finset.sum_ite_eq' Finset.univ named,
        if_pos (Finset.mem_univ _)]
    · rw [Finset.sum_eq_zero fun site _ => if_neg fun hit => found ⟨site, hit⟩]
      exact Nat.zero_le _
  calc (∑ site, (Function.update fixed index next (family site)).used)
      ≤ ∑ site, ((fixed (family site)).used + (if family site = index then 1 else 0)) :=
        Finset.sum_le_sum fun site _ => termwise site
    _ = ∑ site, (fixed (family site)).used +
          ∑ site, (if family site = index then 1 else 0 : ℕ) := Finset.sum_add_distrib
    _ ≤ ∑ site, (fixed (family site)).used + 1 := Nat.add_le_add_left atMostOne _

theorem query_indexUse_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) :
    indexUse family answer.2 ≤ indexUse family oracle + 1 := by
  cases request with
  | fixedForward index input =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact indexUse_update_le family injective oracle.fixed index drawn.2
        ((oracle.fixed index).forward_used_le input.toFin drawn drawnMember)
  | fixedInverse index output =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact indexUse_update_le family injective oracle.fixed index drawn.2
        ((oracle.fixed index).inverse_used_le output.toFin drawn drawnMember)
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | hash _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _

/-- **A program with query budget `b` adds at most `b` entries at an injective index family.** -/
theorem run_indexUse_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Result budget) :
    ∀ (oracle : LState) (result : Result × LState),
      result ∈ (LazyOracle.run program oracle).support →
        indexUse family result.2 ≤ indexUse family oracle + budget := by
  induction program with
  | pure distribution =>
      intro oracle result member
      simp only [LazyOracle.run, Kriterion.ArgoMAC.Security.OperationalOracle.runSampled] at member
      obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_add_right _ _
  | query request next ih =>
      intro oracle result member
      simp only [LazyOracle.run, Kriterion.ArgoMAC.Security.OperationalOracle.runSampled] at member
      obtain ⟨answer, answerMember, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      have step := query_indexUse_le family injective request oracle answer answerMember
      have rest := ih answer.1 answer.2 result resultMember
      omega
  | sample distribution next ih =>
      intro oracle result member
      simp only [LazyOracle.run, Kriterion.ArgoMAC.Security.OperationalOracle.runSampled] at member
      obtain ⟨value, _, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih value oracle result resultMember

theorem indexUse_empty {S : Type} [Fintype S] (family : S → FixedIndex) :
    indexUse family (LazyOracle.empty : LState) = 0 :=
  Finset.sum_eq_zero fun _ _ => rfl

end Budget

/-! ### The key-averaged failure bound, and the reduction -/

/-- The stage-1 entries at the abort sites. -/
def abortUse [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] (oracle : LState) : ℕ :=
  indexUse (Subtype.val : AbortSite → FixedIndex) oracle

/-- **The per-prefix analysis (open).** For every stage-1 source (its key averaged out: the key is
uniform and independent of the published value), every selected input with an output point and
every stage-1 oracle in which each fixed-key index carries at most `q < 2^100` entries, the
installation of `I^U` fails with mass at most `abortQueryCharge q` per stage-1 entry at an abort
site. -/
def KeyAveragedFailBound : Prop :=
  ∀ [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (source : Stage1Source) (input : AffineInput)
    (target : Point) (oracle : LState) (queries : ℕ),
    queries < 2 ^ 100 → (∀ index, (oracle.fixed index).used ≤ queries) →
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
          failMass source.publicValue input
            (Lamport.selectedLabels (key.encode (BitInput.ofAffine input))) target oracle ≤
        ENNReal.ofReal (abortQueryCharge queries) * (abortUse oracle : ℝ≥0∞)


/-! ### The reduction -/

/-- A sum against a bound law is the iterated sum. -/
theorem tsum_bind_mul {α β : Type} (p : PMF α) (f : α → PMF β) (value : β → ℝ≥0∞) :
    ∑' b, (p.bind f) b * value b = ∑' a, p a * ∑' b, f a b * value b := by
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * f a b) * value b = ∑' b, ∑' a, p a * f a b * value b :=
        tsum_congr fun b => ENNReal.tsum_mul_right.symm
    _ = ∑' a, ∑' b, p a * f a b * value b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * value b := tsum_congr fun a => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => by ring

/-- A sum against a mapped law is a sum against the law. -/
theorem tsum_map_mul {α β : Type} (p : PMF α) (g : α → β) (value : β → ℝ≥0∞) :
    ∑' b, (p.map g) b * value b = ∑' a, p a * value (g a) := by
  rw [← PMF.bind_pure_comp, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  rw [tsum_eq_single (g a)]
  · simp
  · intro other different
    simp [Function.comp_apply, PMF.pure_apply, different]

section Reduction

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The stage-1 draw collapses onto the source.** -/
theorem stage1_collapse (parameter : ℕ) (value : Public × Stage1Source × LState → ℝ≥0∞) :
    ∑' first, (planBAbstractSimulator idealSamplers).stage1 parameter LazyOracle.empty
        (some first) * value first =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        value (source.publicValue, source, LazyOracle.empty) := by
  show ∑' first : Public × Stage1Source × LState,
      (((PMF.uniformOfFintype Stage1Source).map some).map
        (Option.map fun source => (source.publicValue, source, LazyOracle.empty))) (some first) *
          value first = _
  rw [PMF.map_comp]
  let extend : Option (Public × Stage1Source × LState) → ℝ≥0∞ := fun option =>
    match option with
    | none => 0
    | some first => value first
  calc ∑' first : Public × Stage1Source × LState,
        ((PMF.uniformOfFintype Stage1Source).map
          (Option.map (fun source : Stage1Source => (source.publicValue, source,
            (LazyOracle.empty : LState))) ∘ some)) (some first) * value first
      = ∑' option : Option (Public × Stage1Source × LState),
          ((PMF.uniformOfFintype Stage1Source).map
            (Option.map (fun source : Stage1Source => (source.publicValue, source,
              (LazyOracle.empty : LState))) ∘ some)) option * extend option := by
        rw [tsum_option _ ENNReal.summable]
        simp only [extend, mul_zero, zero_add]
    _ = _ := tsum_map_mul _ _ _

/-- The same collapse for the opened simulators (same stage 1). -/
theorem stage1_collapse_opened (rows : RowsKernel) (install : Installation) (parameter : ℕ)
    (value : Public × Stage1Source × LState → ℝ≥0∞) :
    ∑' first : Public × Stage1Source × LState, (openedSimulator rows install).stage1 parameter
        LazyOracle.empty (some first) * value first =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        value (source.publicValue, source, LazyOracle.empty) :=
  stage1_collapse parameter value

/-- **The key averages out separately.** -/
theorem key_average (value : Stage1Source → ℝ≥0∞) :
    ∑' source, PMF.uniformOfFintype Stage1Source source * value source =
      ∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' key, PMF.uniformOfFintype InputMacKey key * value (withKey source key) := by
  conv_lhs => rw [← uniform_withKey]
  rw [tsum_bind_mul]
  exact tsum_congr fun source => by rw [tsum_map_mul]

/-- **The prefix average of the entries at an injective index family is at most `q₁`.** -/
theorem stageOneMean_indexUse_le {S : Type} [Fintype S] (family : S → FixedIndex)
    (injective : Function.Injective family) (adversary : PlanBAdversary Unit) (parameter : ℕ) :
    stageOneMean adversary parameter (fun oracle => (indexUse family oracle : ℝ≥0∞)) ≤
      (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
  unfold stageOneMean
  beta_reduce
  refine (le_of_eq (stage1_collapse parameter fun first => ∑' chosen,
    (LazyOracle.run (adversary.chooseInput parameter first.1 ()) first.2.2) chosen *
      (indexUse family chosen.2 : ℝ≥0∞))).trans ?_
  calc (∑' source, PMF.uniformOfFintype Stage1Source source *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
          LazyOracle.empty) chosen * (indexUse family chosen.2 : ℝ≥0∞))
      ≤ ∑' source, PMF.uniformOfFintype Stage1Source source *
          (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun source => mul_le_mul_of_nonneg_left ?_ zero_le
        calc (∑' chosen, (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
              LazyOracle.empty) chosen * (indexUse family chosen.2 : ℝ≥0∞))
            ≤ ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter source.publicValue ())
                LazyOracle.empty) chosen * (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
              refine ENNReal.tsum_le_tsum fun chosen => ?_
              by_cases zero : (LazyOracle.run (adversary.chooseInput parameter
                  source.publicValue ()) LazyOracle.empty) chosen = 0
              · rw [zero, zero_mul, zero_mul]
              · refine mul_le_mul_of_nonneg_left ?_ zero_le
                have used := run_indexUse_le family injective
                  (adversary.chooseInput parameter source.publicValue ()) LazyOracle.empty chosen
                  ((PMF.mem_support_iff _ _).mpr zero)
                rw [indexUse_empty, Nat.zero_add] at used
                exact_mod_cast used
          _ = (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = (adversary.firstQueryBudget parameter : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A single index carries at most `q₁` entries after the adversary's first stage. -/
theorem run_used_le (adversary : PlanBAdversary Unit) (parameter : ℕ) (circuit : Public)
    (chosen : (AffineInput × adversary.State) × LState)
    (member : chosen ∈ (LazyOracle.run (adversary.chooseInput parameter circuit ())
      LazyOracle.empty).support) (index : FixedIndex) :
    (chosen.2.fixed index).used ≤ adversary.firstQueryBudget parameter := by
  have used := run_indexUse_le (fun _ : Unit => index) (fun _ _ _ => rfl)
    (adversary.chooseInput parameter circuit ()) LazyOracle.empty chosen member
  have zero := indexUse_empty (S := Unit) (fun _ => index)
  simp only [indexUse, Finset.univ_unique, Finset.sum_singleton] at used zero
  omega

end Reduction

/-- **The opened games at two installations** are within the prefix average of any bound on their
stage-2 kernels (the stage-1 kernels are the same). -/
theorem openedGame_etvDist_le [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
    [DecidableEq EncPRF.PermutationIndex] (rows : RowsKernel) (first second : Installation)
    (bound : Stage1Source → AffineInput → Option Point → LState → ℝ≥0∞)
    (close : ∀ source input output oracle,
      ((openedSimulator rows first).stage2 source input output oracle).etvDist
        ((openedSimulator rows second).stage2 source input output oracle) ≤
          bound source input output oracle)
    (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    (abstractIdealGame Scheme.scheme (openedSimulator rows first) adversary parameter scalar
        ()).etvDist
      (abstractIdealGame Scheme.scheme (openedSimulator rows second) adversary parameter scalar
        ()) ≤
      ∑' start : Public × Stage1Source × LState, (openedSimulator rows second).stage1 parameter
          LazyOracle.empty (some start) *
        ∑' chosen, (LazyOracle.run (adversary.chooseInput parameter start.1 ()) start.2.2)
          chosen * bound start.2.1 chosen.1.1 (Scheme.scheme.function scalar chosen.1.1)
            chosen.2 := by
  unfold abstractIdealGame
  refine le_trans (Kriterion.ArgoMAC.Security.Phase3.etvDist_map_le' _ _ _) ?_
  refine le_trans (optionT_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun start => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨circuit, state, oracle⟩ := start
  refine le_trans (optionT_lift_bind_etvDist_le _ _ _) ?_
  refine ENNReal.tsum_le_tsum fun chosen => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  obtain ⟨selected, chosen⟩ := chosen
  refine le_trans (optionT_bind_mk_etvDist_le _ _ _) ?_
  exact close _ _ _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
