/-
**Phase 3, P1m — (B1) the fixed-key part: potentials along `M'`'s whole on-curve private stage 2.**

* `runRefill_potential_sites` — a potential not raised by any lazy question of a program and left
  unchanged by programming a mask-site index is a supermartingale along P4's refill run
  (the consumed questions program mask sites only); `runRefillT_potential_sites` the same for the
  runner that returns its touched set.
* `programAllSkip_potential` — a potential left unchanged by programming a designated index is left
  unchanged by the designated installation.
* `onCurve_potential_le` — **on the curve, an event bounded at the final state by such a potential
  has mass at most the potential of the empty state**; `onCurve_split_le` — the same with the
  potential chosen after a first part of the opening (its value), bounded after that part.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPot

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM IsDesignated interceptAnswer
  programRequests)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ runRefill consumeCell
  refillAnswer consumeCell_spec cellOf cellOf_siteIndex runRefillT runRefill_eq_runRefillT
  runRefillT_bind continueT dropTouched uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Potentials along the refill run and the installation -/

section Run

/-- **A supermartingale along the refill run**, for a potential that the consumed programs (at mask
sites) leave unchanged. -/
theorem runRefill_potential_sites (bits : BitInput) (draw : Cell → PMF Block)
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (potential : LState → ℝ≥0∞)
    (siteSame : ∀ (state updated : LState) (index : FixedIndex) (input output : Block),
      cellOf index ≠ none → LazyOracle.program (.fixedForward index input) output state = some updated →
        potential updated = potential state)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      ∑' o, runRefill bits draw computation oracle record touched o * optWeight potential o ≤
        potential oracle := by
  induction computation with
  | pure value =>
    intro oracle record touched
    simp only [runRefill]
    rw [tsum_pure_mul]
    rfl
  | query request next ih =>
    intro oracle record touched
    simp only [runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer => exact ih answer (AllQ.tail holds _) _ _ _
    | none =>
      simp only
      cases consumed : consumeCell touched oracle request with
      | some cell =>
        obtain ⟨index, input, rfl, _, _, siteEq⟩ := consumeCell_spec consumed
        rw [tsum_bind_mul]
        refine le_trans (ENNReal.tsum_le_tsum fun limb => mul_le_mul' le_rfl (?_ :
          _ ≤ potential oracle)) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
        split
        · rw [tsum_pure_mul]
          exact zero_le
        · rename_i updated success
          have isSite : cellOf index ≠ none := by
            rw [← siteEq, cellOf_siteIndex]
            exact Option.some_ne_none _
          rw [← siteSame oracle updated index input _ isSite success]
          exact ih _ (AllQ.tail holds _) _ _ _
      | none =>
        rw [tsum_bind_mul]
        exact le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (ih answer.1 (AllQ.tail holds _) answer.2 _ _))
          (step request oracle (AllQ.head holds))

/-- The potential of a touched-set outcome (an abort weighs nothing). -/
def optWeightT {α : Type} (potential : LState → ℝ≥0∞) :
    Option (α × LState × Record × Set FixedIndex) → ℝ≥0∞
  | none => 0
  | some result => potential result.2.1

theorem runRefillT_potential_sites (bits : BitInput) (draw : Cell → PMF Block)
    (Q : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (potential : LState → ℝ≥0∞)
    (siteSame : ∀ (state updated : LState) (index : FixedIndex) (input output : Block),
      cellOf index ≠ none → LazyOracle.program (.fixedForward index input) output state = some updated →
        potential updated = potential state)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      Q request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    {α : Type} (computation : FreeQuery Programs.Spec α) (holds : AllQ Q computation)
    (oracle : LState) (record : Record) (touched : Set FixedIndex) :
    ∑' o, runRefillT bits draw computation oracle record touched o * optWeightT potential o ≤
      potential oracle := by
  have base := runRefill_potential_sites bits draw Q potential siteSame step computation holds
    oracle record touched
  rw [runRefill_eq_runRefillT, tsum_map_mul] at base
  refine le_trans (le_of_eq (tsum_congr fun o => ?_)) base
  rcases o with _ | o <;> rfl

/-- **A potential blind to the designated indices is blind to the installation.** -/
theorem programAllSkip_potential (bits : BitInput) (potential : LState → ℝ≥0∞)
    (designatedSame : ∀ (state updated : LState) (index : FixedIndex) (input output : Block),
      IsDesignated bits index → LazyOracle.program (.fixedForward index input) output state =
        some updated → potential updated = potential state) :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (state : LState),
      (∀ request ∈ requests, IsDesignated bits request.1) →
        potential (programAllSkip requests state) = potential state := by
  intro requests
  induction requests with
  | nil => exact fun _ _ => rfl
  | cons request rest ih =>
    intro state designated
    obtain ⟨index, input, output⟩ := request
    have restDesignated : ∀ r ∈ rest, IsDesignated bits r.1 := fun r member =>
      designated r (List.mem_cons_of_mem _ member)
    cases input with
    | none => exact ih state restDesignated
    | some input =>
      show potential (programAllSkip rest ((LazyOracle.program (.fixedForward index input)
        (output ^^^ input) state).getD state)) = _
      rw [ih _ restDesignated]
      cases success : LazyOracle.program (.fixedForward index input) (output ^^^ input) state with
      | none => rfl
      | some updated =>
        exact designatedSame state updated index input _ (designated _ List.mem_cons_self) success

theorem programRequests_designated (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    ∀ request ∈ programRequests bits record blocks, IsDesignated bits request.1 := by
  intro request member
  unfold programRequests at member
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at member
  obtain ⟨d, c, b, rfl⟩ := member
  exact ⟨d, c, b, rfl⟩

end Run

/-! ### On the curve -/

section OnCurve

variable [FieldCertificate] [GroupCertificate]

/-- **On the curve, an event bounded by a potential at the final state has mass at most the
potential of the empty state.** -/
theorem onCurve_potential_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (potential : LState → ℝ≥0∞)
    (step : ∀ (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (state : LState),
      ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential answer.2 ≤ potential state)
    (siteSame : ∀ (state updated : LState) (index : FixedIndex) (input output : Block),
      cellOf index ≠ none → LazyOracle.program (.fixedForward index input) output state = some updated →
        potential updated = potential state)
    (designatedSame : ∀ (state updated : LState) (index : FixedIndex) (input' output : Block),
      IsDesignated (restoredBits source input) index →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential updated = potential state)
    (final : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        ind (event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks)))) ≤ potential result.2) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ potential LazyOracle.empty := by
  refine le_trans (onCurve_event_le scalar off source input target event potential
    fun tape ran member blocks => ?_) ?_
  · refine le_trans (tsum_mul_le_of_support _ _ (fun result => potential result.2)
      fun result resultMember => final tape ran member blocks result resultMember) ?_
    refine le_trans (runLazyQ_potential ForwardOnly potential step _
      (shadowOnM_forwardOnly _ _ _) _) (le_of_eq ?_)
    exact programAllSkip_potential _ potential designatedSame _ _
      (programRequests_designated _ _ _)
  · refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape *
      potential LazyOracle.empty) fun tape => mul_le_mul' le_rfl ?_)
      (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    have key := runRefill_potential_sites (restoredBits source input)
      (fun cell => PMF.pure (tape cell)) ForwardOnly potential siteSame step
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
      (openingQueriesM_forwardOnly _ _ _) LazyOracle.empty (fun _ => none) ∅
    unfold openingRun
    exact key

/-- **After the opening**: the continuation's event mass, from a per-installation bound. -/
theorem post_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (bound : ℝ≥0∞)
    (perRun : ∀ blocks : Fin digitCount × Fin 3 → Block × Block × Block,
        ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
              (restoredMac source input))
            (programAllSkip (programRequests (restoredBits source input) ran.2.2 blocks) ran.2.1)
            result *
          ind (event ((pointsOf result.2).union
            (requestPoints (programRequests (restoredBits source input) ran.2.2 blocks)))) ≤
        bound) :
    ∑' o, privateContU (planBShadow scalar off) scalar source input ran o *
      ind (event (outcomePoints o)) ≤ bound := by
  unfold privateContU
  dsimp only
  rw [tsum_bind_mul]
  refine tsum_le_of_support' _ _ _ fun coins _ => ?_
  rw [tsum_bind_mul]
  refine tsum_le_of_support' _ _ _ fun blocks blocksMember => ?_
  rcases blocks with _ | blocks
  · exact absurd blocksMember (preimages_ne_none _)
  · dsimp only
    rw [tsum_bind_mul]
    refine tsum_le_of_support' _ _ _ fun coin _ => ?_
    obtain ⟨delta, offCoin⟩ := coin
    rw [tsum_map_mul]
    simp only [planBShadow_onCurve, outcomePoints]
    have bounded := perRun blocks
    rw [show (Lamport.restore input (sourceLabels source input)).input = restoredBits source input
      from rfl]
    exact bounded

/-- **The split of the opening run**: the mass of an observable of the opening's outcome, as the
first part's run followed by the rest's. -/
theorem openingRun_split {β : Type} (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (first : Programs.M β)
    (rest : β → Programs.M ((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)))
    (split : openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input) = first >>= rest)
    (f : Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) → ℝ≥0∞) :
    ∑' ran, openingRun source input tape ran * f ran =
      ∑' midT, runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
          LazyOracle.empty (fun _ => none) ∅ midT *
        ∑' ranT, continueT (restoredBits source input) (fun cell => PMF.pure (tape cell)) rest
          midT ranT * f (Option.map dropTouched ranT) := by
  unfold openingRun
  rw [split, runRefill_eq_runRefillT, runRefillT_bind, tsum_map_mul, tsum_bind_mul]

/-- **The opening alone, with the potential chosen after a first part.** -/
theorem opening_split_le {β : Type} (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (first : Programs.M β)
    (rest : β → Programs.M ((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)))
    (split : openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input) = first >>= rest)
    (restForward : ∀ value, AllQ ForwardOnly (rest value))
    (G : LState → ℝ≥0∞) (potential : β → LState → ℝ≥0∞)
    (step : ∀ (value : β) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (state : LState), ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential value answer.2 ≤
          potential value state)
    (siteSame : ∀ (value : β) (state updated : LState) (index : FixedIndex)
      (input' output : Block), cellOf index ≠ none →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential value updated = potential value state)
    (c : ℝ≥0∞)
    (initial : ∀ mid : β × LState × Record × Set FixedIndex,
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty (fun _ => none) ∅).support → potential mid.1 mid.2.1 ≤ c)
    (final : ∀ mid : β × LState × Record × Set FixedIndex,
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty (fun _ => none) ∅).support →
      ∀ ranT : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
          LState × Record × Set FixedIndex,
        some ranT ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell))
          (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2).support →
        some (dropTouched ranT) ∈ (openingRun source input tape).support →
        G ranT.2.1 ≤ potential mid.1 ranT.2.1) :
    ∑' ran, openingRun source input tape ran * optWeight G ran ≤ c := by
  rw [openingRun_split source input tape first rest split]
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => c) fun midT midMember => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
  rcases midT with _ | mid
  · exfalso
    apply openingRun_ne_none source input tape
    unfold openingRun
    rw [split, runRefill_eq_runRefillT, runRefillT_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨none, midMember, by simp [continueT]⟩, rfl⟩
  · show ∑' ranT, runRefillT _ _ (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2 ranT * _ ≤ c
    refine le_trans (tsum_mul_le_of_support _ _ (optWeightT (potential mid.1))
      fun ranT ranMember => ?_) (le_trans (runRefillT_potential_sites _ _ ForwardOnly
        (potential mid.1) (siteSame mid.1) (step mid.1) _ (restForward mid.1) _ _ _)
          (initial mid midMember))
    rcases ranT with _ | ranT
    · exfalso
      apply openingRun_ne_none source input tape
      unfold openingRun
      rw [split, runRefill_eq_runRefillT, runRefillT_bind]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
        ⟨some mid, midMember, ranMember⟩, rfl⟩
    · have openMember : some (dropTouched ranT) ∈ (openingRun source input tape).support := by
        unfold openingRun
        rw [split, runRefill_eq_runRefillT, runRefillT_bind]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some ranT,
          (PMF.mem_support_bind_iff _ _ _).mpr ⟨some mid, midMember, ranMember⟩, rfl⟩
      exact final mid midMember ranT ranMember openMember

/-- **On the curve, with the potential chosen after a first part of the opening.** -/
theorem onCurve_split_le {β : Type} (scalar : NonZeroScalar) (off : OffShadow)
    (source : Stage1Source) (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop)
    (first : Programs.M β)
    (rest : β → Programs.M ((Fin pointElementCountX → BaseField) ×
      (Fin pointElementCountY → BaseField)))
    (split : openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input) = first >>= rest)
    (restForward : ∀ value, AllQ ForwardOnly (rest value))
    (potential : Tape → β → LState → ℝ≥0∞)
    (step : ∀ (tape : Tape) (value : β) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (state : LState), ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential tape value answer.2 ≤
          potential tape value state)
    (siteSame : ∀ (tape : Tape) (value : β) (state updated : LState) (index : FixedIndex)
      (input' output : Block), cellOf index ≠ none →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential tape value updated = potential tape value state)
    (designatedSame : ∀ (tape : Tape) (value : β) (state updated : LState) (index : FixedIndex)
      (input' output : Block), IsDesignated (restoredBits source input) index →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential tape value updated = potential tape value state)
    (c : ℝ≥0∞)
    (initial : ∀ (tape : Tape) (mid : β × LState × Record × Set FixedIndex),
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty (fun _ => none) ∅).support → potential tape mid.1 mid.2.1 ≤ c)
    (final : ∀ (tape : Tape) (mid : β × LState × Record × Set FixedIndex),
      some mid ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell)) first
        LazyOracle.empty (fun _ => none) ∅).support →
      ∀ ranT : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
          LState × Record × Set FixedIndex,
        some ranT ∈ (runRefillT (restoredBits source input) (fun cell => PMF.pure (tape cell))
          (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2).support →
        some (dropTouched ranT) ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            (dropTouched ranT).2.2 blocks) (dropTouched ranT).2.1)).support →
        ind (event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) (dropTouched ranT).2.2 blocks)))) ≤
          potential tape mid.1 result.2) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ c := by
  rw [privateStage2U_some_eq, tsum_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape * c)
    fun tape => mul_le_mul' le_rfl ?_) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe,
      one_mul]))
  rw [tsum_bind_mul, openingRun_split source input tape first rest split]
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => c) fun midT midMember => ?_)
    (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
  rcases midT with _ | mid
  · exfalso
    apply openingRun_ne_none source input tape
    unfold openingRun
    rw [split, runRefill_eq_runRefillT, runRefillT_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨none, midMember, by simp [continueT]⟩, rfl⟩
  · show ∑' ranT, runRefillT _ _ (rest mid.1) mid.2.1 mid.2.2.1 mid.2.2.2 ranT * _ ≤ c
    refine le_trans (tsum_mul_le_of_support _ _ (optWeightT (potential tape mid.1))
      fun ranT ranMember => ?_) (le_trans (runRefillT_potential_sites _ _ ForwardOnly
        (potential tape mid.1) (siteSame tape mid.1) (step tape mid.1) _ (restForward mid.1) _ _ _)
          (initial tape mid midMember))
    rcases ranT with _ | ranT
    · exfalso
      apply openingRun_ne_none source input tape
      unfold openingRun
      rw [split, runRefill_eq_runRefillT, runRefillT_bind]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, (PMF.mem_support_bind_iff _ _ _).mpr
        ⟨some mid, midMember, ranMember⟩, rfl⟩
    · have openMember : some (dropTouched ranT) ∈ (openingRun source input tape).support := by
        unfold openingRun
        rw [split, runRefill_eq_runRefillT, runRefillT_bind]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some ranT,
          (PMF.mem_support_bind_iff _ _ _).mpr ⟨some mid, midMember, ranMember⟩, rfl⟩
      simp only [Option.map_some, abortCont, optWeightT]
      refine post_le scalar off source input event (dropTouched ranT) _ fun blocks => ?_
      refine le_trans (tsum_mul_le_of_support _ _ (fun result => potential tape mid.1 result.2)
        fun result resultMember => final tape mid midMember ranT ranMember openMember blocks
          result resultMember) ?_
      refine le_trans (runLazyQ_potential ForwardOnly (potential tape mid.1) (step tape mid.1) _
        (shadowOnM_forwardOnly _ _ _) _) (le_of_eq ?_)
      exact programAllSkip_potential _ (potential tape mid.1) (designatedSame tape mid.1) _ _
        (programRequests_designated _ _ _)

end OnCurve

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
