/-
**Phase 3, P1q — `LawOn`, step (D5), part 1: merging the opening's and the shadow's oracles.**

The private run is the opening on a uniform oracle `O` (overlaid by the zeroed tape `T₀`), then the
shadow on a completion `O'` of the installed state (`shadow_installed_eager`, read through
`overlay T₁ O'`). Here the two oracles become one:

* **the overlay program** (`overlayProg T c`): every site question answered by its tape limb without
  asking the oracle. Its transcript on `O` is the non-site part of `c`'s transcript on `overlay T O`,
  and its value is `c`'s value there (`overlayProg_spec`);
* **site entries are invisible through the overlay** (`completion_sites_map`): planting pairs at
  empty site indices does not change the law of `overlay T O'` for `O'` a completion
  (`public_program_fixed`, `overlay_programFixed`); hence a completion of the opening's whole
  transcript and of its non-site part give the same law of `overlay T₁ O'`
  (`completion_overlay_transcript`);
* **resampling** (`merge_resample`, from `Hidden.resample_joint`): a completion of an adaptive
  transcript, averaged over the first oracle, is the first oracle itself — jointly with anything
  the transcript determines.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnShadow

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM programFixedOracle
  public_program_fixed)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape AllQ Request queriesAlong)
open scoped ENNReal

noncomputable section

/-! ### 1. The overlay program -/

section Program

/-- A transcript entry at no site index. -/
def nonSite (e : Entry FixedIndex EncPRF.PermutationIndex) : Bool :=
  match e.1 with
  | .fixedForward index _ => !(@decide (index ∈ Set.range siteIndex) (Classical.propDecidable _))
  | _ => true

theorem nonSite_site (cell : Cell) (x : Block)
    (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) (siteIndex cell) x).Answer) :
    nonSite ⟨.fixedForward (siteIndex cell) x, y⟩ = false := by
  show (!(@decide (siteIndex cell ∈ Set.range siteIndex) (Classical.propDecidable _))) = false
  rw [@decide_eq_true _ (Classical.propDecidable _) ⟨cell, rfl⟩]
  rfl

theorem nonSite_fixed_other (index : FixedIndex) (notSite : index ∉ Set.range siteIndex) (x : Block)
    (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index x).Answer) :
    nonSite ⟨.fixedForward index x, y⟩ = true := by
  show (!(@decide (index ∈ Set.range siteIndex) (Classical.propDecidable _))) = true
  rw [@decide_eq_false _ (Classical.propDecidable _) notSite]
  rfl

/-- **The overlay program**: a site question is answered by its limb without asking. -/
def overlayProg (T : Tape) {α : Type} : FreeQuery Programs.Spec α → FreeQuery Programs.Spec α
  | .pure value => .pure value
  | .query (.fixedForward index input) next =>
      @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
        (fun hit => overlayProg T (next (input ^^^ T (Classical.choose hit))))
        (fun _ => .query (.fixedForward index input) fun a => overlayProg T (next a))
  | .query (.fixedInverse index output) next =>
      .query (.fixedInverse index output) fun a => overlayProg T (next a)
  | .query (.encForward index input) next =>
      .query (.encForward index input) fun a => overlayProg T (next a)
  | .query (.encInverse index output) next =>
      .query (.encInverse index output) fun a => overlayProg T (next a)
  | .query (.hash key) next => .query (.hash key) fun a => overlayProg T (next a)

theorem overlayProg_site (T : Tape) {α : Type} (cell : Cell) (input : Block)
    (next : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) (siteIndex cell) input).Answer →
      FreeQuery Programs.Spec α) :
    overlayProg T (.query (.fixedForward (siteIndex cell) input) next) =
      overlayProg T (next (input ^^^ T cell)) := by
  have hit : siteIndex cell ∈ Set.range siteIndex := ⟨cell, rfl⟩
  show @dite _ (siteIndex cell ∈ Set.range siteIndex) (Classical.propDecidable _)
      (fun hit => overlayProg T (next (input ^^^ T (Classical.choose hit))))
      (fun _ => .query (.fixedForward (siteIndex cell) input) fun a => overlayProg T (next a)) = _
  rw [dif_pos hit, siteIndex_injective (Classical.choose_spec hit)]

theorem overlayProg_fixed_other (T : Tape) {α : Type} (index : FixedIndex)
    (notSite : index ∉ Set.range siteIndex) (input : Block)
    (next : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer →
      FreeQuery Programs.Spec α) :
    overlayProg T (.query (.fixedForward index input) next) =
      .query (.fixedForward index input) fun a => overlayProg T (next a) := by
  show @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
      (fun hit => overlayProg T (next (input ^^^ T (Classical.choose hit))))
      (fun _ => .query (.fixedForward index input) fun a => overlayProg T (next a)) = _
  rw [dif_neg notSite]

theorem cellOnce_queryOnly {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : CellOnce X c) : Hidden.QueryOnly NoInverse c := by
  induction once with
  | pure X value => exact .pure value
  | site X cell input next inside rest ih =>
      exact .query (.fixedForward (siteIndex cell) input) next trivial ih
  | other X request next notSite forward rest ih => exact .query request next forward ih

/-- **The overlay program's run**: its transcript is the non-site part of the transcript on the
overlaid oracle, and its value the value there. -/
theorem overlayProg_spec (T : Tape) {α : Type} {c : FreeQuery Programs.Spec α}
    (forward : Hidden.QueryOnly NoInverse c) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    Hidden.transcriptOf (publicAnswer O) (overlayProg T c) =
        (transcript (publicAnswer (overlay T O)) c).filter nonSite ∧
      FreeQuery.eval (publicAnswer O) (overlayProg T c) = FreeQuery.eval (publicAnswer (overlay T O)) c := by
  induction forward with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next holds rest ih =>
      cases request with
      | fixedForward index input =>
          by_cases site : index ∈ Set.range siteIndex
          · obtain ⟨cell, rfl⟩ := site
            rw [overlayProg_site]
            obtain ⟨tr, ev⟩ := ih (input ^^^ T cell)
            have answer : publicAnswer (overlay T O) (.fixedForward (siteIndex cell) input) =
                input ^^^ T cell := by
              rw [overlay_site, BitVec.xor_comm]
            refine ⟨?_, ?_⟩
            · rw [tr, transcript_query_eq _ _ next _ answer]
              exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp (nonSite_site cell input _))).symm
            · rw [ev, eval_query_eq _ _ next _ answer]
          · rw [overlayProg_fixed_other T index site]
            have answer : publicAnswer (overlay T O) (.fixedForward index input) =
                publicAnswer O (.fixedForward index input) := overlay_fixed_other T O index site input
            obtain ⟨tr, ev⟩ := ih (publicAnswer O (.fixedForward index input))
            refine ⟨?_, ?_⟩
            · show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                  (overlayProg T (next (publicAnswer O (.fixedForward index input)))) = _
              rw [tr, transcript_query_eq _ _ next _ answer]
              exact (List.filter_cons_of_pos (nonSite_fixed_other index site input _)).symm
            · show FreeQuery.eval (publicAnswer O)
                  (overlayProg T (next (publicAnswer O (.fixedForward index input)))) = _
              rw [ev, eval_query_eq _ _ next _ answer]
      | fixedInverse index output => exact holds.elim
      | encForward index input =>
          obtain ⟨tr, ev⟩ := ih (publicAnswer O (.encForward index input))
          exact ⟨by
            show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                (overlayProg T (next (publicAnswer O (.encForward index input)))) = _
            rw [tr]
            rfl, ev⟩
      | encInverse index output => exact holds.elim
      | hash key =>
          obtain ⟨tr, ev⟩ := ih (publicAnswer O (.hash key))
          exact ⟨by
            show ⟨_, _⟩ :: Hidden.transcriptOf (publicAnswer O)
                (overlayProg T (next (publicAnswer O (.hash key)))) = _
            rw [tr]
            rfl, ev⟩

end Program

/-! ### 2. Site entries are invisible through the overlay -/

section Sites

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- Planting entries at no index `i` leaves `i` alone. -/
theorem plantAll_fixed_notAt (i : FixedIndex) :
    ∀ (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState),
      (∀ e ∈ L, ∀ x y, Hidden.fixedPair e ≠ some (i, x, y)) → (plantAll L s).fixed i = s.fixed i
  | [], _, _ => rfl
  | e :: L, s, absent => by
      rw [plantAll_cons, plantAll_fixed_notAt i L _ fun f member => absent f (List.mem_cons_of_mem _ member)]
      exact Hidden.plant_fixed_other s e i (absent e List.mem_cons_self)

/-- **Site entries at empty indices do not change the law of the overlaid completion.** -/
theorem completion_sites_map (T : Tape) :
    ∀ (L : List (Entry FixedIndex EncPRF.PermutationIndex)) (s : LState),
      (∀ e ∈ L, nonSite e = false) →
      L.Pairwise (fun e f => ∀ i x y, e.1 = .fixedForward i x → f.1 ≠ .fixedForward i y) →
      (∀ e ∈ L, ∀ i x, e.1 = .fixedForward i x → s.fixed i = SparsePermutation.empty _) →
      (publicCompletion (plantAll L s)).map (overlay T) = (publicCompletion s).map (overlay T)
  | [], _, _, _, _ => rfl
  | e :: L, s, sites, pairwise, empty => by
      obtain ⟨request, y⟩ := e
      have isSite := sites _ List.mem_cons_self
      cases request with
      | fixedForward i x =>
          change Block at y
          have emptyHere := empty _ List.mem_cons_self i x rfl
          have programmed : LazyOracle.program (.fixedForward i x) y s = some (storeOne s i x y) :=
            program_empty s i x y emptyHere
          have site : i ∈ Set.range siteIndex := by
            by_contra notSite
            rw [nonSite_fixed_other i notSite x y] at isSite
            cases isSite
          obtain ⟨cell, rfl⟩ := site
          rw [plantAll_cons]
          have planted : plantEntry s ⟨.fixedForward (siteIndex cell) x, y⟩ = storeOne s (siteIndex cell) x y := by
            unfold plantEntry
            rw [programmed]
            rfl
          rw [planted]
          obtain ⟨headPair, tailPair⟩ := List.pairwise_cons.mp pairwise
          rw [completion_sites_map T L _ (fun f member => sites f (List.mem_cons_of_mem _ member)) tailPair
            (fun f member j z same => ?_)]
          · rw [← public_program_fixed s _ (siteIndex cell) x y programmed, PMF.map_comp]
            congr 1
            funext O
            exact overlay_programFixed T O cell x y
          · show Function.update s.fixed (siteIndex cell) _ j = _
            rw [Function.update_of_ne]
            · exact empty f (List.mem_cons_of_mem _ member) j z same
            · rintro rfl
              exact headPair f member (siteIndex cell) x z rfl same
      | fixedInverse _ _ => cases isSite
      | encForward _ _ => cases isSite
      | encInverse _ _ => cases isSite
      | hash _ => cases isSite

/-- Two site questions of a site-once computation are at different indices. -/
theorem cellOnce_pairwise {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : CellOnce X c) : ∀ ans : (r : Request) → r.Answer,
      (queriesAlong ans c).Pairwise (fun q r => ∀ i x y, i ∈ Set.range siteIndex →
        q = .fixedForward i x → r ≠ .fixedForward i y) := by
  induction once with
  | pure X value => intro _; exact List.Pairwise.nil
  | site X cell input next inside rest ih =>
      intro ans
      refine List.Pairwise.cons (fun r member i x y site same other => ?_) (ih _ ans)
      injection same with hi _
      subst hi
      subst other
      exact (cellOnce_inside (rest _) ans _ y site member).2 rfl
  | other X request next notSite forward rest ih =>
      intro ans
      exact List.Pairwise.cons (fun r _ i x y site same _ => notSite i x same site) (ih _ ans)

/-- **A completion of a site-once transcript and of its non-site part give the same overlaid law.** -/
theorem completion_overlay_transcript (T₁ : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    {α : Type} {X : Set FixedIndex} (P : FreeQuery Programs.Spec α) (once : CellOnce X P)
    (f : PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O', publicCompletion (plantAll (transcript (publicAnswer (overlay T₁ O)) P) LazyOracle.empty) O' *
        f (overlay T₁ O') =
      ∑' O', publicCompletion (plantAll ((transcript (publicAnswer (overlay T₁ O)) P).filter nonSite)
        LazyOracle.empty) O' * f (overlay T₁ O') := by
  set L := transcript (publicAnswer (overlay T₁ O)) P with hL
  have consistent : Hidden.Consistent (overlay T₁ O) L :=
    fun e member => ((mem_transcript_iff _ _ e).mp member).2.symm
  have split : SameLookups (plantAll L LazyOracle.empty)
      (plantAll (L.filter nonSite ++ L.filter (fun e => !nonSite e)) LazyOracle.empty) := by
    refine sameLookups_of_mem_iff (overlay T₁ O) _ _ consistent (fun e member => ?_) fun e => ?_
    · rcases List.mem_append.mp member with h | h
      · exact consistent e (List.mem_filter.mp h).1
      · exact consistent e (List.mem_filter.mp h).1
    · constructor
      · intro member
        by_cases keep : nonSite e = true
        · exact List.mem_append_left _ (List.mem_filter.mpr ⟨member, keep⟩)
        · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simpa using keep⟩)
      · intro member
        rcases List.mem_append.mp member with h | h
        · exact (List.mem_filter.mp h).1
        · exact (List.mem_filter.mp h).1
  suffices key : (publicCompletion (plantAll L LazyOracle.empty)).map (overlay T₁) =
      (publicCompletion (plantAll (L.filter nonSite) LazyOracle.empty)).map (overlay T₁) by
    rw [← tsum_map_mul (publicCompletion (plantAll L LazyOracle.empty)) (overlay T₁) f,
      ← tsum_map_mul (publicCompletion (plantAll (L.filter nonSite) LazyOracle.empty)) (overlay T₁) f, key]
  rw [publicCompletion_congr split, ← plantAll_append_empty]
  refine completion_sites_map T₁ (L.filter (fun e => !nonSite e)) (plantAll (L.filter nonSite)
    LazyOracle.empty) (fun e member => by simpa using (List.mem_filter.mp member).2)
    ?_ fun e member i x same => ?_
  · -- the site questions are at pairwise different indices
    have pairQ := cellOnce_pairwise once (publicAnswer (overlay T₁ O))
    rw [← map_fst_transcript, ← hL, List.pairwise_map] at pairQ
    refine (pairQ.filter _).imp_of_mem fun {e f} eMember fMember rel i x y eSame => ?_
    have eSite : i ∈ Set.range siteIndex := by
      have keep := (List.mem_filter.mp eMember).2
      by_contra notSite
      obtain ⟨request, value⟩ := e
      simp only at eSame
      subst eSame
      rw [nonSite_fixed_other i notSite x value] at keep
      cases keep
    exact rel i x y eSite eSame
  · -- the non-site part leaves the site indices empty
    have eSite : i ∈ Set.range siteIndex := by
      have keep := (List.mem_filter.mp member).2
      by_contra notSite
      obtain ⟨request, value⟩ := e
      simp only at same
      subst same
      rw [nonSite_fixed_other i notSite x value] at keep
      cases keep
    rw [plantAll_fixed_notAt i _ _ fun g gMember z w pair => ?_]
    · rfl
    have keep := (List.mem_filter.mp gMember).2
    have forward := cellOnce_forward once _ g.1 (((mem_transcript_iff _ _ g).mp
      (List.mem_filter.mp gMember).1).1)
    obtain ⟨request, value⟩ := g
    cases request with
    | fixedForward j v =>
        simp only [Hidden.fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
        obtain ⟨rfl, -, -⟩ := pair
        obtain ⟨cell, rfl⟩ := eSite
        rw [nonSite_site] at keep
        cases keep
    | fixedInverse _ _ => exact forward.elim
    | encForward _ _ => cases pair
    | encInverse _ _ => cases pair
    | hash _ => cases pair

end Sites

/-! ### 3. Resampling -/

section Resample

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **A completion of an adaptive transcript, averaged over the first oracle, is the first oracle**,
jointly with the computation's value. -/
theorem merge_resample {α : Type} (C : FreeQuery Programs.Spec α)
    (K : α → PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C) LazyOracle.empty) O' *
          K (FreeQuery.eval (publicAnswer O) C) O' =
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        K (FreeQuery.eval (publicAnswer O) C) O := by
  have onSupport : ∀ O O', O' ∈ (publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
      LazyOracle.empty)).support →
      FreeQuery.eval (publicAnswer O) C = FreeQuery.eval (publicAnswer O') C := fun O O' member =>
    ((Hidden.transcriptOf_of_agrees C O O' (Hidden.completion_agrees C O O' member)).2).symm
  have lhs : ∀ O, ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
        LazyOracle.empty) O' * K (FreeQuery.eval (publicAnswer O) C) O' =
      ∑' O', publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C) LazyOracle.empty) O' *
        K (FreeQuery.eval (publicAnswer O') C) O' := by
    intro O
    refine tsum_congr fun O' => ?_
    by_cases member : O' ∈ (publicCompletion (plantAll (Hidden.transcriptOf (publicAnswer O) C)
        LazyOracle.empty)).support
    · rw [onSupport O O' member]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]
  simp_rw [lhs]
  have joint := Hidden.resample_joint C (LazyOracle.empty : LState)
  have averaged := congrArg (fun μ : PMF (List (Entry FixedIndex EncPRF.PermutationIndex) ×
      PublicOracle FixedIndex EncPRF.PermutationIndex) =>
    ∑' p, μ p * K (FreeQuery.eval (publicAnswer p.2) C) p.2) joint
  rw [tsum_bind_mul, tsum_map_mul] at averaged
  simp_rw [tsum_map_mul] at averaged
  rw [Kriterion.ArgoMAC.Phase3.Glue.public_initial] at averaged
  exact averaged

end Resample

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
