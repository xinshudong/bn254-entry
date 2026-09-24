/-
**Phase 3, P1l — the two laws, part 3: the private run on an answer table.**

The designed shadow's private run off the curve (`LiftOff.offPrivate`) is a lazy run: the pads at
the coin `k₁` (EncPRF questions, two per index), then system A (fixed-key questions, each index at
most once; the mask sites programmed from the mask tape). Two reductions turn it into an eager run:

* **lazy = eager, jointly with the final state** (`runLazyQ_eager`): the lazy run of any query
  computation from `s`, read through its result and (the lookups of) its final state, is the eager
  run on a completion of `s` with its transcript planted on `s` (the resampling argument of
  `Hidden.resample_joint`, one query at a time: `public_step`, `query_semEq_plant`);
* **a fresh run is a table run** (`runFill_once`): a fill run of a computation that asks only
  forward fixed-key questions, at pairwise distinct indices unknown to the state and untouched, is
  its eager run on a table whose non-site answers are uniform (one fresh uniform answer per index,
  whatever the input) and whose limbs are the mask tape.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsTable

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape consumeCell touch refillAnswer)
open scoped ENNReal

noncomputable section

section Lazy

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

theorem semEq_of_sameLookups {s t : LState} (same : SameLookups s t) : Hidden.SemEq s t :=
  ⟨fun i x => same.fixed i x, fun i x => same.enc i x, fun key => same.hash key⟩

theorem sameLookups_of_semEq {s t : LState} (same : Hidden.SemEq s t) : SameLookups s t :=
  sameLookups_of_forward same.fixed same.enc same.hash

/-- **One query, split off a completion.** -/
theorem tsum_completion_split (request : PublicQuery FixedIndex EncPRF.PermutationIndex) (s : LState)
    (h : request.Answer → PublicOracle FixedIndex EncPRF.PermutationIndex → ℝ≥0∞) :
    ∑' O, publicCompletion s O * h (publicAnswer O request) O =
      ∑' a, LazyOracle.query request s a * ∑' O, publicCompletion a.2 O * h a.1 O := by
  have step := public_step request s
  have lhs : ∑' p, ((publicCompletion s).map (publicHandler id request)) p * h p.1 p.2 =
      ∑' O, publicCompletion s O * h (publicAnswer O request) O := by
    rw [tsum_map_mul]
    rfl
  have rhs : ∑' p, ((LazyOracle.query request s).bind fun answer =>
        (publicCompletion answer.2).map fun complete => (answer.1, complete)) p * h p.1 p.2 =
      ∑' a, LazyOracle.query request s a * ∑' O, publicCompletion a.2 O * h a.1 O := by
    rw [tsum_bind_mul]
    refine tsum_congr fun a => congrArg _ ?_
    rw [tsum_map_mul]
  rw [← lhs, step, rhs]

/-- **Lazy = eager, jointly with the final state's lookups.** -/
theorem runLazyQ_eager {α : Type} (computation : FreeQuery Programs.Spec α) :
    ∀ (s : LState) (F : α → LState → ℝ≥0∞), (∀ a t t', SameLookups t t' → F a t = F a t') →
      ∑' r, runLazyQ computation s r * F r.1 r.2 =
        ∑' O, publicCompletion s O * F (computation.eval (publicAnswer O))
          (plantAll (transcript (publicAnswer O) computation) s) := by
  induction computation with
  | pure value =>
      intro s F _
      simp only [runLazyQ, tsum_pure_mul]
      show F value s = ∑' O, publicCompletion s O * F value (plantAll [] s)
      rw [plantAll_nil, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query request next ih =>
      intro s F invariant
      simp only [runLazyQ]
      rw [tsum_bind_mul]
      have right : ∑' O, publicCompletion s O *
          F ((FreeQuery.query request next).eval (publicAnswer O))
            (plantAll (transcript (publicAnswer O) (FreeQuery.query request next)) s) =
          ∑' O, publicCompletion s O * (fun b O' => F ((next b).eval (publicAnswer O'))
            (plantAll (transcript (publicAnswer O') (next b)) (plantEntry s ⟨request, b⟩)))
              (publicAnswer O request) O := rfl
      rw [right, tsum_completion_split request s (fun b O' => F ((next b).eval (publicAnswer O'))
        (plantAll (transcript (publicAnswer O') (next b)) (plantEntry s ⟨request, b⟩)))]
      refine tsum_congr fun a => ?_
      by_cases member : a ∈ (LazyOracle.query request s).support
      · congr 1
        rw [ih a.1 a.2 F invariant]
        have same := Hidden.query_semEq_plant request s a member
        rw [Hidden.publicCompletion_congr same]
        refine tsum_congr fun O => congrArg _ ?_
        exact invariant _ _ _ (plantAll_congr _ (sameLookups_of_semEq same))
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Lazy

/-! ### Computations that ask each fixed-key index at most once -/

section Once

/-- **Every path asks only forward fixed-key questions, at pairwise distinct indices of `X`.** -/
inductive OnceIn {α : Type} : Set FixedIndex → FreeQuery Programs.Spec α → Prop
  | pure (X : Set FixedIndex) (value : α) : OnceIn X (FreeQuery.pure value)
  | ask (X : Set FixedIndex) (index : FixedIndex) (input : Block)
      (next : Programs.Spec.Answer (PublicQuery.fixedForward index input) → FreeQuery Programs.Spec α)
      (inside : index ∈ X)
      (rest : ∀ answer, OnceIn (X \ {index}) (next answer)) :
      OnceIn X (FreeQuery.query (PublicQuery.fixedForward index input) next)

theorem OnceIn.mono {α : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X c) (sub : X ⊆ Y) : OnceIn Y c := by
  induction once generalizing Y with
  | pure X value => exact .pure Y value
  | ask X index input next inside rest ih =>
      exact .ask Y index input next (sub inside) fun answer =>
        ih answer (Set.diff_subset_diff_left sub)

theorem OnceIn.bind {α β : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} (first : OnceIn X c) (second : ∀ a, OnceIn Y (f a))
    (disjoint : Disjoint X Y) : OnceIn (X ∪ Y) (c >>= f) := by
  revert disjoint
  induction first with
  | pure X value => exact fun _ => (second value).mono Set.subset_union_right
  | ask X index input next inside rest ih =>
      intro disjoint
      have notY : index ∉ Y := fun hit => Set.disjoint_left.mp disjoint inside hit
      show OnceIn (X ∪ Y) (FreeQuery.query (PublicQuery.fixedForward index input)
        fun answer => next answer >>= f)
      refine .ask (X ∪ Y) index input (fun answer => next answer >>= f) (Or.inl inside)
        fun answer => ?_
      have sets : (X ∪ Y) \ {index} = (X \ {index}) ∪ Y := by
        ext i
        constructor
        · rintro ⟨hi | hi, ne⟩
          · exact Or.inl ⟨hi, ne⟩
          · exact Or.inr hi
        · rintro (⟨hi, ne⟩ | hi)
          · exact ⟨Or.inl hi, ne⟩
          · refine ⟨Or.inr hi, fun same => notY ?_⟩
            rw [Set.mem_singleton_iff.mp same] at hi
            exact hi
      rw [sets]
      exact ih answer (Set.disjoint_of_subset_left Set.diff_subset disjoint)

theorem OnceIn.pure' {α : Type} (X : Set FixedIndex) (value : α) :
    OnceIn X (Pure.pure value : FreeQuery Programs.Spec α) := .pure X value

/-- One Davies–Meyer question. -/
theorem OnceIn.hashM (index : FixedIndex) (label : Block) :
    OnceIn {index} (Programs.hashM index label) :=
  .ask {index} index label _ rfl fun _ => .pure _ _

/-- A loop over pairwise disjoint index sets. -/
theorem OnceIn.vector {α : Type} : ∀ (count : Nat) (X : Fin count → Set FixedIndex)
    (program : Fin count → FreeQuery Programs.Spec α), (∀ k, OnceIn (X k) (program k)) →
    (∀ k k', k ≠ k' → Disjoint (X k) (X k')) → OnceIn (⋃ k, X k) (FreeQuery.vector count program)
  | 0, _, _, _, _ => .pure _ _
  | count + 1, X, program, each, disjoint => by
      have prefixOnce := OnceIn.vector count (fun k => X k.castSucc) (fun k => program k.castSucc)
        (fun k => each _) (fun k k' ne => disjoint _ _ fun same => ne (Fin.castSucc_injective _ same))
      have tail : ∀ values : Vector α count, OnceIn (X (Fin.last count) ∪ ∅)
          (program (Fin.last count) >>= fun value => Pure.pure (values.push value)) :=
        fun values => (each _).bind (fun _ => .pure ∅ _) (Set.disjoint_empty _)
      have apart : Disjoint (⋃ k : Fin count, X k.castSucc) (X (Fin.last count) ∪ ∅) := by
        rw [Set.union_empty, Set.disjoint_iUnion_left]
        exact fun k => disjoint _ _ (Fin.castSucc_lt_last k).ne
      refine (prefixOnce.bind tail apart).mono ?_
      rintro i (⟨_, ⟨k, rfl⟩, hi⟩ | hi | hi)
      · exact Set.mem_iUnion.mpr ⟨k.castSucc, hi⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last count, hi⟩
      · exact hi.elim

/-- A branch: nothing, or a computation. -/
theorem OnceIn.ite {α : Type} (condition : Prop) [Decidable condition] (X : Set FixedIndex)
    (value : α) (c : FreeQuery Programs.Spec α) (once : OnceIn X c) :
    OnceIn (if condition then ∅ else X) (if condition then Pure.pure value else c) := by
  by_cases hit : condition
  · rw [if_pos hit, if_pos hit]
    exact .pure _ _
  · rw [if_neg hit, if_neg hit]
    exact once

/-- **A once-computation reads its answers only at its own indices.** -/
theorem OnceIn.agree {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X c) :
    ∀ (first second : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer),
      (∀ i ∈ X, ∀ x, first (.fixedForward i x) = second (.fixedForward i x)) →
      transcript first c = transcript second c ∧ c.eval first = c.eval second := by
  induction once with
  | pure X value => exact fun _ _ _ => ⟨rfl, rfl⟩
  | ask X index input next inside rest ih =>
      intro first second same
      have head : first (.fixedForward index input) = second (.fixedForward index input) :=
        same index inside input
      have tail := ih (first (.fixedForward index input)) first second
        (fun i hi x => same i hi.1 x)
      refine ⟨?_, ?_⟩
      · show ⟨.fixedForward index input, first (.fixedForward index input)⟩ ::
            transcript first (next (first (.fixedForward index input))) =
          ⟨.fixedForward index input, second (.fixedForward index input)⟩ ::
            transcript second (next (second (.fixedForward index input)))
        rw [tail.1, ← head]
      · show (next (first (.fixedForward index input))).eval first =
          (next (second (.fixedForward index input))).eval second
        rw [tail.2, ← head]

end Once

/-! ### A fresh fill run is a table run -/

section Fill

/-- Averaging a function of one coordinate and of a family that ignores it. -/
theorem tsum_uniform_split {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    [Nonempty β] (i : ι) (h : β → (ι → β) → ℝ≥0∞)
    (irrel : ∀ b v c, h b (Function.update v i c) = h b v) :
    ∑' v, PMF.uniformOfFintype (ι → β) v * h (v i) v =
      ∑' b, PMF.uniformOfFintype β b * ∑' v, PMF.uniformOfFintype (ι → β) v * h b v := by
  let e := Equiv.piSplitAt i (fun _ : ι => β)
  obtain ⟨default⟩ := (inferInstance : Nonempty β)
  let h' : β → ({j : ι // j ≠ i} → β) → ℝ≥0∞ := fun b w => h b (e.symm (default, w))
  have back : ∀ v : ι → β, e.symm (default, (e v).2) = Function.update v i default := by
    intro v
    funext j
    rw [Equiv.piSplitAt_symm_apply]
    by_cases same : j = i
    · subst same
      simp
    · rw [dif_neg same, Function.update_of_ne same]
      rfl
  have reduce : ∀ b v, h b v = h' b (e v).2 := by
    intro b v
    show h b v = h b (e.symm (default, (e v).2))
    rw [back, irrel]
  have average : ∀ g : β × ({j : ι // j ≠ i} → β) → ℝ≥0∞,
      ∑' v, PMF.uniformOfFintype (ι → β) v * g (e v) =
        ∑' b, PMF.uniformOfFintype β b * ∑' w, PMF.uniformOfFintype ({j : ι // j ≠ i} → β) w * g (b, w) := by
    intro g
    rw [← tsum_map_mul (PMF.uniformOfFintype (ι → β)) e g,
      Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv e, tsum_uniform_prod]
  have left := average fun p => h' p.1 p.2
  have lhs : ∑' v, PMF.uniformOfFintype (ι → β) v * h (v i) v =
      ∑' v, PMF.uniformOfFintype (ι → β) v * (fun p : β × ({j : ι // j ≠ i} → β) => h' p.1 p.2) (e v) :=
    tsum_congr fun v => by rw [reduce]; rfl
  rw [lhs, left]
  refine tsum_congr fun b => congrArg _ ?_
  have inner := average fun p => h' b p.2
  have rhs : ∑' v, PMF.uniformOfFintype (ι → β) v * h b v =
      ∑' v, PMF.uniformOfFintype (ι → β) v * (fun p : β × ({j : ι // j ≠ i} → β) => h' b p.2) (e v) :=
    tsum_congr fun v => by rw [reduce]
  rw [rhs, inner]
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The answers of a fixed-key computation from uniform non-site answers and a limb tape. -/
def fixedAnswer (v : OtherIndex → Block) (T : Tape) :
    ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer :=
  tableAnswer (⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0), v, T)

theorem cellOf_none (index : FixedIndex) (notSite : index ∉ Set.range siteIndex) :
    Kriterion.ArgoMAC.Phase3.Lazy.cellOf index = none := by
  unfold Kriterion.ArgoMAC.Phase3.Lazy.cellOf
  rw [dif_neg]
  rintro ⟨cell, same⟩
  exact notSite ⟨cell, same⟩

/-- A lazy query at an empty index, averaged. -/
theorem tsum_query_empty (s : LState) (index : FixedIndex) (input : Block)
    (empty : s.fixed index = SparsePermutation.empty _)
    (g : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer × LState →
      ℝ≥0∞) :
    ∑' a, LazyOracle.query (.fixedForward index input) s a * g a =
      ∑' o : Block, PMF.uniformOfFintype Block o * g (o, storeOne s index input o) := by
  rw [query_empty s index input empty]
  exact tsum_map_mul _ _ g

/-- **A fresh fill run of a once-computation is its run on a uniform table.** -/
theorem runFill_once (T : Tape) {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X c) :
    ∀ (s : LState) (τ : Set FixedIndex), (∀ i ∈ X, s.fixed i = SparsePermutation.empty _) →
      (∀ i ∈ X, i ∉ τ) →
      ∀ (F : Option (α × LState) → ℝ≥0∞),
        (∀ a t t', SameLookups t t' → F (some (a, t)) = F (some (a, t'))) →
        ∑' r, runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) c s τ r * F r =
          ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v *
            F (some (c.eval (fixedAnswer v T), plantAll (transcript (fixedAnswer v T) c) s)) := by
  induction once with
  | pure X value =>
      intro s τ _ _ F _
      simp only [runFillFlag, tsum_pure_mul]
      have const : ∀ v : OtherIndex → Block,
          F (some ((FreeQuery.pure value : FreeQuery Programs.Spec α).eval (fixedAnswer v T),
            plantAll (transcript (fixedAnswer v T) (FreeQuery.pure value : FreeQuery Programs.Spec α)) s))
            = F (some (value, s)) := fun v => rfl
      simp_rw [const]
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | ask X index input next inside rest ih =>
      intro s τ empty untouched F invariant
      have emptyHere := empty index inside
      have later : ∀ output : Block, ∀ i ∈ X \ {index},
          (Kriterion.ArgoMAC.Security.Phase3.PublicFirst.storeOne s index input output).fixed i =
            SparsePermutation.empty _ := by
        intro output i hi
        show Function.update s.fixed index _ i = _
        rw [Function.update_of_ne hi.2]
        exact empty i hi.1
      have laterTouched : ∀ i ∈ X \ {index}, i ∉ touch (.fixedForward index input) τ := by
        rintro i hi (member | same)
        · exact untouched i hi.1 member
        · exact hi.2 (Option.some.inj same).symm
      by_cases site : index ∈ Set.range siteIndex
      · obtain ⟨cell, rfl⟩ := site
        have consumed : consumeCell τ s (.fixedForward (siteIndex cell) input) = some cell := by
          have fresh : ¬ (siteIndex cell ∈ τ ∨ (s.fixed (siteIndex cell)).knownInput input.toFin) := by
            rintro (member | known)
            · exact untouched _ inside member
            · rw [emptyHere] at known
              exact absurd known (by unfold SparsePermutation.knownInput; simp [SparsePermutation.empty])
          simp only [consumeCell, if_neg fresh]
          exact Kriterion.ArgoMAC.Phase3.Lazy.cellOf_siteIndex cell
        simp only [runFillFlag]
        rw [consumed]
        dsimp only
        rw [PMF.pure_bind, if_neg (not_fullTouch_empty _ _)]
        simp only [refillAnswer, program_empty s _ input _ emptyHere]
        rw [ih (T cell ^^^ input) _ _ (later _) laterTouched F invariant]
        refine tsum_congr fun v => congrArg _ ?_
        have answer : fixedAnswer v T (.fixedForward (siteIndex cell) input) = T cell ^^^ input :=
          tableAnswer_site _ cell input
        show _ = F (some ((next (fixedAnswer v T (.fixedForward (siteIndex cell) input))).eval
            (fixedAnswer v T), plantAll (transcript (fixedAnswer v T)
              (next (fixedAnswer v T (.fixedForward (siteIndex cell) input))))
              (plantEntry s ⟨.fixedForward (siteIndex cell) input,
                fixedAnswer v T (.fixedForward (siteIndex cell) input)⟩)))
        rw [answer]
        unfold plantEntry
        rw [program_empty s _ input _ emptyHere]
        rfl
      · have notConsumed : consumeCell τ s (.fixedForward index input) = none := by
          simp only [consumeCell, cellOf_none index site]
          split_ifs <;> rfl
        simp only [runFillFlag]
        rw [notConsumed]
        dsimp only
        rw [tsum_bind_mul, tsum_query_empty s index input emptyHere]
        have step : ∀ o : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input).Answer,
            ∑' r, (if FullTouch (LazyOracle.empty : LState)
                (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input) o then
                PMF.pure none else
              runFillFlag LazyOracle.empty (fun cell => PMF.pure (T cell)) (next o)
                (storeOne s index input o) (touch (.fixedForward index input) τ)) r * F r =
            ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v *
              F (some ((next o).eval (fixedAnswer v T),
                plantAll (transcript (fixedAnswer v T) (next o)) (storeOne s index input o))) := by
          intro o
          rw [if_neg (not_fullTouch_empty _ _)]
          exact ih o _ _ (later o) laterTouched F invariant
        refine (tsum_congr fun o => congrArg (PMF.uniformOfFintype Block o * ·) (step o)).trans ?_
        let o : OtherIndex := ⟨index, site⟩
        have answer : ∀ v, fixedAnswer v T (.fixedForward index input) = v o :=
          fun v => tableAnswer_other _ o input
        have split := tsum_uniform_split (ι := OtherIndex) (β := Block) o
          (fun b v => F (some ((next b).eval (fixedAnswer v T), plantAll
            (transcript (fixedAnswer v T) (next b)) (storeOne s index input b))))
          (fun b v c' => by
            have agree := (rest b).agree (fixedAnswer (Function.update v o c') T) (fixedAnswer v T)
              (fun i hi x => by
                by_cases isSite : i ∈ Set.range siteIndex
                · obtain ⟨cell, rfl⟩ := isSite
                  rw [fixedAnswer, fixedAnswer, tableAnswer_site, tableAnswer_site]
                · rw [fixedAnswer, fixedAnswer, tableAnswer_other _ ⟨i, isSite⟩,
                    tableAnswer_other _ ⟨i, isSite⟩]
                  show Function.update v o c' ⟨i, isSite⟩ = v ⟨i, isSite⟩
                  rw [Function.update_of_ne]
                  intro same
                  exact hi.2 (congrArg Subtype.val same))
            show F (some (_, _)) = F (some (_, _))
            rw [agree.1, agree.2])
        have rhs : ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v *
            F (some ((FreeQuery.query (spec := Programs.Spec) (PublicQuery.fixedForward index input)
                next).eval (fixedAnswer v T),
              plantAll (transcript (fixedAnswer v T) (FreeQuery.query (spec := Programs.Spec)
                (PublicQuery.fixedForward index input) next)) s)) =
            ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v *
              F (some ((next (v o)).eval (fixedAnswer v T), plantAll
                (transcript (fixedAnswer v T) (next (v o))) (storeOne s index input (v o)))) := by
          refine tsum_congr fun v => congrArg _ ?_
          show F (some ((next (fixedAnswer v T (.fixedForward index input))).eval (fixedAnswer v T),
            plantAll (transcript (fixedAnswer v T) (next (fixedAnswer v T (.fixedForward index input))))
              (plantEntry s ⟨.fixedForward index input, fixedAnswer v T (.fixedForward index input)⟩))) = _
          rw [answer]
          unfold plantEntry
          rw [program_empty s _ input _ emptyHere]
          rfl
        rw [rhs, split]

end Fill

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
