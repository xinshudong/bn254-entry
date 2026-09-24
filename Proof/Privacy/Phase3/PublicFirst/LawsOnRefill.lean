/-
**Phase 3, P1p — `LawOn`, step (D), part 1: `HW`'s refill opening, eager.**

The private side of `LawOn` starts with P4's refill run of `HW`'s opening from the empty oracle: a
designated question is intercepted (answered by its own input, recorded, not stored), a site
question is answered from the mask tape and programmed, every other question goes to the lazy
oracle. **`refill_eager`**: for a computation asking each site index at most once (`CellOnce`,
from a state empty and untouched at those indices), the refill run, read through its value, its
final state's lookups and its record, is the eager run on a completion `O` of the start state
**overlaid** by the tape (`overlay`: at every site index the translation by its limb, the designated
limbs zeroed, `zeroDesig`), with the non-designated part of its transcript planted and the
designated inputs recorded (`recordOf`).

The proof is `runLazyQ_eager`'s induction, with two new steps: an intercepted question plants
nothing, and a consumed site question plants its limb — the completion of the programmed state is
the old completion reprogrammed at that index (`public_program_fixed`), which the overlay does not
see (`overlay_programFixed`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnCover

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step IsDesignated interceptAnswer
  recordAfter programFixedOracle public_program_fixed)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record cellOf consumeCell refillAnswer touch
  runRefill)
open scoped ENNReal

noncomputable section

section Overlay

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The fixed-key permutations overlaid by a limb table: at every site index the translation by its
limb (Davies–Meyer value the limb), elsewhere the given ones. (A classical `dite`, never unfolded:
`cellOf`'s decision instance would enumerate the sites.) -/
def overlayF (T : Tape) (O : PermutationOracle FixedIndex Block) : FixedIndex → Equiv.Perm Block :=
  fun index => @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
    (fun hit => xorPerm (T (Classical.choose hit))) (fun _ => O.permutation index)

/-- **An oracle overlaid by a limb table.** -/
def overlay (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    PublicOracle FixedIndex EncPRF.PermutationIndex :=
  (⟨overlayF T O.1⟩, O.2)

theorem overlayF_site (T : Tape) (O : PermutationOracle FixedIndex Block) (cell : Cell) :
    overlayF T O (siteIndex cell) = xorPerm (T cell) := by
  have hit : siteIndex cell ∈ Set.range siteIndex := ⟨cell, rfl⟩
  unfold overlayF
  rw [dif_pos hit, siteIndex_injective (Classical.choose_spec hit)]

theorem overlayF_other (T : Tape) (O : PermutationOracle FixedIndex Block) (index : FixedIndex)
    (notSite : index ∉ Set.range siteIndex) : overlayF T O index = O.permutation index := by
  unfold overlayF
  rw [dif_neg notSite]

theorem overlay_fixed (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (index : FixedIndex) (x : Block) :
    publicAnswer (overlay T O) (.fixedForward index x) = overlayF T O.1 index x := rfl

theorem overlay_site (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (cell : Cell)
    (x : Block) :
    publicAnswer (overlay T O) (.fixedForward (siteIndex cell) x) = x ^^^ T cell := by
  rw [overlay_fixed, overlayF_site]
  rfl

theorem overlay_fixed_other (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (index : FixedIndex) (notSite : index ∉ Set.range siteIndex) (x : Block) :
    publicAnswer (overlay T O) (.fixedForward index x) = publicAnswer O (.fixedForward index x) := by
  rw [overlay_fixed, overlayF_other T O.1 index notSite]
  rfl

/-- The overlay ignores the oracle at every site index. -/
theorem overlay_programFixed (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (cell : Cell) (input output : Block) :
    overlay T (programFixedOracle (siteIndex cell) input output O) = overlay T O := by
  unfold overlay
  refine Prod.ext ?_ rfl
  dsimp only
  congr 1
  funext index
  by_cases hit : index ∈ Set.range siteIndex
  · unfold overlayF
    rw [dif_pos hit, dif_pos hit]
  · rw [overlayF_other _ _ index hit, overlayF_other _ _ index hit]
    show Function.update O.1.permutation (siteIndex cell) _ index = O.1.permutation index
    rw [Function.update_of_ne]
    rintro rfl
    exact hit ⟨cell, rfl⟩

open Classical in
/-- **The tape with the designated limbs zeroed**: an intercepted question returns its input, the
Davies–Meyer value `0`. -/
def zeroDesig (bits : BitInput) (T : Tape) : Tape := fun cell =>
  if IsDesignated bits (siteIndex cell) then 0 else T cell

theorem designated_site (bits : BitInput) {index : FixedIndex} (designated : IsDesignated bits index) :
    index ∈ Set.range siteIndex := by
  obtain ⟨digit, collector, block, rfl⟩ := designated
  exact ⟨(⟨.pointX, Kriterion.ArgoMAC.Phase3.Glue.chunkZero,
    Kriterion.ArgoMAC.Phase3.Glue.designatedSwitch bits,
    xElementIndex digit (Kriterion.ArgoMAC.Phase3.Glue.collectorElement collector)⟩, block), rfl⟩

open Classical in
/-- A transcript entry not at a designated index. -/
def notDesig (bits : BitInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) : Bool :=
  match entry.1 with
  | .fixedForward index _ => !decide (IsDesignated bits index)
  | _ => true

/-- The record after a list of questions. -/
def recordOf (bits : BitInput) (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (record : Record) : Record :=
  entries.foldl (fun r e => recordAfter bits e.1 r) record

end Overlay

/-! ### Computations asking each site index at most once -/

section Once

/-- **Every path asks each site index at most once** (forward, at an index of `X`), and asks no
inverse question and no other site question. -/
inductive CellOnce {α : Type} : Set FixedIndex → FreeQuery Programs.Spec α → Prop
  | pure (X : Set FixedIndex) (value : α) : CellOnce X (FreeQuery.pure value)
  | site (X : Set FixedIndex) (cell : Cell) (input : Block)
      (next : Programs.Spec.Answer (PublicQuery.fixedForward (siteIndex cell) input) →
        FreeQuery Programs.Spec α)
      (inside : siteIndex cell ∈ X) (rest : ∀ answer, CellOnce (X \ {siteIndex cell}) (next answer)) :
      CellOnce X (FreeQuery.query (PublicQuery.fixedForward (siteIndex cell) input) next)
  | other (X : Set FixedIndex) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (next : Programs.Spec.Answer request → FreeQuery Programs.Spec α)
      (notSite : ∀ index x, request = .fixedForward index x → index ∉ Set.range siteIndex)
      (forward : NoInverse request) (rest : ∀ answer, CellOnce X (next answer)) :
      CellOnce X (FreeQuery.query request next)

end Once

/-! ### The refill run, eager -/

section Eager

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

theorem transcript_query_eq {α : Type}
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (next : q.Answer → FreeQuery Programs.Spec α)
    (a : q.Answer) (h : ans q = a) :
    transcript ans (FreeQuery.query q next) = ⟨q, a⟩ :: transcript ans (next a) := by
  subst h
  rfl

theorem eval_query_eq {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (next : q.Answer → FreeQuery Programs.Spec α)
    (a : q.Answer) (h : ans q = a) :
    (FreeQuery.query (spec := Programs.Spec) q next).eval ans = (next a).eval ans := by
  subst h
  rfl

theorem notDesig_other (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notSite : ∀ index x, request = .fixedForward index x → index ∉ Set.range siteIndex)
    (answer : request.Answer) : notDesig bits ⟨request, answer⟩ = true := by
  classical
  cases request with
  | fixedForward index x =>
      have notDesignated : ¬ IsDesignated bits index := fun designated =>
        notSite index x rfl (designated_site bits designated)
      simp [notDesig, notDesignated]
  | _ => rfl

theorem intercept_other (bits : BitInput) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notSite : ∀ index x, request = .fixedForward index x → index ∉ Set.range siteIndex) :
    interceptAnswer bits request = none := by
  classical
  cases request with
  | fixedForward index x =>
      have notDesignated : ¬ IsDesignated bits index := fun designated =>
        notSite index x rfl (designated_site bits designated)
      simp [interceptAnswer, notDesignated]
  | _ => rfl

theorem consume_other (τ : Set FixedIndex) (s : LState)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notSite : ∀ index x, request = .fixedForward index x → index ∉ Set.range siteIndex) :
    consumeCell τ s request = none := by
  cases request with
  | fixedForward index x =>
      simp only [consumeCell, cellOf_none index (notSite index x rfl)]
      split_ifs <;> rfl
  | _ => rfl

theorem answer_overlay_other (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex)
    (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (notSite : ∀ index x, request = .fixedForward index x → index ∉ Set.range siteIndex)
    (forward : NoInverse request) :
    publicAnswer (overlay T O) request = publicAnswer O request := by
  cases request with
  | fixedForward index x => exact overlay_fixed_other T O index (notSite index x rfl) x
  | fixedInverse _ _ => exact forward.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-- **The refill run of a site-once computation, eager.** -/
theorem refill_eager (bits : BitInput) (T : Tape) {α : Type} {X : Set FixedIndex}
    {c : FreeQuery Programs.Spec α} (once : CellOnce X c) : X ⊆ Set.range siteIndex →
    ∀ (s : LState) (record : Record) (τ : Set FixedIndex),
      (∀ i ∈ X, s.fixed i = SparsePermutation.empty _) → (∀ i ∈ X, i ∉ τ) →
      ∀ (F : Option (α × LState × Record) → ℝ≥0∞),
        (∀ a t t' r, SameLookups t t' → F (some (a, t, r)) = F (some (a, t', r))) →
        ∑' o, runRefill bits (fun cell => PMF.pure (T cell)) c s record τ o * F o =
          ∑' O, publicCompletion s O *
            F (some (c.eval (publicAnswer (overlay (zeroDesig bits T) O)),
              plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) c).filter
                (notDesig bits)) s,
              recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) c) record)) := by
  induction once with
  | pure X value =>
      intro _ s record τ _ _ F _
      simp only [runRefill, tsum_pure_mul]
      show F (some (value, s, record)) = ∑' O, publicCompletion s O * F (some (value, plantAll [] s, record))
      rw [plantAll_nil, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | site X cell input next inside rest ih =>
      classical
      intro sites s record τ empty untouched F invariant
      have sitesRest : X \ {siteIndex cell} ⊆ Set.range siteIndex := fun i hi => sites hi.1
      have emptyHere := empty _ inside
      have later : ∀ output : Block, ∀ i ∈ X \ {siteIndex cell},
          (storeOne s (siteIndex cell) input output).fixed i = SparsePermutation.empty _ := by
        intro output i hi
        show Function.update s.fixed (siteIndex cell) _ i = _
        rw [Function.update_of_ne hi.2]
        exact empty i hi.1
      have laterTouched : ∀ i ∈ X \ {siteIndex cell},
          i ∉ touch (.fixedForward (siteIndex cell) input) τ := by
        rintro i hi (member | same)
        · exact untouched i hi.1 member
        · exact hi.2 (Option.some.inj same).symm
      by_cases designated : IsDesignated bits (siteIndex cell)
      · have intercept : interceptAnswer bits (.fixedForward (siteIndex cell) input) = some input := by
          simp only [interceptAnswer]
          exact if_pos designated
        have limbZero : zeroDesig bits T cell = 0 := by
          unfold zeroDesig
          exact if_pos designated
        have answer : ∀ O, publicAnswer (overlay (zeroDesig bits T) O)
            (.fixedForward (siteIndex cell) input) = input := by
          intro O
          rw [overlay_site, limbZero]
          exact BitVec.xor_zero
        rw [Kriterion.ArgoMAC.Phase3.Lazy.runRefill_intercept bits (fun cell => PMF.pure (T cell))
          (.fixedForward (siteIndex cell) input) next s record τ input intercept]
        have emptyRest : ∀ i ∈ X \ {siteIndex cell}, s.fixed i = SparsePermutation.empty _ :=
          fun i hi => empty i hi.1
        have untouchedRest : ∀ i ∈ X \ {siteIndex cell}, i ∉ τ := fun i hi => untouched i hi.1
        rw [ih input sitesRest s _ τ emptyRest untouchedRest F invariant]
        refine tsum_congr fun O => congrArg _ ?_
        rw [transcript_query_eq _ (.fixedForward (siteIndex cell) input) next input (answer O),
          eval_query_eq _ (.fixedForward (siteIndex cell) input) next input (answer O),
          List.filter_cons_of_neg (by simp [notDesig, designated])]
        rfl
      · have intercept : interceptAnswer bits (.fixedForward (siteIndex cell) input) = none := by
          simp only [interceptAnswer]
          exact if_neg designated
        have consumed : consumeCell τ s (.fixedForward (siteIndex cell) input) = some cell := by
          have fresh : ¬ (siteIndex cell ∈ τ ∨ (s.fixed (siteIndex cell)).knownInput input.toFin) := by
            rintro (member | known)
            · exact untouched _ inside member
            · rw [emptyHere] at known
              exact absurd known (by unfold SparsePermutation.knownInput; simp [SparsePermutation.empty])
          simp only [consumeCell, if_neg fresh]
          exact Kriterion.ArgoMAC.Phase3.Lazy.cellOf_siteIndex cell
        have limbEq : zeroDesig bits T cell = T cell := by
          unfold zeroDesig
          exact if_neg designated
        have answer : ∀ O, publicAnswer (overlay (zeroDesig bits T) O)
            (.fixedForward (siteIndex cell) input) = T cell ^^^ input := by
          intro O
          rw [overlay_site, limbEq, BitVec.xor_comm]
        have programmed : LazyOracle.program (.fixedForward (siteIndex cell) input) (T cell ^^^ input) s =
            some (storeOne s (siteIndex cell) input (T cell ^^^ input)) :=
          program_empty s _ input _ emptyHere
        simp only [runRefill]
        rw [intercept]
        dsimp only
        rw [consumed]
        dsimp only
        rw [PMF.pure_bind]
        simp only [refillAnswer]
        rw [programmed]
        dsimp only
        rw [ih (T cell ^^^ input) sitesRest _ record _ (later _) laterTouched F invariant]
        rw [← public_program_fixed s _ (siteIndex cell) input (T cell ^^^ input) programmed,
          tsum_map_mul]
        refine tsum_congr fun O => congrArg _ ?_
        rw [overlay_programFixed]
        rw [transcript_query_eq _ (.fixedForward (siteIndex cell) input) next (T cell ^^^ input)
            (answer O),
          eval_query_eq _ (.fixedForward (siteIndex cell) input) next (T cell ^^^ input) (answer O),
          List.filter_cons_of_pos (by simp [notDesig, designated])]
        have recordHead : recordOf bits (⟨.fixedForward (siteIndex cell) input, T cell ^^^ input⟩ ::
            transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next (T cell ^^^ input))) record =
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (T cell ^^^ input))) record := by
          unfold recordOf
          rw [List.foldl_cons]
          congr 1
          simp [recordAfter, designated]
        rw [recordHead, plantAll_cons]
        unfold plantEntry
        rw [programmed]
        rfl
  | other X request next notSite forward rest ih =>
      intro sites s record τ empty untouched F invariant
      simp only [runRefill]
      rw [intercept_other bits request notSite]
      dsimp only
      rw [consume_other τ s request notSite]
      dsimp only
      rw [tsum_bind_mul]
      have split := tsum_completion_split request s (fun b O =>
        F (some ((next b).eval (publicAnswer (overlay (zeroDesig bits T) O)),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next b)).filter
            (notDesig bits)) (plantEntry s ⟨request, b⟩),
          recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O)) (next b))
            (recordAfter bits request record))))
      have lhsForm : ∀ O : PublicOracle FixedIndex EncPRF.PermutationIndex,
          F (some ((FreeQuery.query (spec := Programs.Spec) request next).eval
              (publicAnswer (overlay (zeroDesig bits T) O)),
            plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (FreeQuery.query request next)).filter (notDesig bits)) s,
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (FreeQuery.query request next)) record)) =
          F (some ((next (publicAnswer O request)).eval (publicAnswer (overlay (zeroDesig bits T) O)),
            plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (publicAnswer O request))).filter (notDesig bits))
                (plantEntry s ⟨request, publicAnswer O request⟩),
            recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
              (next (publicAnswer O request))) (recordAfter bits request record))) := by
        intro O
        have answer := answer_overlay_other (zeroDesig bits T) O request notSite forward
        show F (some ((next (publicAnswer (overlay (zeroDesig bits T) O) request)).eval _,
          plantAll ((⟨request, publicAnswer (overlay (zeroDesig bits T) O) request⟩ ::
            transcript _ (next (publicAnswer (overlay (zeroDesig bits T) O) request))).filter
              (notDesig bits)) s,
          recordOf bits (⟨request, publicAnswer (overlay (zeroDesig bits T) O) request⟩ ::
            transcript _ (next (publicAnswer (overlay (zeroDesig bits T) O) request))) record)) = _
        rw [answer, List.filter_cons_of_pos (notDesig_other bits request notSite _)]
        rfl
      rw [tsum_congr fun O => congrArg _ (lhsForm O), split]
      refine tsum_congr fun a => ?_
      by_cases member : a ∈ (LazyOracle.query request s).support
      · have recordSame : recordAfter bits request record = record := by
          cases request with
          | fixedForward index x =>
              have notDesignated : ¬ IsDesignated bits index := fun designated =>
                notSite index x rfl (designated_site bits designated)
              classical
              simp [recordAfter, notDesignated]
          | _ => rfl
        have notTouched : ∀ i ∈ X, Kriterion.ArgoMAC.Phase3.Lazy.touchedIndex request ≠ some i := by
          intro i hi same
          cases request with
          | fixedForward j x =>
              simp only [Kriterion.ArgoMAC.Phase3.Lazy.touchedIndex, Option.some.injEq] at same
              subst same
              exact notSite _ x rfl (sites hi)
          | fixedInverse _ _ => exact forward.elim
          | encForward _ _ => cases same
          | encInverse _ _ => cases same
          | hash _ => cases same
        have frame : ∀ i ∈ X, a.2.fixed i = SparsePermutation.empty _ := fun i hi =>
          (Kriterion.ArgoMAC.Phase3.Lazy.query_frame request s a member i (notTouched i hi)).trans
            (empty i hi)
        have untouched' : ∀ i ∈ X, i ∉ touch request τ := by
          rintro i hi (old | new)
          · exact untouched i hi old
          · exact notTouched i hi new
        refine congrArg _ ?_
        rw [ih a.1 sites a.2 record (touch request τ) frame untouched' F invariant, recordSame]
        have same := Hidden.query_semEq_plant request s a member
        refine tsum_congr fun O => congrArg _ ?_
        exact invariant _ _ _ _ (plantAll_congr _ (sameLookups_of_semEq same))
      · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

end Eager

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
