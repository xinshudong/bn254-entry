/-
**Phase 3, P1p — `LawOn`, step (D), part 2: `HW`'s opening asks each site index at most once.**

`CellOnce` is closed under `bind` (disjoint index sets) and monotone; a computation asking each
fixed-key index at most once (P1l's `OnceIn`) asks each site index at most once
(`cellOnce_of_onceIn`), and a computation asking only EncPRF and hash questions asks none
(`cellOnce_of_plain`). Hence **`cellOnce_opening`**: `HW`'s opening (`openingQueriesM`: the four
lanes, the bridge hash, the bit-`false` pads) asks each site index of the four lanes at most once,
so `refill_eager` applies to it from the empty oracle (`opening_eager`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnRefill

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Cell Tape Record runRefill)
open scoped ENNReal

noncomputable section

/-! ### `CellOnce` is closed under binds -/

section Tools

theorem CellOnce.mono {α : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : CellOnce X c) (sub : X ⊆ Y) : CellOnce Y c := by
  induction once generalizing Y with
  | pure X value => exact .pure Y value
  | site X cell input next inside rest ih =>
      exact .site Y cell input next (sub inside) fun a => ih a (Set.diff_subset_diff_left sub)
  | other X request next notSite forward rest ih =>
      exact .other Y request next notSite forward fun a => ih a sub

theorem CellOnce.bind {α β : Type} {X Y : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    {f : α → FreeQuery Programs.Spec β} (first : CellOnce X c) (second : ∀ a, CellOnce Y (f a))
    (disjoint : Disjoint X Y) : CellOnce (X ∪ Y) (c >>= f) := by
  revert disjoint
  induction first with
  | pure X value => exact fun _ => (second value).mono Set.subset_union_right
  | site X cell input next inside rest ih =>
      intro disjoint
      have notY : siteIndex cell ∉ Y := fun hit => Set.disjoint_left.mp disjoint inside hit
      show CellOnce (X ∪ Y) (FreeQuery.query (PublicQuery.fixedForward (siteIndex cell) input)
        fun answer => next answer >>= f)
      refine .site (X ∪ Y) cell input (fun answer => next answer >>= f) (Or.inl inside)
        fun answer => ?_
      have sets : (X ∪ Y) \ {siteIndex cell} = (X \ {siteIndex cell}) ∪ Y := by
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
  | other X request next notSite forward rest ih =>
      intro disjoint
      show CellOnce (X ∪ Y) (FreeQuery.query request fun answer => next answer >>= f)
      exact .other (X ∪ Y) request (fun answer => next answer >>= f) notSite forward
        fun answer => ih answer disjoint

/-- **A fixed-key-once computation asks each site index at most once.** -/
theorem cellOnce_of_onceIn {α : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X c) : CellOnce (X ∩ Set.range siteIndex) c := by
  induction once with
  | pure X value => exact .pure _ value
  | ask X index input next inside rest ih =>
      by_cases site : index ∈ Set.range siteIndex
      · obtain ⟨cell, rfl⟩ := site
        refine .site _ cell input next ⟨inside, cell, rfl⟩ fun answer => (ih answer).mono ?_
        rintro i ⟨⟨hX, hne⟩, hs⟩
        exact ⟨⟨hX, hs⟩, hne⟩
      · refine .other _ _ next (fun i x same => ?_) trivial fun answer => (ih answer).mono ?_
        · cases same
          exact site
        · rintro i ⟨⟨hX, _⟩, hs⟩
          exact ⟨hX, hs⟩

/-- A question at no site index, forward. -/
def Plain (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  (∀ index x, q = .fixedForward index x → index ∉ Set.range siteIndex) ∧ NoInverse q

/-- **A computation of plain questions asks no site index.** -/
theorem cellOnce_of_plain {α : Type} (X : Set FixedIndex) {c : FreeQuery Programs.Spec α}
    (plain : Hidden.QueryOnly Plain c) : CellOnce X c := by
  induction plain with
  | pure value => exact .pure X value
  | query request next holds rest ih => exact .other X request next holds.1 holds.2 ih

theorem plain_enc (index : EncPRF.PermutationIndex) (x : Block) : Plain (.encForward index x) :=
  ⟨fun _ _ same => (by cases same), trivial⟩

theorem plain_hash (key : BaseField) : Plain (.hash key) :=
  ⟨fun _ _ same => (by cases same), trivial⟩

theorem whitePadsM_plain (keys : WhiteningKeys) : Hidden.QueryOnly Plain (whitePadsM keys) := by
  have pad : ∀ coordinate index, Hidden.QueryOnly Plain (Programs.padM keys coordinate index false) :=
    fun _ _ => Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ (plain_enc _ _)) fun _ =>
      Hidden.QueryOnly.pure' _
  unfold whitePadsM
  exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _) fun _ =>
      Hidden.QueryOnly.pure' _

theorem onceLaneSet_disjoint {lane lane' : Lane} (different : lane ≠ lane') :
    Disjoint (onceLaneSet lane) (onceLaneSet lane') := by
  rw [Set.disjoint_left]
  intro i left right
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp left
  obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp right
  rcases hc with ⟨f, e, h, rfl⟩ | ⟨s, e, b, rfl⟩ <;>
    rcases hc' with ⟨f', e', h', same⟩ | ⟨s', e', b', same⟩ <;>
    first
      | (simp only [FixedIndex.hot.injEq] at same; exact different same.1)
      | (simp only [FixedIndex.scale.injEq] at same; exact different same.1)
      | cases same

end Tools

/-! ### The opening -/

section Opening

variable [FieldCertificate]

/-- The site indices of the four lanes. -/
def openSites : Set FixedIndex :=
  (onceLaneSet .curveX ∪ onceLaneSet .curveY ∪ onceLaneSet .pointX ∪ onceLaneSet .pointY) ∩
    Set.range siteIndex

theorem openSites_sites : openSites ⊆ Set.range siteIndex := fun _ h => h.2

/-- **`HW`'s opening asks each site index of the four lanes at most once.** -/
theorem cellOnce_opening (table : Public) (bits : BitInput) (mac : InputMac) :
    CellOnce openSites (openingQueriesM table bits mac) := by
  have fitsCX : curveElementCountX ≤ elementCountX := by decide
  have fitsCY : curveElementCountY ≤ elementCountX := by decide
  have fitsPX : pointElementCountX ≤ elementCountX := by decide
  have fitsPY : pointElementCountY ≤ elementCountX := by decide
  let R := Set.range siteIndex
  have lane : ∀ (count : Nat) (fits : count ≤ elementCountX) (ℓ : Lane) joins scale bits labels,
      CellOnce (onceLaneSet ℓ ∩ R) (Programs.evalLaneM count ℓ joins scale bits labels) :=
    fun count fits ℓ joins scale bits labels =>
      cellOnce_of_onceIn (once_evalLaneM count fits ℓ joins scale bits labels)
  have apart : ∀ {ℓ ℓ' : Lane}, ℓ ≠ ℓ' → ∀ Y : Set FixedIndex, Y ⊆ onceLaneSet ℓ' ∩ R →
      Disjoint (onceLaneSet ℓ ∩ R) Y := fun different Y sub =>
    Set.disjoint_of_subset (Set.inter_subset_left) (sub.trans Set.inter_subset_left)
      (onceLaneSet_disjoint different)
  unfold openingQueriesM
  refine (CellOnce.bind (lane _ fitsCX .curveX _ _ _ _) (fun _ =>
    CellOnce.bind (lane _ fitsCY .curveY _ _ _ _) (fun _ =>
      CellOnce.bind (cellOnce_of_plain ∅ (Hidden.QueryOnly.ask _ (plain_hash _))) (fun _ =>
        CellOnce.bind (cellOnce_of_plain ∅ (whitePadsM_plain _)) (fun _ =>
          CellOnce.bind (lane _ fitsPX .pointX _ _ _ _) (fun _ =>
            CellOnce.bind (lane _ fitsPY .pointY _ _ _ _) (fun _ => .pure ∅ _)
              (Set.disjoint_empty _)) ?_) (Set.disjoint_left.mpr fun _ h => h.elim))
        (Set.disjoint_left.mpr fun _ h => h.elim)) ?_) ?_).mono ?_
  · exact apart (by decide) _ (Set.union_empty _).subset
  · rw [Set.empty_union, Set.empty_union]
    rw [Set.disjoint_union_right]
    exact ⟨apart (by decide) _ subset_rfl, apart (by decide) _ (Set.union_empty _).subset⟩
  · rw [Set.disjoint_union_right, Set.disjoint_union_right, Set.disjoint_union_right,
      Set.disjoint_union_right]
    exact ⟨apart (by decide) _ subset_rfl, Set.disjoint_empty _, Set.disjoint_empty _,
      apart (by decide) _ subset_rfl, apart (by decide) _ (Set.union_empty _).subset⟩
  · rintro i (⟨hA, hR⟩ | ⟨hB, hR⟩ | hRest)
    · exact ⟨Or.inl (Or.inl (Or.inl hA)), hR⟩
    · exact ⟨Or.inl (Or.inl (Or.inr hB)), hR⟩
    · rcases hRest with hE | hRest
      · exact hE.elim
      · rcases hRest with hE | hRest
        · exact hE.elim
        · rcases hRest with ⟨hC, hR⟩ | hRest
          · exact ⟨Or.inl (Or.inr hC), hR⟩
          · rcases hRest with ⟨hD, hR⟩ | hE
            · exact ⟨Or.inr hD, hR⟩
            · exact hE.elim

variable [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`HW`'s refill opening from the empty oracle, eager**: a uniform oracle overlaid by the tape
(designated limbs zeroed), its non-designated transcript planted on the empty oracle, the
designated inputs recorded. -/
theorem opening_eager (bits : BitInput) (T : Tape) (table : Public) (mac : InputMac)
    (F : Option (((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) → ℝ≥0∞)
    (invariant : ∀ a t t' r, SameLookups t t' → F (some (a, t, r)) = F (some (a, t', r))) :
    ∑' o, runRefill bits (fun cell => PMF.pure (T cell)) (openingQueriesM table bits mac)
        LazyOracle.empty (fun _ => none) ∅ o * F o =
      ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
        F (some ((openingQueriesM table bits mac).eval (publicAnswer (overlay (zeroDesig bits T) O)),
          plantAll ((transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)).filter (notDesig bits)) LazyOracle.empty,
          recordOf bits (transcript (publicAnswer (overlay (zeroDesig bits T) O))
            (openingQueriesM table bits mac)) (fun _ => none))) := by
  rw [refill_eager bits T (cellOnce_opening table bits mac) openSites_sites LazyOracle.empty
    (fun _ => none) ∅ (fun _ _ => rfl) (fun _ _ member => member.elim) F invariant,
    Kriterion.ArgoMAC.Phase3.Glue.public_initial]

end Opening

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
