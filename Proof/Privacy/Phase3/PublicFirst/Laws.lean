/-
**Phase 3, P1l — the two laws, part 1: generic tools.**

`LawOff` and `LawOn` compare two laws of `(published value, labels, lookups)`: the garbler's, on
`G1U`'s swapped tape, and the designed shadow's private run, on a uniform source. Both are reduced
to **answer tables** (`LawsTable.lean`, `LawsFill.lean`); this file holds the generic facts the
reductions use.

* **evaluation of uniform families** (`uniform_perm_eval`, `uniform_perms_eval`,
  `uniform_fun_eval`): a uniform permutation (family, function) read at one point per index is
  uniform — every fibre of the evaluation is moved onto every other by post-composing with a swap
  (by an update);
* **the swap kernel's Davies–Meyer values** (`swapKernel_dm`): under `MaskSwap.swapKernel` the
  values at the points are the fibre-uniform tape of uniform masks (`fibreTape`), whatever the
  points; so under `swapLaw` they are independent of the rest (`swapLaw_dm`);
* **a transcript is read along itself** (`transcript_agree`): an answer function that agrees with
  a run's transcript runs the same way (`Hidden.transcriptOf_of_agrees`, for any answer function).
-/

import Proof.Privacy.Phase3.PublicFirst.LiftGuess

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### 1. Uniform families read at one point -/

section Eval

/-- **A uniform permutation read at a point is uniform.** -/
theorem uniform_perm_eval {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (x : α) :
    (PMF.uniformOfFintype (Equiv.Perm α)).map (fun π => π x) = PMF.uniformOfFintype α := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun π => ⟨π.1.trans (Equiv.swap first second), by
      show Equiv.swap first second (π.1 x) = second
      rw [show π.1 x = first from π.2, Equiv.swap_apply_left]⟩
    invFun := fun π => ⟨π.1.trans (Equiv.swap second first), by
      show Equiv.swap second first (π.1 x) = first
      rw [show π.1 x = second from π.2, Equiv.swap_apply_left]⟩
    left_inv := fun π => by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      show Equiv.swap second first (Equiv.swap first second (π.1 y)) = π.1 y
      rw [Equiv.swap_comm second first, Equiv.swap_apply_self]
    right_inv := fun π => by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      show Equiv.swap first second (Equiv.swap second first (π.1 y)) = π.1 y
      rw [Equiv.swap_comm first second, Equiv.swap_apply_self] }

/-- **A uniform permutation family read at one point per index is a uniform family.** -/
theorem uniform_perms_eval {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Nonempty α] (x : ι → α) :
    (PMF.uniformOfFintype (ι → Equiv.Perm α)).map (fun π i => π i (x i))
      = PMF.uniformOfFintype (ι → α) := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun π => ⟨fun i => (π.1 i).trans (Equiv.swap (first i) (second i)), funext fun i => by
      show Equiv.swap (first i) (second i) (π.1 i (x i)) = second i
      rw [show π.1 i (x i) = first i from congrFun π.2 i, Equiv.swap_apply_left]⟩
    invFun := fun π => ⟨fun i => (π.1 i).trans (Equiv.swap (second i) (first i)), funext fun i => by
      show Equiv.swap (second i) (first i) (π.1 i (x i)) = first i
      rw [show π.1 i (x i) = second i from congrFun π.2 i, Equiv.swap_apply_left]⟩
    left_inv := fun π => by
      apply Subtype.ext
      funext i
      apply Equiv.ext
      intro y
      show Equiv.swap (second i) (first i) (Equiv.swap (first i) (second i) (π.1 i y)) = π.1 i y
      rw [Equiv.swap_comm (second i) (first i), Equiv.swap_apply_self]
    right_inv := fun π => by
      apply Subtype.ext
      funext i
      apply Equiv.ext
      intro y
      show Equiv.swap (first i) (second i) (Equiv.swap (second i) (first i) (π.1 i y)) = π.1 i y
      rw [Equiv.swap_comm (first i) (second i), Equiv.swap_apply_self] }

/-- **A uniform function read at a point is uniform.** -/
theorem uniform_fun_eval {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
    [Nonempty β] (k : κ) :
    (PMF.uniformOfFintype (κ → β)).map (fun h => h k) = PMF.uniformOfFintype β := by
  classical
  refine uniform_map_of_fibre_equiv _ fun first second => ?_
  exact {
    toFun := fun h => ⟨Function.update h.1 k second, by
      show Function.update h.1 k second k = second
      rw [Function.update_self]⟩
    invFun := fun h => ⟨Function.update h.1 k first, by
      show Function.update h.1 k first k = first
      rw [Function.update_self]⟩
    left_inv := fun h => by
      apply Subtype.ext
      show Function.update (Function.update h.1 k second) k first = h.1
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr (show h.1 k = first from h.2).symm
    right_inv := fun h => by
      apply Subtype.ext
      show Function.update (Function.update h.1 k first) k second = h.1
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr (show h.1 k = second from h.2).symm }

end Eval

/-! ### 2. The swap kernel's Davies–Meyer values -/

section Swap

variable {M : Type} [Fintype M] [DecidableEq M]

/-- `masksOf` is onto (for any site type). -/
theorem masksOf_onto : Function.Surjective (masksOf (M := M)) := by
  intro masks
  have each : ∀ site, ∃ triple : Block × Block × Block,
      sampleFp triple.1 triple.2.1 triple.2.2 = masks site :=
    fun site => sampleFp_surjective (masks site)
  choose triple hTriple using each
  refine ⟨fun cell => ![(triple cell.1).1, (triple cell.1).2.1, (triple cell.1).2.2] cell.2, ?_⟩
  funext site
  exact hTriple site

/-- **The fibre-uniform tape**: uniform masks, then the tape uniformly among those producing
them. -/
def fibreTape : PMF (M × Fin 3 → Block) :=
  (PMF.uniformOfFintype (M → BaseField)).bind (fibreLaw masksOf masksOf_onto)

/-- The fibre law does not depend on the surjectivity proof. -/
theorem fibreLaw_proof_irrel {A B : Type} [Fintype A] [DecidableEq B] (g : A → B)
    (first second : Function.Surjective g) (point : B) :
    fibreLaw g first point = fibreLaw g second point := rfl

/-- One fibre of the Davies–Meyer map, moved onto another. -/
def dmFibreShift (point : M × Fin 3 → Block) (m : M → BaseField)
    (first second : {values : M × Fin 3 → Block // masksOf values = m}) :
    {perms : {perms : SitePerms M // maskMap point perms = m} //
        (⟨dmValues point perms.1, perms.2⟩ : {values : M × Fin 3 → Block // masksOf values = m}) = first}
      ≃ {perms : {perms : SitePerms M // maskMap point perms = m} //
        (⟨dmValues point perms.1, perms.2⟩ : {values : M × Fin 3 → Block // masksOf values = m}) = second} where
  toFun perms :=
    have values : dmValues point perms.1.1 = first.1 := congrArg Subtype.val perms.2
    have moved : dmValues point (fun site => (perms.1.1 site).trans
        (Equiv.swap (first.1 site ^^^ point site) (second.1 site ^^^ point site))) = second.1 := by
      funext site
      have one : perms.1.1 site (point site) ^^^ point site = first.1 site := congrFun values site
      have image : perms.1.1 site (point site) = first.1 site ^^^ point site := by
        rw [← one, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      show xor (Equiv.swap (first.1 site ^^^ point site) (second.1 site ^^^ point site)
        (perms.1.1 site (point site))) (point site) = second.1 site
      rw [image, Equiv.swap_apply_left]
      show (second.1 site ^^^ point site) ^^^ point site = second.1 site
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    ⟨⟨fun site => (perms.1.1 site).trans
        (Equiv.swap (first.1 site ^^^ point site) (second.1 site ^^^ point site)), by
      show masksOf (dmValues point _) = m
      rw [moved]
      exact second.2⟩, Subtype.ext moved⟩
  invFun perms :=
    have values : dmValues point perms.1.1 = second.1 := congrArg Subtype.val perms.2
    have moved : dmValues point (fun site => (perms.1.1 site).trans
        (Equiv.swap (second.1 site ^^^ point site) (first.1 site ^^^ point site))) = first.1 := by
      funext site
      have one : perms.1.1 site (point site) ^^^ point site = second.1 site := congrFun values site
      have image : perms.1.1 site (point site) = second.1 site ^^^ point site := by
        rw [← one, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      show xor (Equiv.swap (second.1 site ^^^ point site) (first.1 site ^^^ point site)
        (perms.1.1 site (point site))) (point site) = first.1 site
      rw [image, Equiv.swap_apply_left]
      show (first.1 site ^^^ point site) ^^^ point site = first.1 site
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    ⟨⟨fun site => (perms.1.1 site).trans
        (Equiv.swap (second.1 site ^^^ point site) (first.1 site ^^^ point site)), by
      show masksOf (dmValues point _) = m
      rw [moved]
      exact first.2⟩, Subtype.ext moved⟩
  left_inv perms := by
    apply Subtype.ext
    apply Subtype.ext
    funext site
    apply Equiv.ext
    intro y
    show Equiv.swap (second.1 site ^^^ point site) (first.1 site ^^^ point site)
      (Equiv.swap (first.1 site ^^^ point site) (second.1 site ^^^ point site) (perms.1.1 site y))
        = perms.1.1 site y
    rw [Equiv.swap_comm (second.1 site ^^^ point site), Equiv.swap_apply_self]
  right_inv perms := by
    apply Subtype.ext
    apply Subtype.ext
    funext site
    apply Equiv.ext
    intro y
    show Equiv.swap (first.1 site ^^^ point site) (second.1 site ^^^ point site)
      (Equiv.swap (second.1 site ^^^ point site) (first.1 site ^^^ point site) (perms.1.1 site y))
        = perms.1.1 site y
    rw [Equiv.swap_comm (first.1 site ^^^ point site), Equiv.swap_apply_self]

/-- **Under the swap kernel the Davies–Meyer values are the fibre-uniform tape**, at any points. -/
theorem swapKernel_dm (point : M × Fin 3 → Block) :
    (swapKernel point).map (dmValues point) = fibreTape := by
  classical
  unfold swapKernel fibreTape
  rw [PMF.map_bind]
  refine congrArg _ (funext fun m => ?_)
  unfold fibreLaw
  rw [PMF.map_comp]
  haveI : Nonempty {values : M × Fin 3 → Block // masksOf values = m} :=
    ⟨⟨Classical.choose (masksOf_onto m), Classical.choose_spec (masksOf_onto m)⟩⟩
  haveI : Nonempty {perms : SitePerms M // maskMap point perms = m} :=
    ⟨⟨Classical.choose (maskMap_surjective point m), Classical.choose_spec (maskMap_surjective point m)⟩⟩
  let h : {perms : SitePerms M // maskMap point perms = m} →
      {values : M × Fin 3 → Block // masksOf values = m} := fun perms => ⟨dmValues point perms.1, perms.2⟩
  have factor : (dmValues point ∘ Subtype.val : {perms : SitePerms M // maskMap point perms = m} → _)
      = Subtype.val ∘ h := rfl
  rw [factor, ← PMF.map_comp]
  have uniform := uniform_map_of_fibre_equiv h (dmFibreShift point m)
  convert congrArg (PMF.map Subtype.val) uniform using 2

/-- **Under `swapLaw` the Davies–Meyer values at the points are the fibre-uniform tape,
independent of the rest.** -/
theorem swapLaw_dm {Rest : Type} (restLaw : PMF Rest) (point : Rest → M × Fin 3 → Block) :
    (swapLaw restLaw point).map (fun tape => (tape.1, dmValues (point tape.1) tape.2))
      = productPMF restLaw fibreTape := by
  rw [swapLaw, PMF.map_bind, productPMF]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp]
  have factor : ((fun tape : Rest × SitePerms M => (tape.1, dmValues (point tape.1) tape.2))
      ∘ Prod.mk rest) = Prod.mk rest ∘ dmValues (point rest) := rfl
  rw [factor, ← PMF.map_comp, swapKernel_dm]

end Swap

/-! ### 3. A transcript is read along itself -/

section Transcript

/-- **An answer function agreeing with a run's transcript runs the same way.** -/
theorem transcript_agree {α : Type} (computation : FreeQuery Programs.Spec α)
    (first second : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (agree : ∀ entry ∈ transcript first computation, second entry.1 = entry.2) :
    transcript second computation = transcript first computation ∧
      computation.eval second = computation.eval first := by
  induction computation with
  | pure value => exact ⟨rfl, rfl⟩
  | query request next ih =>
      have head : second request = first request :=
        agree ⟨request, first request⟩ List.mem_cons_self
      have rest := ih (first request)
        (fun entry member => agree entry (List.mem_cons_of_mem _ member))
      refine ⟨?_, ?_⟩
      · show ⟨request, second request⟩ :: transcript second (next (second request)) = _
        rw [head, rest.1]
        rfl
      · show (next (second request)).eval second = (next (first request)).eval first
        rw [head]
        exact rest.2

end Transcript

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
