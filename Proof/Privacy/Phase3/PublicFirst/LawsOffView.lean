/-
**Phase 3, P1n — the off-curve law, step (ii), part 4: system A reads only the view.**

* `systemAM_view`: off the curve, system A on any published value and MAC asks only the view's
  fold gates (`viewIdx`) and the view's curve cells (`viewSite`, the inactive curve masks' cells),
  so its transcript on fixed-key answers `(v, T)` is its transcript on the answers rebuilt from
  `v ∘ viewIdx` and the view cells of `T` (`extV`, `extT`);
* `fibreLaw_restrict`: the fibre-uniform tape restricted to the view cells is the fibre-uniform
  tape of the view masks; so (`tsum_maskTape_view`) a weight of the masks and the view cells,
  averaged over the mask tape, is its average over uniform masks and the view fibre.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffLaw

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape uniformMaskTape masksOf_surjective)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-! ### 1. The view's curve cells -/

/-- The view's curve sites: the inactive curve masks. -/
abbrev CurveW := Σ e : CurveMembership.Element, {cs : ChunkSwitch // ¬ Active ((offShape input).curveAlpha e) cs}

/-- A view site as a mask site. -/
def viewSite : CurveW input → MaskSite
  | ⟨.inl e, cs⟩ => ⟨.curveX, cs.1.1, cs.1.2, curveXSlots e⟩
  | ⟨.inr e, cs⟩ => ⟨.curveY, cs.1.1, cs.1.2, curveYSlots e⟩

theorem viewSite_key (w : CurveW input) :
    (laneSlots (maskSiteSplit (viewSite input w)).1, (maskSiteSplit (viewSite input w)).2) =
      (.inr w.1, w.2.1) := by
  obtain ⟨e | e, cs⟩ := w <;> simp [viewSite, maskSiteSplit, laneSlots]

theorem viewSite_injective : Function.Injective (viewSite input) := by
  intro w w' same
  have key := congrArg (fun s => (laneSlots (maskSiteSplit s).1, (maskSiteSplit s).2)) same
  simp only [viewSite_key, Prod.mk.injEq, Sum.inr.injEq] at key
  obtain ⟨e, cs⟩ := w
  obtain ⟨e', cs'⟩ := w'
  obtain ⟨rfl, same'⟩ := key
  have : cs = cs' := Subtype.ext same'
  subst this
  rfl

/-- The view masks of a mask family are its visible curve masks. -/
theorem masks_viewSite (m : MaskSite → BaseField) (w : CurveW input) :
    m (viewSite input w) = curveVisible (offShape input) (maskSiteEquiv m).2 w.1 w.2 := by
  obtain ⟨e | e, cs⟩ := w
  · exact (maskSiteEquiv_curveX m e cs.1).symm
  · exact (maskSiteEquiv_curveY m e cs.1).symm

/-! ### 2. The mask tape at the view cells -/

/-- A tape's view cells. -/
def viewCells (T : Tape) : CurveW input × Fin 3 → Block := fun p => T (viewSite input p.1, p.2)

open Classical in
/-- A tape with its view cells replaced. -/
def replaceView (T : Tape) (t : CurveW input × Fin 3 → Block) : Tape := fun c =>
  if h : ∃ w, viewSite input w = c.1 then t (Classical.choose h, c.2) else T c

theorem replaceView_view (T : Tape) (t : CurveW input × Fin 3 → Block) (w : CurveW input) (j : Fin 3) :
    replaceView input T t (viewSite input w, j) = t (w, j) := by
  have h : ∃ w', viewSite input w' = viewSite input w := ⟨w, rfl⟩
  unfold replaceView
  rw [dif_pos h, viewSite_injective input (Classical.choose_spec h)]

theorem replaceView_other (T : Tape) (t : CurveW input × Fin 3 → Block) (c : Cell)
    (h : ¬ ∃ w, viewSite input w = c.1) : replaceView input T t c = T c := by
  unfold replaceView
  rw [dif_neg h]

theorem viewCells_replaceView (T : Tape) (t : CurveW input × Fin 3 → Block) :
    viewCells input (replaceView input T t) = t :=
  funext fun p => replaceView_view input T t p.1 p.2

theorem masksOf_replaceView (m : MaskSite → BaseField) (T : Tape) (hT : masksOf T = m)
    (t : CurveW input × Fin 3 → Block) (ht : masksOf t = m ∘ viewSite input) :
    masksOf (replaceView input T t) = m := by
  funext s
  by_cases h : ∃ w, viewSite input w = s
  · obtain ⟨w, rfl⟩ := h
    show sampleFp _ _ _ = _
    rw [replaceView_view, replaceView_view, replaceView_view]
    exact congrFun ht w
  · show sampleFp _ _ _ = _
    rw [replaceView_other input T t _ h, replaceView_other input T t _ h,
      replaceView_other input T t _ h]
    exact congrFun hT s

theorem replaceView_self (T : Tape) : replaceView input T (viewCells input T) = T := by
  funext c
  by_cases h : ∃ w, viewSite input w = c.1
  · obtain ⟨w, hw⟩ := h
    obtain ⟨s, j⟩ := c
    simp only at hw
    subst hw
    exact replaceView_view input T _ w j
  · exact replaceView_other input T _ c h

theorem replaceView_replaceView (T : Tape) (t t' : CurveW input × Fin 3 → Block) :
    replaceView input (replaceView input T t) t' = replaceView input T t' := by
  funext c
  by_cases h : ∃ w, viewSite input w = c.1
  · unfold replaceView
    rw [dif_pos h, dif_pos h]
  · rw [replaceView_other input _ _ c h, replaceView_other input _ _ c h, replaceView_other input _ _ c h]

/-- **The fibre-uniform tape restricted to the view cells is the view's fibre-uniform tape.** -/
theorem fibreLaw_restrict (m : MaskSite → BaseField) :
    (fibreLaw masksOf masksOf_onto m).map (viewCells input) =
      fibreLaw masksOf masksOf_onto (m ∘ viewSite input) := by
  classical
  have : Nonempty {T : Tape // masksOf T = m} :=
    ⟨⟨Classical.choose (masksOf_onto m), Classical.choose_spec (masksOf_onto m)⟩⟩
  have : Nonempty {t : CurveW input × Fin 3 → Block // masksOf t = m ∘ viewSite input} :=
    ⟨⟨Classical.choose (masksOf_onto (m ∘ viewSite input)),
      Classical.choose_spec (masksOf_onto (m ∘ viewSite input))⟩⟩
  let r : {T : Tape // masksOf T = m} → {t : CurveW input × Fin 3 → Block // masksOf t = m ∘ viewSite input} :=
    fun T => ⟨viewCells input T.1, by
      funext w
      show sampleFp _ _ _ = _
      exact congrFun T.2 (viewSite input w)⟩
  have uniform := uniform_map_of_fibre_equiv r fun b₁ b₂ => {
    toFun := fun a => ⟨⟨replaceView input a.1.1 b₂.1, masksOf_replaceView input m a.1.1 a.1.2 b₂.1 b₂.2⟩,
      Subtype.ext (viewCells_replaceView input _ _)⟩
    invFun := fun a => ⟨⟨replaceView input a.1.1 b₁.1, masksOf_replaceView input m a.1.1 a.1.2 b₁.1 b₁.2⟩,
      Subtype.ext (viewCells_replaceView input _ _)⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      show replaceView input (replaceView input a.1.1 b₂.1) b₁.1 = a.1.1
      rw [replaceView_replaceView, ← congrArg Subtype.val a.2]
      exact replaceView_self input a.1.1
    right_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      show replaceView input (replaceView input a.1.1 b₁.1) b₂.1 = a.1.1
      rw [replaceView_replaceView, ← congrArg Subtype.val a.2]
      exact replaceView_self input a.1.1 }
  unfold fibreLaw
  rw [PMF.map_comp]
  have factor : (viewCells input ∘ Subtype.val : {T : Tape // masksOf T = m} → _) = Subtype.val ∘ r := rfl
  rw [factor, ← PMF.map_comp, uniform]

/-! ### 3. System A reads only the view -/

/-- A fixed-key question at a view index. -/
def ViewQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index _ => (∃ w, (viewIdx input w).1 = index) ∨
      (∃ w j, siteIndex (viewSite input w, j) = index)
  | _ => False

theorem transcript_agree_on {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (same : ∀ q, S q → a q = b q) : transcript a P = transcript b P := by
  induction only with
  | pure value => rfl
  | query request next holds rest ih =>
      show ⟨request, a request⟩ :: transcript a (next (a request)) =
        ⟨request, b request⟩ :: transcript b (next (b request))
      rw [same request holds, ih]

theorem evalFoldM_view (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block)
    (hot : ∀ (r : Nat) (half : Bool) (x : Block), r < 2 → r ≠ value % 2 →
      ViewQ input (.fixedForward (hotIndexNat lane chunk 1 r half) x)) :
    ∀ n, n = 2 → Hidden.QueryOnly (ViewQ input) (Programs.evalFoldM lane chunk value bitLabel join n) := by
  intro n hn
  subst hn
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.bind (Hidden.QueryOnly.pure' _) fun previous =>
    Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _) fun previous =>
      Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  · unfold Programs.evalStepM
    refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ => Hidden.QueryOnly.pure' _
    rw [if_pos (Fin.ext (by
      have := e.isLt
      simp only [pow_zero, Nat.lt_one_iff] at this
      simp [activeAt, this]))]
    exact Hidden.QueryOnly.pure' _
  · unfold Programs.evalStepM
    refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ => Hidden.QueryOnly.pure' _
    by_cases active : e = activeAt value 1
    · rw [if_pos active]
      exact Hidden.QueryOnly.pure' _
    · rw [if_neg active]
      have small : e.val < 2 := e.isLt
      have off : e.val ≠ value % 2 := fun same => active (Fin.ext (by simp only [activeAt]; omega))
      exact Hidden.QueryOnly.bind (hashM_only _ _ (hot e.val false _ small off)) fun _ =>
        Hidden.QueryOnly.bind (hashM_only _ _ (hot e.val true _ small off)) fun _ =>
          Hidden.QueryOnly.pure' _

theorem evalLaneM_view (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block)
    (hot : ∀ (chunk : Fin chunkCount) (r : Nat) (half : Bool) (x : Block), r < 2 →
      r ≠ (chunkOf bits chunk).val % 2 → ViewQ input (.fixedForward (hotIndexNat lane chunk 1 r half) x))
    (mask : ∀ (chunk : Fin chunkCount) (s : Fin (2 ^ chunkWidth chunk)) (element : Fin count)
      (block : Fin 3) (x : Block), s ≠ chunkOf bits chunk →
      ViewQ input (.fixedForward (scaleIndexOf lane chunk s.val element block) x)) :
    Hidden.QueryOnly (ViewQ input) (Programs.evalLaneM count lane joins scale bits labels) := by
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun chunk => ?_) fun _ =>
    Hidden.QueryOnly.pure' _
  unfold Programs.evalChunkM
  have value : (chunkValue bits chunk).toNat = (chunkOf bits chunk).val := chunkValue_toNat _ _
  refine Hidden.QueryOnly.bind (evalFoldM_view input lane chunk _ _ _ (fun r half x small off =>
    hot chunk r half x small (by rw [← value]; exact off)) _ (Hidden.chunkWidth_eq_two chunk))
    fun hotLabels => Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  unfold Programs.evalMasksM
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun s => ?_) fun _ => Hidden.QueryOnly.pure' _
  by_cases active : s = chunkOf bits chunk
  · rw [if_pos active]
    exact Hidden.QueryOnly.pure' _
  · rw [if_neg active]
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun element =>
      Hidden.QueryOnly.bind (hashM_only _ _ (mask chunk s element 0 _ active)) fun _ =>
        Hidden.QueryOnly.bind (hashM_only _ _ (mask chunk s element 1 _ active)) fun _ =>
          Hidden.QueryOnly.bind (hashM_only _ _ (mask chunk s element 2 _ active)) fun _ =>
            Hidden.QueryOnly.pure' _) fun _ => Hidden.QueryOnly.pure' _

/-- **System A asks only view questions**, off the curve, on any published value and MAC. -/
theorem systemAM_only (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (ViewQ input) (systemAM P (BitInput.ofAffine input) mac) := by
  unfold systemAM
  refine Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  · refine evalLaneM_view input _ _ _ _ _ _ (fun c r half x small off => Or.inl ⟨(false, c, half), ?_⟩)
      (fun c s element block x active => Or.inr ⟨⟨.inl (curveXSlots.symm element), ⟨⟨c, s⟩, active⟩⟩,
        block, ?_⟩)
    · have a : activeBit input .curveX c = (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .x) c).val % 2 :=
        rfl
      have bound := activeBit_lt input .curveX c
      show hotIndexNat .curveX c 1 (1 - activeBit input .curveX c) half = _
      congr 1
      omega
    · show scaleIndexOf .curveX c s.val (curveXSlots (curveXSlots.symm element)) block = _
      rw [Equiv.apply_symm_apply]
  · refine evalLaneM_view input _ _ _ _ _ _ (fun c r half x small off => Or.inl ⟨(true, c, half), ?_⟩)
      (fun c s element block x active => Or.inr ⟨⟨.inr (curveYSlots.symm element), ⟨⟨c, s⟩, active⟩⟩,
        block, ?_⟩)
    · have a : activeBit input .curveY c = (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .y) c).val % 2 :=
        rfl
      have bound := activeBit_lt input .curveY c
      show hotIndexNat .curveY c 1 (1 - activeBit input .curveY c) half = _
      congr 1
      omega
    · show scaleIndexOf .curveY c s.val (curveYSlots (curveYSlots.symm element)) block = _
      rw [Equiv.apply_symm_apply]

theorem viewIdx_injective : Function.Injective (viewIdx input) := fun w w' same =>
  viewRest_injective input (Subtype.ext same)

open Classical in
/-- Other answers rebuilt from the view's fold answers. -/
def extV (w : ViewIdx → Block) : OtherIndex → Block := fun i =>
  if h : ∃ x, viewIdx input x = i then w (Classical.choose h) else 0

/-- **System A's transcript on fixed-key answers is its transcript on the view.** -/
theorem systemAM_view (P : Public) (mac : InputMac) (v : OtherIndex → Block) (T : Tape) :
    transcript (fixedAnswer v T) (systemAM P (BitInput.ofAffine input) mac) =
      transcript (fixedAnswer (extV input (v ∘ viewIdx input))
        (replaceView input (fun _ => 0) (viewCells input T))) (systemAM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_on (systemAM_only input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward index x =>
      rcases view with ⟨w, rfl⟩ | ⟨w, j, rfl⟩
      · rw [fixedAnswer, fixedAnswer, tableAnswer_other, tableAnswer_other]
        have h : ∃ y, viewIdx input y = viewIdx input w := ⟨w, rfl⟩
        show v (viewIdx input w) = extV input (v ∘ viewIdx input) (viewIdx input w)
        unfold extV
        rw [dif_pos h, Function.comp, viewIdx_injective input (Classical.choose_spec h)]
      · rw [fixedAnswer, fixedAnswer, tableAnswer_site, tableAnswer_site]
        exact congrArg (· ^^^ x) (replaceView_view input (fun _ => 0) (viewCells input T) w j).symm
  | _ => exact view.elim

/-- **A weight of the masks and the view cells, averaged over the mask tape**, is its average over
uniform masks and the view's fibre-uniform cells. -/
theorem tsum_maskTape_view (G : (MaskSite → BaseField) → (CurveW input × Fin 3 → Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * G (masksOf T) (viewCells input T) =
      ∑' m, PMF.uniformOfFintype (MaskSite → BaseField) m *
        ∑' t, fibreLaw masksOf masksOf_onto (m ∘ viewSite input) t * G m t := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  refine tsum_congr fun m => congrArg _ ?_
  have onFibre : ∀ T, fibreLaw masksOf masksOf_surjective m T * G (masksOf T) (viewCells input T) =
      fibreLaw masksOf masksOf_onto m T * G m (viewCells input T) := by
    intro T
    rw [fibreLaw_proof_irrel masksOf masksOf_surjective masksOf_onto m, fibreLaw_apply]
    split_ifs with hit
    · rw [hit]
    · rw [zero_mul, zero_mul]
  rw [tsum_congr onFibre, ← fibreLaw_restrict input m, tsum_map_mul]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
