/-
**Phase 3, P1r — `LawOn`, step (E), part 6: the view's sites and the two tapes.**

The view's inactive sites are F4's **visible** sites (`VisIdx`: digit elements off the active and
the designated switch, curve elements off the active switch, `visSite`) and the **designated** ones
(`DSite`, `desSite`); together `WIdx`, `wSite` (injective, `wSite_injective`, and covering every
inactive site, `inact_cover`). The kernel reads a tape only through its triples at these sites
(`onKW`, `onKV_tape`). F4's visible cells are the functions on `VisIdx` (`visEquiv`), and a mask
family's values at the view sites are its F4 visible and designated masks (`masks_visSite`,
`masks_desSite`).

The two tapes at the view: the garbler's fibre-uniform tape is uniform masks and the product of the
per-site limb laws there (`real_tape`); the private side's mask tape at the visible sites with the
collector preimages at the designated ones is uniform visible masks and the product of the per-site
laws at the visible masks and the targets (`sim_tape`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEFibre

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (designatedSwitch chunkZero collectorElement limbAt idealPreimage)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape masksOf_surjective)
open scoped ENNReal

noncomputable section

/-! ### 1. Restricting the fibre-uniform limbs -/

section Restrict

variable [FieldCertificate] {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem limbWeight_total (μ : N → BaseField) :
    ∑' bd : N → Block × Block × Block, limbWeight μ bd = 1 := by
  rw [tsum_fintype]
  unfold limbWeight
  rw [← Fintype.prod_sum (fun n tr => idealPreimage (μ n) tr)]
  refine Finset.prod_eq_one fun n _ => ?_
  have total := PMF.tsum_coe (idealPreimage (μ n))
  rwa [tsum_fintype] at total

/-- **The fibre-uniform limbs read along an injective site map** are the product of the per-site
laws at the restricted masks. -/
theorem fibre_restrict (ι : N → M) (inj : Function.Injective ι) (m : M → BaseField)
    (G : (N → Block × Block × Block) → ℝ≥0∞) :
    ∑' T, fibreLaw masksOf masksOf_onto m T * G (fun n => triplesOf T (ι n)) =
      ∑' bd : N → Block × Block × Block, limbWeight (m ∘ ι) bd * G bd := by
  classical
  rw [fibre_limbs m (fun T => G fun n => triplesOf T (ι n))]
  show ∑' bd : M → Block × Block × Block, limbWeight m bd * G (fun n => bd (ι n)) = _
  rw [← (splitAlong ι inj).symm.tsum_eq, ENNReal.tsum_prod']
  have split : ∀ (a : N → Block × Block × Block) (b : {i : M // i ∉ Set.range ι} → Block × Block × Block),
      limbWeight m ((splitAlong ι inj).symm (a, b)) =
        limbWeight (m ∘ ι) a * ∏ r : {i : M // i ∉ Set.range ι}, idealPreimage (m r.1) (b r) := by
    intro a b
    unfold limbWeight
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : M => i ∈ Set.range ι)
      (fun s => idealPreimage (m s) ((splitAlong ι inj).symm (a, b) s))]
    congr 1
    · convert Fintype.prod_equiv (Equiv.ofInjective ι inj).symm
        (fun i => idealPreimage (m i.1) ((splitAlong ι inj).symm (a, b) i.1))
        (fun n => idealPreimage ((m ∘ ι) n) (a n)) fun i => ?_
      obtain ⟨_, n, rfl⟩ := i
      have back : (Equiv.ofInjective ι inj).symm ⟨ι n, ⟨n, rfl⟩⟩ = n :=
        (Equiv.ofInjective ι inj).symm_apply_apply n
      rw [back]
      show idealPreimage (m (ι n)) ((splitAlong ι inj).symm (a, b) (ι n)) = idealPreimage (m (ι n)) (a n)
      rw [splitAlong_symm_image]
    · refine Fintype.prod_congr _ _ fun r => ?_
      rw [splitAlong_symm_rest]
  have image : ∀ (a : N → Block × Block × Block) (b : {i : M // i ∉ Set.range ι} → Block × Block × Block),
      (fun n => (splitAlong ι inj).symm (a, b) (ι n)) = a := fun a b =>
    funext fun n => splitAlong_symm_image ι inj a b n
  simp only [split, image]
  refine tsum_congr fun a => ?_
  have rest : ∑' b : {i : M // i ∉ Set.range ι} → Block × Block × Block,
      ∏ r : {i : M // i ∉ Set.range ι}, idealPreimage (m r.1) (b r) = 1 :=
    limbWeight_total (fun r : {i : M // i ∉ Set.range ι} => m r.1)
  have eq : ∀ b : {i : M // i ∉ Set.range ι} → Block × Block × Block,
      limbWeight (m ∘ ι) a * (∏ r, idealPreimage (m r.1) (b r)) * G a =
        (limbWeight (m ∘ ι) a * G a) * ∏ r, idealPreimage (m r.1) (b r) := fun b => by ring
  rw [tsum_congr eq, ENNReal.tsum_mul_left, rest, mul_one]

theorem limbWeight_sum {A B : Type} [Fintype A] [Fintype B] (μ : A → BaseField) (ν : B → BaseField)
    (bd : A ⊕ B → Block × Block × Block) :
    limbWeight (Sum.elim μ ν) bd = limbWeight μ (bd ∘ Sum.inl) * limbWeight ν (bd ∘ Sum.inr) := by
  unfold limbWeight
  rw [Fintype.prod_sum_type]
  rfl

/-- Two independent limb families are one on the sum. -/
theorem tsum_limbs_sum {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (μ : A → BaseField) (ν : B → BaseField) (G : (A ⊕ B → Block × Block × Block) → ℝ≥0∞) :
    ∑' a : A → Block × Block × Block, limbWeight μ a *
        ∑' b : B → Block × Block × Block, limbWeight ν b * G (Sum.elim a b) =
      ∑' bd : A ⊕ B → Block × Block × Block, limbWeight (Sum.elim μ ν) bd * G bd := by
  rw [← (Equiv.sumArrowEquivProdArrow A B (Block × Block × Block)).symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  show _ = limbWeight (Sum.elim μ ν) (Sum.elim a b) * G (Sum.elim a b)
  rw [limbWeight_sum]
  show _ = limbWeight μ a * limbWeight ν b * G (Sum.elim a b)
  ring

end Restrict

/-! ### 2. The view's sites -/

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-- **F4's visible sites**: digit elements off the active and the designated switch, curve
elements off the active switch. -/
abbrev VisIdx :=
  (Fin digitCount × Σ e : Biquadratic.Element, {cs : ChunkSwitch // (offShape input).DigitVisibleAt e cs}) ⊕
    CurveW input

/-- A mask site is a (digit or curve) element and a (chunk, switch) pair. -/
def siteEquiv : MaskSite ≃ ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch :=
  maskSiteSplit.trans (Equiv.prodCongr laneSlots (Equiv.refl _))

/-- The key of a visible site. -/
def visKey : VisIdx input → ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch
  | .inl (d, ⟨e, cs⟩) => (.inl (d, e), cs.1)
  | .inr ⟨e, cs⟩ => (.inr e, cs.1)

/-- A visible site as a mask site. -/
def visSite (i : VisIdx input) : MaskSite := siteEquiv.symm (visKey input i)

noncomputable instance visIdxDecEq : DecidableEq (VisIdx input) := Classical.decEq _

/-- **The view's sites**: the visible and the designated ones. -/
abbrev WIdx := VisIdx input ⊕ DSite

noncomputable instance wIdxDecEq : DecidableEq (WIdx input) := Classical.decEq _

/-- The key of a view site. -/
def wKey : WIdx input → ((Fin digitCount × Biquadratic.Element) ⊕ CurveMembership.Element) × ChunkSwitch
  | .inl i => visKey input i
  | .inr (d, c) => (.inl (d, .inl (collectorElement c)), (offShape input).designated)

/-- A view site as a mask site. -/
def wSite (w : WIdx input) : MaskSite := siteEquiv.symm (wKey input w)

theorem desSite_eq (dc : DSite) :
    wSite input (.inr dc) = desSite (BitInput.ofAffine input) dc.1 dc.2 := rfl

theorem wKey_injective : Function.Injective (wKey input) := by
  rintro ((⟨d, e, cs, h⟩ | ⟨e, cs, h⟩) | ⟨d, c⟩) ((⟨d', e', cs', h'⟩ | ⟨e', cs', h'⟩) | ⟨d', c'⟩) same <;>
    simp only [wKey, visKey, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      and_false] at same
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    exact absurd ⟨(isCollector_inl _).mpr ⟨c', rfl⟩, rfl⟩ h.2
  · obtain ⟨rfl, rfl⟩ := same
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
    exact absurd ⟨(isCollector_inl _).mpr ⟨c, rfl⟩, rfl⟩ h'.2
  · obtain ⟨⟨rfl, same⟩, -⟩ := same
    have : c = c' := Kriterion.ArgoMAC.Phase3.Glue.collectorElement_injective same
    subst this
    rfl

theorem wSite_injective : Function.Injective (wSite input) := fun _ _ same =>
  wKey_injective input (siteEquiv.symm.injective same)

theorem visSite_injective : Function.Injective (visSite input) := fun i j same =>
  Sum.inl_injective (wSite_injective input (a₁ := .inl i) (a₂ := .inl j) same)

/-- **Every inactive site is a view site.** -/
theorem inact_cover (s : MaskSite) (inact : Inact input s) : ∃ w, wSite input w = s := by
  have back : siteEquiv.symm (siteEquiv s) = s := siteEquiv.symm_apply_apply s
  rcases hkey : siteEquiv s with ⟨(⟨d, e⟩ | e), cs⟩
  · rw [hkey] at back
    subst back
    by_cases visible : (offShape input).DigitVisibleAt e cs
    · exact ⟨.inl (.inl (d, ⟨e, ⟨cs, visible⟩⟩)), rfl⟩
    · have active : ¬ Active ((offShape input).digitAlpha e) cs := by
        rcases e with xe | ye <;> exact inact
      have des : IsCollector e ∧ cs = (offShape input).designated := by
        by_contra other
        exact visible ⟨active, other⟩
      obtain ⟨collector, rfl⟩ := des
      rcases e with xe | ye
      · obtain ⟨c, rfl⟩ := (isCollector_inl xe).mp collector
        exact ⟨.inr (d, c), rfl⟩
      · rcases collector with h | h | h <;> cases h
  · rw [hkey] at back
    subst back
    have active : ¬ Active ((offShape input).curveAlpha e) cs := by
      rcases e with xe | ye <;> exact inact
    exact ⟨.inl (.inr ⟨e, ⟨cs, active⟩⟩), rfl⟩

/-! ### 3. The kernel on the view sites -/

open Classical in
/-- A tape rebuilt from the view sites' triples. -/
def wTape (bd : WIdx input → Block × Block × Block) : Tape := fun c =>
  if h : ∃ w, wSite input w = c.1 then limbAt c.2 (bd (Classical.choose h)) else 0

theorem wTape_site (bd : WIdx input → Block × Block × Block) (w : WIdx input) (j : Fin 3) :
    wTape input bd (wSite input w, j) = limbAt j (bd w) := by
  have h : ∃ w', wSite input w' = wSite input w := ⟨w, rfl⟩
  unfold wTape
  rw [dif_pos h, wSite_injective input (Classical.choose_spec h)]

theorem limbAt_triplesOf {N : Type} (t : N × Fin 3 → Block) (n : N) (j : Fin 3) :
    limbAt j (triplesOf t n) = t (n, j) := by
  obtain ⟨j, hj⟩ := j
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- **The kernel on the view sites' triples.** -/
def onKW (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle) (x : VO → Block)
    (bd : WIdx input → Block × Block × Block) : ℝ≥0∞ :=
  onKV input Ψ P key E H x (fun c => wTape input bd c.1)

/-- **The kernel reads a tape only through its triples at the view sites.** -/
theorem onKV_tape (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle) (x : VO → Block)
    (T : Tape) :
    onKV input Ψ P key E H x (fun c => T c.1) =
      onKW input Ψ P key E H x (fun w => triplesOf T (wSite input w)) := by
  unfold onKW
  refine congrArg (onKV input Ψ P key E H x) ?_
  funext c
  obtain ⟨⟨s, j⟩, inact⟩ := c
  obtain ⟨w, rfl⟩ := inact_cover input s inact
  show T (wSite input w, j) = wTape input _ (wSite input w, j)
  rw [wTape_site, limbAt_triplesOf]

/-! ### 4. F4's visible and designated masks -/

/-- **F4's visible cells are the functions on the visible sites.** -/
def visEquiv : VisibleCells (offShape input) ≃ (VisIdx input → BaseField) where
  toFun vis i := match i with
    | .inl (d, ⟨e, cs⟩) => vis.1 d e cs
    | .inr ⟨e, cs⟩ => vis.2 e cs
  invFun f := (fun d e cs => f (.inl (d, ⟨e, cs⟩)), fun e cs => f (.inr ⟨e, cs⟩))
  left_inv _ := rfl
  right_inv f := funext fun i => by rcases i with ⟨d, e, cs⟩ | ⟨e, cs⟩ <;> rfl

theorem maskSiteEquiv_key (m : MaskSite → BaseField) (d : Fin digitCount) (e : Biquadratic.Element)
    (cs : ChunkSwitch) : (maskSiteEquiv m).1 d e cs = m (siteEquiv.symm (.inl (d, e), cs)) := rfl

theorem maskSiteEquiv_curveKey (m : MaskSite → BaseField) (e : CurveMembership.Element)
    (cs : ChunkSwitch) : (maskSiteEquiv m).2 e cs = m (siteEquiv.symm (.inr e, cs)) := rfl

/-- The visible masks of a mask family. -/
def visPart (m : MaskSite → BaseField) : VisibleCells (offShape input) :=
  (fun d => digitVisible (offShape input) ((maskSiteEquiv m).1 d),
    curveVisible (offShape input) (maskSiteEquiv m).2)

/-- The designated masks of a mask family. -/
def desPart (m : MaskSite → BaseField) : DSite → BaseField := fun dc =>
  (maskSiteEquiv m).1 dc.1 (.inl (collectorElement dc.2)) (offShape input).designated

/-- **A mask family at the view sites is its visible and designated masks.** -/
theorem masks_wSite (m : MaskSite → BaseField) :
    m ∘ wSite input = Sum.elim (visEquiv input (visPart input m)) (desPart input m) := by
  funext w
  rcases w with (⟨d, e, cs⟩ | ⟨e, cs⟩) | ⟨d, c⟩ <;> rfl

theorem masks_visSite (m : MaskSite → BaseField) :
    m ∘ visSite input = visEquiv input (visPart input m) := by
  funext i
  rcases i with ⟨d, e, cs⟩ | ⟨e, cs⟩ <;> rfl

/-! ### 5. The two tapes at the view -/

/-- **The garbler's tape at the view**: uniform masks, and the per-site limb laws at the view sites. -/
theorem real_tape (G : (MaskSite → BaseField) → (WIdx input → Block × Block × Block) → ℝ≥0∞) :
    ∑' T, fibreTape T * G (masksOf T) (fun w => triplesOf T (wSite input w)) =
      ∑' m, PMF.uniformOfFintype (MaskSite → BaseField) m *
        ∑' bd, limbWeight (m ∘ wSite input) bd * G m bd := by
  unfold fibreTape
  rw [tsum_bind_mul]
  refine tsum_congr fun m => congrArg _ ?_
  have onFibre : ∀ T, fibreLaw masksOf masksOf_onto m T * G (masksOf T) (fun w => triplesOf T (wSite input w)) =
      fibreLaw masksOf masksOf_onto m T * G m (fun w => triplesOf T (wSite input w)) := by
    intro T
    rw [fibreLaw_apply]
    split_ifs with hit
    · rw [hit]
    · rw [zero_mul, zero_mul]
  rw [tsum_congr onFibre]
  exact fibre_restrict (wSite input) (wSite_injective input) m (G m)

/-- **The private side's mask tape at the visible sites**: uniform visible masks, and the per-site
limb laws there. -/
theorem sim_tape (G : (VisIdx input → BaseField) → (VisIdx input → Block × Block × Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * G (masksOf T ∘ visSite input) (fun i => triplesOf T (visSite input i)) =
      ∑' μ, PMF.uniformOfFintype (VisIdx input → BaseField) μ *
        ∑' bd, limbWeight μ bd * G μ bd := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  have perMask : ∀ m : MaskSite → BaseField,
      ∑' T, fibreLaw masksOf masksOf_surjective m T *
          G (masksOf T ∘ visSite input) (fun i => triplesOf T (visSite input i)) =
        ∑' bd, limbWeight (m ∘ visSite input) bd * G (m ∘ visSite input) bd := by
    intro m
    have onFibre : ∀ T, fibreLaw masksOf masksOf_surjective m T *
        G (masksOf T ∘ visSite input) (fun i => triplesOf T (visSite input i)) =
        fibreLaw masksOf masksOf_onto m T *
          G (m ∘ visSite input) (fun i => triplesOf T (visSite input i)) := by
      intro T
      rw [fibreLaw_proof_irrel masksOf masksOf_surjective masksOf_onto m, fibreLaw_apply]
      split_ifs with hit
      · rw [hit]
      · rw [zero_mul, zero_mul]
    rw [tsum_congr onFibre]
    exact fibre_restrict (visSite input) (visSite_injective input) m (G (m ∘ visSite input))
  rw [tsum_congr fun m => congrArg _ (perMask m)]
  exact tsum_restrict (visSite input) (visSite_injective input)
    (fun μ => ∑' bd, limbWeight μ bd * G μ bd)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
