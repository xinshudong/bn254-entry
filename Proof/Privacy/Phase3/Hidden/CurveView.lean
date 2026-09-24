/-
**Phase 3, P1h — `StageTwoBridgeGuess`, real: off the curve, `t` is `1/(p−1)`-hidden given the
stage-2 view.**

The curve family changes the hidden (active-switch) curve masks, and the swapped tape's density is not
invariant under a mask-changing map of permutations. So work on the **curve coordinates**
`(rest, site permutations off the hidden sites, masks at the hidden sites)` (`curveCoord`):

* under the swapped tape they are `rest × swapKernel(off) × uniform` (`swapped_curveCoord`, from
  `Split.swapKernel_split` and `swapKernel_masks`);
* off the curve the stage-2 view factors through them (`view_eq`): the published value through
  `publishedOf` of the combined masks, the EncPRF entries and the labels through the rest, the
  designed entries through the curve lanes' off-hidden permutations (`CurveDesigned`);
* the curve family acts on them (`curveShiftCoord`: the rest by `curveRest`, the hidden masks by the
  correction), keeps their law (`curveLaw_shift`) and the view (`curveView_shift`), and moves `t`
  injectively in `c ∈ F_p^*` (`curveRest_bridgeKey_injective`).

`event_le_of_symmetry` over the `p − 1` units, transferred back: `stageTwoBridgeGuess`.
-/

import Proof.Privacy.Phase3.Hidden.CurveDesigned

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-! ### The curve coordinates -/

/-- The site permutations of a tape. -/
def sitePermsOf (tape : Coins × Oracle) : SitePerms MaskSite :=
  fun site => tape.2.1.permutation (siteIndex site)

/-- The garbler's points off the hidden sites. -/
def pointOff (input : AffineInput) (rest : RestTape TapeRest) :
    SiteOff (IsHidden input) × Fin 3 → Block :=
  restrictPoint (fun m => ¬ IsHidden input m) (planBPoint garblerKeys rest)

/-- The garbler's points at the hidden sites. -/
def pointOn (input : AffineInput) (rest : RestTape TapeRest) : SiteOn (IsHidden input) × Fin 3 → Block :=
  restrictPoint (IsHidden input) (planBPoint garblerKeys rest)

/-- **The curve coordinates.** -/
abbrev CurveCoord (input : AffineInput) :=
  RestTape TapeRest × SitePerms (SiteOff (IsHidden input)) × (SiteOn (IsHidden input) → BaseField)

/-- The curve coordinates of a tape. -/
def curveCoord (input : AffineInput) (tape : Coins × Oracle) : CurveCoord input :=
  (restOf tape, (splitPerms (IsHidden input) (sitePermsOf tape)).1,
    (splitMasks (IsHidden input) (maskOf tape)).2)

/-- The masks from the curve coordinates. -/
def combineMasks (input : AffineInput) (z : CurveCoord input) : MaskSite → BaseField :=
  (splitMasks (IsHidden input)).symm (maskMap (pointOff input z.1) z.2.1, z.2.2)

theorem maskOf_eq (tape : Coins × Oracle) :
    maskOf tape = maskMap (planBPoint garblerKeys (restOf tape)) (sitePermsOf tape) := by
  have oracle : tape.2.1 = oracleOf (restOf tape).2 (sitePermsOf tape) := (oracleOf_splitParts tape.2.1).symm
  unfold maskOf
  conv_lhs => rw [oracle]
  exact garblerMask_oracleOf garblerKeys (restOf tape) (sitePermsOf tape)

theorem maskOf_combine (input : AffineInput) (tape : Coins × Oracle) :
    maskOf tape = combineMasks input (curveCoord input tape) := by
  unfold combineMasks curveCoord
  apply (splitMasks (IsHidden input)).injective
  rw [Equiv.apply_symm_apply]
  refine Prod.ext ?_ rfl
  show (splitMasks (IsHidden input) (maskOf tape)).1 = _
  rw [maskOf_eq, maskMap_split]
  rfl

/-- A tape with the given rest and off-hidden permutations (identity at the hidden sites). -/
def curveTape (input : AffineInput) (rest : RestTape TapeRest) (off : SitePerms (SiteOff (IsHidden input))) :
    Coins × Oracle :=
  reassembleEquiv (assemble (rest, (splitPerms (IsHidden input)).symm (off, fun _ => Equiv.refl Block)))

/-- **The stage-2 view on the curve coordinates.** -/
def curveView (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (z : CurveCoord input) :
    (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex) :=
  ((publishedOf scalar (z.1, combineMasks input z), encOf z.1), Scheme.scheme.encode z.1.1.1.inputMacKey input,
    curveDesigned scalar (curveTape input z.1 z.2.1) input)

theorem curveTape_agree (input : AffineInput) (tape : Coins × Oracle) :
    ∀ index, ¬ IsHIndex input index →
      tape.2.1.permutation index = (curveTape input (restOf tape) (curveCoord input tape).2.1).2.1.permutation index := by
  intro index notH
  show _ = (oracleOf (restOf tape).2 _).permutation index
  by_cases site : index ∈ Set.range siteIndex
  · obtain ⟨site, rfl⟩ := site
    rw [oracleOf_site]
    have off : ¬ IsHidden input site.1 := fun h => notH ⟨site, rfl, h⟩
    show _ = (splitPerms (IsHidden input)).symm ((splitPerms (IsHidden input) (sitePermsOf tape)).1,
      fun _ => Equiv.refl Block) site
    simp only [splitPerms, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, dif_neg off]
    rfl
  · rw [oracleOf_other (restOf tape).2 _ ⟨index, site⟩]
    rfl

/-- **Off the curve, the stage-2 view factors through the curve coordinates.** -/
theorem view_eq (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (invalid : validate input = false)
    (tape : Coins × Oracle) :
    stageTwoView designedRule parameter scalar input tape = curveView parameter scalar input (curveCoord input tape) := by
  have designed : curveDesigned scalar (curveTape input (restOf tape) (curveCoord input tape).2.1) input =
      curveDesigned scalar tape input :=
    curveDesigned_congr scalar tape _ input rfl rfl rfl fun index h => (curveTape_agree input tape index h).symm
  unfold stageTwoView stageOneView curveView
  rw [published_eq, encEntries_eq, designedEntries_offCurve parameter scalar tape input invalid,
    maskOf_combine input tape]
  exact Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl designed.symm)

/-! ### The law of the curve coordinates -/

/-- **The law of the curve coordinates under the swapped tape.** -/
def curveLaw (input : AffineInput) : PMF (CurveCoord input) :=
  (restLaw restUniform).bind fun rest =>
    (productPMF (swapKernel (pointOff input rest)) (PMF.uniformOfFintype (SiteOn (IsHidden input) → BaseField))).map
      fun q => (rest, q.1, q.2)

theorem curveCoord_assemble (input : AffineInput) (rest : RestTape TapeRest) (scale : SitePerms MaskSite) :
    curveCoord input (reassembleEquiv (assemble (rest, scale))) =
      (rest, (splitPerms (IsHidden input) scale).1,
        maskMap (pointOn input rest) (splitPerms (IsHidden input) scale).2) := by
  have restEq : restOf (reassembleEquiv (assemble (rest, scale))) = rest := by
    obtain ⟨⟨coins, enc, hash⟩, other⟩ := rest
    show ((coins, enc, hash), fun index : OtherIndex => (oracleOf other scale).permutation index.1) = _
    refine Prod.ext rfl (funext fun index => oracleOf_other other scale index)
  have sitesEq : sitePermsOf (reassembleEquiv (assemble (rest, scale))) = scale :=
    funext fun site => oracleOf_site rest.2 scale site
  unfold curveCoord
  rw [restEq, sitesEq, maskOf_eq, restEq, sitesEq, maskMap_split]
  rfl

/-- **Under the swapped tape the curve coordinates have `curveLaw`.** -/
theorem swapped_curveCoord (input : AffineInput) :
    swappedChallengeTape.map (curveCoord input) = curveLaw input := by
  unfold swappedChallengeTape swappedTape swapLaw curveLaw
  rw [PMF.map_comp, PMF.map_comp, PMF.map_bind]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp]
  have factor : ((curveCoord input ∘ reassembleEquiv) ∘ assemble) ∘ Prod.mk rest =
      (fun q => (rest, q.1, q.2)) ∘ Prod.map id (maskMap (pointOn input rest)) ∘ splitPerms (IsHidden input) := by
    funext scale
    exact curveCoord_assemble input rest scale
  rw [factor, ← PMF.map_comp, ← PMF.map_comp, swapKernel_split, productPMF_map, PMF.map_id,
    show restrictPoint (IsHidden input) (planBPoint garblerKeys rest) = pointOn input rest from rfl,
    swapKernel_masks]
  rfl

/-! ### The family on the curve coordinates -/

/-- **The curve family on the coordinates.** -/
def curveShiftCoord (input : AffineInput) (c : BaseFieldˣ) (z : CurveCoord input) : CurveCoord input :=
  (curveRest input c z.1, z.2.1, fun h => z.2.2 h - siteCorr input (curveStep c z.1) h.1)

theorem planBPoint_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    planBPoint garblerKeys (curveRest input c rest) = planBPoint garblerKeys rest := by
  unfold planBPoint
  rw [garblerKeys_curve]
  rfl

theorem pointOff_curve (input : AffineInput) (c : BaseFieldˣ) (rest : RestTape TapeRest) :
    pointOff input (curveRest input c rest) = pointOff input rest := by
  unfold pointOff
  rw [planBPoint_curve]

theorem restLaw_uniform : restLaw restUniform = PMF.uniformOfFintype (RestTape TapeRest) := by
  rw [restLaw, restUniform, ← uniformOfFintype_productPMF]

/-- **The curve family keeps the law of the curve coordinates.** -/
theorem curveLaw_shift (input : AffineInput) (c : BaseFieldˣ) :
    (curveLaw input).map (curveShiftCoord input c) = curveLaw input := by
  unfold curveLaw
  rw [PMF.map_bind]
  have each : ∀ rest : RestTape TapeRest,
      ((productPMF (swapKernel (pointOff input rest))
          (PMF.uniformOfFintype (SiteOn (IsHidden input) → BaseField))).map fun q => (rest, q.1, q.2)).map
        (curveShiftCoord input c) =
      (productPMF (swapKernel (pointOff input (curveRest input c rest)))
          (PMF.uniformOfFintype (SiteOn (IsHidden input) → BaseField))).map
        fun q => (curveRest input c rest, q.1, q.2) := by
    intro rest
    rw [PMF.map_comp, pointOff_curve]
    have factor : (curveShiftCoord input c ∘ fun q => (rest, q.1, q.2)) =
        (fun q => (curveRest input c rest, q.1, q.2)) ∘
          Prod.map id (Equiv.subRight fun h : SiteOn (IsHidden input) => siteCorr input (curveStep c rest) h.1) := rfl
    rw [factor, ← PMF.map_comp, productPMF_map, PMF.map_id, uniformOfFintype_map_equiv]
  simp only [each]
  rw [restLaw_uniform]
  conv_rhs => rw [← uniformOfFintype_map_equiv (curveRestEquiv input c)]
  rw [PMF.bind_map]
  rfl

theorem combineMasks_shift (input : AffineInput) (c : BaseFieldˣ) (z : CurveCoord input) :
    combineMasks input (curveShiftCoord input c z) = curveMasks input (curveStep c z.1) (combineMasks input z) := by
  funext site
  unfold combineMasks curveShiftCoord curveMasks
  simp only [splitMasks, Equiv.coe_fn_symm_mk]
  by_cases h : IsHidden input site
  · rw [dif_pos h, if_pos h, dif_pos h]
  · rw [dif_neg h, if_neg h, dif_neg h, pointOff_curve]

/-- **The curve family keeps the view.** -/
theorem curveView_shift (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (c : BaseFieldˣ)
    (z : CurveCoord input) :
    curveView parameter scalar input (curveShiftCoord input c z) = curveView parameter scalar input z := by
  have e1 : publishedOf scalar ((curveShiftCoord input c z).1,
      curveMasks input (curveStep c z.1) (combineMasks input z)) = publishedOf scalar (z.1, combineMasks input z) :=
    publishedOf_curve scalar input c z.1 (combineMasks input z)
  have e2 : encOf (curveShiftCoord input c z).1 = encOf z.1 := encOf_curve input c z.1
  have oracleSame : (curveTape input (curveShiftCoord input c z).1 (curveShiftCoord input c z).2.1).2.1 =
      (curveTape input z.1 z.2.1).2.1 := rfl
  have e3 : curveDesigned scalar (curveTape input (curveShiftCoord input c z).1 (curveShiftCoord input c z).2.1)
      input = curveDesigned scalar (curveTape input z.1 z.2.1) input :=
    curveDesigned_congr scalar (curveTape input z.1 z.2.1) _ input rfl rfl rfl fun index _ => by rw [oracleSame]
  have e4 : (curveShiftCoord input c z).1.1.1.inputMacKey = z.1.1.1.inputMacKey := rfl
  unfold curveView
  rw [combineMasks_shift, e1, e2, e3, e4]

/-! ### The bound -/

theorem card_units_base : Fintype.card BaseFieldˣ = baseFieldModulus - 1 := by
  rw [← ZMod.card_units baseFieldModulus]

/-- **`StageTwoBridgeGuess`, real.** -/
theorem stageTwoBridgeGuess : StageTwoBridgeGuess := by
  intro field group parameter scalar input view key invalid
  let Φ := curveCoord input
  have transfer : ∀ S : Set (CurveCoord input),
      swappedChallengeTape.toOuterMeasure (Φ ⁻¹' S) = (curveLaw input).toOuterMeasure S := by
    intro S
    rw [← swapped_curveCoord input, PMF.toOuterMeasure_map_apply]
  have left : {tape : Coins × Oracle | stageTwoView designedRule parameter scalar input tape = view ∧
      tape.1.bridgeKey = key} = Φ ⁻¹' {z | curveView parameter scalar input z = view ∧ z.1.1.1.bridgeKey = key} := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_preimage, view_eq parameter scalar input invalid tape]
    rfl
  have right : {tape : Coins × Oracle | stageTwoView designedRule parameter scalar input tape = view} =
      Φ ⁻¹' {z | curveView parameter scalar input z = view} := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_preimage, view_eq parameter scalar input invalid tape]
    rfl
  rw [left, right, transfer, transfer]
  have bound := event_le_of_symmetry (curveLaw input) (curveView parameter scalar input)
    (fun z => z.1.1.1.bridgeKey = key) (fun c => curveShiftCoord input c)
    (fun c => curveLaw_shift input c) (fun c z => curveView_shift parameter scalar input c z)
    (fun z c c' first second => curveRest_bridgeKey_injective input invalid z.1 c c' (first.trans second.symm))
    view
  rwa [card_units_base] at bound

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
