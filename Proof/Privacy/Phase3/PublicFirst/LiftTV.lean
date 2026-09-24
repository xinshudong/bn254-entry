/-
**Phase 3, P1j — the lift, part 3: the designed shadow and the refined mask-tape distance.**

**The designed shadow** (`designedShadow scalar := planBShadow scalar designedOff`): on the curve
P1i's (the prefix again, the bit-`true` pads, the whole evaluator, the generalised exceptional
reveal); **off the curve** `designedOff`: both pads of every position at a uniform coin `k₁`
(`Programs.padsM`, the garbler's own EncPRF questions) and system A's two lanes (`systemAM`, the
evaluator's; exactly the designed entries of `G1U°` off the curve), no reveal flag.

**The refined distance** (`designedShadow_etvDist_le`): the two tape readings of `M'` are within
`#CurveSite · δ₃ = 2540 · δ₃`, not `N·δ₃`:

* the off-curve fill of the designed shadow asks fixed-key questions only on the curve lanes
  (`designedOffM_allQ`: `evalLaneM_allQ`; the pads are EncPRF), so it reads the tape only at the
  curve lanes' cells (`runFillFlag_tape_congr_on`);
* the mask tape restricted to those cells is the mask tape of the curve sites
  (`maskTape_restrict`: the fibre of the per-site `sampleFp` map splits, `fibreSplit`), and the
  uniform tape restricts to the uniform one (`uniform_restrict`);
* so the distance is `MaskSwap`'s at `M := CurveSite` (`fill_etvDist_le`, `masksOf_etvDist_le`),
  and `#CurveSite = 127 · 4 · (3 + 2) = 2540` (`card_curveSite`).

`LiftHop.lean`'s budget is stated at `offCurveSites = 2540` (`coincidence_slack`:
`2^272 ≤ 416052 · (2^384 mod p)`). **`planB_publicFirst_of_lift`**: the Glue's `publicFirst` from
`DesignedLift` (the F4 lift for the designed shadow, at the designed rule), `DesignedBounds`
(P1k's (B1)/(B2) for the designed shadow) and `CoincidenceBound coincidenceError`.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftHop
import Proof.Privacy.Phase3.PublicFirst.Shadow
import Proof.Privacy.Phase3.Lazy.Decompose

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option exponentiation.threshold 500
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary Stage1Source maskSwapError)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Tape Cell Request uniformMaskTape AllQ FixedAt IndexAt
  EncAt consumeCell_spec evalLaneM_allQ padM_allQ etvDist_bind_le_of_support masksOf_surjective)
open scoped ENNReal

noncomputable section

/-! ### 1. The designed off-curve shadow -/

section Shadow

variable [FieldCertificate] [GroupCertificate]

/-- **System A's two lanes**: the evaluator's prefix without the bridge hash. -/
def systemAM (table : Public) (bits : BitInput) (mac : InputMac) : Programs.M Unit :=
  Programs.evalLaneM curveElementCountX .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun _ =>
    Programs.evalLaneM curveElementCountY .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun _ => pure ()

/-- **The designed off-curve questions**: both pads of every position at the key `k₁`, then
system A. -/
def designedOffM (table : Public) (bits : BitInput) (mac : InputMac) (first : Block) :
    Programs.M Unit :=
  Programs.padsM ⟨first, 0⟩ >>= fun _ => systemAM table bits mac

/-- **The designed off-curve shadow**: a uniform `k₁`, the pads and system A, no reveal. -/
def designedOff : OffShadow where
  Coin := Block
  law := PMF.uniformOfFintype Block
  offCurve source input first :=
    designedOffM source.publicValue (Lamport.restore input (sourceLabels source input)).input
      (Lamport.restore input (sourceLabels source input)).inputMac first
  revealOff _ _ _ _ := False

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The designed shadow of `M'`**: P1i's on the curve, `designedOff` off it. -/
def designedShadow (scalar : NonZeroScalar) : Shadow := planBShadow scalar designedOff

end Shadow

/-! ### 2. The curve sites and their cells -/

/-- A curve-lane mask site (system A). -/
def CurveSiteP (site : MaskSite) : Prop := laneIsCurve site.1 = true

instance : DecidablePred CurveSiteP := fun site =>
  inferInstanceAs (Decidable (laneIsCurve site.1 = true))

/-- The curve-lane mask sites. -/
abbrev CurveSite := {site : MaskSite // CurveSiteP site}

/-- The other mask sites. -/
abbrev OtherSite := {site : MaskSite // ¬ CurveSiteP site}

noncomputable instance curveTapeFintype : Fintype (CurveSite × Fin 3 → Block) := Pi.instFintype

noncomputable instance otherTapeFintype : Fintype (OtherSite × Fin 3 → Block) := Pi.instFintype

noncomputable instance curveMasksFintype : Fintype (CurveSite → BaseField) := Pi.instFintype

noncomputable instance otherMasksFintype : Fintype (OtherSite → BaseField) := Pi.instFintype

/-- The curve sites, as a sigma type over the two curve lanes. -/
def curveSiteEquiv : CurveSite ≃
    Σ lane : {lane : Lane // laneIsCurve lane = true},
      Σ chunk : Fin chunkCount, Fin (2 ^ chunkWidth chunk) × Fin (laneCount lane.1) where
  toFun site := ⟨⟨site.1.1, site.2⟩, site.1.2⟩
  invFun site := ⟨⟨site.1.1, site.2⟩, site.1.2⟩
  left_inv site := rfl
  right_inv site := rfl

/-- **`#CurveSite = 127 · 4 · (3 + 2) = 2540`.** -/
theorem card_curveSite : Fintype.card CurveSite = 2540 := by
  rw [Fintype.card_congr curveSiteEquiv, Fintype.card_sigma]
  have each : ∀ lane : {lane : Lane // laneIsCurve lane = true},
      Fintype.card (Σ chunk : Fin chunkCount, Fin (2 ^ chunkWidth chunk) × Fin (laneCount lane.1))
        = 508 * laneCount lane.1 := by
    intro lane
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [← Finset.sum_mul, sum_twoPow_chunkWidth]
  simp only [each]
  decide

/-- The curve cells of a tape. -/
def curvePart (tape : Tape) : CurveSite × Fin 3 → Block := fun cell => tape (cell.1.1, cell.2)

/-- The other cells of a tape. -/
def otherPart (tape : Tape) : OtherSite × Fin 3 → Block := fun cell => tape (cell.1.1, cell.2)

/-- A tape from its two parts. -/
def joinParts (curve : CurveSite × Fin 3 → Block) (other : OtherSite × Fin 3 → Block) : Tape :=
  fun cell => if inside : CurveSiteP cell.1 then curve (⟨cell.1, inside⟩, cell.2)
    else other (⟨cell.1, inside⟩, cell.2)

/-- **The tape splits into its curve cells and the others.** -/
def tapeSplit : Tape ≃ (CurveSite × Fin 3 → Block) × (OtherSite × Fin 3 → Block) where
  toFun tape := (curvePart tape, otherPart tape)
  invFun parts := joinParts parts.1 parts.2
  left_inv tape := by
    funext cell
    show joinParts (curvePart tape) (otherPart tape) cell = tape cell
    unfold joinParts curvePart otherPart
    split <;> rfl
  right_inv parts := by
    obtain ⟨curve, other⟩ := parts
    refine Prod.ext (funext fun cell => ?_) (funext fun cell => ?_)
    · show joinParts curve other (cell.1.1, cell.2) = curve cell
      unfold joinParts
      rw [dif_pos cell.1.2]
    · show joinParts curve other (cell.1.1, cell.2) = other cell
      unfold joinParts
      rw [dif_neg cell.1.2]

/-- The curve masks of a mask family. -/
def curveMasks (masks : MaskSite → BaseField) : CurveSite → BaseField := fun site => masks site.1

/-- The other masks of a mask family. -/
def otherMasks (masks : MaskSite → BaseField) : OtherSite → BaseField := fun site => masks site.1

/-- **The masks split likewise.** -/
def maskSplit : (MaskSite → BaseField) ≃ (CurveSite → BaseField) × (OtherSite → BaseField) where
  toFun masks := (curveMasks masks, otherMasks masks)
  invFun parts := fun site => if inside : CurveSiteP site then parts.1 ⟨site, inside⟩
    else parts.2 ⟨site, inside⟩
  left_inv masks := by
    funext site
    show (if inside : CurveSiteP site then curveMasks masks ⟨site, inside⟩
      else otherMasks masks ⟨site, inside⟩) = masks site
    unfold curveMasks otherMasks
    split <;> rfl
  right_inv parts := by
    obtain ⟨curve, other⟩ := parts
    refine Prod.ext (funext fun site => ?_) (funext fun site => ?_)
    · show (if inside : CurveSiteP site.1 then curve ⟨site.1, inside⟩ else other ⟨site.1, inside⟩)
        = curve site
      rw [dif_pos site.2]
    · show (if inside : CurveSiteP site.1 then curve ⟨site.1, inside⟩ else other ⟨site.1, inside⟩)
        = other site
      rw [dif_neg site.2]

theorem curveMasks_masksOf (tape : Tape) :
    curveMasks (masksOf tape) = masksOf (curvePart tape) := rfl

theorem otherMasks_masksOf (tape : Tape) :
    otherMasks (masksOf tape) = masksOf (otherPart tape) := rfl

/-! ### 3. The fibre splits, and the mask tape restricts -/

/-- **The fibre of the mask map splits** into the curve fibre and the other fibre. -/
def fibreSplit (masks : MaskSite → BaseField) :
    {tape : Tape // masksOf tape = masks} ≃
      {curve : CurveSite × Fin 3 → Block // masksOf curve = curveMasks masks} ×
        {other : OtherSite × Fin 3 → Block // masksOf other = otherMasks masks} where
  toFun tape := (⟨curvePart tape.1, by rw [← curveMasks_masksOf, tape.2]⟩,
    ⟨otherPart tape.1, by rw [← otherMasks_masksOf, tape.2]⟩)
  invFun parts := ⟨joinParts parts.1.1 parts.2.1, by
    have curveEq := parts.1.2
    have otherEq := parts.2.2
    funext site
    by_cases inside : CurveSiteP site
    · have := congrFun curveEq ⟨site, inside⟩
      simpa [masksOf, joinParts, inside, curveMasks] using this
    · have := congrFun otherEq ⟨site, inside⟩
      simpa [masksOf, joinParts, inside, otherMasks] using this⟩
  left_inv tape := by
    apply Subtype.ext
    exact tapeSplit.left_inv tape.1
  right_inv parts := by
    obtain ⟨⟨curve, curveEq⟩, ⟨other, otherEq⟩⟩ := parts
    have both := tapeSplit.right_inv (curve, other)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Prod.fst both
    · exact congrArg Prod.snd both

theorem masksOf_surjective_curve :
    Function.Surjective (masksOf : (CurveSite × Fin 3 → Block) → CurveSite → BaseField) := by
  intro masks
  have each : ∀ site, ∃ triple : Block × Block × Block,
      sampleFp triple.1 triple.2.1 triple.2.2 = masks site :=
    fun site => sampleFp_surjective (masks site)
  choose triple hTriple using each
  refine ⟨fun cell => ![(triple cell.1).1, (triple cell.1).2.1, (triple cell.1).2.2] cell.2, ?_⟩
  funext site
  exact hTriple site

/-- The mask tape of the curve sites. -/
def curveMaskTape : PMF (CurveSite × Fin 3 → Block) :=
  (PMF.uniformOfFintype (CurveSite → BaseField)).bind
    (fibreLaw masksOf masksOf_surjective_curve)

/-- A map along an equivalence reads the law at the preimage. -/
theorem uniform_map_fst_of_equiv {X A B : Type} [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (split : X ≃ A × B) (first : X → A)
    (agree : ∀ x, first x = (split x).1) :
    (PMF.uniformOfFintype X).map first = PMF.uniformOfFintype A := by
  have factor : first = Prod.fst ∘ split := funext agree
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv,
    uniformOfFintype_productPMF]
  unfold productPMF
  rw [PMF.map_bind]
  have constant : ∀ a : A, ((PMF.uniformOfFintype B).map (Prod.mk a)).map Prod.fst = PMF.pure a :=
    fun a => by rw [PMF.map_comp]; exact PMF.map_const _ a
  simp only [constant]
  exact PMF.bind_pure _

/-- **The curve fibre law is the curve part of the fibre law.** -/
theorem fibreLaw_curvePart (masks : MaskSite → BaseField) :
    (fibreLaw masksOf masksOf_surjective masks).map curvePart =
      fibreLaw masksOf masksOf_surjective_curve (curveMasks masks) := by
  classical
  haveI : Nonempty {tape : Tape // masksOf tape = masks} :=
    ⟨⟨Classical.choose (masksOf_surjective masks), Classical.choose_spec (masksOf_surjective masks)⟩⟩
  haveI : Nonempty {curve : CurveSite × Fin 3 → Block // masksOf curve = curveMasks masks} :=
    ⟨⟨Classical.choose (masksOf_surjective_curve (curveMasks masks)),
      Classical.choose_spec (masksOf_surjective_curve (curveMasks masks))⟩⟩
  haveI : Nonempty {other : OtherSite × Fin 3 → Block // masksOf other = otherMasks masks} :=
    ⟨(fibreSplit masks ⟨Classical.choose (masksOf_surjective masks),
      Classical.choose_spec (masksOf_surjective masks)⟩).2⟩
  unfold fibreLaw
  rw [PMF.map_comp]
  have marginal := uniform_map_fst_of_equiv (fibreSplit masks)
    (fun tape => (⟨curvePart tape.1, by rw [← curveMasks_masksOf, tape.2]⟩ :
      {curve : CurveSite × Fin 3 → Block // masksOf curve = curveMasks masks}))
    (fun _ => rfl)
  have factor : (curvePart ∘ Subtype.val : {tape : Tape // masksOf tape = masks} → _) =
      Subtype.val ∘ (fun tape => (⟨curvePart tape.1, by rw [← curveMasks_masksOf, tape.2]⟩ :
        {curve : CurveSite × Fin 3 → Block // masksOf curve = curveMasks masks})) := rfl
  rw [factor, ← PMF.map_comp, marginal]

/-- **The mask tape restricted to the curve cells is the curve mask tape.** -/
theorem maskTape_restrict : uniformMaskTape.map curvePart = curveMaskTape := by
  unfold uniformMaskTape curveMaskTape
  rw [PMF.map_bind]
  have step : (fun masks => (fibreLaw masksOf masksOf_surjective masks).map curvePart) =
      (fibreLaw masksOf masksOf_surjective_curve) ∘ curveMasks :=
    funext fibreLaw_curvePart
  rw [step, ← PMF.bind_map, uniform_map_fst_of_equiv maskSplit curveMasks (fun _ => rfl)]

/-- **The uniform tape restricts to the uniform one.** -/
theorem uniform_restrict :
    (PMF.uniformOfFintype Tape).map curvePart = PMF.uniformOfFintype (CurveSite × Fin 3 → Block) :=
  uniform_map_fst_of_equiv tapeSplit curvePart (fun _ => rfl)

/-- **The refined distance**: a law read off the curve cells only moves by `#CurveSite · δ₃`. -/
theorem fill_etvDist_le {β : Type} (read : Tape → PMF β)
    (local_ : ∀ first second, curvePart first = curvePart second → read first = read second) :
    (uniformMaskTape.bind read).etvDist ((PMF.uniformOfFintype Tape).bind read)
      ≤ (Fintype.card CurveSite : ℝ≥0∞) * delta3 := by
  let extend : (CurveSite × Fin 3 → Block) → Tape := fun curve => joinParts curve fun _ => 0
  have restrictExtend : ∀ curve, curvePart (extend curve) = curve := fun curve =>
    congrArg Prod.fst (tapeSplit.right_inv (curve, fun _ => 0))
  have factor : read = (read ∘ extend) ∘ curvePart :=
    funext fun tape => local_ tape _ (restrictExtend (curvePart tape)).symm
  rw [factor, ← PMF.bind_map uniformMaskTape curvePart (read ∘ extend),
    ← PMF.bind_map (PMF.uniformOfFintype Tape) curvePart (read ∘ extend), maskTape_restrict,
    uniform_restrict]
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  unfold curveMaskTape
  rw [uniform_eq_bind_fibreLaw (masksOf : (CurveSite × Fin 3 → Block) → CurveSite → BaseField)
    masksOf_surjective_curve]
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  rw [PMF.etvDist_comm]
  exact masksOf_etvDist_le

/-! ### 4. The designed off-curve fill reads only the curve cells -/

/-- A question consumes, if anything, a curve cell. -/
def CurveCellsOnly : Request → Prop
  | .fixedForward index _ => ∀ cell : Cell, siteIndex cell = index → CurveSiteP cell.1
  | _ => True

theorem curveCellsOnly_of_lane (lane : Lane) (curve : laneIsCurve lane = true) (request : Request)
    (inside : FixedAt (fun index => ∃ c, IndexAt lane c index) request) :
    CurveCellsOnly request := by
  cases request with
  | fixedForward index input =>
    intro cell same
    obtain ⟨c, at_⟩ := inside
    unfold siteIndex scaleIndexOf scaleIndexNat at same
    subst same
    obtain ⟨laneEq, _⟩ := at_
    unfold CurveSiteP
    rw [laneEq]
    exact curve
  | fixedInverse _ _ => trivial
  | encForward _ _ => trivial
  | encInverse _ _ => trivial
  | hash _ => trivial

theorem curveCellsOnly_of_enc (request : Request) (inside : EncAt request) :
    CurveCellsOnly request := by
  cases request with
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => trivial
  | encForward _ _ => trivial
  | encInverse _ _ => trivial
  | hash _ => trivial

theorem padsM_allQ (keys : WhiteningKeys) : AllQ EncAt (Programs.padsM keys) := by
  unfold Programs.padsM
  exact (AllQ.vector fun _ => (padM_allQ _ _ _ _).bind fun _ =>
    (padM_allQ _ _ _ _).bind fun _ => .pure _).bind fun _ =>
      (AllQ.vector fun _ => (padM_allQ _ _ _ _).bind fun _ =>
        (padM_allQ _ _ _ _).bind fun _ => .pure _).bind fun _ => .pure _

theorem designedOffM_allQ [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)
    (first : Block) : AllQ CurveCellsOnly (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine ((padsM_allQ _).mono curveCellsOnly_of_enc).bind fun _ => ?_
  refine ((evalLaneM_allQ _ _ _ _ _ _).mono (curveCellsOnly_of_lane .curveX rfl)).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _ _).mono (curveCellsOnly_of_lane .curveY rfl)).bind fun _ =>
    .pure _

section Fill

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **The fill reads the tape only at the cells its questions consume.** -/
theorem runFillFlag_tape_congr_on (planted : LState) {α : Type}
    {computation : FreeQuery Programs.Spec α} (holds : AllQ CurveCellsOnly computation) :
    ∀ (oracle : LState) (touched : Set FixedIndex) (first second : Tape),
      curvePart first = curvePart second →
      runFillFlag planted (fun cell => PMF.pure (first cell)) computation oracle touched =
        runFillFlag planted (fun cell => PMF.pure (second cell)) computation oracle touched := by
  induction holds with
  | pure value => intros; rfl
  | query request next here _ ih =>
      intro oracle touched first second agree
      simp only [runFillFlag]
      split
      · rename_i cell consumed
        obtain ⟨index, input, rfl, _, _, siteEq⟩ := consumeCell_spec consumed
        have curve : CurveSiteP cell.1 := here cell siteEq
        have same : first cell = second cell :=
          congrFun agree (⟨cell.1, curve⟩, cell.2)
        rw [same]
        congr 1
        funext limb
        split
        · rfl
        · split
          · rfl
          · exact ih _ _ _ _ _ agree
      · congr 1
        funext answer
        split
        · rfl
        · exact ih _ _ _ _ _ agree

end Fill

/-! ### 5. The refined distance of the designed shadow's `M'` -/

section Distance

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The two tape readings of the designed shadow's `M'` are within `2540 · δ₃`.** -/
theorem designedShadow_etvDist_le (scalar : NonZeroScalar) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) :
    (middleGameFill uniformMaskTape (designedShadow scalar) adversary parameter scalar).etvDist
        (middleGameFill (PMF.uniformOfFintype Tape) (designedShadow scalar) adversary parameter
          scalar)
      ≤ (Fintype.card CurveSite : ℝ≥0∞) * delta3 := by
  unfold middleGameFill
  refine etvDist_bind_le_of_support _ _ _ _ fun source _ => ?_
  refine etvDist_bind_le_of_support _ _ _ _ fun selected _ => ?_
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  generalize Scheme.scheme.function scalar selected.1.1 = output
  cases output with
  | some target =>
    simp only [middleStage2Fill, PMF.etvDist_self]
    exact zero_le
  | none =>
    simp only [middleStage2Fill]
    refine etvDist_bind_le_of_support _ _ _ _ fun coin _ => ?_
    refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
    exact fill_etvDist_le _ fun first second agree =>
      runFillFlag_tape_congr_on selected.2 (designedOffM_allQ _ _ _ _) _ _ first second agree

end Distance

/-! ### 6. The obligation of `LiftHop.lean` for the designed shadow -/

/-- **The lift at the designed rule, for the designed shadow** (the remaining content of (A)). -/
def DesignedLift : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (adversary : PlanBAdversary Unit)
    (parameter : ℕ) (scalar : NonZeroScalar),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      (letI := field
       letI := group
       letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
       letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
       letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
       letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
       FlagMono (g1uLaterWith designedInstall adversary parameter scalar)
         (middleGameFill uniformMaskTape (designedShadow scalar) adversary parameter scalar))

/-- **P1k's two (B) bounds, for the designed shadow.** -/
def DesignedBounds : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field) (scalar : NonZeroScalar),
    (letI := field
     letI := group
     letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
     letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
     letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
     letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
     PerPairBound (designedShadow scalar) scalar (4 / 2 ^ 128) ∧
       RevealBound (designedShadow scalar) scalar
         (ENNReal.ofReal Kriterion.ArgoMAC.Phase3.Glue.exceptionalError))

/-- **`LiftHop.lean`'s shadow obligation, from the lift and the bounds**: the refined distance is
real for the designed shadow. -/
theorem shadowObligationDesigned_of (lift : DesignedLift) (bounds : DesignedBounds) :
    ShadowObligationDesigned := by
  intro field group adversary parameter scalar small
  refine ⟨designedShadow (letI := field; letI := group; scalar), ?_⟩
  obtain ⟨perPair, reveal⟩ := bounds field group scalar
  refine ⟨lift field group adversary parameter scalar small, perPair, reveal, ?_⟩
  letI := field
  letI := group
  letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
  letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  have distance := designedShadow_etvDist_le scalar adversary parameter
  rw [card_curveSite] at distance
  exact distance

/-- **The Glue's `publicFirst`, from the lift, P1k's bounds and the coincidence bound.** -/
theorem planB_publicFirst_of_lift (lift : DesignedLift) (bounds : DesignedBounds)
    (coincidence : CoincidenceBound coincidenceError) :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError + maskSwapError :=
  planB_publicFirst_of_designed (shadowObligationDesigned_of lift bounds) coincidence

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
