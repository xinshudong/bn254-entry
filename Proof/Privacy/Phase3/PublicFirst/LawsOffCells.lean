/-
**Phase 3, P1n — the off-curve law, step (ii), part 1: the source is its published cells.**

A stage-1 source is, bijectively, F4's published cells (`JointExactness.PublicCells`: every digit's
joins on both point lanes and its row constants, the curve joins and constants, one fold join per
(lane, chunk), one gadget entry per digit) and its Lamport key (`cellsEquiv`): the scale word of a
chunk is its four lanes' joins (`Mismatch.wordEquiv`), whose element slots are the digits' and the
curve's elements (`pointXSlots`, `curveXSlots`, …), and at `b = 2` every chunk pays exactly one
fold join (`foldVector`, `chunkSlot`).

So a uniform source publishes `cellsSource` of uniform cells (`tsum_source_cells`).

Also here: **splitting a uniform function along an injective map** (`splitAlong`,
`tsum_split_along`, `uniform_comp_injective`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffTable
import Proof.Privacy.Phase3.PublicFirst.Mismatch
import Proof.Privacy.Phase3.PublicFirst.FlagBound

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

/-! ### 1. One fold join per chunk -/

theorem chunkCount_eq_foldStepCount : chunkCount = foldStepCount := rfl

/-- The flat fold slot of a chunk. -/
def chunkSlot (c : Fin chunkCount) : Fin foldStepCount := ⟨c.val, c.isLt⟩

theorem slotChunk_chunkSlot (c : Fin chunkCount) : slotChunk (chunkSlot c) = c :=
  Fin.ext (by simp [slotChunk, chunkSlot, chunkBits])

theorem chunkSlot_slotChunk (slot : Fin foldStepCount) : chunkSlot (slotChunk slot) = slot :=
  Fin.ext (by simp [slotChunk, chunkSlot, chunkBits])

/-- A fold-join vector from one block per chunk. -/
def foldVector (f : Fin chunkCount → Block) : Vector Block foldStepCount :=
  Vector.ofFn fun slot => f (slotChunk slot)

theorem foldVector_get (f : Fin chunkCount → Block) (c : Fin chunkCount) :
    (foldVector f).get (chunkSlot c) = f c := by
  rw [foldVector, Vector.get_ofFn, slotChunk_chunkSlot]

theorem foldVector_read (hot : Vector Block foldStepCount) :
    foldVector (fun c => hot.get (chunkSlot c)) = hot := by
  apply Vector.ext
  intro slot bound
  show (foldVector (fun c => hot.get (chunkSlot c))).get ⟨slot, bound⟩ = hot.get ⟨slot, bound⟩
  rw [foldVector, Vector.get_ofFn, chunkSlot_slotChunk]

/-! ### 2. The source and its cells -/

variable [FieldCertificate]

/-- The scale word of a chunk, from the cells. -/
def cellsJoins (cells : PublicCells) (chunk : Fin chunkCount) : Fin elementCount → BaseField :=
  wordEquiv (fun slot => (cells.1 (pointXSlots.symm slot).1).1 (.inl (pointXSlots.symm slot).2) chunk,
    fun slot => cells.2.1.1 (.inl (curveXSlots.symm slot)) chunk,
    fun slot => (cells.1 (pointYSlots.symm slot).1).1 (.inr (pointYSlots.symm slot).2) chunk,
    fun slot => cells.2.1.1 (.inr (curveYSlots.symm slot)) chunk)

/-- **The source of some cells and a key.** -/
def cellsSource (cells : PublicCells) (key : InputMacKey) : Stage1Source where
  curve := cells.2.1.2
  rows := Vector.ofFn fun d => (cells.1 d).2
  exception := Vector.ofFn cells.2.2.2
  curveXHot := foldVector (cells.2.2.1 .curveX)
  curveYHot := foldVector (cells.2.2.1 .curveY)
  pointXHot := foldVector (cells.2.2.1 .pointX)
  pointYHot := foldVector (cells.2.2.1 .pointY)
  joins := cellsJoins cells
  key := key

/-- A source's fold joins, by lane. -/
def sourceHot (source : Stage1Source) : Lane → Vector Block foldStepCount
  | .curveX => source.curveXHot
  | .curveY => source.curveYHot
  | .pointX => source.pointXHot
  | .pointY => source.pointYHot

/-- **The cells of a source.** -/
def sourceCells (source : Stage1Source) : PublicCells :=
  (fun d => (fun element c => Sum.elim
      (fun e => Pipeline.readPointX (source.joins c) (pointXSlots (d, e)))
      (fun e => Pipeline.readPointY (source.joins c) (pointYSlots (d, e))) element,
    source.rows.get d),
   (fun element c => Sum.elim (fun e => Pipeline.readCurveX (source.joins c) (curveXSlots e))
      (fun e => Pipeline.readCurveY (source.joins c) (curveYSlots e)) element, source.curve),
   fun lane c => (sourceHot source lane).get (chunkSlot c),
   fun d => source.exception.get d)

theorem sourceCells_cellsSource (cells : PublicCells) (key : InputMacKey) :
    sourceCells (cellsSource cells key) = cells := by
  obtain ⟨digits, curve, fold, gadget⟩ := cells
  have word : ∀ c, cellsJoins (digits, curve, fold, gadget) c = Pipeline.assembleWord
      (fun slot => (digits (pointXSlots.symm slot).1).1 (.inl (pointXSlots.symm slot).2) c)
      (fun slot => curve.1 (.inl (curveXSlots.symm slot)) c)
      (fun slot => (digits (pointYSlots.symm slot).1).1 (.inr (pointYSlots.symm slot).2) c)
      (fun slot => curve.1 (.inr (curveYSlots.symm slot)) c) := fun _ => rfl
  refine Prod.ext (funext fun d => Prod.ext (funext fun element => funext fun c => ?_) ?_)
    (Prod.ext (Prod.ext (funext fun element => funext fun c => ?_) rfl)
      (Prod.ext (funext fun lane => funext fun c => ?_) (funext fun d => ?_)))
  · show Sum.elim (fun e => Pipeline.readPointX (cellsJoins _ c) (pointXSlots (d, e)))
      (fun e => Pipeline.readPointY (cellsJoins _ c) (pointYSlots (d, e))) element = _
    rw [word]
    rcases element with e | e
    · show Pipeline.readPointX _ _ = _
      rw [Pipeline.readPointX_assembleWord, Equiv.symm_apply_apply]
    · show Pipeline.readPointY _ _ = _
      rw [Pipeline.readPointY_assembleWord, Equiv.symm_apply_apply]
  · exact Vector.get_ofFn _ d
  · show Sum.elim (fun e => Pipeline.readCurveX (cellsJoins _ c) (curveXSlots e))
      (fun e => Pipeline.readCurveY (cellsJoins _ c) (curveYSlots e)) element = _
    rw [word]
    rcases element with e | e
    · show Pipeline.readCurveX _ _ = _
      rw [Pipeline.readCurveX_assembleWord, Equiv.symm_apply_apply]
    · show Pipeline.readCurveY _ _ = _
      rw [Pipeline.readCurveY_assembleWord, Equiv.symm_apply_apply]
  · cases lane <;> exact foldVector_get _ c
  · exact Vector.get_ofFn _ d

theorem cellsSource_sourceCells (source : Stage1Source) :
    cellsSource (sourceCells source) source.key = source := by
  obtain ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩ := source
  have rowsEq : Vector.ofFn (fun d => rows.get d) = rows := by
    apply Vector.ext; intro i bound; simp [Vector.get_eq_getElem]
  have exceptionEq : Vector.ofFn (fun d => exception.get d) = exception := by
    apply Vector.ext; intro i bound; simp [Vector.get_eq_getElem]
  have joinsEq : cellsJoins (sourceCells ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩) =
      joins := by
    funext c
    show wordEquiv (fun slot => Pipeline.readPointX (joins c)
        (pointXSlots ((pointXSlots.symm slot).1, (pointXSlots.symm slot).2)),
      fun slot => Pipeline.readCurveX (joins c) (curveXSlots (curveXSlots.symm slot)),
      fun slot => Pipeline.readPointY (joins c)
        (pointYSlots ((pointYSlots.symm slot).1, (pointYSlots.symm slot).2)),
      fun slot => Pipeline.readCurveY (joins c) (curveYSlots (curveYSlots.symm slot))) = _
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    exact assembleWord_read (joins c)
  show Stage1Source.mk curve (Vector.ofFn fun d => rows.get d) (Vector.ofFn fun d => exception.get d)
    (foldVector fun c => cx.get (chunkSlot c)) (foldVector fun c => cy.get (chunkSlot c))
    (foldVector fun c => px.get (chunkSlot c)) (foldVector fun c => py.get (chunkSlot c))
    (cellsJoins (sourceCells ⟨curve, rows, exception, cx, cy, px, py, joins, key⟩)) key = _
  rw [rowsEq, exceptionEq, foldVector_read, foldVector_read, foldVector_read, foldVector_read, joinsEq]

/-- **A source is its cells and its key.** -/
def cellsEquiv : PublicCells × InputMacKey ≃ Stage1Source where
  toFun pair := cellsSource pair.1 pair.2
  invFun source := (sourceCells source, source.key)
  left_inv pair := by
    obtain ⟨cells, key⟩ := pair
    exact Prod.ext (sourceCells_cellsSource cells key) rfl
  right_inv source := cellsSource_sourceCells source

/-- **A uniform source is uniform cells and an independent uniform key.** -/
theorem tsum_source_cells (F : Stage1Source → ℝ≥0∞) :
    ∑' source, PMF.uniformOfFintype Stage1Source source * F source =
      ∑' cells, PMF.uniformOfFintype PublicCells cells *
        ∑' key, PMF.uniformOfFintype InputMacKey key * F (cellsSource cells key) := by
  rw [← Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv cellsEquiv, tsum_map_mul,
    tsum_uniform_prod]
  rfl

/-! ### 3. Splitting a function along an injective map -/

section Split

variable {I J β : Type} (ι : J → I) (inj : Function.Injective ι)

open Classical in
/-- **A function is its values on the image of `ι` and its values elsewhere.** -/
def splitAlong : (I → β) ≃ (J → β) × ({i : I // i ∉ Set.range ι} → β) where
  toFun f := (f ∘ ι, fun i => f i.1)
  invFun p i := if h : i ∈ Set.range ι then p.1 (Classical.choose h) else p.2 ⟨i, h⟩
  left_inv f := by
    funext i
    by_cases h : i ∈ Set.range ι
    · simp only [dif_pos h, Function.comp]
      rw [Classical.choose_spec h]
    · simp only [dif_neg h]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
    · have h : ι j ∈ Set.range ι := ⟨j, rfl⟩
      show (if h' : ι j ∈ Set.range ι then a (Classical.choose h') else b ⟨ι j, h'⟩) = a j
      rw [dif_pos h, inj (Classical.choose_spec h)]
    · show (if h' : i.1 ∈ Set.range ι then a (Classical.choose h') else b ⟨i.1, h'⟩) = b i
      rw [dif_neg i.2]

theorem splitAlong_symm_image (a : J → β) (b : {i : I // i ∉ Set.range ι} → β) (j : J) :
    (splitAlong ι inj).symm (a, b) (ι j) = a j :=
  congrFun (congrArg Prod.fst ((splitAlong ι inj).apply_symm_apply (a, b))) j

theorem splitAlong_symm_rest (a : J → β) (b : {i : I // i ∉ Set.range ι} → β)
    (i : {i : I // i ∉ Set.range ι}) : (splitAlong ι inj).symm (a, b) i.1 = b i :=
  congrFun (congrArg Prod.snd ((splitAlong ι inj).apply_symm_apply (a, b))) i

end Split

/-! ### 4. The hidden and the visible other indices, off the curve -/

section Indices

variable (input : AffineInput)

/-- The active parent at step `1` of a (lane, chunk) at the input. -/
def activeBit (lane : Lane) (chunk : Fin chunkCount) : Nat :=
  (chunkOf (inputBits input lane.coord) chunk).val % 2

theorem activeBit_lt (lane : Lane) (chunk : Fin chunkCount) : activeBit input lane chunk < 2 :=
  Nat.mod_lt _ (by omega)

/-- The hidden coins among the other indices: one gate half of the active parent per (lane, chunk)
(the fold join's hidden material) and one gadget position per digit (the digest's hidden part). -/
abbrev HiddenIdx := (Lane × Fin chunkCount) ⊕ Fin digitCount

/-- The gadget position whose answer hides a digit's digest. -/
def gadgetOther (d : Fin digitCount) : OtherIndex :=
  ⟨.gadget d .x ⟨0, by unfold PlanB.coordinateBits; omega⟩, by
    rintro ⟨site, same⟩
    simp only [siteIndex, scaleIndexOf, scaleIndexNat] at same
    cases same⟩

/-- The hidden coins' indices. -/
def hiddenIdx : HiddenIdx → OtherIndex
  | .inl p => hotOther p.1 p.2 1 (activeBit input p.1 p.2) false
  | .inr d => gadgetOther d

theorem hiddenIdx_injective : Function.Injective (hiddenIdx input) := by
  rintro (⟨ℓ, c⟩ | d) (⟨ℓ', c'⟩ | d') same <;>
    simp only [hiddenIdx, hotOther, gadgetOther, Subtype.mk.injEq, hotIndexNat, FixedIndex.hot.injEq,
      reduceCtorEq, FixedIndex.gadget.injEq] at same
  · obtain ⟨rfl, rfl, -⟩ := same
    rfl
  · obtain ⟨rfl, -⟩ := same
    rfl

/-- The view's fold gates: both halves of the inactive parent at step `1`, on the curve lanes. -/
abbrev ViewIdx := Bool × Fin chunkCount × Bool

/-- The curve lane of a view index. -/
def viewLane (curveY : Bool) : Lane := if curveY then .curveY else .curveX

theorem viewLane_curve (curveY : Bool) : laneIsCurve (viewLane curveY) = true := by
  cases curveY <;> rfl

/-- The view's fold gates. -/
def viewIdx (w : ViewIdx) : OtherIndex :=
  hotOther (viewLane w.1) w.2.1 1 (1 - activeBit input (viewLane w.1) w.2.1) w.2.2

theorem viewIdx_not_hidden (w : ViewIdx) : viewIdx input w ∉ Set.range (hiddenIdx input) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;>
    simp only [hiddenIdx, viewIdx, hotOther, gadgetOther, Subtype.mk.injEq, hotIndexNat,
      FixedIndex.hot.injEq, reduceCtorEq] at same
  obtain ⟨rfl, rfl, -, entry, -⟩ := same
  have small := activeBit_lt input (viewLane w.1) w.2.1
  simp only [Fin.mk.injEq, chunkBits] at entry
  omega

/-- The view's fold gates among the rest. -/
def viewRest (w : ViewIdx) : {i : OtherIndex // i ∉ Set.range (hiddenIdx input)} :=
  ⟨viewIdx input w, viewIdx_not_hidden input w⟩

end Indices

/-! ### 5. The coins of the off-curve garbler on a table, as F4's coins and the rest -/


section Omega

open Kriterion.ArgoMAC.Scheme (Coins)

variable (input : AffineInput)

/-- The offsets the coins may carry. -/
abbrev ClampedOffsets :=
  {offsets : SuccessfulOffsets // ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped}

/-- The coins, field by field, the vectors read as functions. -/
abbrev CoinsParts := ClampedOffsets × (Fin outputMacCount → RowRandomness) ×
  (Fin outputMacCount → Exception.Entry) × BaseField × NonZeroBase × BaseField × BaseField ×
  (Coord → Fin coordinateBitCount → Block) × (Coord → Block)

theorem ofFn_get' {α : Type} {n : Nat} (v : Vector α n) : Vector.ofFn v.get = v := by
  apply Vector.ext
  intro i bound
  simp [Vector.get_eq_getElem]

/-- **The coins are their fields.** -/
def coinsSplit : Coins ≃ CoinsParts where
  toFun c := (⟨c.offsets, c.offsetsClamped⟩, c.pointRandomness.get, c.exceptionPad.get, c.bridgeKey,
    c.curveMask, c.curveR1, c.curveR2, c.inputZero, c.inputDelta)
  invFun p := ⟨p.1.1, p.1.2, Vector.ofFn p.2.1, Vector.ofFn p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
    p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv c := by
    obtain ⟨offsets, clamped, pR, pad, t, mask, r1, r2, Z, Δ⟩ := c
    show Kriterion.ArgoMAC.Scheme.Coins.mk offsets clamped (Vector.ofFn pR.get) (Vector.ofFn pad.get)
      t mask r1 r2 Z Δ = _
    rw [ofFn_get', ofFn_get']
  right_inv p := by
    obtain ⟨offsets, pR, pad, t, mask, r1, r2, Z, Δ⟩ := p
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · exact funext fun d => Vector.get_ofFn pR d
    · exact funext fun d => Vector.get_ofFn pad d

/-- The other indices that hide nothing. -/
abbrev RestIdx := {i : OtherIndex // i ∉ Set.range (hiddenIdx input)}

/-- **What F4's coins leave out**: the offsets, the `ρ`s, the labels and `Δ`, the other answers. -/
abbrev Outer := ClampedOffsets × (Fin digitCount → NonZeroBase) ×
  (Coord → Fin coordinateBitCount → Block) × (Coord → Block) × (RestIdx input → Block)

/-- **The coins' fields, the other answers and the masks are the rest and F4's coins.** -/
def regroup : CoinsParts × (OtherIndex → Block) × (MaskSite → BaseField) ≃ Outer input × JointCoins where
  toFun ω :=
    ((ω.1.1, fun d => (ω.1.2.1 d).rho, ω.1.2.2.2.2.2.2.2.1, ω.1.2.2.2.2.2.2.2.2,
        (splitAlong (hiddenIdx input) (hiddenIdx_injective input) ω.2.1).2),
      (fun d => ((maskSiteEquiv ω.2.2).1 d, ((ω.1.2.1 d).x, (ω.1.2.1 d).y, (ω.1.2.1 d).z)),
        ((maskSiteEquiv ω.2.2).2, ω.1.2.2.2.1, ⟨ω.1.2.2.2.2.1.value, ω.1.2.2.2.2.1.nonzero⟩,
          ω.1.2.2.2.2.2.1, ω.1.2.2.2.2.2.2.1),
        (fun ℓ c => ω.2.1 (hiddenIdx input (.inl (ℓ, c))),
          fun d => (ω.1.2.2.1 d, ω.2.1 (hiddenIdx input (.inr d))))))
  invFun p :=
    ((p.1.1, fun d => ⟨p.1.2.1 d, (p.2.1 d).2.1, (p.2.1 d).2.2.1, (p.2.1 d).2.2.2⟩,
        fun d => (p.2.2.2.2 d).1, p.2.2.1.2.1, ⟨p.2.2.1.2.2.1.1, p.2.2.1.2.2.1.2⟩,
        p.2.2.1.2.2.2.1, p.2.2.1.2.2.2.2, p.1.2.2.1, p.1.2.2.2.1),
      (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm
        (Sum.elim (fun q => p.2.2.2.1 q.1 q.2) (fun d => (p.2.2.2.2 d).2), p.1.2.2.2.2),
      maskSiteEquiv.symm (fun d => (p.2.1 d).1, p.2.2.1.1))
  left_inv ω := by
    obtain ⟨⟨offsets, pR, pad, t, mask, r1, r2, Z, Δ⟩, v, m⟩ := ω
    have hidden : (Sum.elim (fun q : Lane × Fin chunkCount => v (hiddenIdx input (.inl (q.1, q.2))))
        (fun d => v (hiddenIdx input (.inr d)))) =
        (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).1 := by
      funext q
      rcases q with ⟨ℓ, c⟩ | d <;> rfl
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm
        (Sum.elim (fun q : Lane × Fin chunkCount => v (hiddenIdx input (.inl (q.1, q.2))))
          (fun d => v (hiddenIdx input (.inr d))),
         (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2) = v
      rw [hidden, Prod.mk.eta, Equiv.symm_apply_apply]
    · show maskSiteEquiv.symm ((maskSiteEquiv m).1, (maskSiteEquiv m).2) = m
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨offsets, rho, Z, Δ, rest⟩, digits, ⟨cm, t, mask, r1, r2⟩, fold, gadget⟩ := p
    have masks : maskSiteEquiv (maskSiteEquiv.symm (fun d => (digits d).1, cm)) =
        (fun d => (digits d).1, cm) := Equiv.apply_symm_apply _ _
    refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
      (Prod.ext (funext fun d => ?_) (Prod.ext (Prod.ext ?_ rfl) (Prod.ext
        (funext fun ℓ => funext fun c => ?_) (funext fun d => ?_))))
    · show ((splitAlong (hiddenIdx input) (hiddenIdx_injective input))
        ((splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm (_, rest))).2 = rest
      rw [Equiv.apply_symm_apply]
    · exact Prod.ext (congrFun (congrArg Prod.fst masks) d) rfl
    · exact congrArg Prod.snd masks
    · exact splitAlong_symm_image (hiddenIdx input) (hiddenIdx_injective input) _ _ (.inl (ℓ, c))
    · exact Prod.ext rfl
        (splitAlong_symm_image (hiddenIdx input) (hiddenIdx_injective input) _ _ (.inr d))

/-- The garbler's coins on a table, the other answers and the masks. -/
abbrev Omega := Coins × (OtherIndex → Block) × (MaskSite → BaseField)

/-- **The garbler's randomness is the rest and F4's coins.** -/
def omegaEquiv : Omega ≃ Outer input × JointCoins :=
  (coinsSplit.prodCongr (Equiv.refl _)).trans (regroup input)

end Omega

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
