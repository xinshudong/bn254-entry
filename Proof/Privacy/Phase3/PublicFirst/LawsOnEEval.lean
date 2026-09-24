/-
**Phase 3, P1r — `LawOn`, step (E), part 1: the evaluator's values read only the Davies–Meyer
limbs.**

An answer function is *Davies–Meyer on a tape* `T` (`DMOn`) when every site question `(cell, x)` is
answered `x ⊕ T cell`: the table answers (`tableAnswer`) and every overlaid oracle (`overlay`) are.
On such answers every lane of the evaluator delivers `laneValue` — the free fold of the tape's masks
at the switches off the active one, the active one recovered from the published join — whatever the
lane's labels and whatever the fold gates answer (`evalLaneM_dm`): the fold answers only move the
one-hot labels, the inputs of the site questions, and a site's Davies–Meyer value does not see its
input. Consequences:

* `openingQueriesM_dm`: `HW`'s opening delivers the point lanes' `laneValue`s — so the collector
  targets of the private side do not read the oracle's non-site answers, nor the pads, nor the hash;
* `curvePrefixM_dm`: the prefix asks the hash at `curveKey` (the curve lanes' `laneValue`s), and
  returns the answer there.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (openingQueriesM whitePadsM)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open scoped ENNReal

noncomputable section

/-! ### 1. Answers that are Davies–Meyer on a tape -/

/-- **Every site question is answered by its input XOR the tape's limb.** -/
def DMOn (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (T : Tape) : Prop :=
  ∀ (cell : Cell) (x : Block), a (.fixedForward (siteIndex cell) x) = x ^^^ T cell

theorem dmOn_table (A : Table) : DMOn (tableAnswer A) A.2.2.2 := fun cell x => by
  rw [tableAnswer_site, BitVec.xor_comm]

theorem dmOn_overlay [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex] (T : Tape)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    DMOn (publicAnswer (OnLaw.overlay T O)) T := fun cell x => OnLaw.overlay_site T O cell x

variable {a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer} {T : Tape}

theorem hashM_site (dm : DMOn a T) (cell : Cell) (x : Block) :
    (Programs.hashM (siteIndex cell) x).eval a = T cell := by
  rw [hashM_eval, dm, id, BitVec.xor_comm x, xor_xor_cancel]

/-- A switch's masks on Davies–Meyer answers: the tape's masks, whatever the label. -/
theorem switchMaskM_dm (dm : DMOn a T) (lane : Lane) (c : Fin chunkCount)
    (j : Fin (2 ^ chunkWidth c)) (label : Block) :
    (Programs.switchMaskM (laneCount lane) lane c j.val label).eval a =
      fun e => masksOf T ⟨lane, c, j, e⟩ := by
  funext e
  simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn]
  show sampleFp ((Programs.hashM (siteIndex (⟨lane, c, j, e⟩, 0)) label).eval a)
    ((Programs.hashM (siteIndex (⟨lane, c, j, e⟩, 1)) label).eval a)
    ((Programs.hashM (siteIndex (⟨lane, c, j, e⟩, 2)) label).eval a) = _
  rw [hashM_site dm, hashM_site dm, hashM_site dm]
  rfl

/-- The masks a chunk reads: the tape's, off the active switch. -/
def chunkMasks (lane : Lane) (c : Fin chunkCount) (alpha : Fin (2 ^ chunkWidth c)) (T : Tape) :
    Fin (2 ^ chunkWidth c) → Fin (laneCount lane) → BaseField :=
  fun j e => if j = alpha then 0 else masksOf T ⟨lane, c, j, e⟩

theorem evalMasksM_dm (dm : DMOn a T) (lane : Lane) (c : Fin chunkCount)
    (hot : HotLabels (chunkWidth c)) (alpha : Fin (2 ^ chunkWidth c)) :
    (Programs.evalMasksM (laneCount lane) lane c (chunkWidth c) hot alpha).eval a =
      chunkMasks lane c alpha T := by
  funext j e
  simp only [Programs.evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, chunkMasks]
  by_cases active : j = alpha
  · rw [if_pos active, if_pos active]
    rfl
  · rw [if_neg active, if_neg active, switchMaskM_dm dm]

/-- **A lane's delivered values from the tape**: per chunk the free fold of the masks off the active
switch, the active one recovered from the published join. -/
def laneValue (lane : Lane) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (T : Tape) : Fin (laneCount lane) → BaseField :=
  fun e => ∑ c : Fin chunkCount,
    Programs.evalScaleOf (chunkWidth c) (chunkMasks lane c (chunkOf bits c) T) (chunkOf bits c) (scale c) e

/-- **On Davies–Meyer answers a lane delivers `laneValue`**, whatever its labels and fold joins. -/
theorem evalLaneM_dm (dm : DMOn a T) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    (Programs.evalLaneM (laneCount lane) lane joins scale bits labels).eval a =
      laneValue lane scale bits T := by
  funext e
  simp only [Programs.evalLaneM, Programs.evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn, evalMasksM_dm dm, laneValue]

/-! ### 2. The opening and the prefix -/

variable [FieldCertificate]

/-- The point lanes' delivered values. -/
def pointValues (P : Public) (bits : BitInput) (T : Tape) :
    (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField) :=
  (laneValue .pointX (fun chunk => Pipeline.readPointX (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .x) T,
    laneValue .pointY (fun chunk => Pipeline.readPointY (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .y) T)

/-- The curve lanes' bridge value. -/
def curveKey (P : Public) (bits : BitInput) (T : Tape) : BaseField :=
  CurveMembership.evaluate P.curve bits.toAffine
    (Pipeline.curveValues
      (laneValue .curveX (fun chunk => Pipeline.readCurveX (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .x) T)
      (laneValue .curveY (fun chunk => Pipeline.readCurveY (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .y) T))

/-- **`HW`'s opening delivers the point lanes' `laneValue`s** on Davies–Meyer answers. -/
theorem openingQueriesM_dm (dm : DMOn a T) (P : Public) (bits : BitInput) (mac : InputMac) :
    (openingQueriesM P bits mac).eval a = pointValues P bits T := by
  have px : ∀ labels, (Programs.evalLaneM pointElementCountX .pointX P.pointXHot
      (fun chunk => Pipeline.readPointX (unpack (P.scale.get chunk))) (Pipeline.coordBits bits .x)
      labels).eval a = (pointValues P bits T).1 := fun labels => evalLaneM_dm dm .pointX _ _ _ labels
  have py : ∀ labels, (Programs.evalLaneM pointElementCountY .pointY P.pointYHot
      (fun chunk => Pipeline.readPointY (unpack (P.scale.get chunk))) (Pipeline.coordBits bits .y)
      labels).eval a = (pointValues P bits T).2 := fun labels => evalLaneM_dm dm .pointY _ _ _ labels
  unfold openingQueriesM
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, px, py]

/-- **The prefix returns the hash answer at the curve lanes' bridge value.** -/
theorem curvePrefixM_dm (dm : DMOn a T) (P : Public) (bits : BitInput) (mac : InputMac) :
    (curvePrefixM P bits mac).eval a = a (.hash (curveKey P bits T)) := by
  have cx : (Programs.evalLaneM curveElementCountX .curveX P.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (P.scale.get chunk))) (Pipeline.coordBits bits .x)
      (Pipeline.macLabels mac .x)).eval a =
      laneValue .curveX (fun chunk => Pipeline.readCurveX (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .x) T := evalLaneM_dm dm .curveX _ _ _ _
  have cy : (Programs.evalLaneM curveElementCountY .curveY P.curveYHot
      (fun chunk => Pipeline.readCurveY (unpack (P.scale.get chunk))) (Pipeline.coordBits bits .y)
      (Pipeline.macLabels mac .y)).eval a =
      laneValue .curveY (fun chunk => Pipeline.readCurveY (unpack (P.scale.get chunk)))
        (Pipeline.coordBits bits .y) T := evalLaneM_dm dm .curveY _ _ _ _
  unfold curvePrefixM
  rw [FreeQuery.eval_bind, cx, FreeQuery.eval_bind, cy]
  rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
