/-
**Phase 3, P1m — (B1) the fixed-key part on the curve, per index.**

For a source and an on-curve target, per fixed index:

* `scaleIn_le`, `scaleOut_le` — a scale index: input and output mass `≤ 1/2^128` each;
* `hotOut_le`, `gadgetOut_le` — fold and gadget outputs `≤ 1/2^128` (`offScale_out_le`);
* `hotCurveIn_le` — a curve fold input is the source's own label (`≤ ind`, averaged over the key
  later);
* `hotPointIn_le`, `gadgetIn_le` — a point fold input or a gadget input is a pad plus a fixed
  block: `≤ 1/(2^128 − 1)` (`pad_le`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedDesig

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests designatedIndex)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt FixedAt IndexAt
  runRefill cellOf runRefillT dropTouched uniformMaskTape queriesAlong queriesAlong_bind
  runRefill_eq_runRefillT fq_bind_assoc)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The final pairs, reduced -/

section Reduce

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 blocks) ran.2.1)).support)

include member resultMember

/-- **A point at an index's input is its canonical input.** -/
theorem fixedIn_reduce (i : FixedIndex) (x : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 blocks))).fixedIn i x) :
    inputOf source.publicValue (restoredBits source input) (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1))
      (refillAns (restoredBits source input) ran.2.1)
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) i = x := by
  rcases hit with found | ⟨out, inReq⟩
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp found
    rw [← final_input source input tape ran member blocks result resultMember i _ _ hy,
      BitVec.ofFin_toFin]
  · exact (request_input source input tape ran member blocks _ i x out inReq).symm

/-- **A point at a non-designated mask site's output is `tape ⊕ input`.** -/
theorem fixedOut_site_reduce (i : FixedIndex) (isScale : ∃ l c s e b, i = .scale l c s e b)
    (notDesignated : ¬ IsDesignated (restoredBits source input) i) {cell : Cell}
    (cellEq : cellOf i = some cell) (y : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 blocks))).fixedOut i y) :
    inputOf source.publicValue (restoredBits source input) (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1))
      (refillAns (restoredBits source input) ran.2.1)
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) i =
      y ^^^ tape cell := by
  rcases hit with ⟨x, found⟩ | ⟨inp, out, inReq, _⟩
  · have outEq := final_site_output source input tape ran member blocks result resultMember i
      isScale notDesignated cellEq x y.toFin found
    rw [BitVec.ofFin_toFin] at outEq
    rw [← final_input source input tape ran member blocks result resultMember i x y.toFin found,
      outEq, BitVec.xor_comm (tape cell), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · obtain ⟨d, c, b, rfl, _, _⟩ := mem_programRequests inReq
    exact absurd ⟨d, c, b, rfl⟩ notDesignated

end Reduce

/-! ### Scale, fold and gadget outputs; scale inputs -/

section Scale

variable [FieldCertificate] [GroupCertificate]

theorem scale_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (z : Tape → Block)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks))) →
        inputOf source.publicValue (restoredBits source input) (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1))
          (refillAns (restoredBits source input) ran.2.1)
          (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
            (restoredMac source input) (answerOf result.2)) (restoredMac source input))
          (.scale lane c s e b) = z tape) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ delta := by
  cases lane with
  | curveX =>
    exact curveScale_le scalar off source input target .curveX (Or.inl rfl) c s e b event z reduce
  | curveY =>
    exact curveScale_le scalar off source input target .curveY (Or.inr rfl) c s e b event z reduce
  | pointX =>
    exact pointScale_le scalar off source input target .pointX (Or.inl rfl) c s e b event z reduce
  | pointY =>
    exact pointScale_le scalar off source input target .pointY (Or.inr rfl) c s e b event z reduce

/-- **The input mass at a scale index.** -/
theorem scaleIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.scale lane c s e b) x) ≤ delta :=
  scale_le scalar off source input target lane c s e b (fun p => p.fixedIn (.scale lane c s e b) x)
    (fun _ => x) fun tape ran member blocks result resultMember hit =>
      fixedIn_reduce source input tape ran member blocks result resultMember _ x hit

/-- **The output mass at a scale index.** -/
theorem scaleOut_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut (.scale lane c s e b) y) ≤ delta := by
  by_cases designated : IsDesignated (restoredBits source input) (.scale lane c s e b)
  · obtain ⟨d, col, blk, same⟩ := designated
    rw [← same]
    exact designated_out_le scalar off source input target d col blk y
  · cases cellEq : cellOf (.scale lane c s e b) with
    | none => exact offScale_out_le scalar off source input target _ cellEq designated y
    | some cell =>
      exact scale_le scalar off source input target lane c s e b
        (fun p => p.fixedOut (.scale lane c s e b) y) (fun tape => y ^^^ tape cell)
        fun tape ran member blocks result resultMember hit =>
          fixedOut_site_reduce source input tape ran member blocks result resultMember _
            ⟨lane, c, s, e, b, rfl⟩ designated cellEq y hit

/-- **The output mass at a fold index.** -/
theorem hotOut_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut (.hot lane c f e h) y) ≤ delta :=
  offScale_out_le scalar off source input target _ (hot_noCell lane c f e h)
    (hot_notDesignated _ lane c f e h) y

/-- **The output mass at a gadget index.** -/
theorem gadgetOut_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (d : Fin digitCount) (κ : Coord)
    (pos : Fin coordinateBitCount) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut (.gadget d κ pos) y) ≤ delta :=
  offScale_out_le scalar off source input target _ (gadget_noCell d κ pos)
    (gadget_notDesignated _ d κ pos) y

end Scale

/-! ### Curve fold inputs: the source's own label -/

section CurveFold

variable [FieldCertificate] [GroupCertificate]

/-- **A deterministic event**: if every run's event forces `Q`, its mass is `≤ ind Q`. -/
theorem onCurve_const_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (Q : Prop)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks))) → Q) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ ind Q :=
  onCurve_potential_le scalar off source input target event (fun _ => ind Q)
    (fun request state _ => le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    fun tape ran member blocks result resultMember =>
      ind_mono (reduce tape ran member blocks result resultMember)

/-- The curve labels do not read the pads. -/
theorem curveLabels_pads (mac : InputMac) (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    laneLabels mac pads lane = laneLabels mac (fun _ _ => (0, 0)) lane := by
  rcases curve with rfl | rfl <;> rfl

/-- **The input mass at a curve fold index** is the indicator of the source's own fold input. -/
theorem hotCurveIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤
      ind (laneW (laneJoins source.publicValue lane)
        (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c = x) :=
  onCurve_const_le scalar off source input target (fun p => p.fixedIn (.hot lane c f e h) x)
    (laneW (laneJoins source.publicValue lane)
      (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c = x)
    fun tape ran member blocks result resultMember hit => by
      have same := fixedIn_reduce source input tape ran member blocks result resultMember _ x hit
      rw [← curveLabels_pads _ lane curve (wPadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (refillAns (restoredBits source input) ran.2.1))]
      exact same

end CurveFold

/-! ### Point fold and gadget inputs: a pad plus a fixed block -/

section Labels

/-- An EncPRF answer, as a block. -/
def encAns (ans : (request : Request) → request.Answer) (j : EncPRF.PermutationIndex)
    (w : Block) : Block :=
  ans (.encForward j w)

/-- The EncPRF coordinate of a coordinate. -/
def encCoord : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- The bits of an EncPRF coordinate. -/
def encWord (bits : BitInput) : EncPRF.Coordinate → BitVec coordinateBitCount
  | .x => bits.xBits
  | .y => bits.yBits

theorem eval_padM' (ans : (request : Request) → request.Answer) (keys : WhiteningKeys)
    (coord : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool) :
    FreeQuery.eval ans (Programs.padM keys coord index bit) =
      encAns ans (coord, index) (encodeBit bit ^^^ keys.first) ^^^ keys.second := rfl

theorem evalPads_snd (bits : BitInput) (keys : WhiteningKeys)
    (ans : (request : Request) → request.Answer) (coord : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (Programs.evalPadsM keys bits) coord index).2 =
      FreeQuery.eval ans (Programs.padM keys coord index ((encWord bits coord).getLsb index)) := by
  cases coord <;>
  · simp only [Programs.evalPadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn, encWord]
    split
    · rename_i bitSet
      simp only [bitSet, FreeQuery.eval_bind, FreeQuery.eval_pure]
    · rename_i bitClear
      simp only [Bool.not_eq_true] at bitClear
      simp only [bitClear, FreeQuery.eval_bind, FreeQuery.eval_pure]

theorem whiten_label (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) (κ : Coord) (p : Fin coordinateBitCount) :
    Pipeline.macLabels (Programs.whitenMacOf pads mac) κ p =
      (pads (encCoord κ) p).1 ^^^ Pipeline.macLabels mac κ p := by
  cases κ <;> simp only [Pipeline.macLabels, Programs.whitenMacOf, Vector.get_ofFn, encCoord] <;> rfl

theorem transform_label (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) (κ : Coord) (p : Fin coordinateBitCount) :
    Pipeline.macLabels (Programs.transformMacOf pads mac) κ p =
      (pads (encCoord κ) p).2 ^^^ Pipeline.macLabels mac κ p := by
  cases κ <;> simp only [Pipeline.macLabels, Programs.transformMacOf, Vector.get_ofFn, encCoord] <;>
    rfl

theorem chunkWidth_pos (c : Fin chunkCount) : 0 < chunkWidth c := by
  rw [chunkWidth_eq_two]
  norm_num

/-- The first bit of a chunk, as a label position. -/
def firstBit (c : Fin chunkCount) : Fin coordinateBitCount :=
  ⟨(chunkBitIndex c ⟨0, chunkWidth_pos c⟩).val, (chunkBitIndex c ⟨0, chunkWidth_pos c⟩).isLt⟩

theorem zero_xor' (a : Block) : (0 : Block) ^^^ a = a := BitVec.zero_xor

/-- **A level-1 fold input is the label of the chunk's first bit** (its join is free). -/
theorem laneW_eq (joins : Vector Block foldStepCount) (labels : Fin coordinateBitCount → Block)
    (c : Fin chunkCount) :
    laneW joins labels c = labels (firstBit c) := by
  have j0 : joinAt (hotSlice joins c) 0 = 0 := by
    unfold joinAt
    rw [if_pos rfl]
  have l0 : labelAt (chunkLabels labels c) 0 = labels (firstBit c) := by
    unfold labelAt
    rw [dif_pos (chunkWidth_pos c)]
    rfl
  show joinAt (hotSlice joins c) 0 ^^^ labelAt (chunkLabels labels c) 0 = _
  rw [j0, l0]
  exact zero_xor' _

theorem xor_solve (a k w x : Block) (same : (a ^^^ k) ^^^ w = x) : a = x ^^^ w ^^^ k := by
  rw [← same, BitVec.xor_assoc (a ^^^ k) w w, BitVec.xor_self, BitVec.xor_zero, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

end Labels

section PadFinal

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 blocks) ran.2.1)).support)

include member resultMember

/-- The whitening pads' EncPRF answers are the final state's. -/
theorem whitePad_final (j : EncPRF.PermutationIndex) :
    encAns (refillAns (restoredBits source input) ran.2.1) j (encodeBit false ^^^
      (kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1) =
      encAns (answerOf result.2) j (encodeBit false ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1) := by
  have onPath := whitePads_mem_opening source.publicValue (restoredBits source input)
    (restoredMac source input) (refillAns (restoredBits source input) ran.2.1) _
    (mem_queriesAlong_of_transcript (refillAns (restoredBits source input) ran.2.1)
      (whitePadsM ⟨(kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1, (kOf source.publicValue
          (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).2⟩) _
      (whitePad_mem_transcript (refillAns (restoredBits source input) ran.2.1)
        ⟨(kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1, (kOf source.publicValue
            (restoredBits source input) (restoredMac source input)
              (refillAns (restoredBits source input) ran.2.1)).2⟩ j))
  exact (opening_agree source input tape ran member result.2
    (final_grows source input tape ran member blocks result resultMember) _ onPath rfl).symm

/-- **A point fold input, reduced to its whitening pad.** -/
theorem hotPoint_reduce (lane : Lane) (κ : Coord)
    (labelsEq : ∀ mac pads, laneLabels mac pads lane =
      Pipeline.macLabels (Programs.whitenMacOf pads mac) κ)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 blocks))).fixedIn (.hot lane c f e h) x) :
    encAns (answerOf result.2) (encCoord κ, firstBit c)
        (encodeBit false ^^^ (kOf source.publicValue (restoredBits source input)
          (restoredMac source input) (refillAns (restoredBits source input) ran.2.1)).1) =
      x ^^^ Pipeline.macLabels (restoredMac source input) κ (firstBit c) ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).2 := by
  have same : laneW (laneJoins source.publicValue lane) (laneLabels (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)) lane) c = x :=
    fixedIn_reduce source input tape ran member blocks result resultMember _ x hit
  rw [laneW_eq, labelsEq, whiten_label, whitePads_fst, eval_padM',
    whitePad_final source input tape ran member blocks result resultMember] at same
  exact xor_solve _ _ _ _ same

/-- **A gadget input, reduced to its evaluation pad.** -/
theorem gadget_reduce (d : Fin digitCount) (κ : Coord) (pos : Fin coordinateBitCount) (x : Block)
    (hit : ((pointsOf result.2).union (requestPoints (programRequests (restoredBits source input)
      ran.2.2 blocks))).fixedIn (.gadget d κ pos) x) :
    encAns (answerOf result.2) (encCoord κ, pos)
        (encodeBit ((encWord (restoredBits source input) (encCoord κ)).getLsb pos) ^^^
          (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).1) =
      x ^^^ Pipeline.macLabels (restoredMac source input) κ pos ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).2 := by
  have same : Pipeline.macLabels (Programs.transformMacOf (ePadsOf source.publicValue
      (restoredBits source input) (restoredMac source input) (answerOf result.2))
        (restoredMac source input)) κ pos = x :=
    fixedIn_reduce source input tape ran member blocks result resultMember _ x hit
  rw [transform_label, evalPads_snd, eval_padM',
    kOf_final source input tape ran member blocks result resultMember] at same
  exact xor_solve _ _ _ _ same

end PadFinal

section PadBounds

variable [FieldCertificate] [GroupCertificate]

/-- **The input mass at a point fold index**: `≤ 1/(2^128 − 1)`. -/
theorem hotPointIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (point : lane = .pointX ∨ lane = .pointY)
    (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits)) (h : Bool) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.hot lane c f e h) x) ≤ epsOne := by
  obtain ⟨κ, labelsEq⟩ : ∃ κ : Coord, ∀ mac pads, laneLabels mac pads lane =
      Pipeline.macLabels (Programs.whitenMacOf pads mac) κ := by
    rcases point with rfl | rfl
    · exact ⟨.x, fun _ _ => rfl⟩
    · exact ⟨.y, fun _ _ => rfl⟩
  exact pad_le scalar off source input target (fun p => p.fixedIn (.hot lane c f e h) x)
    (encCoord κ, firstBit c) false
    (fun k => x ^^^ Pipeline.macLabels (restoredMac source input) κ (firstBit c) ^^^ k.2)
    fun tape ran member blocks result resultMember hit =>
      hotPoint_reduce source input tape ran member blocks result resultMember lane κ labelsEq c f e
        h x hit

/-- **The input mass at a gadget index**: `≤ 1/(2^128 − 1)`. -/
theorem gadgetIn_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (d : Fin digitCount) (κ : Coord)
    (pos : Fin coordinateBitCount) (x : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedIn (.gadget d κ pos) x) ≤ epsOne :=
  pad_le scalar off source input target (fun p => p.fixedIn (.gadget d κ pos) x) (encCoord κ, pos)
    ((encWord (restoredBits source input) (encCoord κ)).getLsb pos)
    (fun k => x ^^^ Pipeline.macLabels (restoredMac source input) κ pos ^^^ k.2)
    fun tape ran member blocks result resultMember hit =>
      gadget_reduce source input tape ran member blocks result resultMember d κ pos x hit

end PadBounds



end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
