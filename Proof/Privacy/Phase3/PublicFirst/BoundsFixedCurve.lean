/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: fold/gadget outputs and system A's masks.**

* `onCurve_whole_le` — the whole-process form of `onCurve_split_le` (the potential may read the
  tape).
* `offScale_out_le` — at a fold or gadget index, `Pr[y ∈ fixedOut_i] ≤ 1/2^128` (`singlePot`:
  every pair there is at the index's canonical input, so there is at most one).
* `curveScale_le` — at a mask index of system A, `Pr[inputOf i = z] ≤ 1/2^128` for any `z`
  that may read the tape (`foldPot`: the input is a fixed block xor the fold material of the
  chunk, the xor of two fresh answers).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedProc

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM IsDesignated interceptAnswer
  programRequests designatedIndex)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ runRefill cellOf
  runRefillT dropTouched uniformMaskTape queriesAlong foldLabels inactiveEntry program_frame
  hot_not_designated cellOf_hot)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### Potentials blind to the sites and to the designated indices -/

section Blind

theorem fixed_siteSame (i : FixedIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (noCell : cellOf i = none) (state updated : LState) (index : FixedIndex) (input output : Block)
    (isCell : cellOf index ≠ none)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    F (updated.fixed i) = F (state.fixed i) := by
  have different : i ≠ index := fun same => isCell (same ▸ noCell)
  rw [program_frame index input output state updated success i different]

theorem fixed_designatedSame (bits : BitInput) (i : FixedIndex)
    (F : SparsePermutation (2 ^ 128) → ℝ≥0∞) (notDesignated : ¬ IsDesignated bits i)
    (state updated : LState) (index : FixedIndex) (input output : Block)
    (designated : IsDesignated bits index)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    F (updated.fixed i) = F (state.fixed i) := by
  have different : i ≠ index := fun same => notDesignated (same ▸ designated)
  rw [program_frame index input output state updated success i different]

theorem enc_programSame (j : EncPRF.PermutationIndex) (F : SparsePermutation (2 ^ 128) → ℝ≥0∞)
    (state updated : LState) (index : FixedIndex) (input output : Block)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    F (updated.enc j) = F (state.enc j) := by
  rw [program_fixed_enc index input output state updated success]

/-- A permutation whose stored inputs are all one input has at most one pair. -/
theorem used_le_one (S : SparsePermutation (2 ^ 128)) (x₀ : Fin (2 ^ 128))
    (all : ∀ x y, lk S x = some y → x = x₀) : S.used ≤ 1 := by
  classical
  rw [← card_known]
  refine le_trans (Fintype.card_le_of_injective (fun _ : {z // S.knownInput z} => (0 : Fin 1))
    ?_) (by simp)
  intro a b _
  apply Subtype.ext
  obtain ⟨ya, ha⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp a.2)
  obtain ⟨yb, hb⟩ := Option.ne_none_iff_exists'.mp ((knownInput_iff _ _).mp b.2)
  rw [all _ _ ha, all _ _ hb]

theorem gadget_noCell (d : Fin digitCount) (κ : Coord) (pos : Fin coordinateBitCount) :
    cellOf (.gadget d κ pos) = none := by
  unfold cellOf
  rw [dif_neg]
  rintro ⟨cell, same⟩
  simp [Kriterion.ArgoMAC.Security.Phase3.siteIndex, scaleIndexOf, scaleIndexNat] at same

theorem gadget_notDesignated (bits : BitInput) (d : Fin digitCount) (κ : Coord)
    (pos : Fin coordinateBitCount) : ¬ IsDesignated bits (.gadget d κ pos) := by
  rintro ⟨digit, collector, block, same⟩
  simp [designatedIndex, scaleIndexOf, scaleIndexNat] at same

theorem hot_eq (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits) (e : Fin (2 ^ chunkBits))
    (h : Bool) : (FixedIndex.hot lane c f e h) = hotIndexNat lane c f.val e.val h :=
  (hotIndexNat_eq lane c f.val e.val h f.isLt e.isLt).symm

theorem hot_noCell (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) : cellOf (.hot lane c f e h) = none := by
  rw [hot_eq]
  exact cellOf_hot lane c f.val e.val h

theorem hot_notDesignated (bits : BitInput) (lane : Lane) (c : Fin chunkCount) (f : Fin chunkBits)
    (e : Fin (2 ^ chunkBits)) (h : Bool) : ¬ IsDesignated bits (.hot lane c f e h) := by
  rw [hot_eq]
  exact hot_not_designated bits lane c f.val e.val h

end Blind

/-! ### The whole process, and the fold/gadget outputs -/

section Whole

variable [FieldCertificate] [GroupCertificate]

/-- **On the curve, with a potential that may read the tape.** -/
theorem onCurve_whole_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (potential : Tape → LState → ℝ≥0∞)
    (step : ∀ (tape : Tape) (request : PublicQuery FixedIndex EncPRF.PermutationIndex)
      (state : LState), ForwardOnly request →
        ∑' answer, LazyOracle.query request state answer * potential tape answer.2 ≤
          potential tape state)
    (siteSame : ∀ (tape : Tape) (state updated : LState) (index : FixedIndex)
      (input' output : Block), cellOf index ≠ none →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential tape updated = potential tape state)
    (designatedSame : ∀ (tape : Tape) (state updated : LState) (index : FixedIndex)
      (input' output : Block), IsDesignated (restoredBits source input) index →
        LazyOracle.program (.fixedForward index input') output state = some updated →
          potential tape updated = potential tape state)
    (c : ℝ≥0∞) (initial : ∀ tape, potential tape LazyOracle.empty ≤ c)
    (final : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        ind (event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks)))) ≤ potential tape result.2) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ c :=
  onCurve_split_le scalar off source input target event (Pure.pure ())
    (fun _ => openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input))
    (Kriterion.ArgoMAC.Phase3.Lazy.fq_pure_bind () (fun _ => openingQueriesM source.publicValue
      (restoredBits source input) (restoredMac source input))).symm
    (fun _ => openingQueriesM_forwardOnly _ _ _)
    (fun tape _ => potential tape) (fun tape _ => step tape) (fun tape _ => siteSame tape)
    (fun tape _ => designatedSame tape) c
    (fun tape mid midMember => by
      change some mid ∈ (PMF.pure (some (((), LazyOracle.empty, fun _ => none, ∅) :
        Unit × LState × Record × Set FixedIndex))).support at midMember
      simp only [PMF.mem_support_pure_iff, Option.some.injEq] at midMember
      subst midMember
      exact initial tape)
    (fun tape _ _ ranT _ openMember blocks result resultMember =>
      final tape _ openMember blocks result resultMember)

/-- **The output mass at a fold or gadget index.** -/
theorem offScale_out_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (i : FixedIndex) (noCell : cellOf i = none)
    (notDesignated : ¬ IsDesignated (restoredBits source input) i) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut i y) ≤ delta := by
  refine le_trans (onCurve_potential_le scalar off source input target (fun p => p.fixedOut i y)
    (fun s => singleF y.toFin (s.fixed i))
    (fun request state forward => fixed_lift_step i _ (singleF_step _) request forward state)
    (fun state updated index input' output isCell success =>
      fixed_siteSame i _ noCell state updated index input' output isCell success)
    (fun state updated index input' output designated success =>
      fixed_designatedSame _ i _ notDesignated state updated index input' output designated success)
    fun tape ran member blocks result resultMember => ?_) (le_of_eq ?_)
  swap
  · show singleF y.toFin (SparsePermutation.empty _) = delta
    have zero : (SparsePermutation.empty (2 ^ 128)).used = 0 := rfl
    unfold singleF
    rw [if_pos zero]
  refine le_trans (ind_mono fun hit => ?_) (singleF_bound _ _ (used_le_one _
    (inputOf source.publicValue (restoredBits source input) (restoredMac source input)
      (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1))
      (refillAns (restoredBits source input) ran.2.1)
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) i).toFin
    fun x y' found => by
      rw [← final_input source input tape ran member blocks result resultMember i x y' found,
        BitVec.toFin_ofFin]))
  rcases hit with ⟨x, found⟩ | ⟨inp, out, inReq, _⟩
  · exact ⟨x, found⟩
  · obtain ⟨d, c, b, rfl, _, _⟩ := mem_programRequests inReq
    exact absurd ⟨d, c, b, rfl⟩ notDesignated

end Whole

/-! ### The fold of every chunk at the final state -/

section FoldFinal

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

/-- **Every fold index holds exactly the opening's pair at the final state.** -/
theorem fold_final (lane : Lane) (c : Fin chunkCount) (half : Bool) :
    let pads := wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) ran.2.1)
    let W := laneW (laneJoins source.publicValue lane) (laneLabels (restoredMac source input) pads
      lane) c
    let index := foldIdx lane c (chunkValue (laneWord (restoredBits source input) lane) c).toNat half
    (result.2.fixed index).used = 1 ∧
      lk (result.2.fixed index) W.toFin =
        some (fwdAns (refillAns (restoredBits source input) ran.2.1) index W).toFin := by
  intro pads W index
  have onA := lane_mem_opening _ _ _ _ lane _ (fold_mem_lane (refillAns (restoredBits source input)
    ran.2.1) _ lane _ (laneScale source.publicValue lane) _
      (laneLabels (restoredMac source input) pads lane) c half)
  obtain ⟨stored, answerEq⟩ := curve_stored_answer source input tape ran member _ onA
    (intercept_none_of_hot lane c _ half _)
  have lk1 := stored_fixed_lk (a := fwdAns (answerOf ran.2.1) index W) stored
  have lk3 := (final_grows source input tape ran member blocks result resultMember).fixed _ _ _ lk1
  have fwdEq : fwdAns (refillAns (restoredBits source input) ran.2.1) index W =
      fwdAns (answerOf ran.2.1) index W := answerEq
  refine ⟨?_, by rw [fwdEq]; exact lk3⟩
  have small := used_le_one _ (inputOf source.publicValue (restoredBits source input)
      (restoredMac source input) pads (refillAns (restoredBits source input) ran.2.1)
      (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
        (restoredMac source input) (answerOf result.2)) (restoredMac source input)) index).toFin
    fun x y found => by
      rw [← final_input source input tape ran member blocks result resultMember index x y found,
        BitVec.toFin_ofFin]
  have positive : (result.2.fixed index).used ≠ 0 := by
    intro zero
    have known : (result.2.fixed index).knownInput W.toFin :=
      (knownInput_iff _ _).mpr (by rw [lk3]; exact Option.some_ne_none _)
    unfold SparsePermutation.knownInput at known
    omega
  omega

end FoldFinal

/-! ### A mask index's canonical input is a fixed block xor the fold material -/

theorem xor_eq_iff (a b z : Block) : a ^^^ b = z ↔ b = z ^^^ a := by
  constructor
  · intro same
    rw [← same, BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro same
    rw [same, BitVec.xor_comm z a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- **The canonical input of a mask index.** -/
theorem inputOf_scale (table : Public) (bits : BitInput) (mac : InputMac)
    (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (ans : (request : Request) → request.Answer) (tmac : InputMac) (lane : Lane)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3) :
    inputOf table bits mac pads ans tmac (.scale lane c s e b) =
      foldLabels (chunkValue (laneWord bits lane) c).toNat
          (labelAt (chunkLabels (laneLabels mac pads lane) c))
          (joinAt (hotSlice (laneJoins table lane) c)) 0 ⟨s.val, by
            have := s.isLt; unfold chunkBits at this; exact this⟩ ^^^
        (fwdAns ans (foldIdx lane c (chunkValue (laneWord bits lane) c).toNat false)
            (laneW (laneJoins table lane) (laneLabels mac pads lane) c) ^^^
          fwdAns ans (foldIdx lane c (chunkValue (laneWord bits lane) c).toNat true)
            (laneW (laneJoins table lane) (laneLabels mac pads lane) c)) := by
  show foldLabels _ _ _ _ _ = _
  rw [Kriterion.ArgoMAC.Phase3.Lazy.foldLabels_linear]
  rfl

theorem foldIdx_ne (lane : Lane) (c : Fin chunkCount) (value : ℕ) :
    foldIdx lane c value false ≠ foldIdx lane c value true := by
  simp [foldIdx, hotIndexNat]

/-- The fold potential of a chunk, as a lazy-state potential. -/
abbrev chunkFoldPot (lane : Lane) (c : Fin chunkCount) (value : ℕ) (z : Block) (s : LState) :
    ℝ≥0∞ :=
  foldF z (s.fixed (foldIdx lane c value false)) (s.fixed (foldIdx lane c value true))

theorem chunkFoldPot_step (lane : Lane) (c : Fin chunkCount) (value : ℕ) (z : Block)
    (request : Request) (state : LState) (forward : ForwardOnly request) :
    ∑' answer, LazyOracle.query request state answer * chunkFoldPot lane c value z answer.2 ≤
      chunkFoldPot lane c value z state :=
  fixed2_lift_step _ _ (foldIdx_ne lane c value) (foldF z) (foldF_step₀ z) (foldF_step₁ z) request
    forward state

theorem chunkFoldPot_siteSame (lane : Lane) (c : Fin chunkCount) (value : ℕ) (z : Block)
    (state updated : LState) (index : FixedIndex) (input output : Block)
    (isCell : cellOf index ≠ none)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    chunkFoldPot lane c value z updated = chunkFoldPot lane c value z state := by
  have n0 : foldIdx lane c value false ≠ index := fun same =>
    isCell (same ▸ cellOf_hot lane c 1 _ false)
  have n1 : foldIdx lane c value true ≠ index := fun same =>
    isCell (same ▸ cellOf_hot lane c 1 _ true)
  show foldF z _ _ = foldF z _ _
  rw [program_frame index input output state updated success _ n0,
    program_frame index input output state updated success _ n1]

theorem chunkFoldPot_designatedSame (bits : BitInput) (lane : Lane) (c : Fin chunkCount)
    (value : ℕ) (z : Block) (state updated : LState) (index : FixedIndex) (input output : Block)
    (designated : IsDesignated bits index)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    chunkFoldPot lane c value z updated = chunkFoldPot lane c value z state := by
  have n0 : foldIdx lane c value false ≠ index := fun same =>
    hot_not_designated bits lane c 1 _ false (same ▸ designated)
  have n1 : foldIdx lane c value true ≠ index := fun same =>
    hot_not_designated bits lane c 1 _ true (same ▸ designated)
  show foldF z _ _ = foldF z _ _
  rw [program_frame index input output state updated success _ n0,
    program_frame index input output state updated success _ n1]

theorem chunkFoldPot_empty (lane : Lane) (c : Fin chunkCount) (value : ℕ) (z : Block) :
    chunkFoldPot lane c value z LazyOracle.empty = delta := by
  have zero : (SparsePermutation.empty (2 ^ 128)).used = 0 := rfl
  show foldF z (SparsePermutation.empty _) (SparsePermutation.empty _) = delta
  unfold foldF
  rw [if_pos ⟨zero.le.trans zero_le_one, zero.le.trans zero_le_one⟩, if_neg fun h => by
    rw [zero] at h
    exact absurd h.1 (by decide)]

section CurveScale

variable [FieldCertificate] [GroupCertificate]

/-- **At a mask index of system A, the canonical input hits any tape-dependent target with mass
`≤ 1/2^128`.** -/
theorem curveScale_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (curve : lane = .curveX ∨ lane = .curveY)
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
  have labelsSame : ∀ pads, laneLabels (restoredMac source input) pads lane =
      laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane := by
    intro pads
    rcases curve with rfl | rfl <;> rfl
  set value := (chunkValue (laneWord (restoredBits source input) lane) c).toNat with valueDef
  set fixedPart : Block := foldLabels value
    (labelAt (chunkLabels (laneLabels (restoredMac source input) (fun _ _ => (0, 0)) lane) c))
    (joinAt (hotSlice (laneJoins source.publicValue lane) c)) 0 ⟨s.val, by
      have := s.isLt; unfold chunkBits at this; exact this⟩ with fixedDef
  refine onCurve_whole_le scalar off source input target event
    (fun tape => chunkFoldPot lane c value (z tape ^^^ fixedPart))
    (fun tape => chunkFoldPot_step lane c value _)
    (fun tape => chunkFoldPot_siteSame lane c value _)
    (fun tape => chunkFoldPot_designatedSame _ lane c value _) delta
    (fun tape => le_of_eq (chunkFoldPot_empty lane c value _))
    fun tape ran member blocks result resultMember => ?_
  obtain ⟨used0, lk0⟩ := fold_final source input tape ran member blocks result resultMember lane c false
  obtain ⟨used1, lk1⟩ := fold_final source input tape ran member blocks result resultMember lane c true
  refine le_trans (ind_mono fun hit => ?_) (foldF_bound _ _ _ used0 used1 _ _ _ _ lk0 lk1)
  have same := reduce tape ran member blocks result resultMember hit
  rw [inputOf_scale, labelsSame] at same
  rw [BitVec.ofFin_toFin, BitVec.ofFin_toFin, labelsSame]
  exact (xor_eq_iff _ _ _).mp same

end CurveScale

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
