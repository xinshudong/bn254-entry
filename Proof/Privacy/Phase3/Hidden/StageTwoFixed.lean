/-
**Phase 3, P1h — stage 2, fixed-key hits: at most `2^-128` each, given the stage-2 view.**

* `stageTwoView_shift`: a join-keeping tape shift that keeps `u`'s labels and moves no garbler entry
  at a designed index keeps the whole stage-2 view (`designedEntries_eq` makes the designed entries a
  filter of the garbler's transcript, which the shift maps entrywise).
* The three families of `StageTwoShift` move no designed entry (`deltaU_fixed`, `key2_fixed` off
  the curve, `hotOut_fixed` at a hidden gate), and for every hidden index `i` one of them moves the
  garbler's point (`inFamily`) or output (`outFamily`) at `i` by `c`.
* `stageTwo_touch`: a touch of the stage-2 extra entries is a hit at a **hidden** index, or the
  bridge key off the curve.
* **`hiddenInput_le`, `hiddenOutput_le`**: `μ{view₂ = v ∧ i hidden ∧ the garbler's point (output) at
  i is x} ≤ 2^-128 · μ{view₂ = v}` (`event_le_of_symmetry`, `swapped_shift_invariant`).
-/

import Proof.Privacy.Phase3.Hidden.Containment

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

section Instances

variable [FieldCertificate] [GroupCertificate]

/-! ### The stage-2 view on a shifted tape -/

theorem designedIndex_shift (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (index : FixedIndex) :
    designedIndex scalar (shiftTape T scalar tape) input index = designedIndex scalar tape input index := by
  cases index <;> rfl

theorem designedRule_shiftEntry (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar (shiftTape T scalar tape) input (shiftEntry T scalar tape.1 entry) =
      designedRule scalar tape input entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x => exact designedIndex_shift T scalar tape input index
  | fixedInverse index x => exact designedIndex_shift T scalar tape input index
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash value =>
      by_cases h : value = tape.1.bridgeKey <;> simp [shiftEntry, h, designedRule]

theorem designedRule_shiftTape (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar (shiftTape T scalar tape) input entry = designedRule scalar tape input entry := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x => exact designedIndex_shift T scalar tape input index
  | fixedInverse index x => exact designedIndex_shift T scalar tape input index
  | _ => rfl

theorem designedRule_shiftEntry' (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    designedRule scalar tape input (shiftEntry T scalar tape.1 entry) = designedRule scalar tape input entry := by
  rw [← designedRule_shiftTape T scalar tape input, designedRule_shiftEntry]

/-- **The designed entries are kept** by a shift that moves no designed garbler entry. -/
theorem designedEntries_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (input : AffineInput)
    (fixed : ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry) :
    designedEntries designedRule parameter scalar (shiftTape T scalar tape) input =
      designedEntries designedRule parameter scalar tape input := by
  rw [designedEntries_eq, designedEntries_eq, garblerTranscript_shift T valid]
  have pred : (fun e : Entry FixedIndex EncPRF.PermutationIndex =>
      !e.IsEnc && designedRule scalar (shiftTape T scalar tape) input e) =
      fun e => !e.IsEnc && designedRule scalar tape input e :=
    funext fun e => by rw [designedRule_shiftTape]
  rw [pred]
  refine filter_map_eq _ _ _ (fun e _ => ?_) (fun e member keep => ?_)
  · rw [isEnc_shiftEntry, designedRule_shiftEntry']
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at keep
    exact fixed e member keep.1 keep.2

/-- **The stage-2 view is kept.** -/
theorem stageTwoView_shift (T : TapeShift) (valid : T.Valid) (parameter : ℕ) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (input : AffineInput)
    (labels : Scheme.scheme.encode (shiftCoins T tape.1).inputMacKey input =
      Scheme.scheme.encode tape.1.inputMacKey input)
    (fixed : ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry) :
    stageTwoView designedRule parameter scalar input (shiftTape T scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  unfold stageTwoView
  rw [stageOneView_shift T valid, designedEntries_shift T valid parameter scalar tape input fixed]
  have key : (Scheme.scheme.garble parameter scalar (shiftTape T scalar tape)).2 =
      (shiftCoins T tape.1).inputMacKey := rfl
  have key' : (Scheme.scheme.garble parameter scalar tape).2 = tape.1.inputMacKey := rfl
  rw [key, key', labels]

/-! ### Moving no designed entry -/

theorem shiftEntry_fixed_zero (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex)
    (x : Block) (answer : Block) (s : indexShift T scalar coins index = (0, 0)) :
    shiftEntry T scalar coins ⟨.fixedForward index x, answer⟩ = ⟨.fixedForward index x, answer⟩ := by
  have h1 : (indexShift T scalar coins index).1 = 0 := by rw [s]
  have h2 : (indexShift T scalar coins index).2 = 0 := by rw [s]
  show (⟨.fixedForward index (x ^^^ (indexShift T scalar coins index).1),
    answer ^^^ (indexShift T scalar coins index).2⟩ : Entry FixedIndex EncPRF.PermutationIndex) = _
  rw [h1, h2, bxor_zero, bxor_zero]

theorem shiftEntry_hash_zero (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (value : BaseField)
    (answer : Block × Block) (k : T.key2 = 0) :
    shiftEntry T scalar coins ⟨.hash value, answer⟩ = ⟨.hash value, answer⟩ := by
  by_cases h : value = coins.bridgeKey
  · show (if value = coins.bridgeKey then (⟨.hash value, (answer.1, answer.2 ^^^ T.key2)⟩ :
      Entry FixedIndex EncPRF.PermutationIndex) else ⟨.hash value, answer⟩) = _
    rw [if_pos h, k, bxor_zero]
  · show (if value = coins.bridgeKey then (⟨.hash value, (answer.1, answer.2 ^^^ T.key2)⟩ :
      Entry FixedIndex EncPRF.PermutationIndex) else ⟨.hash value, answer⟩) = _
    rw [if_neg h]

/-- The garbler's index shapes. -/
def IndexShape (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) : Prop :=
  GarblerAsk scalar coins (.fixedForward index 0)

theorem indexShape_of_ask (scalar : NonZeroScalar) (coins : Coins) (index : FixedIndex) (x : Block)
    (ask : GarblerAsk scalar coins (.fixedForward index x)) : IndexShape scalar coins index := by
  cases index <;> exact ask

/-- A shift that vanishes at every designed index of the garbler's shape (and at the bridge key on
the curve) moves no designed garbler entry. -/
theorem fixed_of_zero (T : TapeShift) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (zero : ∀ index, IndexShape scalar tape.1 index → designedIndex scalar tape input index = true →
      indexShift T scalar tape.1 index = (0, 0))
    (key : validate input = true → T.key2 = 0) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true → shiftEntry T scalar tape.1 entry = entry := by
  intro entry member _ designed
  have good := garblerTranscript_good scalar tape entry member
  have shape := garblerTranscript_ask scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      exact shiftEntry_fixed_zero T scalar tape.1 index x answer
        (zero index (indexShape_of_ask scalar tape.1 index x shape) designed)
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash value => exact shiftEntry_hash_zero T scalar tape.1 value answer (key designed)

theorem indexShift_hot (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (ℓ : Lane) (k : Fin chunkCount)
    (fold : Fin chunkBits) (r : Fin (2 ^ chunkBits)) (half : Bool) (foldOne : fold.val = 1) :
    indexShift T scalar coins (.hot ℓ k fold r half) = ((T.lane ℓ).fold k).hot 1 r.val half := by
  show ((T.lane ℓ).fold k).hot fold.val r.val half = _
  rw [foldOne]

theorem indexShift_scale (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (ℓ : Lane) (k : Fin chunkCount)
    (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3) :
    indexShift T scalar coins (.scale ℓ k s e b) =
      (((T.lane ℓ).fold k).level 2 s.val, ((T.lane ℓ).fold k).level 2 s.val) := by
  show ((((T.lane ℓ).fold k).level (chunkWidth k) s.val, ((T.lane ℓ).fold k).level (chunkWidth k) s.val)) = _
  rw [fold_level_width]

theorem switch_lt_four (s : Fin (2 ^ chunkBits)) : s.val < 4 := s.isLt

/-- **The Δ-family moves no designed entry.** -/
theorem deltaU_fixed (κ : Coord) (c : Block) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyDeltaU κ input c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_) (fun _ => rfl)
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
      rw [indexShift_hot _ scalar tape.1 ℓ k fold r half foldOne]
      have off := designed.1
      rw [foldOne] at off
      exact deltaU_hot_off κ input c ℓ k r.val half rSmall off
  | scale ℓ k s e b =>
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
      rw [indexShift_scale, deltaU_level_off κ input c ℓ k s.val (switch_lt_four s) designed.1]
  | gadget o κ' position =>
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq] at designed
      show (gadgetShift _ scalar tape.1 o κ' position, gadgetShift _ scalar tape.1 o κ' position) = _
      rw [deltaU_gadget, if_neg (fun h => h.2 designed.2)]

/-- **Off the curve the `k₂`-family moves no designed entry.** -/
theorem key2_fixed (z : Nat) (c : Block) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (invalid : validate input = false) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyKey2 z c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_)
    (fun valid => by rw [invalid] at valid; cases valid)
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq, invalid, Bool.or_false] at designed
      rw [indexShift_hot _ scalar tape.1 ℓ k fold r half foldOne]
      have curve : laneIsPoint ℓ = false := by
        cases ℓ <;> simp_all [laneIsCurve, laneIsPoint]
      exact key2_hot_curve z c ℓ k curve 1 r.val half le_rfl
  | scale ℓ k s e b =>
      simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq, invalid, Bool.or_false] at designed
      have curve : laneIsPoint ℓ = false := by
        cases ℓ <;> simp_all [laneIsCurve, laneIsPoint]
      rw [indexShift_scale, key2_level_curve z c ℓ k curve]
  | gadget o κ position =>
      simp only [designedIndex, invalid, Bool.false_and] at designed
      cases designed

/-- **At a hidden gate the hot-output family moves no designed entry.** -/
theorem hotOut_fixed (ℓ : Lane) (k : Fin chunkCount) (r : Nat) (c : Block) (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (input : AffineInput)
    (hidden : ∀ (fold : Fin chunkBits) (entry : Fin (2 ^ chunkBits)) (half : Bool), fold.val = 1 →
      entry.val = r → designedIndex scalar tape input (.hot ℓ k fold entry half) = false) :
    ∀ entry ∈ garblerTranscript scalar tape, entry.IsEnc = false →
      designedRule scalar tape input entry = true →
        shiftEntry (familyHotOut ℓ k r c) scalar tape.1 entry = entry := by
  refine fixed_of_zero _ scalar tape input (fun index shape designed => ?_) (fun _ => rfl)
  cases index with
  | hot ℓ' k' fold r' half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      rw [indexShift_hot _ scalar tape.1 ℓ' k' fold r' half foldOne, hotOut_hot ℓ k r c ℓ' k' 1 r'.val half le_rfl]
      by_cases same : ℓ' = ℓ ∧ k' = k ∧ r'.val = r
      · obtain ⟨rfl, rfl, hr⟩ := same
        rw [hidden fold r' half foldOne hr] at designed
        cases designed
      · have : ¬ (ℓ' = ℓ ∧ k' = k ∧ 1 = 1 ∧ r'.val = r) := fun h => same ⟨h.1, h.2.1, h.2.2.2⟩
        rw [if_neg this]
  | scale ℓ' k' s e b => rw [indexShift_scale, hotOut_level]
  | gadget o κ position =>
      show (gadgetShift _ scalar tape.1 o κ position, gadgetShift _ scalar tape.1 o κ position) = _
      rw [hotOut_gadget]

/-! ### The families at a hidden index -/

/-- **The family moving the garbler's point at `i`.** -/
def inFamily (input : AffineInput) : FixedIndex → Block → TapeShift
  | .hot ℓ _ _ _ _, c => if laneIsCurve ℓ || validate input then familyDeltaU ℓ.coord input c else familyKey2 0 c
  | .scale ℓ _ s _ _, c =>
      if laneIsCurve ℓ || validate input then familyDeltaU ℓ.coord input c
      else familyKey2 (if s.val < 2 then s.val else 3 - s.val) c
  | .gadget _ κ _, c => if validate input then familyDeltaU κ input c else familyKey2 0 c

/-- **The family moving the garbler's output at `i`.** -/
def outFamily (input : AffineInput) : FixedIndex → Block → TapeShift
  | .hot ℓ k _ r _, c => familyHotOut ℓ k r.val c
  | index, c => inFamily input index c

theorem inFamily_hot (input : AffineInput) (ℓ : Lane) (k : Fin chunkCount) (fold : Fin chunkBits)
    (r : Fin (2 ^ chunkBits)) (half : Bool) (c : Block) :
    inFamily input (.hot ℓ k fold r half) c =
      if (laneIsCurve ℓ || validate input) = true then familyDeltaU ℓ.coord input c else familyKey2 0 c := rfl

theorem inFamily_scale (input : AffineInput) (ℓ : Lane) (k : Fin chunkCount) (s : Fin (2 ^ chunkBits))
    (e : Fin elementCountX) (b : Fin 3) (c : Block) :
    inFamily input (.scale ℓ k s e b) c =
      if (laneIsCurve ℓ || validate input) = true then familyDeltaU ℓ.coord input c
      else familyKey2 (if s.val < 2 then s.val else 3 - s.val) c := rfl

theorem inFamily_gadget (input : AffineInput) (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits)
    (c : Block) :
    inFamily input (.gadget o κ position) c =
      if validate input = true then familyDeltaU κ input c else familyKey2 0 c := rfl

theorem inFamily_valid (input : AffineInput) (index : FixedIndex) (c : Block) :
    (inFamily input index c).Valid := by
  cases index with
  | hot ℓ k fold r half =>
      rw [inFamily_hot]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact familyDeltaU_valid _ _ _
      · rw [if_neg h]
        exact familyKey2_valid 0 (by omega) c
  | scale ℓ k s e b =>
      rw [inFamily_scale]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact familyDeltaU_valid _ _ _
      · rw [if_neg h]
        refine familyKey2_valid _ ?_ c
        have := switch_lt_four s
        split <;> omega
  | gadget o κ position =>
      rw [inFamily_gadget]
      by_cases h : validate input = true
      · rw [if_pos h]
        exact familyDeltaU_valid _ _ _
      · rw [if_neg h]
        exact familyKey2_valid 0 (by omega) c

theorem outFamily_hot (input : AffineInput) (ℓ : Lane) (k : Fin chunkCount) (fold : Fin chunkBits)
    (r : Fin (2 ^ chunkBits)) (half : Bool) (c : Block) :
    outFamily input (.hot ℓ k fold r half) c = familyHotOut ℓ k r.val c := rfl

theorem outFamily_scale (input : AffineInput) (ℓ : Lane) (k : Fin chunkCount) (s : Fin (2 ^ chunkBits))
    (e : Fin elementCountX) (b : Fin 3) (c : Block) :
    outFamily input (.scale ℓ k s e b) c = inFamily input (.scale ℓ k s e b) c := rfl

theorem outFamily_gadget (input : AffineInput) (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits)
    (c : Block) : outFamily input (.gadget o κ position) c = inFamily input (.gadget o κ position) c := rfl

theorem outFamily_valid (input : AffineInput) (index : FixedIndex) (c : Block) :
    (outFamily input index c).Valid := by
  cases index with
  | hot ℓ k fold r half =>
      rw [outFamily_hot]
      exact familyHotOut_valid _ _ _ _
  | scale ℓ k s e b =>
      rw [outFamily_scale]
      exact inFamily_valid _ _ _
  | gadget o κ position =>
      rw [outFamily_gadget]
      exact inFamily_valid _ _ _

theorem inFamily_coins (input : AffineInput) (index : FixedIndex) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (inFamily input index c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  cases index with
  | hot ℓ k fold r half =>
      rw [inFamily_hot]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact deltaU_encode _ _ _ _
      · rw [if_neg h, key2_coins]
  | scale ℓ k s e b =>
      rw [inFamily_scale]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact deltaU_encode _ _ _ _
      · rw [if_neg h, key2_coins]
  | gadget o κ position =>
      rw [inFamily_gadget]
      by_cases h : validate input = true
      · rw [if_pos h]
        exact deltaU_encode _ _ _ _
      · rw [if_neg h, key2_coins]

theorem outFamily_coins (input : AffineInput) (index : FixedIndex) (c : Block) (coins : Coins) :
    Scheme.scheme.encode (shiftCoins (outFamily input index c) coins).inputMacKey input =
      Scheme.scheme.encode coins.inputMacKey input := by
  cases index with
  | hot ℓ k fold r half => rw [outFamily_hot, hotOut_coins]
  | scale ℓ k s e b =>
      rw [outFamily_scale]
      exact inFamily_coins _ _ _ _
  | gadget o κ position =>
      rw [outFamily_gadget]
      exact inFamily_coins _ _ _ _

theorem not_or_valid (ℓ : Lane) (input : AffineInput) (h : ¬ (laneIsCurve ℓ || validate input) = true) :
    validate input = false := by
  cases hv : validate input
  · rfl
  · rw [hv, Bool.or_true] at h
    exact absurd rfl h

/-- **`inFamily` keeps the stage-2 view.** -/
theorem inFamily_view (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex)
    (c : Block) (tape : Coins × Oracle) :
    stageTwoView designedRule parameter scalar input (shiftTape (inFamily input index c) scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  refine stageTwoView_shift _ (inFamily_valid input index c) parameter scalar tape input
    (inFamily_coins input index c tape.1) ?_
  cases index with
  | hot ℓ k fold r half =>
      rw [inFamily_hot]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact deltaU_fixed _ _ scalar tape input
      · rw [if_neg h]
        exact key2_fixed _ _ scalar tape input (not_or_valid ℓ input h)
  | scale ℓ k s e b =>
      rw [inFamily_scale]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        exact deltaU_fixed _ _ scalar tape input
      · rw [if_neg h]
        exact key2_fixed _ _ scalar tape input (not_or_valid ℓ input h)
  | gadget o κ position =>
      rw [inFamily_gadget]
      by_cases h : validate input = true
      · rw [if_pos h]
        exact deltaU_fixed _ _ scalar tape input
      · rw [if_neg h]
        exact key2_fixed _ _ scalar tape input (by simpa using h)

theorem point_of_not_curve (ℓ : Lane) (input : AffineInput) (h : ¬ (laneIsCurve ℓ || validate input) = true) :
    laneIsPoint ℓ = true := by
  cases ℓ <;> simp_all [laneIsCurve, laneIsPoint]

/-- **`inFamily` moves the garbler's point at a hidden index by `c`.** -/
theorem inFamily_moves (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (index : FixedIndex) (c : Block) (shape : IndexShape scalar tape.1 index)
    (hidden : designedIndex scalar tape input index = false) :
    (indexShift (inFamily input index c) scalar tape.1 index).1 = c := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      rw [indexShift_hot _ scalar tape.1 ℓ k fold r half foldOne, inFamily_hot]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        have on : r.val = lowOf input ℓ.coord k := by
          by_contra ne
          have designed : designedIndex scalar tape input (.hot ℓ k fold r half) = true := by
            simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨?_, h⟩
            rw [foldOne]
            exact ne
          rw [hidden] at designed
          cases designed
        rw [on]
        exact deltaU_hot_on ℓ.coord input c ℓ k half rfl
      · rw [if_neg h]
        exact key2_hot_point 0 c ℓ k (point_of_not_curve ℓ input h) r.val half
  | scale ℓ k s e b =>
      rw [indexShift_scale, inFamily_scale]
      by_cases h : (laneIsCurve ℓ || validate input) = true
      · rw [if_pos h]
        have on : s.val = (chunkOf (inputBits input ℓ.coord) k).val := by
          by_contra ne
          have designed : designedIndex scalar tape input (.scale ℓ k s e b) = true := by
            simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨ne, h⟩
          rw [hidden] at designed
          cases designed
        rw [on]
        exact deltaU_level_on ℓ.coord input c ℓ k rfl
      · rw [if_neg h]
        exact key2_level_point _ c ℓ k (point_of_not_curve ℓ input h) s.val (switch_lt_four s) rfl
  | gadget o κ position =>
      show gadgetShift (inFamily input (.gadget o κ position) c) scalar tape.1 o κ position = c
      rw [inFamily_gadget]
      by_cases h : validate input = true
      · rw [if_pos h, deltaU_gadget]
        have differ : (inputBits input κ).getLsb position ≠ exceptionalBit scalar tape.1.offsets o κ position := by
          intro same
          have designed : designedIndex scalar tape input (.gadget o κ position) = true := by
            simp only [designedIndex, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨h, same⟩
          rw [hidden] at designed
          cases designed
        rw [if_pos ⟨rfl, differ⟩]
      · rw [if_neg h]
        exact key2_gadget 0 c scalar tape.1 o κ position

theorem designedIndex_hot_tape (scalar : NonZeroScalar) (tape tape' : Coins × Oracle) (input : AffineInput)
    (ℓ : Lane) (k : Fin chunkCount) (fold : Fin chunkBits) (r : Fin (2 ^ chunkBits)) (half : Bool) :
    designedIndex scalar tape input (.hot ℓ k fold r half) = designedIndex scalar tape' input (.hot ℓ k fold r half) :=
  rfl

/-- **`outFamily` keeps the stage-2 view at a hidden index of the garbler's shape.** -/
theorem outFamily_view (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex)
    (c : Block) (tape : Coins × Oracle) (tape₀ : Coins × Oracle) (shape : IndexShape scalar tape₀.1 index)
    (hidden : designedIndex scalar tape₀ input index = false) :
    stageTwoView designedRule parameter scalar input (shiftTape (outFamily input index c) scalar tape) =
      stageTwoView designedRule parameter scalar input tape := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      refine stageTwoView_shift _ (outFamily_valid input _ c) parameter scalar tape input
        (outFamily_coins input _ c tape.1) ?_
      rw [outFamily_hot]
      refine hotOut_fixed ℓ k r.val c scalar tape input fun fold' entry half' foldOne' same => ?_
      have eq : designedIndex scalar tape input (.hot ℓ k fold' entry half') =
          designedIndex scalar tape₀ input (.hot ℓ k fold r half) := by
        simp only [designedIndex, foldOne, foldOne', same]
      rw [eq]
      exact hidden
  | scale ℓ k s e b =>
      rw [outFamily_scale]
      exact inFamily_view parameter scalar input _ c tape
  | gadget o κ position =>
      rw [outFamily_gadget]
      exact inFamily_view parameter scalar input _ c tape

theorem outFamily_moves (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (index : FixedIndex) (c : Block) (shape : IndexShape scalar tape.1 index)
    (hidden : designedIndex scalar tape input index = false) :
    (indexShift (outFamily input index c) scalar tape.1 index).2 = c := by
  cases index with
  | hot ℓ k fold r half =>
      obtain ⟨foldOne, rSmall⟩ := shape
      rw [outFamily_hot, indexShift_hot _ scalar tape.1 ℓ k fold r half foldOne,
        hotOut_hot ℓ k r.val c ℓ k 1 r.val half le_rfl]
      simp
  | scale ℓ k s e b =>
      have one := inFamily_moves scalar tape input (.scale ℓ k s e b) c shape hidden
      rw [outFamily_scale, indexShift_scale]
      rw [indexShift_scale] at one
      exact one
  | gadget o κ position =>
      rw [outFamily_gadget]
      exact inFamily_moves scalar tape input (.gadget o κ position) c shape hidden

/-! ### Touches of the stage-2 extra entries -/

/-- The garbler asks the **hidden** index `i` at `x`. -/
def HiddenInput (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex) (x : Block)
    (tape : Coins × Oracle) : Prop :=
  designedIndex scalar tape input index = false ∧ InputHit scalar index x tape

/-- The garbler's answer at the **hidden** index `i` is `y`. -/
def HiddenOutput (scalar : NonZeroScalar) (input : AffineInput) (index : FixedIndex) (y : Block)
    (tape : Coins × Oracle) : Prop :=
  designedIndex scalar tape input index = false ∧ OutputHit scalar index y tape

theorem designed_mem (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (member : entry ∈ garblerTranscript scalar tape)
    (plain : entry.IsEnc = false) (designed : designedRule scalar tape input entry = true) :
    entry ∈ designedEntries designedRule parameter scalar tape input := by
  rw [designedEntries_eq]
  exact List.mem_filter.mpr ⟨member, by simp [plain, designed]⟩

theorem designedRule_of_fixedPair (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) (member : entry ∈ garblerTranscript scalar tape)
    {index : FixedIndex} {x y : Fin (2 ^ 128)} (pair : fixedPair entry = some (index, x, y)) :
    designedRule scalar tape input entry = designedIndex scalar tape input index := by
  have good := garblerTranscript_good scalar tape entry member
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward i input' =>
      simp only [fixedPair, Option.some.injEq, Prod.mk.injEq] at pair
      obtain ⟨rfl, _, _⟩ := pair
      rfl
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => simp [fixedPair] at pair
  | encInverse _ _ => simp [fixedPair] at pair
  | hash _ => simp [fixedPair] at pair

/-- A stage-2 extra fixed-key pair is a garbler pair at a hidden index. -/
theorem stageTwo_fixed (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (tape : Coins × Oracle)
    {index : FixedIndex} {x y : Fin (2 ^ 128)}
    (extra : (stageTwoExtra designedRule parameter scalar input tape).fixed index x y) :
    designedIndex scalar tape input index = false ∧
      (⟨.fixedForward index (BitVec.ofFin x), BitVec.ofFin y⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
        garblerTranscript scalar tape := by
  obtain ⟨⟨e, member, pair⟩, notDesigned⟩ := extra
  have inT : e ∈ garblerTranscript scalar tape := (List.mem_filter.mp member).1
  refine ⟨?_, fixedPair_good scalar tape e inT pair⟩
  by_contra designed
  have d : designedIndex scalar tape input index = true := by simpa using designed
  have plain : Entry.IsEnc e = false := isEnc_of_fixedPair pair
  exact notDesigned ⟨e, designed_mem parameter scalar tape input e inT plain
    ((designedRule_of_fixedPair scalar tape input e inT pair).trans d), pair⟩

/-- **A stage-2 touch is a hidden hit, or the bridge key off the curve.** -/
theorem stageTwo_touch (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (tape : Coins × Oracle)
    (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (touch : Touches (stageTwoExtra designedRule parameter scalar input tape) entry) :
    match entry with
    | ⟨.fixedForward index x, answer⟩ =>
        HiddenInput scalar input index x tape ∨ HiddenOutput scalar input index (show Block from answer) tape
    | ⟨.fixedInverse index y, answer⟩ =>
        HiddenOutput scalar input index y tape ∨ HiddenInput scalar input index (show Block from answer) tape
    | ⟨.hash key, _⟩ => validate input = false ∧ key = tape.1.bridgeKey
    | _ => False := by
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      rcases touch with ⟨y, extra⟩ | ⟨x', extra⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inl ⟨hidden, _, member⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inr ⟨hidden, _, member⟩
  | fixedInverse index y =>
      rcases touch with ⟨x, extra⟩ | ⟨y', extra⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inl ⟨hidden, _, member⟩
      · obtain ⟨hidden, member⟩ := stageTwo_fixed parameter scalar input tape extra
        exact Or.inr ⟨hidden, _, member⟩
  | encForward index x =>
      rcases touch with ⟨y, extra⟩ | ⟨x', extra⟩ <;>
      · obtain ⟨⟨e, member, pair⟩, _⟩ := extra
        have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | encInverse index y =>
      rcases touch with ⟨x, extra⟩ | ⟨y', extra⟩ <;>
      · obtain ⟨⟨e, member, pair⟩, _⟩ := extra
        have notEnc := (List.mem_filter.mp member).2
        rw [isEnc_of_encPair pair] at notEnc
        cases notEnc
  | hash key =>
      have notDesigned : ¬ ∃ d ∈ designedEntries designedRule parameter scalar tape input, ∃ value,
          hashPair d = some (key, value) := by
        intro found
        simp only [Touches, stageTwoExtra, dropAll, if_pos found] at touch
        cases touch
      have listed : ∃ e ∈ plainEntries scalar tape, ∃ value, hashPair e = some (key, value) := by
        by_contra none'
        simp only [Touches, stageTwoExtra, dropAll, if_neg notDesigned, stageOneExtra, extraOf,
          if_neg none'] at touch
        cases touch
      obtain ⟨e, member, value, pair⟩ := listed
      have inT : e ∈ garblerTranscript scalar tape := (List.mem_filter.mp member).1
      have good := garblerTranscript_good scalar tape e inT
      obtain ⟨request', answer'⟩ := e
      cases request' <;> simp only [hashPair, Option.some.injEq, reduceCtorEq] at pair
      obtain ⟨rfl, _⟩ := pair
      refine ⟨?_, good⟩
      by_contra valid
      have v : validate input = true := by simpa using valid
      exact notDesigned ⟨_, designed_mem parameter scalar tape input _ inT rfl v, _, rfl⟩

/-! ### The bounds -/

/-- An input hit on a shifted tape comes from a garbler entry of the garbler's shape. -/
theorem inputHit_shape (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (index : FixedIndex) (x : Block) (hit : InputHit scalar index x (shiftTape T scalar tape)) :
    IndexShape scalar tape.1 index := by
  obtain ⟨y, member⟩ := hit
  rw [garblerTranscript_shift T valid] at member
  obtain ⟨e, eMember, same⟩ := List.mem_map.mp member
  have shape := garblerTranscript_ask scalar tape e eMember
  obtain ⟨request, answer⟩ := e
  cases request with
  | fixedForward i input' =>
      simp only [shiftEntry, Sigma.mk.inj_iff, PublicQuery.fixedForward.injEq] at same
      obtain ⟨⟨rfl, _⟩, _⟩ := same
      exact indexShape_of_ask scalar tape.1 _ _ shape
  | fixedInverse _ _ => unfold shiftEntry at same; cases same
  | encForward _ _ => unfold shiftEntry at same; cases same
  | encInverse _ _ => unfold shiftEntry at same; cases same
  | hash value =>
      have fst := congrArg Sigma.fst same
      rw [shiftEntry_fst_hash] at fst
      cases fst

theorem outputHit_shape (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (index : FixedIndex) (y : Block) (hit : OutputHit scalar index y (shiftTape T scalar tape)) :
    IndexShape scalar tape.1 index := by
  obtain ⟨x, member⟩ := hit
  exact inputHit_shape T valid scalar tape index x ⟨y, member⟩

/-- **Stage 2: a hidden input hit, at most `2^-128` given the view.** -/
theorem hiddenInput_le (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (x : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          HiddenInput scalar input index x tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view} := by
  have bound := event_le_of_symmetry swappedChallengeTape (stageTwoView designedRule parameter scalar input)
    (HiddenInput scalar input index x) (fun c tape => shiftTape (inFamily input index c) scalar tape)
    (fun c => swapped_shift_invariant _ (inFamily_valid input index c) scalar)
    (fun c tape => inFamily_view parameter scalar input index c tape)
    (fun tape c c' first second => by
      have moves : ∀ d, HiddenInput scalar input index x (shiftTape (inFamily input index d) scalar tape) →
          garblerPointOf scalar tape index ^^^ d = x := by
        intro d hit
        have hidden : designedIndex scalar tape input index = false := by
          rw [← designedIndex_shift (inFamily input index d)]
          exact hit.1
        have shape := inputHit_shape _ (inFamily_valid input index d) scalar tape index x hit.2
        have shifted := inputHit_shift _ (inFamily_valid input index d) scalar tape index x hit.2
        rwa [inFamily_moves scalar tape input index d shape hidden] at shifted
      have := (moves c first).trans (moves c' second).symm
      rwa [BitVec.xor_right_inj] at this) view
  rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound

/-- **Stage 2: a hidden output hit, at most `2^-128` given the view.** -/
theorem hiddenOutput_le (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (view : (Public × List (Entry FixedIndex EncPRF.PermutationIndex)) × LamportSignature ×
      List (Entry FixedIndex EncPRF.PermutationIndex)) (index : FixedIndex) (y : Block) :
    swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view ∧
          HiddenOutput scalar input index y tape} ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ * swappedChallengeTape.toOuterMeasure
        {tape | stageTwoView designedRule parameter scalar input tape = view} := by
  by_cases some : ∃ tape₀, HiddenOutput scalar input index y tape₀
  · obtain ⟨tape₀, hidden₀, hit₀⟩ := some
    have shape₀ : IndexShape scalar tape₀.1 index := by
      obtain ⟨x, member⟩ := hit₀
      exact indexShape_of_ask scalar tape₀.1 index x (garblerTranscript_ask scalar tape₀ _ member)
    have bound := event_le_of_symmetry swappedChallengeTape (stageTwoView designedRule parameter scalar input)
      (HiddenOutput scalar input index y) (fun c tape => shiftTape (outFamily input index c) scalar tape)
      (fun c => swapped_shift_invariant _ (outFamily_valid input index c) scalar)
      (fun c tape => outFamily_view parameter scalar input index c tape tape₀ shape₀ hidden₀)
      (fun tape c c' first second => by
        have moves : ∀ d, HiddenOutput scalar input index y (shiftTape (outFamily input index d) scalar tape) →
            tape.2.1.permutation index (garblerPointOf scalar tape index) ^^^ d = y := by
          intro d hit
          have hidden : designedIndex scalar tape input index = false := by
            rw [← designedIndex_shift (outFamily input index d)]
            exact hit.1
          have shape := outputHit_shape _ (outFamily_valid input index d) scalar tape index y hit.2
          have shifted := outputHit_shift _ (outFamily_valid input index d) scalar tape index y hit.2
          rwa [outFamily_moves scalar tape input index d shape hidden] at shifted
        have := (moves c first).trans (moves c' second).symm
        rwa [BitVec.xor_right_inj] at this) view
    rwa [card_block', Nat.cast_pow, Nat.cast_ofNat] at bound
  · have empty : {tape | stageTwoView designedRule parameter scalar input tape = view ∧
        HiddenOutput scalar input index y tape} = ∅ := by
      ext tape
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ hit => some ⟨tape, hit⟩
    rw [empty, MeasureTheory.measure_empty]
    exact bot_le

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
