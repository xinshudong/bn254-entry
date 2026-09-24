/-
**Phase 3, P4b — the `pointX` part of the per-prefix failure bound: (a) and (b).**

`failObs`: given the lanes and the record, the probability over the target rows and the preimages
that some designated program collides with a stage-1 entry at its index (input `E*` known there,
or output `o_b xor E*` used there).

**`pointPart_bound`** — from any state that agrees with stage 1 on chunk 0 of `pointX` and has not
touched it, the `pointX`/`pointY` part of the run fails with mass at most

  `1[W ∈ dom σ₁(i₁)] + (1/(2^128 − n(i₁))) · (Σ_{mask indices} n + 2 · Σ_{designated} n)`,

where `W` is the whitened bit-0 label and `i₁` the second half of the inactive level-1 fold gate.
Off the fold hit, the answer at `i₁` is uniform on the unused outputs, and every chunk-0 label,
`E*` included, is a fixed block XOR it (`foldLabels_linear`):

* **(a)** `E*` hits a designated domain with mass `≤ n/(2^128 − n(i₁))` per slot;
* the labels hit a mask index's domain (then its cached answer would be read) with mass
  `≤ n/(2^128 − n(i₁))` per index (`maskCharge`);
* **(b)** otherwise every mask is consumed from the tape (`masks_detRun_ne_none`), the lane values
  do not depend on the fold answers (`masks_value`, `runRefillT_value_frame`), and the output
  `o_b xor E*` hits a designated range with mass `≤ n/(2^128 − n(i₁))` per slot.
-/

import Proof.Privacy.Phase3.Lazy.FailHelpers
import Proof.Privacy.Phase3.Opened

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (simulatedRows laneCount)
open scoped ENNReal

noncomputable section

/-! ### More expectation algebra -/

section Expect

variable {β γ : Type}

theorem expectO_congr_support (μ : PMF (Option β)) {f g : β → ℝ≥0∞}
    (same : ∀ b, some b ∈ μ.support → f b = g b) : expectO μ f = expectO μ g :=
  le_antisymm (expectO_mono_support μ fun b member => (same b member).le)
    (expectO_mono_support μ fun b member => (same b member).ge)

theorem expectO_tsum (μ : PMF (Option β)) (f : γ → β → ℝ≥0∞) :
    expectO μ (fun b => ∑' a, f a b) = ∑' a, expectO μ (f a) := by
  unfold expectO
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp
  | some b => exact ENNReal.tsum_mul_left.symm

theorem expectO_finsum (μ : PMF (Option β)) {ι : Type} [Fintype ι] (f : ι → β → ℝ≥0∞) :
    expectO μ (fun b => ∑ s, f s b) = ∑ s, expectO μ (f s) := by
  have eachTsum := expectO_tsum μ f
  simp only [tsum_fintype] at eachTsum
  exact eachTsum

theorem expectO_frame_value {α : Type} (μ ν : PMF (Option (α × LState × Record × Set FixedIndex)))
    (law : μ.map (Option.map Prod.fst) = ν.map (Option.map Prod.fst)) (record : Record)
    (recordSame : ∀ r, some r ∈ μ.support → r.2.2.1 = record) (g : α → Record → ℝ≥0∞) :
    expectO μ (fun r => g r.1 r.2.2.1) = expectO ν (fun r => g r.1 record) := by
  rw [expectO_congr_support μ (g := fun r => g r.1 record) fun r member => by
    rw [recordSame r member]]
  have first := expectO_map μ Prod.fst (fun v => g v record)
  have second := expectO_map ν Prod.fst (fun v => g v record)
  rw [law] at first
  exact first.symm.trans second

end Expect

/-! ### The failure observable -/

/-- A designated slot: (digit, collector, block). -/
abbrev Slot := Fin digitCount × Fin 3 × Fin 3

/-- The designated index of a slot. -/
abbrev slotIndex (bits : BitInput) (slot : Slot) : FixedIndex :=
  designatedIndex bits slot.1 slot.2.1 slot.2.2

section Observable

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- The law of the 819 program outputs' triples, given the lanes: the target rows, then the
preimages of the collector targets (`installInputs`' last two draws). -/
def blockLaw (table : Public) (input : AffineInput) (target : Point) (bits : BitInput)
    (lanes : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :
    PMF (Option (Fin digitCount × Fin 3 → Block × Block × Block)) :=
  (simulatedRows input target).bind fun targets => match targets with
  | none => PMF.pure none
  | some targets => preimages idealSamplers (collectorTargets bits
      (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
        (Pipeline.digitValues lanes.1 lanes.2) bits.toAffine) targets)

/-- One slot's program collides with the stage-1 oracle. -/
def SlotCollides (stage : LState) (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (slot : Slot) : Prop :=
  ∃ x, record (slotIndex bits slot) = some x ∧
    ((stage.fixed (slotIndex bits slot)).knownInput x.toFin ∨
      (stage.fixed (slotIndex bits slot)).knownOutput
        (limbAt slot.2.2 (blocks (slot.1, slot.2.1)) ^^^ x).toFin)

open Classical in
/-- **The failure observable** of a run result: the mass of a slot collision. -/
def failObs (stage : LState) (table : Public) (input : AffineInput) (target : Point)
    (bits : BitInput)
    (lanes : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (record : Record) : ℝ≥0∞ :=
  expectO (blockLaw table input target bits lanes) fun blocks =>
    if ∃ slot, SlotCollides stage bits record blocks slot then 1 else 0

theorem failObs_le_one (stage : LState) (table : Public) (input : AffineInput) (target : Point)
    (bits : BitInput)
    (lanes : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (record : Record) : failObs stage table input target bits lanes record ≤ 1 := by
  unfold failObs
  exact expectO_le_one _ fun _ => by split <;> simp

open Classical in
/-- The two per-slot collision indicators for a given designated input `E`. -/
def slotInput (stage : LState) (bits : BitInput) (label : Block) (slot : Slot) : ℝ≥0∞ :=
  if (stage.fixed (slotIndex bits slot)).knownInput label.toFin then 1 else 0

open Classical in
def slotOutput (stage : LState) (bits : BitInput) (label : Block) (slot : Slot)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) : ℝ≥0∞ :=
  if (stage.fixed (slotIndex bits slot)).knownOutput
      (limbAt slot.2.2 (blocks (slot.1, slot.2.1)) ^^^ label).toFin then 1 else 0

open Classical in
/-- **With every designated record `none` or `E`, the failure is at most the per-slot input and
output collisions of `E`.** -/
theorem failObs_le (stage : LState) (table : Public) (input : AffineInput) (target : Point)
    (bits : BitInput)
    (lanes : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (record : Record) (label : Block)
    (recorded : ∀ slot, record (slotIndex bits slot) = none ∨
      record (slotIndex bits slot) = some label) :
    failObs stage table input target bits lanes record ≤
      ∑ slot, (slotInput stage bits label slot +
        expectO (blockLaw table input target bits lanes) (slotOutput stage bits label slot)) := by
  classical
  unfold failObs
  calc expectO (blockLaw table input target bits lanes)
        (fun blocks => if ∃ slot, SlotCollides stage bits record blocks slot then 1 else 0)
      ≤ expectO (blockLaw table input target bits lanes) (fun blocks =>
          ∑ slot, (slotInput stage bits label slot + slotOutput stage bits label slot blocks)) := by
        refine expectO_mono _ fun blocks => (indicator_exists_le _).trans ?_
        refine Finset.sum_le_sum fun slot _ => ?_
        split
        · rename_i collides
          obtain ⟨x, same, hit⟩ := collides
          rcases recorded slot with none | some
          · rw [none] at same
            cases same
          · rw [some] at same
            cases same
            unfold slotInput slotOutput
            rcases hit with hit | hit
            · rw [if_pos hit]
              exact le_self_add
            · rw [if_pos hit]
              exact le_add_self
        · exact zero_le
    _ = ∑ slot, expectO (blockLaw table input target bits lanes)
          (fun blocks => slotInput stage bits label slot + slotOutput stage bits label slot blocks) :=
        expectO_finsum _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun slot _ => ?_
        rw [expectO_add]
        exact add_le_add (expectO_const_le _ _) le_rfl

end Observable

/-! ### Where the chunk-0 masks ask -/

/-- A query of the masks of a chunk: at a mask index, at its switch's label. -/
def MaskQuery {width : Nat} (count : Nat) (lane : Lane) (chunk : Fin chunkCount)
    (hot : HotLabels width) (request : Request) : Prop :=
  ∃ (switch : Fin (2 ^ width)) (element : Fin count) (block : Fin 3),
    request = .fixedForward (maskIndex lane chunk switch.val element block) (hot switch)

theorem evalMasksM_maskQuery (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha : Fin (2 ^ width)) :
    AllQ (MaskQuery count lane chunk hot)
      (Programs.evalMasksM count lane chunk width hot alpha) := by
  refine (AllQ.vector fun switch => AllQ.ite (.pure _) ?_).bind fun _ => .pure _
  refine (AllQ.vector fun element => ?_).bind fun _ => .pure _
  have one : ∀ block : Fin 3, ∀ {β : Type} (k : Block → FreeQuery Programs.Spec β),
      (∀ value, AllQ (MaskQuery count lane chunk hot) (k value)) →
        AllQ (MaskQuery count lane chunk hot)
          (Programs.hashM (scaleIndexOf lane chunk switch.val element block) (hot switch) >>= k) :=
    fun block _ k rest => (AllQ.bind (.query _ _ ⟨switch, element, block, rfl⟩ fun _ => .pure _)
      fun _ => .pure _).bind rest
  exact one 0 _ fun _ => one 1 _ fun _ => one 2 _ fun _ => .pure _

/-- A designated mask index of chunk 0 of `pointX` is at the designated switch. -/
theorem designated_switch (bits : BitInput) (switch : Fin (2 ^ chunkWidth chunkZero))
    (element : Fin pointElementCountX) (block : Fin 3)
    (designated : IsDesignated bits (maskIndex .pointX chunkZero switch.val element block)) :
    switch = designatedSwitch bits := by
  obtain ⟨digit, collector, block', same⟩ := designated
  exact (maskIndex_injective .pointX chunkZero (chunkWidth chunkZero) (chunkWidth_le chunkZero)
    (by unfold pointElementCountX elementCountX; omega) same).1.symm

/-! ### The `pointX` fold and masks -/

/-- The cleartext value of chunk 0 of `x`. -/
def chunkZeroValue (bits : BitInput) : Nat :=
  (chunkValue (Pipeline.coordBits bits .x) chunkZero).toNat

/-- The halves of the inactive level-1 fold gate of chunk 0 of a lane. -/
def foldIndex (lane : Lane) (bits : BitInput) (half : Bool) : FixedIndex :=
  hotIndexNat lane chunkZero 1 (inactiveEntry (chunkZeroValue bits)) half

theorem foldIndex_indexAt (lane : Lane) (bits : BitInput) (half : Bool) :
    IndexAt lane chunkZero (foldIndex lane bits half) :=
  hotIndexNat_indexAt _ _ _ _ _

theorem foldIndex_ne (lane : Lane) (bits : BitInput) :
    foldIndex lane bits false ≠ foldIndex lane bits true := by
  simp [foldIndex, hotIndexNat]

theorem foldIndex_ne_mask {count : Nat} (lane lane' : Lane) (bits : BitInput) (half : Bool)
    (switch : Nat) (element : Fin count) (block : Fin 3) :
    foldIndex lane bits half ≠ maskIndex lane' chunkZero switch element block := by
  simp [foldIndex, hotIndexNat, maskIndex, scaleIndexOf, scaleIndexNat]

/-- The level-1 label of chunk 0 of a lane: `join 0 xor` the bit-0 label. -/
def chunkLabel (joins : Vector Block foldStepCount) (labels : Fin coordinateBitCount → Block) :
    Block :=
  joinAt (hotSlice joins chunkZero) 0 ^^^ labelAt (chunkLabels labels chunkZero) 0

/-- The one-hot labels of chunk 0 of a lane, as a function of the fold material. -/
def chunkHot (bits : BitInput) (joins : Vector Block foldStepCount)
    (labels : Fin coordinateBitCount → Block) (material : Block) : Fin (2 ^ 2) → Block :=
  foldLabels (chunkZeroValue bits) (labelAt (chunkLabels labels chunkZero))
    (joinAt (hotSlice joins chunkZero)) material

/-- The mask indices of chunk 0 that a stage-1 hit can make the run read from the cache: every
inactive switch, element, block, not designated. -/
def MaskHitSite (bits : BitInput) (lane : Lane) {count : Nat}
    (site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3) : Prop :=
  site.1 ≠ chunkOf (Pipeline.coordBits bits .x) chunkZero ∧
    ¬ IsDesignated bits (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)

open Classical in
/-- The stage-1 entries at the mask indices of chunk 0 of a lane. -/
def maskCharge (stage : LState) (bits : BitInput) (lane : Lane) (count : Nat) : ℝ≥0∞ :=
  ∑ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3,
    if MaskHitSite bits lane site then
      ((stage.fixed (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)).used : ℝ≥0∞)
    else 0

/-- The stage-1 entries at the designated indices. -/
def slotCharge (stage : LState) (bits : BitInput) : ℝ≥0∞ :=
  ∑ slot : Slot, ((stage.fixed (slotIndex bits slot)).used : ℝ≥0∞)

open Classical in
/-- Some chunk-0 label hits a mask index's stage-1 domain. -/
def maskHit (stage : LState) (bits : BitInput) (lane : Lane) (count : Nat)
    (hot : Fin (2 ^ chunkWidth chunkZero) → Block) : ℝ≥0∞ :=
  if ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3, MaskHitSite bits lane site ∧
      (stage.fixed (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)).knownInput
        (hot site.1).toFin then 1 else 0

/-- **The mask hit, summed over the fresh fold answer, is at most the mask entries.** -/
theorem maskHit_sum_le (stage : LState) (bits : BitInput) (lane : Lane) (count : Nat)
    (joins : Vector Block foldStepCount) (labels : Fin coordinateBitCount → Block)
    (first : Block) :
    ∑' a, maskHit stage bits lane count (chunkHot bits joins labels (first ^^^ a)) ≤
      maskCharge stage bits lane count := by
  classical
  unfold maskHit maskCharge
  calc ∑' a, (if ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3,
          MaskHitSite bits lane site ∧
            (stage.fixed (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)).knownInput
              (chunkHot bits joins labels (first ^^^ a) site.1).toFin then (1 : ℝ≥0∞) else 0)
      ≤ ∑' a, ∑ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3,
          (if MaskHitSite bits lane site ∧
            (stage.fixed (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)).knownInput
              (chunkHot bits joins labels (first ^^^ a) site.1).toFin then (1 : ℝ≥0∞) else 0) :=
        ENNReal.tsum_le_tsum fun a => indicator_exists_le _
    _ = ∑ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3, ∑' a,
          (if MaskHitSite bits lane site ∧
            (stage.fixed (maskIndex lane chunkZero site.1.val site.2.1 site.2.2)).knownInput
              (chunkHot bits joins labels (first ^^^ a) site.1).toFin then (1 : ℝ≥0∞) else 0) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ _ := by
        refine Finset.sum_le_sum fun site _ => ?_
        split
        · rename_i hitSite
          simp only [hitSite, true_and]
          have shift : ∀ a, chunkHot bits joins labels (first ^^^ a) site.1 =
              (chunkHot bits joins labels 0 site.1 ^^^ first) ^^^ a := by
            intro a
            exact (foldLabels_linear _ _ _ (first ^^^ a) site.1).trans (BitVec.xor_assoc _ _ _).symm
          simp only [shift]
          exact (sum_knownInput_xor _ _).le
        · simp only [show ¬ MaskHitSite bits lane site from by assumption, false_and, if_false,
            tsum_zero, le_refl]

theorem slotInput_sum (stage : LState) (bits : BitInput) (slot : Slot) (base : Block) :
    ∑' a, slotInput stage bits (base ^^^ a) slot = (stage.fixed (slotIndex bits slot)).used :=
  sum_knownInput_xor _ _

theorem slotOutput_sum (stage : LState) (bits : BitInput) (slot : Slot) (base : Block)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    ∑' a, slotOutput stage bits (base ^^^ a) slot blocks =
      (stage.fixed (slotIndex bits slot)).used := by
  unfold slotOutput
  have shift : ∀ a, limbAt slot.2.2 (blocks (slot.1, slot.2.1)) ^^^ (base ^^^ a) =
      (limbAt slot.2.2 (blocks (slot.1, slot.2.1)) ^^^ base) ^^^ a := fun a =>
    (BitVec.xor_assoc _ _ _).symm
  simp only [shift]
  exact sum_knownOutput_xor _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
