/-
**Phase 3, P4b — (d) the key-averaged failure bound, and the restated `AbortBound.perQuery`.**

Per tape and per key the installation of `I^U` fails with mass at most (`opening_bound`)

  `1[W_c ∈ dom(i₁ᶜ)] + κ_c·M_c + E_pads[1[W ∈ dom(i₁)]] + κ_p·(M_p + 2·D)`,

`κ = 1/(2^128 − n(i₁))`, `M` the stage-1 entries at the chunk-0 mask indices, `D` those at the
designated indices. Averaged over the key, the two fold hits cost `n(i₁ᶜ)/2^128` and
`n(i₁)/2^128` (`key_sum_le`, (c)). Every coefficient is at most `1/(2^128 − q)`, twice for `D`,
and the five index families are disjoint abort sites (`families_le_abortUse`), so

  `Σ_key failMass ≤ 2/(2^128 − q) · Σ_{abort sites} n = abortQueryCharge q · abortUse`.

**`keyAveragedFailBound : KeyAveragedFailBound`** and, with `abortBound_perQuery'_of`,
**`abortBound_perQuery' : AbortPerQuery' openedHybrid idealUniformHybrid`**.
-/

import Proof.Privacy.Phase3.Lazy.KeyAverage
import Proof.Privacy.Phase3.Lazy.AbortPerQuery

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (openedHybrid)
open scoped ENNReal

noncomputable section

/-- The wire adapter restores the selected labels. -/
theorem restore_selectedLabels (input : AffineInput) (mac : InputMac) :
    Lamport.restore input (Lamport.selectedLabels mac) = ⟨BitInput.ofAffine input, mac⟩ := by
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine input))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

theorem zero_xor_block (a : Block) : (0 : Block) ^^^ a = a := BitVec.zero_xor

section Assembly

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]
  (stage : LState) (table : Public) (bits : BitInput) (tape : Tape)

open Classical in
/-- **(c) The fold hits of both lanes, averaged over the key.** -/
theorem key_sum_le :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
            (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅)
          (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
        (stage.fixed (foldIndex .pointX bits true)).used) := by
  rw [key_resample]
  set bit := bits.xBits.getLsb ⟨0, by decide⟩
  have inner : ∀ key : InputMacKey,
      ∑' pair, PMF.uniformOfFintype BitAdaptor.Key pair *
        ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table ((setX0 key pair).encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits ((setX0 key pair).encode bits) (curveMasks bits tape)) stage
              (fun _ => none) ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table ((setX0 key pair).encode bits) q.1).toFin then 1 else 0)) ≤
        ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
          (stage.fixed (foldIndex .pointX bits true)).used) := by
    intro key
    simp only [curveLabel_eq, pointLabel_eq, encode_setX0_zero, curveRest_setX0]
    set μ := runRefillT bits (fun cell => PMF.pure (tape cell))
      (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅
    simp only [mul_add]
    rw [ENNReal.tsum_add]
    refine add_le_add ?_ ?_
    · have mapped := tsum_map_mul (PMF.uniformOfFintype BitAdaptor.Key)
        (fun pair => BitAdaptor.encode pair bit)
        (fun a : Block => if (stage.fixed (foldIndex .curveX bits true)).knownInput a.toFin
          then (1 : ℝ≥0∞) else 0)
      rw [uniform_encode] at mapped
      rw [← mapped]
      have shifted := uniform_known_sum (stage.fixed (foldIndex .curveX bits true)) 0
      simp only [zero_xor_block] at shifted
      exact shifted.le
    · rw [tsum_congr fun pair => (expectO_mul_left μ _ _).symm, ← expectO_tsum]
      refine (expectO_mono μ fun q => ?_).trans (expectO_const_le μ _)
      have mapped := tsum_map_mul (PMF.uniformOfFintype BitAdaptor.Key)
        (fun pair => BitAdaptor.encode pair bit)
        (fun a : Block => if (stage.fixed (foldIndex .pointX bits true)).knownInput
          ((q.1 .x ⟨0, by decide⟩).1 ^^^ a).toFin then (1 : ℝ≥0∞) else 0)
      rw [uniform_encode] at mapped
      rw [← mapped]
      exact (uniform_known_sum _ _).le
  calc _ ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((stage.fixed (foldIndex .curveX bits true)).used +
            (stage.fixed (foldIndex .pointX bits true)).used)) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (inner key) zero_le
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The five index families are disjoint abort sites -/

/-- The stage-1 entries at one index, as an extended real. -/
abbrev entries (index : FixedIndex) : ℝ≥0∞ := ((stage.fixed index).used : ℝ≥0∞)

/-- The chunk-0 mask indices of a lane, as an embedding of the sites. -/
def maskEmbedding (lane : Lane) (count : Nat) (countLe : count ≤ elementCountX) :
    (Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3) ↪ FixedIndex :=
  ⟨fun site => maskIndex lane chunkZero site.1.val site.2.1 site.2.2, fun first second same => by
    obtain ⟨switch, element, block⟩ := maskIndex_injective lane chunkZero (chunkWidth chunkZero)
      (chunkWidth_le chunkZero) countLe same
    exact Prod.ext switch (Prod.ext element block)⟩

open Classical in
/-- The chunk-0 mask indices a hit can make the run read, as a finset. -/
def maskFamily (lane : Lane) (count : Nat) (countLe : count ≤ elementCountX) :
    Finset FixedIndex :=
  (Finset.univ.filter (MaskHitSite bits lane (count := count))).map
    (maskEmbedding lane count countLe)

theorem maskEmbedding_apply (lane : Lane) (count : Nat) (countLe : count ≤ elementCountX)
    (site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3) :
    maskEmbedding lane count countLe site = maskIndex lane chunkZero site.1.val site.2.1 site.2.2 :=
  rfl

/-- The designated indices, as an embedding of the slots. -/
def slotEmbedding : Slot ↪ FixedIndex :=
  ⟨slotIndex bits, fun _ _ same => designatedIndex_injective bits same⟩

theorem slotEmbedding_apply (slot : Slot) : slotEmbedding bits slot = slotIndex bits slot := rfl

/-- The designated indices, as a finset. -/
def slotFamily : Finset FixedIndex := Finset.univ.map (slotEmbedding bits)

open Classical in
theorem maskCharge_eq (lane : Lane) (count : Nat) (countLe : count ≤ elementCountX) :
    maskCharge stage bits lane count =
      ∑ index ∈ maskFamily bits lane count countLe, entries stage index := by
  unfold maskCharge maskFamily
  rw [Finset.sum_map, Finset.sum_filter]
  simp only [maskEmbedding_apply]

theorem slotCharge_eq : slotCharge stage bits = ∑ index ∈ slotFamily bits, entries stage index := by
  unfold slotCharge slotFamily
  rw [Finset.sum_map]
  simp only [slotEmbedding_apply]

theorem isAbort_fold (lane : Lane) (inLanes : lane = .pointX ∨ lane = .curveX) (bits : BitInput) :
    IsAbortIndex (foldIndex lane bits true) := by
  refine ⟨inLanes, rfl, ?_⟩
  simp [chunkBits]

theorem isAbort_mask {count : Nat} (lane : Lane) (inLanes : lane = .pointX ∨ lane = .curveX)
    (switch : Nat) (element : Fin count) (block : Fin 3) :
    IsAbortIndex (maskIndex lane chunkZero switch element block) :=
  ⟨inLanes, rfl⟩

theorem mask_ne_mask {count count' : Nat} (switch switch' : Nat) (element : Fin count)
    (element' : Fin count') (block block' : Fin 3) :
    maskIndex .curveX chunkZero switch element block ≠
      maskIndex .pointX chunkZero switch' element' block' := by
  simp [maskIndex, scaleIndexOf, scaleIndexNat]

theorem mask_ne_slot {count : Nat} (switch : Nat) (element : Fin count) (block : Fin 3)
    (slot : Slot) : maskIndex .curveX chunkZero switch element block ≠ slotIndex bits slot := by
  simp [maskIndex, scaleIndexOf, scaleIndexNat, slotIndex, designatedIndex]

theorem fold_ne_slot (lane : Lane) (half : Bool) (slot : Slot) :
    foldIndex lane bits half ≠ slotIndex bits slot := by
  simp [foldIndex, hotIndexNat, slotIndex, designatedIndex, scaleIndexOf, scaleIndexNat]

open Classical in
theorem mem_maskFamily {lane : Lane} {count : Nat} {countLe : count ≤ elementCountX}
    {index : FixedIndex} (member : index ∈ maskFamily bits lane count countLe) :
    ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin count × Fin 3, MaskHitSite bits lane site ∧
      maskIndex lane chunkZero site.1.val site.2.1 site.2.2 = index := by
  unfold maskFamily at member
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    maskEmbedding_apply] at member
  exact member

theorem mem_slotFamily {index : FixedIndex} (member : index ∈ slotFamily bits) :
    ∃ slot, slotIndex bits slot = index := by
  unfold slotFamily at member
  simp only [Finset.mem_map, Finset.mem_univ, true_and, slotEmbedding_apply] at member
  exact member

/-- The abort sites, as a finset. -/
noncomputable def abortSet : Finset FixedIndex := by
  classical
  exact Finset.univ.filter IsAbortIndex

theorem mem_abortSet {index : FixedIndex} : index ∈ abortSet ↔ IsAbortIndex index := by
  classical
  unfold abortSet
  simp

theorem abortUse_eq : (abortUse stage : ℝ≥0∞) = ∑ index ∈ abortSet, entries stage index := by
  unfold abortUse indexUse
  rw [Nat.cast_sum, Finset.sum_subtype (p := IsAbortIndex) abortSet (fun index => mem_abortSet)
    (fun index => entries stage index)]

theorem curveCountLe : curveElementCountX ≤ elementCountX := by
  unfold curveElementCountX elementCountX; omega

theorem pointCountLe : pointElementCountX ≤ elementCountX := by
  unfold pointElementCountX elementCountX; omega

/-- The `curveX` chunk-0 mask family. -/
def curveFamily : Finset FixedIndex := maskFamily bits .curveX curveElementCountX curveCountLe

/-- The `pointX` chunk-0 mask family. -/
def pointFamily : Finset FixedIndex := maskFamily bits .pointX pointElementCountX pointCountLe

theorem mem_curveFamily {index : FixedIndex} (member : index ∈ curveFamily bits) :
    ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin curveElementCountX × Fin 3,
      maskIndex .curveX chunkZero site.1.val site.2.1 site.2.2 = index := by
  obtain ⟨site, _, same⟩ := mem_maskFamily bits member
  exact ⟨site, same⟩

set_option maxRecDepth 20000 in
theorem mem_pointFamily {index : FixedIndex} (member : index ∈ pointFamily bits) :
    ∃ site : Fin (2 ^ chunkWidth chunkZero) × Fin pointElementCountX × Fin 3,
      MaskHitSite bits .pointX site ∧
        maskIndex .pointX chunkZero site.1.val site.2.1 site.2.2 = index :=
  mem_maskFamily bits member

set_option maxRecDepth 20000 in
/-- **The five families are disjoint abort sites**: their entries sum to at most `abortUse`. -/
theorem families_le_abortUse :
    entries stage (foldIndex .curveX bits true) + entries stage (foldIndex .pointX bits true) +
        maskCharge stage bits .curveX curveElementCountX +
        maskCharge stage bits .pointX pointElementCountX + slotCharge stage bits ≤
      (abortUse stage : ℝ≥0∞) := by
  rw [maskCharge_eq stage bits .curveX curveElementCountX curveCountLe,
    maskCharge_eq stage bits .pointX pointElementCountX pointCountLe, slotCharge_eq]
  have mem3 := fun index (member : index ∈ curveFamily bits) => mem_curveFamily bits member
  have mem4 := fun index (member : index ∈ pointFamily bits) => mem_pointFamily bits member
  have mem5 := fun index (member : index ∈ slotFamily bits) => mem_slotFamily bits member
  change entries stage (foldIndex .curveX bits true) + entries stage (foldIndex .pointX bits true) +
      ∑ index ∈ curveFamily bits, entries stage index +
      ∑ index ∈ pointFamily bits, entries stage index +
      ∑ index ∈ slotFamily bits, entries stage index ≤ _
  set F1 : Finset FixedIndex := {foldIndex .curveX bits true}
  set F2 : Finset FixedIndex := {foldIndex .pointX bits true}
  set F3 := curveFamily bits
  set F4 := pointFamily bits
  set F5 := slotFamily bits
  have d12 : Disjoint F1 F2 := by
    simp only [F1, F2, Finset.disjoint_singleton]
    simp [foldIndex, hotIndexNat]
  have d3 : Disjoint (F1 ∪ F2) F3 := by
    refine Finset.disjoint_left.mpr fun index left right => ?_
    obtain ⟨site, rfl⟩ := mem3 index right
    rcases Finset.mem_union.mp left with one | two
    · exact foldIndex_ne_mask .curveX .curveX bits true _ _ _ (Finset.mem_singleton.mp one).symm
    · exact foldIndex_ne_mask .pointX .curveX bits true _ _ _ (Finset.mem_singleton.mp two).symm
  have d4 : Disjoint (F1 ∪ F2 ∪ F3) F4 := by
    refine Finset.disjoint_left.mpr fun index left right => ?_
    obtain ⟨site, _, rfl⟩ := mem4 index right
    rcases Finset.mem_union.mp left with left | three
    · rcases Finset.mem_union.mp left with one | two
      · exact foldIndex_ne_mask .curveX .pointX bits true _ _ _ (Finset.mem_singleton.mp one).symm
      · exact foldIndex_ne_mask .pointX .pointX bits true _ _ _ (Finset.mem_singleton.mp two).symm
    · obtain ⟨site', same⟩ := mem3 _ three
      exact mask_ne_mask _ _ _ _ _ _ same
  have d5 : Disjoint (F1 ∪ F2 ∪ F3 ∪ F4) F5 := by
    refine Finset.disjoint_left.mpr fun index left right => ?_
    obtain ⟨slot, rfl⟩ := mem5 index right
    rcases Finset.mem_union.mp left with left | four
    · rcases Finset.mem_union.mp left with left | three
      · rcases Finset.mem_union.mp left with one | two
        · exact fold_ne_slot bits .curveX true slot (Finset.mem_singleton.mp one).symm
        · exact fold_ne_slot bits .pointX true slot (Finset.mem_singleton.mp two).symm
      · obtain ⟨site, same⟩ := mem3 _ three
        exact mask_ne_slot bits _ _ _ slot same
    · obtain ⟨site, hitSite, same⟩ := mem4 _ four
      exact hitSite.2 (same ▸ ⟨slot.1, slot.2.1, slot.2.2, rfl⟩)
  have union : entries stage (foldIndex .curveX bits true) +
      entries stage (foldIndex .pointX bits true) + ∑ index ∈ F3, entries stage index +
      ∑ index ∈ F4, entries stage index + ∑ index ∈ F5, entries stage index =
      ∑ index ∈ F1 ∪ F2 ∪ F3 ∪ F4 ∪ F5, entries stage index := by
    rw [Finset.sum_union d5, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d12,
      Finset.sum_singleton, Finset.sum_singleton]
  rw [union]
  rw [abortUse_eq]
  refine Finset.sum_le_sum_of_subset fun index member => ?_
  refine mem_abortSet.mpr ?_
  rcases Finset.mem_union.mp member with left | five
  · rcases Finset.mem_union.mp left with left | four
    · rcases Finset.mem_union.mp left with left | three
      · rcases Finset.mem_union.mp left with one | two
        · rw [Finset.mem_singleton.mp one]
          exact isAbort_fold .curveX (Or.inr rfl) bits
        · rw [Finset.mem_singleton.mp two]
          exact isAbort_fold .pointX (Or.inl rfl) bits
      · obtain ⟨site, rfl⟩ := mem3 _ three
        exact isAbort_mask .curveX (Or.inr rfl) _ _ _
    · obtain ⟨site, _, rfl⟩ := mem4 _ four
      exact isAbort_mask .pointX (Or.inl rfl) _ _ _
  · obtain ⟨slot, rfl⟩ := mem5 _ five
    exact candidateIndex_isAbort (slot.1, slot.2.1, slot.2.2, designatedSwitch bits)

/-! ### The charges -/

theorem charge_eq (queries : ℕ) (small : queries < 2 ^ 100) :
    ENNReal.ofReal (abortQueryCharge queries) =
      2 * (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ := by
  have le : queries ≤ 2 ^ 128 := by omega
  have cast : ((2 ^ 128 - queries : ℕ) : ℝ) = 2 ^ 128 - (queries : ℝ) := by
    rw [Nat.cast_sub le]
    push_cast
    ring
  have pos : (0 : ℝ) < 2 ^ 128 - queries := lt_of_lt_of_le (by positivity) (room_le queries small)
  unfold abortQueryCharge abortInputCharge abortOutputCharge
  rw [← two_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, one_div,
    ENNReal.ofReal_inv_of_pos pos, ← cast, ENNReal.ofReal_natCast]

theorem freshCharge_le_kappa (state : SparsePermutation (2 ^ 128)) (queries : ℕ)
    (used : state.used ≤ queries) :
    freshCharge state ≤ (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ :=
  ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.sub_le_sub_left used _))

theorem inv_two_pow_le_kappa (queries : ℕ) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹ :=
  ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.sub_le _ _))

/-- **The per-tape bound, charged.** -/
theorem bound_le_charge (queries : ℕ) (small : queries < 2 ^ 100)
    (usedLe : ∀ index, (stage.fixed index).used ≤ queries) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries stage (foldIndex .curveX bits true) +
        entries stage (foldIndex .pointX bits true)) +
      (freshCharge (stage.fixed (foldIndex .curveX bits true)) *
          maskCharge stage bits .curveX curveElementCountX +
        freshCharge (stage.fixed (foldIndex .pointX bits true)) *
          (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)) ≤
      ENNReal.ofReal (abortQueryCharge queries) * (abortUse stage : ℝ≥0∞) := by
  set κ := (((2 ^ 128 - queries : ℕ) : ℝ≥0∞))⁻¹
  rw [charge_eq queries small]
  calc _ ≤ κ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true)) +
        (κ * maskCharge stage bits .curveX curveElementCountX +
          κ * (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)) :=
        add_le_add (mul_le_mul_of_nonneg_right (inv_two_pow_le_kappa queries) zero_le)
          (add_le_add (mul_le_mul_of_nonneg_right (freshCharge_le_kappa _ _ (usedLe _)) zero_le)
            (mul_le_mul_of_nonneg_right (freshCharge_le_kappa _ _ (usedLe _)) zero_le))
    _ ≤ 2 * κ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true) +
          maskCharge stage bits .curveX curveElementCountX +
          maskCharge stage bits .pointX pointElementCountX + slotCharge stage bits) := by
        have expand : 2 * κ * (entries stage (foldIndex .curveX bits true) +
            entries stage (foldIndex .pointX bits true) +
            maskCharge stage bits .curveX curveElementCountX +
            maskCharge stage bits .pointX pointElementCountX + slotCharge stage bits) =
            (κ * (entries stage (foldIndex .curveX bits true) +
              entries stage (foldIndex .pointX bits true)) +
            (κ * maskCharge stage bits .curveX curveElementCountX +
              κ * (maskCharge stage bits .pointX pointElementCountX +
                2 * slotCharge stage bits))) +
            κ * (entries stage (foldIndex .curveX bits true) +
              entries stage (foldIndex .pointX bits true) +
              maskCharge stage bits .curveX curveElementCountX +
              maskCharge stage bits .pointX pointElementCountX) := by ring
        rw [expand]
        exact le_self_add
    _ ≤ 2 * κ * (abortUse stage : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left (families_le_abortUse stage bits) zero_le

end Assembly

section Final

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **The per-tape key average.** -/
theorem perTape_le (stage : LState) (table : Public) (input : AffineInput) (target : Point)
    (bits : BitInput) (tape : Tape) :
    ∑' key, PMF.uniformOfFintype InputMacKey key *
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) *
          maskCharge stage bits .curveX curveElementCountX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅)
          (fun q => pointBound stage table bits (key.encode bits) q.1)) ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries stage (foldIndex .curveX bits true) +
          entries stage (foldIndex .pointX bits true)) +
        (freshCharge (stage.fixed (foldIndex .curveX bits true)) *
            maskCharge stage bits .curveX curveElementCountX +
          freshCharge (stage.fixed (foldIndex .pointX bits true)) *
            (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)) := by
  classical
  set C := freshCharge (stage.fixed (foldIndex .curveX bits true)) *
      maskCharge stage bits .curveX curveElementCountX +
    freshCharge (stage.fixed (foldIndex .pointX bits true)) *
      (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)
  have each : ∀ key : InputMacKey,
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        freshCharge (stage.fixed (foldIndex .curveX bits true)) *
          maskCharge stage bits .curveX curveElementCountX +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
          (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅)
          (fun q => pointBound stage table bits (key.encode bits) q.1)) ≤
      ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then 1 else 0) +
        expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
            (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅)
          (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C := by
    intro key
    set μ := runRefillT bits (fun cell => PMF.pure (tape cell))
      (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage (fun _ => none) ∅
    unfold pointBound
    rw [expectO_add]
    have constant := expectO_const_le μ (freshCharge (stage.fixed (foldIndex .pointX bits true)) *
      (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits))
    calc _ ≤ (if (stage.fixed (foldIndex .curveX bits true)).knownInput
          (curveLabel table (key.encode bits)).toFin then (1 : ℝ≥0∞) else 0) +
          freshCharge (stage.fixed (foldIndex .curveX bits true)) *
            maskCharge stage bits .curveX curveElementCountX +
          (expectO μ (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
            (pointLabel table (key.encode bits) q.1).toFin then 1 else 0) +
          freshCharge (stage.fixed (foldIndex .pointX bits true)) *
            (maskCharge stage bits .pointX pointElementCountX + 2 * slotCharge stage bits)) :=
          add_le_add le_rfl (add_le_add le_rfl constant)
      _ = _ := by ring
  calc _ ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
        (((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table (key.encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage
              (fun _ => none) ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (each key) zero_le
    _ = ∑' key, PMF.uniformOfFintype InputMacKey key *
        ((if (stage.fixed (foldIndex .curveX bits true)).knownInput
            (curveLabel table (key.encode bits)).toFin then 1 else 0) +
          expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
              (curveRest table bits (key.encode bits) (curveMasks bits tape)) stage
              (fun _ => none) ∅)
            (fun q => if (stage.fixed (foldIndex .pointX bits true)).knownInput
              (pointLabel table (key.encode bits) q.1).toFin then 1 else 0)) + C := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := add_le_add (key_sum_le stage table bits tape) le_rfl

/-- **(d) The key-averaged failure bound.** -/
theorem keyAveragedFailBound : KeyAveragedFailBound := by
  intro _ _ _ _ source input target oracle queries small usedLe
  set bits := BitInput.ofAffine input
  set table := source.publicValue
  set bound := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * (entries oracle (foldIndex .curveX bits true) +
      entries oracle (foldIndex .pointX bits true)) +
    (freshCharge (oracle.fixed (foldIndex .curveX bits true)) *
        maskCharge oracle bits .curveX curveElementCountX +
      freshCharge (oracle.fixed (foldIndex .pointX bits true)) *
        (maskCharge oracle bits .pointX pointElementCountX + 2 * slotCharge oracle bits))
  set A : Tape → InputMac → ℝ≥0∞ := fun tape mac =>
    (if (oracle.fixed (foldIndex .curveX bits true)).knownInput
        (curveLabel table mac).toFin then 1 else 0) +
      freshCharge (oracle.fixed (foldIndex .curveX bits true)) *
        maskCharge oracle bits .curveX curveElementCountX +
      expectO (runRefillT bits (fun cell => PMF.pure (tape cell))
        (curveRest table bits mac (curveMasks bits tape)) oracle (fun _ => none) ∅)
        (fun q => pointBound oracle table bits mac q.1)
  have perKey : ∀ key : InputMacKey,
      failMass table input (Lamport.selectedLabels (key.encode bits)) target oracle ≤
        ∑' tape, uniformMaskTape tape * A tape (key.encode bits) := by
    intro key
    have base := failMass_le_runs oracle table input target
      (Lamport.selectedLabels (key.encode bits))
    rw [restore_selectedLabels] at base
    exact base.trans (ENNReal.tsum_le_tsum fun tape => mul_le_mul_of_nonneg_left
      (opening_bound oracle table input target bits (key.encode bits) tape) zero_le)
  calc ∑' key, PMF.uniformOfFintype InputMacKey key *
        failMass table input (Lamport.selectedLabels (key.encode bits)) target oracle
      ≤ ∑' key, PMF.uniformOfFintype InputMacKey key *
          ∑' tape, uniformMaskTape tape * A tape (key.encode bits) :=
        ENNReal.tsum_le_tsum fun key => mul_le_mul_of_nonneg_left (perKey key) zero_le
    _ = ∑' tape, uniformMaskTape tape *
          ∑' key, PMF.uniformOfFintype InputMacKey key * A tape (key.encode bits) := by
        simp only [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun tape => tsum_congr fun key => by ring
    _ ≤ ∑' tape, uniformMaskTape tape * bound :=
        ENNReal.tsum_le_tsum fun tape => mul_le_mul_of_nonneg_left
          (perTape_le oracle table input target bits tape) zero_le
    _ = bound := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ENNReal.ofReal (abortQueryCharge queries) * (abortUse oracle : ℝ≥0∞) :=
        bound_le_charge oracle bits queries small usedLe

/-- **The restated `AbortBound.perQuery`, proved**: `H → I^U` costs `abortQueryCharge q₁` per
stage-1 entry at an abort site. -/
theorem abortBound_perQuery' : AbortPerQuery' openedHybrid idealUniformHybrid :=
  abortBound_perQuery'_of keyAveragedFailBound

end Final

end

end Kriterion.ArgoMAC.Phase3.Lazy
