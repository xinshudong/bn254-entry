/-
**Phase 3, P1m — (B1): the hash conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`.**

On the curve the only hash key of `M'`'s private state is the bridge input `t` of the opening
(`opening_hash_key`, `shadow_hash_key`: the shadow re-asks the stored prefix only). The opening
consumes system A's masks from the tape, so `t` is a function of the tape's **masks** alone
(`tOf_opening`: `lane_eval_eq` with the tape's Davies–Meyer values, `laneValue_tapeH`), and it
is affine in the `x7` mask of chunk `0` at the switch `α₀ ⊕ 1` with the nonzero coefficient
`ι(α₀ ⊕ 1) − ι(α₀)` (`curveMap_shift`). Under `uniformMaskTape` the masks are uniform, so
`Pr[t = k] ≤ 1/p` (`uniform_affine_le`), and `1/p ≤ 4/2^128`. Off the curve the designed shadow asks
no hash question (mass `0`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsOpening

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests activeSwitch designatedSwitch chunkZero)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request AllQ EncAt FixedAt IndexAt
  queriesAlong queriesAlong_bind cellOf uniformMaskTape masksOf_surjective evalLaneM_allQ
  cellOf_maskIndex maskIndex)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The installation keeps the hash part -/

theorem programAllSkip_hash :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (state : LState),
      (programAllSkip requests state).hash = state.hash := by
  intro requests
  induction requests with
  | nil => exact fun state => rfl
  | cons request rest ih =>
    intro state
    obtain ⟨index, input, output⟩ := request
    cases input with
    | none => exact ih state
    | some input =>
      show (programAllSkip rest
        ((LazyOracle.program (.fixedForward index input) (output ^^^ input) state).getD state)).hash
          = state.hash
      rw [ih]
      cases success : LazyOracle.program (.fixedForward index input) (output ^^^ input) state with
      | none => rfl
      | some updated => exact program_hash index input _ state updated success

/-! ### The free fold, linearly -/

section Linear

open Kriterion.ArgoMAC.PlanB in
/-- **The free fold is `ι(α)·join + Σ_{s ≠ α} (ι(s) − ι(α))·mask_s`.** -/
theorem evalScaleOf_linear {count : ℕ} (w : ℕ) (masks : Fin (2 ^ w) → Fin count → BaseField)
    (alpha : Fin (2 ^ w)) (join : Fin count → BaseField) (el : Fin count) :
    Programs.evalScaleOf w masks alpha join el =
      iota _ alpha * join el +
        ∑ s ∈ Finset.univ.erase alpha, (iota _ s - iota _ alpha) * masks s el := by
  unfold Programs.evalScaleOf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), if_pos rfl]
  have rest : ∑ s ∈ Finset.univ.erase alpha, iota _ s *
      (if s = alpha then join el - ∑ other ∈ Finset.univ.erase alpha, masks other el
        else masks s el) =
      ∑ s ∈ Finset.univ.erase alpha, iota _ s * masks s el :=
    Finset.sum_congr rfl fun s member => by rw [if_neg (Finset.ne_of_mem_erase member)]
  rw [rest, mul_sub, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

end Linear

/-! ### The lanes' values from the masks -/

section Masks

/-- The tape's Davies–Meyer value at a mask site (`0` elsewhere). -/
def tapeH (tape : Tape) (index : FixedIndex) : Block :=
  ((cellOf index).map tape).getD 0

theorem tapeH_of_cell {tape : Tape} {index : FixedIndex} {cell : Kriterion.ArgoMAC.Phase3.Lazy.Cell}
    (found : cellOf index = some cell) : tapeH tape index = tape cell := by
  rw [tapeH, found]
  rfl

/-- The masks of chunk `c` of a lane, from a mask family. -/
def chunkMasks (m : MaskSite → BaseField) (lane : Lane) (count : ℕ)
    (countLe : count ≤ laneCount lane) (c : Fin chunkCount) (alpha : Fin (2 ^ chunkWidth c)) :
    Fin (2 ^ chunkWidth c) → Fin count → BaseField :=
  fun switch el => if switch = alpha then 0 else
    m ⟨lane, c, switch, ⟨el.val, lt_of_lt_of_le el.isLt countLe⟩⟩

/-- **A lane's value from a mask family.** -/
def laneValueM (m : MaskSite → BaseField) (lane : Lane) (count : ℕ)
    (countLe : count ≤ laneCount lane) (scale : Fin chunkCount → Fin count → BaseField)
    (word : BitVec coordinateBitCount) : Fin count → BaseField :=
  fun el => ∑ c : Fin chunkCount, Programs.evalScaleOf (chunkWidth c)
    (chunkMasks m lane count countLe c (chunkOf word c)) (chunkOf word c) (scale c) el

/-- **With the tape's Davies–Meyer values, a lane's value is that of the tape's masks.** -/
theorem laneValue_tapeH (tape : Tape) (lane : Lane) (count : ℕ) (countLe : count ≤ laneCount lane)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount) :
    laneValue count lane scale word (tapeH tape) =
      laneValueM (masksOf tape) lane count countLe scale word := by
  have each : ∀ c : Fin chunkCount, maskValuesOf count lane (tapeH tape) c (chunkOf word c) =
      chunkMasks (masksOf tape) lane count countLe c (chunkOf word c) := by
    intro c
    funext switch el'
    unfold maskValuesOf chunkMasks
    by_cases active : switch = chunkOf word c
    · rw [if_pos active, if_pos active]
    · rw [if_neg active, if_neg active]
      have limb : ∀ b : Fin 3, tapeH tape (maskIndex lane c switch.val el' b) =
          tape (⟨lane, c, switch, ⟨el'.val, lt_of_lt_of_le el'.isLt countLe⟩⟩, b) := fun b =>
        tapeH_of_cell (cellOf_maskIndex lane c switch el' b countLe)
      rw [limb 0, limb 1, limb 2]
      rfl
  funext el
  unfold laneValue laneValueM
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [each c]

end Masks

/-! ### The bridge input as a function of the masks, and its shift -/

section Shift

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- The countLe facts of the curve lanes. -/
theorem curveXLe : curveElementCountX ≤ laneCount .curveX := le_rfl
theorem curveYLe : curveElementCountY ≤ laneCount .curveY := le_rfl

/-- **The bridge input of the opening, as a function of the masks.** -/
def curveMap (m : MaskSite → BaseField) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues
      (laneValueM m .curveX curveElementCountX curveXLe
        (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .x))
      (laneValueM m .curveY curveElementCountY curveYLe
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y)))

/-- The shifted site: `x7` of chunk `0` of `curveX`, at the switch `α₀ ⊕ 1`. -/
def starSite : MaskSite :=
  ⟨.curveX, chunkZero, designatedSwitch bits, ⟨2, by decide⟩⟩

/-- The shift of one mask. -/
def maskShift (δ : BaseField) : (MaskSite → BaseField) ≃ (MaskSite → BaseField) where
  toFun m := Function.update m (starSite bits) (m (starSite bits) + δ)
  invFun m := Function.update m (starSite bits) (m (starSite bits) - δ)
  left_inv m := by
    funext site
    by_cases same : site = starSite bits
    · subst same
      simp
    · simp [Function.update_of_ne same]
  right_inv m := by
    funext site
    by_cases same : site = starSite bits
    · subst same
      simp
    · simp [Function.update_of_ne same]

theorem chunkMasks_shift_other (δ : BaseField) (m : MaskSite → BaseField) (lane : Lane)
    (count : ℕ) (countLe : count ≤ laneCount lane) (c : Fin chunkCount)
    (alpha : Fin (2 ^ chunkWidth c)) (different : lane ≠ .curveX ∨ c ≠ chunkZero) :
    chunkMasks (maskShift bits δ m) lane count countLe c alpha =
      chunkMasks m lane count countLe c alpha := by
  funext switch el
  unfold chunkMasks
  split
  · rfl
  · show Function.update m (starSite bits) (m (starSite bits) + δ) _ = _
    rw [Function.update_of_ne]
    intro same
    unfold starSite at same
    rcases different with different | different
    · exact different (congrArg Sigma.fst same)
    · have := congrArg (fun site : MaskSite => site.2.1) same
      exact different this

/-- The coefficient of the shifted mask. -/
def shiftCoeff : BaseField :=
  iota _ (designatedSwitch bits) - iota _ (activeSwitch bits)

theorem shiftCoeff_ne : shiftCoeff bits ≠ 0 := by
  unfold shiftCoeff
  intro zero
  have same := sub_eq_zero.mp zero
  exact Kriterion.ArgoMAC.Phase3.Lazy.designatedSwitch_ne bits
    (iota_injective (Nat.pow_le_pow_right (by norm_num) (chunkWidth_le chunkZero)) same)

/-- **The `curveX` lane under the shift**: only the `x7` element moves, by `coeff · δ`. -/
theorem laneValueM_shift_curveX (δ : BaseField) (m : MaskSite → BaseField)
    (scale : Fin chunkCount → Fin curveElementCountX → BaseField) (el : Fin curveElementCountX) :
    laneValueM (maskShift bits δ m) .curveX curveElementCountX curveXLe scale
        (Pipeline.coordBits bits .x) el =
      laneValueM m .curveX curveElementCountX curveXLe scale (Pipeline.coordBits bits .x) el +
        (if el.val = 2 then shiftCoeff bits * δ else 0) := by
  unfold laneValueM
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ chunkZero),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ chunkZero)]
  have others : ∑ c ∈ Finset.univ.erase chunkZero, Programs.evalScaleOf (chunkWidth c)
      (chunkMasks (maskShift bits δ m) .curveX curveElementCountX curveXLe c
        (chunkOf (Pipeline.coordBits bits .x) c)) (chunkOf (Pipeline.coordBits bits .x) c)
        (scale c) el =
      ∑ c ∈ Finset.univ.erase chunkZero, Programs.evalScaleOf (chunkWidth c)
        (chunkMasks m .curveX curveElementCountX curveXLe c
          (chunkOf (Pipeline.coordBits bits .x) c)) (chunkOf (Pipeline.coordBits bits .x) c)
          (scale c) el :=
    Finset.sum_congr rfl fun c member => by
      rw [chunkMasks_shift_other bits δ m .curveX _ curveXLe c _
        (Or.inr (Finset.ne_of_mem_erase member))]
  rw [others, evalScaleOf_linear, evalScaleOf_linear]
  have masksEq : ∀ s : Fin (2 ^ chunkWidth chunkZero),
      chunkMasks (maskShift bits δ m) .curveX curveElementCountX curveXLe chunkZero
          (activeSwitch bits) s el =
        chunkMasks m .curveX curveElementCountX curveXLe chunkZero (activeSwitch bits) s el +
          (if s = designatedSwitch bits ∧ el.val = 2 then δ else 0) := by
    intro s
    unfold chunkMasks
    by_cases active : s = activeSwitch bits
    · rw [if_pos active, if_pos active, if_neg]
      · simp
      · rintro ⟨same, _⟩
        exact Kriterion.ArgoMAC.Phase3.Lazy.designatedSwitch_ne bits (same.symm.trans active)
    · rw [if_neg active, if_neg active]
      show Function.update m (starSite bits) (m (starSite bits) + δ) _ = _
      by_cases hit : s = designatedSwitch bits ∧ el.val = 2
      · obtain ⟨rfl, two⟩ := hit
        have siteEq : (⟨.curveX, chunkZero, designatedSwitch bits,
            ⟨el.val, lt_of_lt_of_le el.isLt curveXLe⟩⟩ : MaskSite) = starSite bits := by
          unfold starSite
          simp only [two]
        rw [siteEq, Function.update_self, if_pos ⟨rfl, two⟩]
      · rw [if_neg hit, add_zero, Function.update_of_ne]
        intro same
        apply hit
        unfold starSite at same
        have inner := eq_of_heq (Sigma.mk.inj_iff.mp same).2
        have pair := eq_of_heq (Sigma.mk.inj_iff.mp inner).2
        have switchEq := congrArg (fun p : Fin (2 ^ chunkWidth chunkZero) × Fin (laneCount .curveX) =>
          p.1) pair
        have elEq := congrArg (fun p : Fin (2 ^ chunkWidth chunkZero) × Fin (laneCount .curveX) =>
          p.2.val) pair
        exact ⟨switchEq, elEq⟩
  have alphaEq : chunkOf (Pipeline.coordBits bits .x) chunkZero = activeSwitch bits := rfl
  rw [alphaEq]
  simp only [masksEq, mul_add, Finset.sum_add_distrib]
  have single : ∑ s ∈ Finset.univ.erase (activeSwitch bits),
      (iota _ s - iota _ (activeSwitch bits)) *
        (if s = designatedSwitch bits ∧ el.val = 2 then δ else 0) =
      if el.val = 2 then shiftCoeff bits * δ else 0 := by
    by_cases two : el.val = 2
    · simp only [two, and_true, if_true, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_erase.mpr ⟨Kriterion.ArgoMAC.Phase3.Lazy.designatedSwitch_ne bits,
        Finset.mem_univ _⟩)]
      rfl
    · simp [two]
  rw [single]
  ring

theorem laneValueM_shift_curveY (δ : BaseField) (m : MaskSite → BaseField)
    (scale : Fin chunkCount → Fin curveElementCountY → BaseField)
    (word : BitVec coordinateBitCount) :
    laneValueM (maskShift bits δ m) .curveY curveElementCountY curveYLe scale word =
      laneValueM m .curveY curveElementCountY curveYLe scale word := by
  funext el
  unfold laneValueM
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chunkMasks_shift_other bits δ m .curveY _ curveYLe c _ (Or.inl (by decide))]

/-- **The bridge input under the shift.** -/
theorem curveMap_shift (δ : BaseField) (m : MaskSite → BaseField) :
    curveMap table bits (maskShift bits δ m) = curveMap table bits m + shiftCoeff bits * δ := by
  unfold curveMap
  rw [laneValueM_shift_curveY]
  simp only [CurveMembership.evaluate, Pipeline.curveValues]
  have x7 : (curveXElementIndex .x7).val = 2 := rfl
  have x5 : (curveXElementIndex .x5).val = 1 := rfl
  have x3 : (curveXElementIndex .x3).val = 0 := rfl
  rw [laneValueM_shift_curveX, laneValueM_shift_curveX, laneValueM_shift_curveX, x7, x5, x3]
  simp only [if_true, show (1 : ℕ) ≠ 2 from by decide, show (0 : ℕ) ≠ 2 from by decide, if_false,
    add_zero]
  ring

end Shift

/-! ### A uniform family shifted affinely -/

section Uniform

variable [FieldCertificate]

/-- **An affine function of a uniform family, shifted along one coordinate, hits a point with mass
`1/p`.** -/
theorem uniform_affine_le {X : Type} [Fintype X] [Nonempty X] (Φ : X → BaseField)
    (shift : BaseField → X ≃ X) (a : BaseField) (nonzero : a ≠ 0)
    (shifted : ∀ δ x, Φ (shift δ x) = Φ x + a * δ) (k : BaseField) :
    ∑' x, PMF.uniformOfFintype X x * ind (Φ x = k) ≤
      ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  set S := ∑' x, PMF.uniformOfFintype X x * ind (Φ x = k) with hS
  have each : ∀ δ : BaseField, S = ∑' x, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) := by
    intro δ
    rw [hS, ← (shift δ).tsum_eq]
    refine tsum_congr fun x => ?_
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, shifted]
  have one : ∀ x, ∑ δ : BaseField, ind (Φ x + a * δ = k) = 1 := by
    intro x
    have iff : ∀ δ, Φ x + a * δ = k ↔ δ = a⁻¹ * (k - Φ x) := by
      intro δ
      constructor
      · intro h
        rw [← h, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
      · rintro rfl
        rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul, add_sub_cancel]
    simp only [iff]
    rw [Finset.sum_eq_single (a⁻¹ * (k - Φ x))]
    · exact ind_pos rfl
    · intro δ _ different
      exact ind_neg different
    · intro outside
      exact absurd (Finset.mem_univ _) outside
  have total : (Fintype.card BaseField : ℝ≥0∞) * S = 1 := by
    calc (Fintype.card BaseField : ℝ≥0∞) * S = ∑ _δ : BaseField, S := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ δ : BaseField, ∑' x, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) :=
          Finset.sum_congr rfl fun δ _ => each δ
      _ = ∑' x, ∑ δ : BaseField, PMF.uniformOfFintype X x * ind (Φ x + a * δ = k) :=
          (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      _ = ∑' x, PMF.uniformOfFintype X x * 1 := tsum_congr fun x => by
          rw [← Finset.mul_sum, one x]
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have ne : (Fintype.card BaseField : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card BaseField := Fintype.card_pos
    exact_mod_cast this.ne'
  have top : (Fintype.card BaseField : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine le_of_eq ?_
  rw [← ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact total)]

/-- `1/p ≤ 4/2^128`. -/
theorem inv_modulus_le : ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ ≤ 4 / 2 ^ 128 := by
  have card : Fintype.card BaseField = baseFieldModulus := ZMod.card _
  have big : 2 ^ 128 ≤ baseFieldModulus := by
    unfold baseFieldModulus
    norm_num
  rw [card]
  calc ((baseFieldModulus : ℕ) : ℝ≥0∞)⁻¹ ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr (by exact_mod_cast big)
    _ ≤ 4 * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := le_mul_of_one_le_left zero_le (by norm_num)
    _ = 4 / 2 ^ 128 := by
        rw [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

end Uniform

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
