/-
**The rejection samplers against their exact laws.**

`rejectLaw_close`: a bounded rejection sampler read through a decoding `φ` (`none` off its domain) that is a
bijection from the accepted draws onto a finite type `β` is abort-close to the uniform law on `β`,
with extra abort mass the sampler's cutoff `rejectLaw … none`. Instances:

* `fieldCell_close`: a field cell against the uniform field element;
* `lambda_close`: a lift randomiser against the uniform `NonZeroBase`;
* `preimage_close`: a `sampleFp`-preimage against `idealPreimage`.

`optionProduct_uniform`: independent uniform draws are the uniform law on the product.
-/

import Proof.Simulator.AbortClose
import Proof.Simulator.AbortMass
import Proof.Simulator.Law

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

/-! ### The kept draw of bounded rejection has at most the uniform mass -/

/-- The accepted `width`-bit draws. -/
def acceptedSet (width : Nat) (accept : Nat → Bool) : Finset (Fin (2 ^ width)) :=
  Finset.univ.filter fun value => accept value.val = true

/-- Every accepted draw has mass at most `1 / #accepted`. -/
theorem rejectLaw_some_mul_le (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (good : accept value = true ∧ value < 2 ^ width) :
    rejectLaw width accept count (some value) * (acceptedSet width accept).card ≤ 1 := by
  have each : ∀ other ∈ acceptedSet width accept,
      rejectLaw width accept count (some other.val) = rejectLaw width accept count (some value) := by
    intro other member
    simp only [acceptedSet, Finset.mem_filter, Finset.mem_univ, true_and] at member
    exact rejectLaw_uniform width accept count other.val value ⟨member, other.isLt⟩ good
  have sumEq : ∑ other ∈ acceptedSet width accept, rejectLaw width accept count (some other.val) =
      (acceptedSet width accept).card * rejectLaw width accept count (some value) := by
    rw [Finset.sum_congr rfl each, Finset.sum_const, nsmul_eq_mul]
  have sumLe : ∑ other ∈ acceptedSet width accept, rejectLaw width accept count (some other.val) ≤
      ∑' candidate : Nat, rejectLaw width accept count (some candidate) := by
    rw [← Finset.sum_image (f := fun candidate : Nat => rejectLaw width accept count (some candidate))
      (fun first _ second _ same => Fin.ext same)]
    exact ENNReal.sum_le_tsum _
  rw [mul_comm, ← sumEq]
  exact sumLe.trans (tsum_some_le_one _)

/-- **Bounded rejection through a bijective decoding is abort-close to the uniform law.** The
decoding `φ` sends every accepted draw to a value (`total`), is injective on the accepted draws
with inverse `ψ` (`unique`), and `ψ` lands in the accepted draws (`encode`). -/
theorem rejectLaw_close {β : Type} [Fintype β] [Nonempty β] (width : Nat) (accept : Nat → Bool)
    (count : Nat) (φ : Nat → Option β) (ψ : β → Nat)
    (encode : ∀ b, accept (ψ b) = true ∧ ψ b < 2 ^ width ∧ φ (ψ b) = some b)
    (unique : ∀ value b, accept value = true → value < 2 ^ width → φ value = some b → value = ψ b)
    (total : ∀ value, accept value = true → value < 2 ^ width → φ value ≠ none) :
    AbortClose (rejectLaw width accept count none)
      ((rejectLaw width accept count).map fun drawn => drawn.bind φ)
      ((PMF.uniformOfFintype β).map some) := by
  classical
  refine ⟨fun b => ?_, ?_⟩
  · rw [PMF.map_apply, tsum_option]
    simp only [Option.bind_none, reduceCtorEq, if_false, zero_add, Option.bind_some]
    rw [tsum_eq_single (ψ b)]
    · rw [if_pos (encode b).2.2.symm, PMF.map_apply, tsum_eq_single b]
      · simp only [if_true, PMF.uniformOfFintype_apply]
        have cardLe : Fintype.card β ≤ (acceptedSet width accept).card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun b => (⟨ψ b, (encode b).2.1⟩ : Fin (2 ^ width)))
            (fun b _ => ?_) (fun first _ second _ same => ?_)
          · simp only [acceptedSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
            exact (encode b).1
          · have := congrArg Fin.val same
            simp only at this
            have firstEq := (encode first).2.2
            rw [this, (encode second).2.2] at firstEq
            exact (Option.some_injective _ firstEq).symm
        have mass := rejectLaw_some_mul_le width accept count (ψ b) ⟨(encode b).1, (encode b).2.1⟩
        have positive : (0 : ENNReal) < (acceptedSet width accept).card := by
          have : 0 < Fintype.card β := Fintype.card_pos
          exact_mod_cast lt_of_lt_of_le this cardLe
        calc rejectLaw width accept count (some (ψ b))
            ≤ ((acceptedSet width accept).card : ENNReal)⁻¹ := by
              rw [ENNReal.le_inv_iff_mul_le]
              exact mass
          _ ≤ (Fintype.card β : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (by exact_mod_cast cardLe)
      · intro other different
        rw [if_neg (fun same => different (Option.some_injective _ same).symm)]
    · intro value different
      split
      · rename_i hit
        by_cases good : accept value = true ∧ value < 2 ^ width
        · exact absurd (unique value b good.1 good.2 hit.symm) different
        · exact rejectLaw_off width accept count value good
      · rfl
  · rw [PMF.map_apply, tsum_option]
    simp only [Option.bind_none, if_true, Option.bind_some]
    have idealNone : ((PMF.uniformOfFintype β).map some) none = 0 := by
      rw [PMF.map_apply]
      simp
    rw [idealNone, zero_add]
    apply le_of_eq
    convert add_zero (rejectLaw width accept count none) using 2
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    split
    · rename_i miss
      by_cases good : accept value = true ∧ value < 2 ^ width
      · exact absurd miss.symm (total value good.1 good.2)
      · exact rejectLaw_off width accept count value good
    · rfl

/-! ### The field cell, the randomiser, the preimage -/

/-- `p` as the library's modulus. -/
theorem pNat_eq : pNat = baseFieldModulus := rfl

theorem pNat_lt : pNat < 2 ^ fieldWidth := by unfold pNat fieldWidth; norm_num

/-- The field cell is `rejectLaw` read through the cast. -/
theorem fieldCellLaw_eq : fieldCellLaw = (rejectLaw fieldWidth (fun value => decide (value < pNat))
    attempts).map fun drawn => drawn.bind fun value => some ((value : Nat) : BaseField) := by
  unfold fieldCellLaw
  congr 1
  funext drawn
  cases drawn <;> rfl

/-- **A field cell is abort-close to the uniform field element.** -/
theorem fieldCell_close [FieldCertificate] :
    AbortClose (rejectLaw fieldWidth (fun value => decide (value < pNat)) attempts none)
      fieldCellLaw ((PMF.uniformOfFintype BaseField).map some) := by
  rw [fieldCellLaw_eq]
  refine rejectLaw_close _ _ _ _ (fun x : BaseField => x.val) (fun x => ⟨?_, ?_, ?_⟩) ?_ ?_
  · simp only [decide_eq_true_eq]
    exact x.val_lt
  · exact lt_trans x.val_lt pNat_lt
  · simp
  · intro value x below _ equal
    simp only [decide_eq_true_eq, Option.some.injEq] at below equal
    rw [← equal, ZMod.val_natCast]
    exact (Nat.mod_eq_of_lt below).symm
  · intro value _ _
    simp

/-- The randomiser law is `rejectLaw` read through the nonzero cast. -/
theorem lambdaLaw_eq : lambdaLaw = (rejectLaw fieldWidth
    (fun value => decide (1 ≤ value ∧ value < pNat)) attempts).map fun drawn =>
      drawn.bind fun value =>
        if nonzero : ((value : Nat) : BaseField) ≠ 0 then some ⟨value, nonzero⟩ else none := rfl

/-- **A lift randomiser is abort-close to the uniform nonzero field element.** -/
theorem lambda_close [FieldCertificate] :
    AbortClose (rejectLaw fieldWidth (fun value => decide (1 ≤ value ∧ value < pNat)) attempts none)
      lambdaLaw ((PMF.uniformOfFintype NonZeroBase).map some) := by
  rw [lambdaLaw_eq]
  refine rejectLaw_close _ _ _ _ (fun x : NonZeroBase => x.value.val) (fun x => ⟨?_, ?_, ?_⟩) ?_ ?_
  · simp only [decide_eq_true_eq]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun zero => x.nonzero ?_, x.value.val_lt⟩
    exact (ZMod.val_eq_zero _).mp zero
  · exact lt_trans x.value.val_lt pNat_lt
  · simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    rw [dif_pos x.nonzero]
  · intro value x below _ equal
    simp only [decide_eq_true_eq] at below
    split at equal
    · simp only [Option.some.injEq] at equal
      rw [← equal]
      simp only [ZMod.val_natCast]
      exact (Nat.mod_eq_of_lt below.2).symm
    · exact absurd equal (by simp)
  · intro value below _
    simp only [decide_eq_true_eq] at below
    have nonzero : ((value : Nat) : BaseField) ≠ 0 := by
      intro zero
      rw [ZMod.natCast_eq_zero_iff] at zero
      have := Nat.le_of_dvd (by omega) zero
      rw [← pNat_eq] at this
      omega
    simp [nonzero]

/-- The accepted multipliers of a preimage: `q + [y < ρ]`, which is `preimageCount y + 1`. -/
theorem preimageCount_succ (value : BaseField) :
    preimageCount value + 1 =
      preimageQuotient + (if value.val < preimageRemainder then 1 else 0) := by
  have below : value.val < baseFieldModulus := value.val_lt
  have split : 2 ^ 384 = preimageQuotient * baseFieldModulus + preimageRemainder := by
    unfold preimageQuotient preimageRemainder
    rw [pNat_eq, Nat.div_add_mod']
  have remainderLt : preimageRemainder < baseFieldModulus := by
    unfold preimageRemainder
    rw [pNat_eq]
    exact Nat.mod_lt _ (by unfold baseFieldModulus; norm_num)
  have quotientPos : 1 ≤ preimageQuotient := by
    unfold preimageQuotient
    exact Nat.le_of_ble_eq_true rfl
  have modulusPos : 0 < baseFieldModulus := by unfold baseFieldModulus; norm_num
  unfold preimageCount
  split
  · rename_i small
    have : 2 ^ 384 - 1 - value.val = (preimageRemainder - 1 - value.val) +
        preimageQuotient * baseFieldModulus := by omega
    rw [this, Nat.add_mul_div_right _ _ modulusPos, Nat.div_eq_of_lt (by omega)]
    omega
  · rename_i large
    have : 2 ^ 384 - 1 - value.val = (baseFieldModulus + preimageRemainder - 1 - value.val) +
        (preimageQuotient - 1) * baseFieldModulus := by
      have expand : (preimageQuotient - 1) * baseFieldModulus + baseFieldModulus =
          preimageQuotient * baseFieldModulus := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel quotientPos]
      omega
    rw [this, Nat.add_mul_div_right _ _ modulusPos, Nat.div_eq_of_lt (by omega)]
    omega

/-- The support of bounded rejection: only accepted draws are kept. -/
theorem rejectLaw_support (width : Nat) (accept : Nat → Bool) (count value : Nat)
    (member : some value ∈ (rejectLaw width accept count).support) :
    accept value = true ∧ value < 2 ^ width := by
  by_contra bad
  exact (PMF.mem_support_iff _ _).mp member (rejectLaw_off width accept count value bad)

/-- The preimage law, factored through the multiplier's index. -/
theorem preimageLaw_eq (value : BaseField) : preimageLaw value =
    ((rejectLaw multiplierWidth
        (fun candidate => decide (candidate < preimageQuotient +
          (if value.val < preimageRemainder then 1 else 0))) attempts).map
      fun drawn => drawn.bind fun multiplier =>
        if inside : multiplier < preimageCount value + 1 then some ⟨multiplier, inside⟩ else none).map
      (Option.map fun multiplier : Fin (preimageCount value + 1) =>
        limbs (value.val + baseFieldModulus * multiplier.val)) := by
  unfold preimageLaw
  rw [PMF.map_comp]
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn member
  cases drawn with
  | none => rfl
  | some multiplier =>
      have good := rejectLaw_support _ _ _ _ member
      simp only [decide_eq_true_eq] at good
      have inside : multiplier < preimageCount value + 1 := by
        rw [preimageCount_succ]
        exact good.1
      simp only [Function.comp_apply, Option.bind_some, Option.map_some, dif_pos inside]

theorem preimageLimit_lt (value : BaseField) :
    preimageQuotient + (if value.val < preimageRemainder then 1 else 0) < 2 ^ multiplierWidth := by
  have : preimageQuotient + 2 ≤ 2 ^ multiplierWidth := Nat.le_of_ble_eq_true rfl
  split <;> omega

/-- **A preimage draw is abort-close to the uniform `sampleFp`-preimage.** -/
theorem preimage_close [FieldCertificate] (value : BaseField) :
    AbortClose (rejectLaw multiplierWidth
        (fun candidate => decide (candidate < preimageQuotient +
          (if value.val < preimageRemainder then 1 else 0))) attempts none)
      (preimageLaw value) ((idealPreimage value).map some) := by
  rw [preimageLaw_eq]
  have idealEq : (idealPreimage value).map some =
      ((PMF.uniformOfFintype (Fin (preimageCount value + 1))).map some).map
        (Option.map fun multiplier : Fin (preimageCount value + 1) =>
          limbs (value.val + baseFieldModulus * multiplier.val)) := by
    unfold idealPreimage
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [idealEq]
  refine AbortClose.map_opt ?_ _ rfl
  have limit := preimageCount_succ value
  have small := preimageLimit_lt value
  refine rejectLaw_close _ _ _ _ (fun m : Fin (preimageCount value + 1) => m.val)
    (fun m => ⟨?_, ?_, ?_⟩) ?_ ?_
  · have := m.isLt
    simp only [decide_eq_true_eq]
    omega
  · have := m.isLt
    omega
  · simp only [dif_pos m.isLt, Fin.eta]
  · intro candidate m below _ equal
    simp only [decide_eq_true_eq] at below
    split at equal
    · simp only [Option.some.injEq] at equal
      rw [← equal]
    · exact absurd equal (by simp)
  · intro candidate below _
    simp only [decide_eq_true_eq] at below
    have inside : candidate < preimageCount value + 1 := by omega
    simp [inside]

/-! ### Independent uniform draws -/

/-- Independent draws commute with a map of their values. -/
theorem optionProduct_map {α β : Type} (f : α → β) :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)),
      optionProduct count (fun index => (sample index).map (Option.map f)) =
        (optionProduct count sample).map (Option.map fun values => f ∘ values)
  | 0, sample => by
      simp only [optionProduct, PMF.pure_map, Option.map_some]
      congr 2
      funext index
      exact index.elim0
  | count + 1, sample => by
      simp only [optionProduct]
      rw [PMF.bind_map, PMF.map_bind]
      congr 1
      funext head
      cases head with
      | none => simp [PMF.pure_map]
      | some head =>
          simp only [Function.comp_apply, Option.map_some]
          rw [optionProduct_map f count, PMF.map_comp, PMF.map_comp]
          congr 1
          funext values
          cases values with
          | none => rfl
          | some values =>
              simp only [Function.comp_apply, Option.map_some, Option.some.injEq]
              funext index
              cases index using Fin.cases <;> rfl

/-- **Independent uniform draws are uniform on the product.** -/
theorem optionProduct_uniform [FieldCertificate] {α : Type} [Fintype α] [Nonempty α] :
    ∀ (count : Nat),
      optionProduct count (fun _ => (PMF.uniformOfFintype α).map some) =
        (PMF.uniformOfFintype (Fin count → α)).map some
  | 0 => by
      simp only [optionProduct]
      have single : PMF.uniformOfFintype (Fin 0 → α) = PMF.pure Fin.elim0 := by
        apply PMF.ext
        intro values
        have : values = Fin.elim0 := funext fun index => index.elim0
        subst this
        simp [PMF.uniformOfFintype_apply]
      rw [single, PMF.pure_map]
  | count + 1 => by
      simp only [optionProduct]
      rw [PMF.bind_map]
      have rest := optionProduct_uniform (α := α) count
      have step : (fun head => match (some head : Option α) with
          | none => PMF.pure none
          | some head => (optionProduct count fun _ => (PMF.uniformOfFintype α).map some).map
              (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)) =
          fun head : α => (PMF.uniformOfFintype (Fin count → α)).map
            fun tail => some (Fin.cons (α := fun _ => α) head tail) := by
        funext head
        simp only
        rw [rest, PMF.map_comp]
        rfl
      simp only [Function.comp_def]
      rw [show (fun head : α => match (some head : Option α) with
          | none => PMF.pure none
          | some head => (optionProduct count fun _ => (PMF.uniformOfFintype α).map some).map
              (Option.map fun tail => Fin.cons (α := fun _ => α) head tail)) =
          fun head : α => (PMF.uniformOfFintype (Fin count → α)).map
            fun tail => some (Fin.cons (α := fun _ => α) head tail) from step]
      have product := uniform_product (A := α) (B := Fin count → α)
      have cons := uniform_equiv (Fin.consEquiv fun _ : Fin (count + 1) => α)
      rw [← cons, ← product, PMF.map_comp, PMF.map_bind]
      congr 1
      funext head
      rw [PMF.map_comp]
      rfl

end

end Kriterion.ArgoMAC.PlanB.SimMachine
