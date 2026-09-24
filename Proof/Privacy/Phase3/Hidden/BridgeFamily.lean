/-
**Phase 3, P1f — `StageOneBridgeGuess`, real.**

On the (rest, masks) coordinates, where the swapped tape is uniform × uniform
(`swapped_restMasks`), the family over `δ ∈ F_p`

```
t ↦ t + δ,   hash ↦ hash ∘ swap(t, t + δ),
Y(curveX, chunk 0, switch 1, x7) += δ,   Y(curveX, chunk 0, switch 0, x7) −= δ
```

keeps the stage-1 view: `K_x7` moves by `ι 1 − ι 0 = 1` and absorbs `t` in `c0`; every published
switch sum `Σ_j Y` is kept; no slope reads `K_x7`; `hash'(t + δ) = hash t` keeps the pads, the
whitened keys and the gadget. It moves `t` by `δ`, so `t` hits a key with conditional mass `1/p`.
-/

import Proof.Privacy.Phase3.Hidden.Bridge

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- The `x7` slot of the `curveX` lane. -/
def x7Slot : Fin curveElementCountX := curveXElementIndex .x7

/-- The bridge family on the rest. -/
def bridgeRest (δ : BaseField) (rest : RestTape TapeRest) : RestTape TapeRest :=
  (({ rest.1.1 with bridgeKey := rest.1.1.bridgeKey + δ }, rest.1.2.1,
      rest.1.2.2 ∘ Equiv.swap rest.1.1.bridgeKey (rest.1.1.bridgeKey + δ)), rest.2)

/-- The bridge family on the masks. -/
def bridgeMasks (δ : BaseField) (masks : MaskSite → BaseField) : MaskSite → BaseField
  | ⟨ℓ, c, switch, e⟩ => masks ⟨ℓ, c, switch, e⟩ +
      (if ℓ = .curveX ∧ c.val = 0 ∧ switch.val = 1 ∧ e.val = x7Slot.val then δ else 0) -
      (if ℓ = .curveX ∧ c.val = 0 ∧ switch.val = 0 ∧ e.val = x7Slot.val then δ else 0)

/-- The bridge family. -/
def bridgeShift (δ : BaseField) (z : RestTape TapeRest × (MaskSite → BaseField)) :
    RestTape TapeRest × (MaskSite → BaseField) :=
  (bridgeRest δ z.1, bridgeMasks δ z.2)

theorem bridgeShift_neg (δ : BaseField) (z : RestTape TapeRest × (MaskSite → BaseField)) :
    bridgeShift (-δ) (bridgeShift δ z) = z := by
  obtain ⟨⟨⟨coins, enc, hash⟩, other⟩, masks⟩ := z
  refine Prod.ext (Prod.ext (Prod.ext ?_ (Prod.ext rfl ?_)) rfl) ?_
  · show { coins with bridgeKey := coins.bridgeKey + δ + -δ } = coins
    simp
  · funext value
    show hash (Equiv.swap coins.bridgeKey (coins.bridgeKey + δ)
      (Equiv.swap (coins.bridgeKey + δ) (coins.bridgeKey + δ + -δ) value)) = hash value
    rw [add_neg_cancel_right, Equiv.swap_comm, Equiv.swap_apply_self]
  · funext site
    obtain ⟨ℓ, c, switch, e⟩ := site
    simp only [bridgeShift, bridgeMasks]
    split_ifs <;> ring

/-- The bridge family, as a permutation. -/
def bridgeEquiv (δ : BaseField) : (RestTape TapeRest × (MaskSite → BaseField)) ≃
    (RestTape TapeRest × (MaskSite → BaseField)) where
  toFun := bridgeShift δ
  invFun := bridgeShift (-δ)
  left_inv := bridgeShift_neg δ
  right_inv z := by
    have := bridgeShift_neg (-δ) z
    rwa [neg_neg] at this

theorem chunk_zero_lt : 0 < chunkCount := by unfold chunkCount; omega

theorem switch_lt (c : Fin chunkCount) (k : Nat) (small : k < 4) : k < 2 ^ chunkWidth c := by
  rw [chunkWidth_two]
  omega

/-- A double sum with one live cell. -/
theorem double_single (k : Nat) (small : k < 4)
    (f : (c : Fin chunkCount) → Fin (2 ^ chunkWidth c) → BaseField) :
    (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c),
        if c.val = 0 ∧ sw.val = k then f c sw else 0) =
      f ⟨0, chunk_zero_lt⟩ ⟨k, switch_lt _ k small⟩ := by
  rw [Finset.sum_eq_single ⟨0, chunk_zero_lt⟩]
  · rw [Finset.sum_eq_single ⟨k, switch_lt _ k small⟩]
    · simp
    · intro sw _ ne
      have : sw.val ≠ k := fun same => ne (Fin.ext same)
      simp [this]
    · intro absent
      exact absurd (Finset.mem_univ _) absent
  · intro c _ ne
    have : c.val ≠ 0 := fun same => ne (Fin.ext same)
    exact Finset.sum_eq_zero fun sw _ => by simp [this]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- A sum over one chunk's switches with one live cell. -/
theorem single_switch (c : Fin chunkCount) (k : Nat) (small : k < 4) (value : BaseField) :
    (∑ sw : Fin (2 ^ chunkWidth c), if sw.val = k then value else 0) = value := by
  rw [Finset.sum_eq_single ⟨k, switch_lt _ k small⟩]
  · simp
  · intro sw _ ne
    have : sw.val ≠ k := fun same => ne (Fin.ext same)
    simp [this]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

section Instances

variable [FieldCertificate] [GroupCertificate]

theorem bridgeMasks_curveX (δ : BaseField) (masks : MaskSite → BaseField) (c : Fin chunkCount)
    (sw : Fin (2 ^ chunkWidth c)) (e : Fin curveElementCountX) :
    bridgeMasks δ masks ⟨.curveX, c, sw, e⟩ = masks ⟨.curveX, c, sw, e⟩ +
      (if e = x7Slot then ((if c.val = 0 ∧ sw.val = 1 then δ else 0) -
        (if c.val = 0 ∧ sw.val = 0 then δ else 0)) else 0) := by
  simp only [bridgeMasks, true_and]
  by_cases he : e = x7Slot
  · subst he
    simp only [if_true, true_and, and_true]
    split_ifs <;> first | ring | (exfalso; omega)
  · have : e.val ≠ x7Slot.val := fun same => he (Fin.ext same)
    simp [this, he]

/-- **The published switch sums are kept.** -/
theorem sum_bridgeMasks (δ : BaseField) (masks : MaskSite → BaseField) (c : Fin chunkCount)
    (e : Fin curveElementCountX) :
    (∑ sw : Fin (2 ^ chunkWidth c), bridgeMasks δ masks ⟨.curveX, c, sw, e⟩) =
      ∑ sw : Fin (2 ^ chunkWidth c), masks ⟨.curveX, c, sw, e⟩ := by
  rw [Finset.sum_congr rfl fun sw _ => bridgeMasks_curveX δ masks c sw e, Finset.sum_add_distrib]
  suffices rest : (∑ sw : Fin (2 ^ chunkWidth c), (if e = x7Slot then
      ((if c.val = 0 ∧ sw.val = 1 then δ else 0) - (if c.val = 0 ∧ sw.val = 0 then δ else 0))
      else 0)) = 0 by rw [rest, add_zero]
  by_cases he : e = x7Slot
  · rw [Finset.sum_congr rfl fun sw _ => if_pos he, Finset.sum_sub_distrib]
    by_cases hc : c.val = 0
    · simp only [hc, true_and]
      rw [single_switch c 1 (by omega) δ, single_switch c 0 (by omega) δ, sub_self]
    · rw [Finset.sum_eq_zero fun sw _ => if_neg (fun h => hc h.1),
        Finset.sum_eq_zero fun sw _ => if_neg (fun h => hc h.1), sub_self]
  · exact Finset.sum_eq_zero fun sw _ => if_neg he

/-- **`K_x7` moves by `δ`; no other offset moves.** -/
theorem offsets_bridgeMasks (δ : BaseField) (masks : MaskSite → BaseField) (e : Fin curveElementCountX) :
    (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c),
        iota _ sw * bridgeMasks δ masks ⟨.curveX, c, sw, e⟩) =
      (∑ c : Fin chunkCount, ∑ sw : Fin (2 ^ chunkWidth c), iota _ sw * masks ⟨.curveX, c, sw, e⟩) +
        (if e = x7Slot then δ else 0) := by
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun sw _ => by
    rw [bridgeMasks_curveX, mul_add]]
  simp only [Finset.sum_add_distrib]
  rw [add_right_inj]
  by_cases he : e = x7Slot
  · simp only [he, if_true, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
    rw [double_single 1 (by omega) fun c sw => iota _ sw * δ,
      double_single 0 (by omega) fun c sw => iota _ sw * δ]
    simp [iota]
  · simp only [he, if_false, mul_zero, Finset.sum_const_zero]

end Instances

section Invariance

variable [FieldCertificate] [GroupCertificate]

theorem bridgeRest_hash (δ : BaseField) (rest : RestTape TapeRest) :
    (bridgeRest δ rest).1.2.2 (bridgeRest δ rest).1.1.bridgeKey = rest.1.2.2 rest.1.1.bridgeKey := by
  show rest.1.2.2 (Equiv.swap rest.1.1.bridgeKey (rest.1.1.bridgeKey + δ) (rest.1.1.bridgeKey + δ)) = _
  rw [Equiv.swap_apply_right]

theorem garblerKeys_bridge (δ : BaseField) (rest : RestTape TapeRest) :
    garblerKeys (bridgeRest δ rest).1 = garblerKeys rest.1 := by
  have white : Pipeline.whitenedKey (bridgeRest δ rest).1.2.1 (bridgeRest δ rest).1.2.2
      (bridgeRest δ rest).1.1.bridgeKey (bridgeRest δ rest).1.1.inputMacKey =
      Pipeline.whitenedKey rest.1.2.1 rest.1.2.2 rest.1.1.bridgeKey rest.1.1.inputMacKey := by
    unfold Pipeline.whitenedKey EncPRF.whiteningKeys
    rw [bridgeRest_hash]
    rfl
  unfold garblerKeys
  rw [white]
  rfl

theorem tablesOf_bridgeRest (δ : BaseField) (rest : RestTape TapeRest) (masks : MaskSite → BaseField)
    (ℓ : Lane) : tablesOf (bridgeRest δ rest) masks ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  rw [garblerKeys_bridge]
  rfl

theorem tablesOf_bridgeMasks (δ : BaseField) (rest : RestTape TapeRest) (masks : MaskSite → BaseField)
    (ℓ : Lane) (other : ℓ ≠ .curveX) :
    tablesOf rest (bridgeMasks δ masks) ℓ = tablesOf rest masks ℓ := by
  unfold tablesOf
  congr 1
  funext c switch element
  simp only [bridgeMasks, other, false_and, if_false, add_zero, sub_zero]

/-- **The EncPRF entries are kept.** -/
theorem encOf_bridge (δ : BaseField) (rest : RestTape TapeRest) : encOf (bridgeRest δ rest) = encOf rest := by
  unfold encOf
  rw [bridgeRest_hash]
  have same : ∀ request : PublicQuery FixedIndex EncPRF.PermutationIndex, IsEncForward request →
      publicAnswer (restOracle (bridgeRest δ rest)) request = publicAnswer (restOracle rest) request := by
    intro request enc
    cases request with
    | encForward index input => rfl
    | _ => exact enc.elim
  exact ((padsM_encOnly _).agree (restOracle rest) (restOracle (bridgeRest δ rest)) same).1

theorem curveValues_bridge (δ : BaseField) (xs : Fin curveElementCountX → BaseField)
    (ys : Fin curveElementCountY → BaseField) :
    Pipeline.curveValues (fun e => xs e + (if e = x7Slot then δ else 0)) ys =
      fun element => Pipeline.curveValues xs ys element +
        (if element = .inl .x7 then δ else 0) := by
  funext element
  rcases element with (_ | _ | _) | (_ | _) <;> simp [Pipeline.curveValues, x7Slot, curveXElementIndex,
    CurveXElement.slot]

theorem assemble_bridge (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (t δ : BaseField) (curveMask : NonZeroBase)
    (curveR1 curveR2 : BaseField) (cx cx' : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount)
    (offsets : cx'.offsets = fun e => cx.offsets e + (if e = x7Slot then δ else 0))
    (joins : ∀ slopes, cx'.scaleJoins slopes = cx.scaleJoins slopes) (hot : cx'.hotJoins = cx.hotJoins) :
    Programs.assemble outputKeys pointRandomness (t + δ) curveMask curveR1 curveR2 cx' cy px py gadget =
      Programs.assemble outputKeys pointRandomness t curveMask curveR1 curveR2 cx cy px py gadget := by
  have slopes : ∀ K : CurveMembership.Values,
      CurveMembership.slopes curveR1 curveR2
          (fun element => K element + (if element = .inl .x7 then δ else 0)) =
        CurveMembership.slopes curveR1 curveR2 K := by
    intro K
    funext element
    rcases element with (_ | _ | _) | (_ | _) <;> simp [CurveMembership.slopes]
  have garbled : ∀ K : CurveMembership.Values,
      CurveMembership.garble (t + δ) curveMask.value curveR1 curveR2
          (fun element => K element + (if element = .inl .x7 then δ else 0)) =
        CurveMembership.garble t curveMask.value curveR1 curveR2 K := by
    intro K
    simp only [CurveMembership.garble, reduceCtorEq, if_false, if_true, add_zero, Prod.mk.injEq]
    first | trivial | exact ⟨by ring, rfl, rfl⟩ | (refine ⟨?_, trivial⟩; ring)
  unfold Programs.assemble
  simp only [offsets, joins, hot, curveValues_bridge, slopes, garbled]

/-- **The published value is kept.** -/
theorem publishedOf_bridge (scalar : NonZeroScalar) (δ : BaseField)
    (z : RestTape TapeRest × (MaskSite → BaseField)) :
    publishedOf scalar (bridgeShift δ z) = publishedOf scalar z := by
  obtain ⟨rest, masks⟩ := z
  unfold publishedOf
  simp only [bridgeShift, tablesOf_bridgeRest]
  rw [tablesOf_bridgeMasks δ rest masks .curveY (by decide),
    tablesOf_bridgeMasks δ rest masks .pointX (by decide),
    tablesOf_bridgeMasks δ rest masks .pointY (by decide)]
  have white : EncPRF.whiteningKeys (bridgeRest δ rest).1.2.2 (bridgeRest δ rest).1.1.bridgeKey =
      EncPRF.whiteningKeys rest.1.2.2 rest.1.1.bridgeKey := by
    unfold EncPRF.whiteningKeys
    rw [bridgeRest_hash]
  rw [white]
  exact assemble_bridge _ _ rest.1.1.bridgeKey δ _ _ _ (tablesOf rest masks .curveX)
    (tablesOf rest (bridgeMasks δ masks) .curveX) _ _ _ _
    (funext fun e => offsets_bridgeMasks δ masks e)
    (fun slopes => funext fun c => funext fun e => congrArg (· + _) (sum_bridgeMasks δ masks c e)) rfl

end Invariance

/-- **`StageOneBridgeGuess`, real.** -/
theorem stageOneBridgeGuess : StageOneBridgeGuess := by
  intro field group parameter scalar view key
  let Φ : Coins × Oracle → RestTape TapeRest × (MaskSite → BaseField) :=
    fun tape => (restOf tape, maskOf tape)
  let V : RestTape TapeRest × (MaskSite → BaseField) →
      Public × List (Entry FixedIndex EncPRF.PermutationIndex) :=
    fun z => (publishedOf scalar z, encOf z.1)
  have factor : ∀ tape, stageOneView parameter scalar tape = V (Φ tape) := fun tape => by
    show ((Scheme.scheme.garble parameter scalar tape).1, encEntries scalar tape) = _
    rw [published_eq, encEntries_eq]
  have law : swappedChallengeTape.map Φ =
      PMF.uniformOfFintype (RestTape TapeRest × (MaskSite → BaseField)) := by
    rw [swapped_restMasks, restLaw, restUniform, ← uniformOfFintype_productPMF,
      ← uniformOfFintype_productPMF]
  have transfer : ∀ S : Set (RestTape TapeRest × (MaskSite → BaseField)),
      swappedChallengeTape.toOuterMeasure (Φ ⁻¹' S) =
        (PMF.uniformOfFintype (RestTape TapeRest × (MaskSite → BaseField))).toOuterMeasure S := by
    intro S
    rw [← law, PMF.toOuterMeasure_map_apply]
  have left : {tape : Coins × Oracle | stageOneView parameter scalar tape = view ∧ tape.1.bridgeKey = key} =
      Φ ⁻¹' {z | V z = view ∧ z.1.1.1.bridgeKey = key} := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_preimage, factor]
    rfl
  have right : {tape : Coins × Oracle | stageOneView parameter scalar tape = view} =
      Φ ⁻¹' {z | V z = view} := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_preimage, factor]
  rw [left, right, transfer, transfer]
  have bound := event_le_of_symmetry (PMF.uniformOfFintype (RestTape TapeRest × (MaskSite → BaseField))) V
    (fun z => z.1.1.1.bridgeKey = key) (fun δ => bridgeShift δ)
    (fun δ => Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv (bridgeEquiv δ))
    (fun δ z => by
      show (publishedOf scalar (bridgeShift δ z), encOf (bridgeShift δ z).1) = (publishedOf scalar z, encOf z.1)
      rw [publishedOf_bridge]
      exact congrArg _ (encOf_bridge δ z.1))
    (fun z δ δ' first second => by
      have one : z.1.1.1.bridgeKey + δ = key := first
      have two : z.1.1.1.bridgeKey + δ' = key := second
      exact add_left_cancel (one.trans two.symm)) view
  rwa [ZMod.card] at bound

end

end Kriterion.ArgoMAC.Security.Phase3
