/-
**Phase 3, P1f — the swapped tape is invariant under every join-keeping tape shift.**

`swapped_shift_invariant`: `swappedChallengeTape.map (shiftTape T scalar) = swappedChallengeTape`
for every `TapeShift` that keeps every join. The shift acts on the rest of the tape (coins, EncPRF,
hash, the non-site permutations) by an involution, so it keeps the uniform rest; it moves every
garbler point at a scale site by its level shift (`planBPoint_shift`, from `sim_garbleChunkM`),
and it conjugates the site permutations by exactly that shift, which keeps every garbler mask, so
it maps each fibre of the swap kernel onto the fibre of the moved points over the same masks.
-/

import Proof.Privacy.Phase3.Hidden.GarblerSim

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv)
open scoped ENNReal

noncomputable section

/-! ### Fibre laws under an equivalence -/

theorem fibreLaw_map_equiv {A B : Type} [Fintype A] [DecidableEq B] (g g' : A → B)
    (onto : Function.Surjective g) (onto' : Function.Surjective g') (e : A ≃ A)
    (compat : ∀ a, g' (e a) = g a) (point : B) :
    (fibreLaw g onto point).map e = fibreLaw g' onto' point := by
  classical
  have cards : Fintype.card {y : A // g y = point} = Fintype.card {y : A // g' y = point} :=
    Fintype.card_congr
      { toFun := fun y => ⟨e y.1, by rw [compat]; exact y.2⟩
        invFun := fun y => ⟨e.symm y.1, by rw [← compat, Equiv.apply_symm_apply]; exact y.2⟩
        left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
        right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  refine PMF.ext fun x => ?_
  rw [PMF.map_apply, tsum_eq_single (e.symm x)]
  · rw [if_pos (e.apply_symm_apply x).symm, fibreLaw_apply, fibreLaw_apply, ← compat,
      Equiv.apply_symm_apply, cards]
  · intro other miss
    rw [if_neg (fun same => miss (by rw [same, Equiv.symm_apply_apply]))]

/-! ### The two parts of the shift -/

section Parts

variable [FieldCertificate] [GroupCertificate]

/-- The shift of the rest of the tape: coins, EncPRF, hash, the non-site permutations. -/
def restShift (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest) : RestTape TapeRest :=
  ((shiftCoins T rest.1.1, rest.1.2.1, shiftHash T rest.1.1.bridgeKey rest.1.2.2),
    fun index => shiftPerm (indexShift T scalar rest.1.1 index.1).1
      (indexShift T scalar rest.1.1 index.1).2 (rest.2 index))

/-- The shift of the site permutations: each conjugated by its switch's level shift. -/
def scaleShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) (scale : SitePerms MaskSite) :
    SitePerms MaskSite := fun site =>
  shiftPerm (indexShift T scalar coins (siteIndex site)).1 (indexShift T scalar coins (siteIndex site)).2
    (scale site)

theorem shiftCoins_offsets (T : TapeShift) (coins : Coins) : (shiftCoins T coins).offsets = coins.offsets :=
  rfl

theorem indexShift_shiftCoins (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    indexShift T scalar (shiftCoins T coins) = indexShift T scalar coins := by
  funext index
  cases index with
  | gadget o κ position =>
      simp only [indexShift, gadgetShift, shiftCoins_offsets]
      rfl
  | _ => rfl

theorem xor_pair_cancel (p x a : Block) : (p ^^^ a) ^^^ (x ^^^ a) = p ^^^ x := by
  rw [BitVec.xor_assoc, BitVec.xor_comm x a, xor_self_left]

theorem shiftCoins_shiftCoins (T : TapeShift) (coins : Coins) : shiftCoins T (shiftCoins T coins) = coins := by
  apply Scheme.Coins.data_injective
  simp only [Scheme.Coins.data, shiftCoins, xor_cancel_right]

theorem shiftHash_shiftHash (T : TapeShift) (key : BaseField) (hash : EncPRF.HashOracle) :
    shiftHash T key (shiftHash T key hash) = hash := by
  funext value
  unfold shiftHash
  split
  · subst_vars
    simp only [xor_cancel_right]
  · rfl

theorem restShift_involutive (T : TapeShift) (scalar : NonZeroScalar) :
    Function.Involutive (restShift T scalar) := by
  rintro ⟨⟨coins, enc, hash⟩, other⟩
  simp only [restShift, shiftCoins_shiftCoins, indexShift_shiftCoins]
  refine Prod.ext (Prod.ext rfl (Prod.ext rfl ?_)) (funext fun index => shiftPerm_involutive _ _ _)
  exact shiftHash_shiftHash T coins.bridgeKey hash

theorem scaleShift_involutive (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    Function.Involutive (scaleShift T scalar coins) :=
  fun scale => funext fun site => shiftPerm_involutive _ _ _

/-- The rest shift, as a permutation. -/
def restShiftEquiv (T : TapeShift) (scalar : NonZeroScalar) : RestTape TapeRest ≃ RestTape TapeRest :=
  (restShift_involutive T scalar).toPerm _

/-- The scale shift, as a permutation. -/
def scaleShiftEquiv (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins) :
    SitePerms MaskSite ≃ SitePerms MaskSite :=
  (scaleShift_involutive T scalar coins).toPerm _

/-- **The masks are kept**: conjugating each site's permutation by the shift of its point keeps its
Davies–Meyer value at the shifted point. -/
theorem maskMap_scaleShift (T : TapeShift) (scalar : NonZeroScalar) (coins : Coins)
    (point : MaskSite × Fin 3 → Block) (scale : SitePerms MaskSite) :
    maskMap (fun site => point site ^^^ (indexShift T scalar coins (siteIndex site)).1)
        (scaleShift T scalar coins scale) = maskMap point scale := by
  funext mask
  have each : ∀ site : MaskSite × Fin 3,
      daviesMeyer (scaleShift T scalar coins scale site)
        (point site ^^^ (indexShift T scalar coins (siteIndex site)).1) =
      daviesMeyer (scale site) (point site) := by
    intro site
    obtain ⟨⟨lane, c, switch, element⟩, block⟩ := site
    have equal := indexShift_scaleIndexOf T scalar coins lane c switch.val element block switch.isLt
    unfold daviesMeyer Cryptography.xor scaleShift
    rw [shiftPerm_shift]
    have second : (indexShift T scalar coins (siteIndex (⟨lane, c, switch, element⟩, block))).2 =
        (indexShift T scalar coins (siteIndex (⟨lane, c, switch, element⟩, block))).1 := by
      show (indexShift T scalar coins (scaleIndexOf lane c switch.val element block)).2 =
        (indexShift T scalar coins (scaleIndexOf lane c switch.val element block)).1
      rw [equal]
    rw [second, xor_pair_cancel]
  simp only [maskMap, masksOf, dmValues, each]

/-! ### The garbler's keys and points move by the shift -/

theorem realPads_shift (T : TapeShift) (enc : PermutationOracle EncPRF.PermutationIndex Block)
    (hash : EncPRF.HashOracle) (key : BaseField) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    Programs.realPads enc (EncPRF.whiteningKeys (shiftHash T key hash) key) coordinate index bit =
      Programs.realPads enc (EncPRF.whiteningKeys hash key) coordinate index bit ^^^ T.key2 := by
  simp only [Programs.realPads, EncPRF.evenMansourPad, evenMansour, EncPRF.whiteningKeys, shiftHash,
    if_true, Cryptography.xor]
  ac_rfl

theorem garblerKeys_delta (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest) (lane : Lane) :
    (garblerKeys (restShift T scalar rest).1).1 lane = (garblerKeys rest.1).1 lane ^^^ (T.lane lane).delta :=
  rfl

theorem garblerKeys_zero (T : TapeShift) (scalar : NonZeroScalar) (rest : RestTape TapeRest) (lane : Lane)
    (position : Fin PlanB.coordinateBits) :
    ((garblerKeys (restShift T scalar rest).1).2 lane position).1 =
      ((garblerKeys rest.1).2 lane position).1 ^^^ (T.lane lane).zero position := by
  cases lane
  · rw [lane_zero_curveX]
    exact shift_curve_key T rest.1.1 .x position
  · rw [lane_zero_curveY]
    exact shift_curve_key T rest.1.1 .y position
  · rw [lane_zero_pointX]
    exact shift_point_key T rest.1.1 _ _ (realPads_shift T rest.1.2.1 rest.1.2.2 rest.1.1.bridgeKey) .x position
  · rw [lane_zero_pointY]
    exact shift_point_key T rest.1.1 _ _ (realPads_shift T rest.1.2.1 rest.1.2.2 rest.1.1.bridgeKey) .y position

theorem hotIndexNat_not_site (lane : Lane) (c : Fin chunkCount) (n r : Nat) (half : Bool)
    (small : n < chunkWidth c) (entry : r < 2 ^ n) : hotIndexNat lane c n r half ∉ Set.range siteIndex := by
  obtain ⟨fold, e, _, _, same⟩ := hotIndexNat_of_lt lane c n r half small entry
  rw [same]
  exact hot_not_site lane c fold e half

/-- **Every garbler point at a scale site moves by its level shift.** -/
theorem planBPoint_shift (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar)
    (rest : RestTape TapeRest) :
    planBPoint garblerKeys (restShift T scalar rest) =
      fun site => planBPoint garblerKeys rest site ^^^ (indexShift T scalar rest.1.1 (siteIndex site)).1 := by
  funext site
  obtain ⟨⟨lane, c, switch, element⟩, block⟩ := site
  let O : Oracle := (oracleOf rest.2 fun _ => Equiv.refl Block, rest.1.2.1, rest.1.2.2)
  let O' : Oracle := (oracleOf (restShift T scalar rest).2 fun _ => Equiv.refl Block, rest.1.2.1, rest.1.2.2)
  have sim := sim_garbleChunkM (rel := fun _ _ => True) O O' (T.lane lane) (valid lane) lane
    ((garblerKeys rest.1).1 lane) ((garblerKeys rest.1).2 lane)
    ((garblerKeys (restShift T scalar rest).1).2 lane) (garblerKeys_zero T scalar rest lane) c
    (fun n r half x small entry => by
      have notSite := hotIndexNat_not_site lane c n r half small entry
      show (oracleOf (restShift T scalar rest).2 _).permutation _ _ = (oracleOf rest.2 _).permutation _ _ ^^^ _
      rw [oracleOf_other _ _ ⟨_, notSite⟩, oracleOf_other _ _ ⟨_, notSite⟩]
      show shiftPerm (indexShift T scalar rest.1.1 _).1 (indexShift T scalar rest.1.1 _).2 _ _ = _
      rw [indexShift_hotIndexNat T scalar rest.1.1 lane c n r half small entry, shiftPerm_shift])
    (fun _ _ _ _ _ => trivial)
  have moved := sim.2.2.1 switch
  erw [Programs.eval_garbleChunkM O', Programs.eval_garbleChunkM O] at moved
  show (garbleChunk (oracleOf (restShift T scalar rest).2 _) lane _ _ c).1 switch = _
  rw [garblerKeys_delta]
  refine moved.trans ?_
  have equal := indexShift_scaleIndexOf T scalar rest.1.1 lane c switch.val element block switch.isLt
  show _ = _ ^^^ (indexShift T scalar rest.1.1 (scaleIndexOf lane c switch.val element block)).1
  rw [equal]
  rfl

end Parts


/-! ### The swapped tape is invariant -/

theorem swapKernel_map {M : Type} [Fintype M] [DecidableEq M] (point point' : M × Fin 3 → Block)
    (e : SitePerms M ≃ SitePerms M) (compat : ∀ scale, maskMap point' (e scale) = maskMap point scale) :
    (swapKernel point).map e = swapKernel point' := by
  unfold swapKernel
  rw [PMF.map_bind]
  exact congrArg _ (funext fun masks =>
    fibreLaw_map_equiv _ _ (maskMap_surjective point) (maskMap_surjective point') e compat masks)

section Main

variable [FieldCertificate] [GroupCertificate]

/-- The shift on the split tape. -/
def splitShift (T : TapeShift) (scalar : NonZeroScalar)
    (tape : RestTape TapeRest × SitePerms MaskSite) : RestTape TapeRest × SitePerms MaskSite :=
  (restShift T scalar tape.1, scaleShift T scalar tape.1.1.1 tape.2)

theorem shiftTape_split (T : TapeShift) (scalar : NonZeroScalar)
    (tape : RestTape TapeRest × SitePerms MaskSite) :
    shiftTape T scalar (reassembleEquiv (assemble tape)) =
      reassembleEquiv (assemble (splitShift T scalar tape)) := by
  obtain ⟨⟨⟨coins, enc, hash⟩, other⟩, scale⟩ := tape
  show (shiftCoins T coins, shiftOracle T scalar coins (oracleOf other scale, enc, hash)) =
    (shiftCoins T coins, oracleOf _ _, enc, shiftHash T coins.bridgeKey hash)
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  refine oracle_ext fun index => ?_
  show shiftPerm _ _ ((oracleOf other scale).permutation index) = _
  by_cases hit : index ∈ Set.range siteIndex
  · obtain ⟨site, rfl⟩ := hit
    rw [oracleOf_site, oracleOf_site]
    rfl
  · rw [oracleOf_other other scale ⟨index, hit⟩, oracleOf_other _ _ ⟨index, hit⟩]
    rfl

/-- **The swapped tape is invariant under every join-keeping tape shift.** -/
theorem swapped_shift_invariant (T : TapeShift) (valid : T.Valid) (scalar : NonZeroScalar) :
    swappedChallengeTape.map (shiftTape T scalar) = swappedChallengeTape := by
  have law : (swapLaw (restLaw restUniform) (planBPoint garblerKeys)).map (splitShift T scalar) =
      swapLaw (restLaw restUniform) (planBPoint garblerKeys) := by
    unfold swapLaw
    rw [PMF.map_bind]
    have each : ∀ rest : RestTape TapeRest,
        (((swapKernel (planBPoint garblerKeys rest)).map (Prod.mk rest)).map (splitShift T scalar)) =
          (swapKernel (planBPoint garblerKeys (restShift T scalar rest))).map
            (Prod.mk (restShift T scalar rest)) := by
      intro rest
      rw [PMF.map_comp]
      have factor : (splitShift T scalar ∘ Prod.mk rest) =
          Prod.mk (restShift T scalar rest) ∘ scaleShiftEquiv T scalar rest.1.1 := rfl
      rw [factor, ← PMF.map_comp, swapKernel_map _ _ (scaleShiftEquiv T scalar rest.1.1)]
      intro scale
      rw [planBPoint_shift T valid scalar rest]
      exact maskMap_scaleShift T scalar rest.1.1 _ scale
    simp only [each]
    have restInvariant : (restLaw restUniform).map (restShiftEquiv T scalar) = restLaw restUniform := by
      unfold restLaw restUniform
      rw [← uniformOfFintype_productPMF]
      exact uniformOfFintype_map_equiv _
    conv_rhs => rw [← restInvariant]
    rw [PMF.bind_map]
    rfl
  unfold swappedChallengeTape swappedTape
  rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
  have factor : ((shiftTape T scalar ∘ reassembleEquiv) ∘ assemble) =
      (reassembleEquiv ∘ assemble) ∘ splitShift T scalar := by
    funext tape
    exact shiftTape_split T scalar tape
  rw [factor, ← PMF.map_comp, law]

end Main

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
