/-
**Phase 3, P1n — the off-curve law, step (ii), part 2: the garbler's published value is F4's
published cells.**

On a table the garbler's published value is `tablePub` of its coins, its pads, its other answers
and its limbs (`garbleM_tablePub`). Read through `LawsOffCells.omegaEquiv` (the coins, the other
answers and the masks as the rest and F4's coins), it is the source of F4's published cells
`publicOf (offContext …) jc` (`tablePub_cells`): the lanes' masks are the masks of the limbs, the
lanes' offsets and joins are F4's per-element offsets and joins, the fold join of a (lane, chunk)
is its hidden gate half XOR the rest (`foldJoin_split`), and a digit's gadget entry is F4's
`gadgetEntry` of its pad and one hidden gadget answer (`digest_split`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOffCells

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source)
open scoped ENNReal

noncomputable section

/-! ### 1. The published value on a table -/

/-- Two answer functions agreeing on a program's questions evaluate it alike. -/
theorem eval_agree {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (same : ∀ q, S q → a q = b q) : P.eval a = P.eval b := by
  induction only with
  | pure value => rfl
  | query request next holds rest ih =>
      show (next (a request)).eval a = (next (b request)).eval b
      rw [same request holds]
      exact ih _

theorem get_ofFn_digit {α : Type} (f : Fin digitCount → α) (d : Fin digitCount) :
    (Vector.ofFn (n := outputMacCount) f).get d = f d :=
  Vector.get_ofFn f d

theorem ofFn_congr_digit {α : Type} (f : Fin outputMacCount → α) (g : Fin digitCount → α)
    (same : ∀ d : Fin digitCount, f d = g d) :
    Vector.ofFn (n := outputMacCount) f = Vector.ofFn (n := digitCount) g :=
  congrArg Vector.ofFn (funext same)

/-- The table with only fixed-key answers. -/
def fixedTable (v : OtherIndex → Block) (T : Tape) : Table :=
  (⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0), v, T)

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)

/-- **The garbler's published value on a table**, from its coins, its pads, its other answers and
its limbs. -/
def tablePub (coins : Coins) (pads : Programs.Pads) (v : OtherIndex → Block) (T : Tape) : Public :=
  Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
    coins.pointRandomness coins.bridgeKey coins.curveMask coins.curveR1 coins.curveR2
    (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountX .curveX
      (coins.inputDelta .x) (Pipeline.bitKeyOf coins.inputMacKey .x))
    (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountY .curveY
      (coins.inputDelta .y) (Pipeline.bitKeyOf coins.inputMacKey .y))
    (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountX .pointX
      (coins.inputDelta .x) (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .x))
    (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountY .pointY
      (coins.inputDelta .y) (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .y))
    ((Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      (Programs.transformKeyOf pads coins.inputMacKey) coins.exceptionPad).eval
        (tableAnswer (fixedTable v T)))

/-- **The garbler on a table publishes `tablePub`.** -/
theorem garbleM_tablePub (A : Table) (coins : Coins) :
    ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 =
      tablePub scalar coins (tablePads A coins) A.2.2.1 A.2.2.2 := by
  rw [garbleM_table]
  have gadget := eval_agree (Hidden.gadgetM_fixedOnly
      (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
      (Programs.transformKeyOf (tablePads A coins) coins.inputMacKey) coins.exceptionPad)
    (tableAnswer A) (tableAnswer (fixedTable A.2.2.1 A.2.2.2)) (by
      intro q fixed
      cases q with
      | fixedForward index input => rfl
      | _ => exact fixed.elim)
  unfold tablePub
  rw [← gadget]
  rfl

/-! ### 2. The lanes on the table's oracle -/

section Lanes

variable (v : OtherIndex → Block) (T : Tape) (lane : Lane) (delta : Block)
  (bitKey : Fin coordinateBitCount → Block × Block)

theorem laneMasks_fixed (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (laneCount lane) lane delta bitKey).masks
      chunk switch element = masksOf T ⟨lane, chunk, switch, element⟩ := by
  show sampleFp (hash _ (siteIndex (laneCell lane chunk switch element 0)) _)
    (hash _ (siteIndex (laneCell lane chunk switch element 1)) _)
    (hash _ (siteIndex (laneCell lane chunk switch element 2)) _) = _
  rw [hash_tableOracle_site, hash_tableOracle_site, hash_tableOracle_site]
  rfl

theorem laneOffsets_fixed (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (laneCount lane) lane delta bitKey).offsets
      element = ∑ c : Fin chunkCount, ∑ switch : Fin (2 ^ chunkWidth c),
        iota _ switch * masksOf T ⟨lane, c, switch, element⟩ := by
  unfold Programs.LaneTables.offsets
  simp only [laneMasks_fixed]

theorem laneScaleJoins_fixed (slopes : Fin (laneCount lane) → BaseField) (chunk : Fin chunkCount)
    (element : Fin (laneCount lane)) :
    (Programs.laneTables (tableOracle (fixedTable v T)) (laneCount lane) lane delta bitKey).scaleJoins
      slopes chunk element = (∑ switch : Fin (2 ^ chunkWidth chunk),
        masksOf T ⟨lane, chunk, switch, element⟩) + slopes element * weight chunk := by
  unfold Programs.LaneTables.scaleJoins
  simp only [laneMasks_fixed]
  rfl

/-- **The fold join of a (lane, chunk)** from the other answers: the four gate halves of step `1`
and the bit-`1` zero label. -/
def foldJoin (chunk : Fin chunkCount) (zero : Block) : Block :=
  ((v (hotOther lane chunk 1 0 false) ^^^ v (hotOther lane chunk 1 0 true)) ^^^
    (v (hotOther lane chunk 1 1 false) ^^^ v (hotOther lane chunk 1 1 true))) ^^^ zero

/-- The bit-`1` zero label of a chunk. -/
def zeroOne (chunk : Fin chunkCount) : Block :=
  labelAt (fun position => (chunkKey bitKey chunk position).1) 1

theorem garbleFold_two_join (chunk : Fin chunkCount) (zeroLabel : Nat → Block) :
    ∀ w, w = 2 → (garbleFold (tableOracle (fixedTable v T)) lane chunk delta zeroLabel w).2 1 =
      foldJoin v lane chunk (zeroLabel 1) := by
  intro w hw
  subst hw
  show stepJoin 1 (zeroLabel 1) (garbleStep (tableOracle (fixedTable v T)) lane chunk 1 (zeroLabel 1)
    (garbleFold (tableOracle (fixedTable v T)) lane chunk delta zeroLabel 1).1) = _
  unfold stepJoin
  rw [xorFold_two]
  show (foldMask _ lane chunk 1 0 _ ^^^ foldMask _ lane chunk 1 1 _) ^^^ zeroLabel 1 = _
  unfold foldMask
  rw [show hotIndexNat lane chunk 1 0 false = (hotOther lane chunk 1 0 false).1 from rfl,
    show hotIndexNat lane chunk 1 0 true = (hotOther lane chunk 1 0 true).1 from rfl,
    show hotIndexNat lane chunk 1 1 false = (hotOther lane chunk 1 1 false).1 from rfl,
    show hotIndexNat lane chunk 1 1 true = (hotOther lane chunk 1 1 true).1 from rfl,
    hash_tableOracle_other, hash_tableOracle_other, hash_tableOracle_other, hash_tableOracle_other]
  rfl

/-- **A lane's published fold joins** on the table's oracle. -/
theorem laneHotJoins_fixed (count : Nat) :
    (Programs.laneTables (tableOracle (fixedTable v T)) count lane delta bitKey).hotJoins =
      foldVector fun chunk => foldJoin v lane chunk (zeroOne bitKey chunk) := by
  apply Vector.ext
  intro slot bound
  show (Programs.laneTables _ count lane delta bitKey).hotJoins.get ⟨slot, bound⟩ =
    (foldVector _).get ⟨slot, bound⟩
  rw [foldVector, Vector.get_ofFn]
  unfold Programs.LaneTables.hotJoins flattenHot
  rw [Vector.get_ofFn]
  have width := Hidden.chunkWidth_eq_two (slotChunk ⟨slot, bound⟩)
  have offset : slotOffset ⟨slot, bound⟩ = 0 := by simp [slotOffset, chunkBits, Nat.mod_one]
  have inRange : slotOffset ⟨slot, bound⟩ < chunkWidth (slotChunk ⟨slot, bound⟩) - 1 := by
    rw [offset, width]; omega
  beta_reduce
  rw [dif_pos inRange]
  show (Vector.ofFn fun position : Fin (chunkWidth (slotChunk ⟨slot, bound⟩) - 1) =>
    (garbleFold _ lane _ delta _ (chunkWidth (slotChunk ⟨slot, bound⟩))).2 (position.val + 1)).get
      ⟨slotOffset ⟨slot, bound⟩, inRange⟩ = _
  rw [Vector.get_ofFn]
  simp only [offset, Nat.zero_add]
  exact garbleFold_two_join v T lane delta _ _ _ width

end Lanes

/-! ### 3. The hidden answers split off -/

section Hidden

variable (input : AffineInput)

/-- The other answers with the hidden ones zeroed. -/
def zeroHidden (rest : RestIdx input → Block) : OtherIndex → Block :=
  (splitAlong (hiddenIdx input) (hiddenIdx_injective input)).symm (fun _ => 0, rest)

theorem zeroHidden_of_hidden (rest : RestIdx input → Block) (h : HiddenIdx) :
    zeroHidden input rest (hiddenIdx input h) = 0 :=
  splitAlong_symm_image _ _ _ _ h

theorem zeroHidden_of_rest (v : OtherIndex → Block) (i : OtherIndex)
    (notHidden : i ∉ Set.range (hiddenIdx input)) :
    zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2 i = v i :=
  splitAlong_symm_rest _ _ _ _ ⟨i, notHidden⟩

theorem xor_bits (a b : Block) (same : ∀ i, a.getLsbD i = b.getLsbD i) : a = b :=
  BitVec.eq_of_getLsbD_eq fun i _ => same i

theorem hot_not_hidden (lane : Lane) (chunk : Fin chunkCount) (e : Nat) (small : e < 2) (half : Bool)
    (off : ¬ (e = activeBit input lane chunk ∧ half = false)) :
    hotOther lane chunk 1 e half ∉ Set.range (hiddenIdx input) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;>
    simp only [hiddenIdx, hotOther, gadgetOther, Subtype.mk.injEq, hotIndexNat, FixedIndex.hot.injEq,
      reduceCtorEq] at same
  obtain ⟨rfl, rfl, -, entry, rfl⟩ := same
  have bound := activeBit_lt input ℓ c
  simp only [Fin.mk.injEq, chunkBits] at entry
  apply off
  refine ⟨?_, rfl⟩
  omega

/-- **A fold join is its hidden gate half XOR the rest.** -/
theorem foldJoin_split (v : OtherIndex → Block) (lane : Lane) (chunk : Fin chunkCount) (zero : Block) :
    foldJoin v lane chunk zero = v (hiddenIdx input (.inl (lane, chunk))) ^^^
      foldJoin (zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2)
        lane chunk zero := by
  have values : ∀ e (small : e < 2) half, ¬ (e = activeBit input lane chunk ∧ half = false) →
      zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2
        (hotOther lane chunk 1 e half) = v (hotOther lane chunk 1 e half) :=
    fun e small half off => zeroHidden_of_rest input v _ (hot_not_hidden input lane chunk e small half off)
  have hidden : zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2
      (hotOther lane chunk 1 (activeBit input lane chunk) false) = 0 :=
    zeroHidden_of_hidden input _ (.inl (lane, chunk))
  have which := activeBit_lt input lane chunk
  unfold foldJoin
  show _ = v (hotOther lane chunk 1 (activeBit input lane chunk) false) ^^^ _
  rcases (show activeBit input lane chunk = 0 ∨ activeBit input lane chunk = 1 by omega) with a | a
  · rw [a] at hidden ⊢
    rw [hidden, values 0 (by omega) true (by simp), values 1 (by omega) false (by simp [a]),
      values 1 (by omega) true (by simp)]
    refine xor_bits _ _ fun i => ?_
    simp only [BitVec.getLsbD_xor]
    cases (v (hotOther lane chunk 1 0 false)).getLsbD i <;> simp
  · rw [a] at hidden ⊢
    rw [hidden, values 0 (by omega) false (by simp [a]), values 0 (by omega) true (by simp),
      values 1 (by omega) true (by simp)]
    refine xor_bits _ _ fun i => ?_
    simp only [BitVec.getLsbD_xor]
    cases (v (hotOther lane chunk 1 1 false)).getLsbD i <;>
      cases (v (hotOther lane chunk 1 0 false)).getLsbD i <;> simp

/-- A gadget position, as an other index. -/
def gadgetAt (output : Fin digitCount) (κ : Coord) (index : Fin coordinateBitCount) : OtherIndex :=
  ⟨.gadget output κ index, by
    rintro ⟨site, same⟩
    simp only [siteIndex, scaleIndexOf, scaleIndexNat] at same
    cases same⟩

/-- **A digit's gadget digest** at some labels, from the other answers. -/
def digest (v : OtherIndex → Block) (output : Fin digitCount) (mac : InputMac) : Block :=
  xorFold (fun index : Fin coordinateBitCount => v (gadgetAt output .x index) ^^^ mac.x.get index) ^^^
    xorFold (fun index : Fin coordinateBitCount => v (gadgetAt output .y index) ^^^ mac.y.get index)

theorem gadget_not_hidden (output : Fin digitCount) (κ : Coord) (index : Fin coordinateBitCount)
    (off : ¬ (κ = .x ∧ index.val = 0)) : gadgetAt output κ index ∉ Set.range (hiddenIdx input) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;> have value := congrArg Subtype.val same <;>
    simp only [hiddenIdx, hotOther, gadgetOther, gadgetAt, hotIndexNat] at value
  · cases value
  · injection value with outputEq coordEq position
    subst coordEq
    exact off ⟨rfl, (congrArg Fin.val position).symm⟩

theorem xorFold_split {count : Nat} (skip : Fin count) (family : Fin count → Block) :
    xorFold family = xorFoldExcept skip family ^^^ family skip := by
  rw [xorFoldExcept_eq, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **A digest is its hidden gadget answer XOR the rest.** -/
theorem digest_split (v : OtherIndex → Block) (output : Fin digitCount) (mac : InputMac) :
    digest v output mac = v (hiddenIdx input (.inr output)) ^^^
      digest (zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2)
        output mac := by
  set w := zeroHidden input (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2
  have zeroIndex : (0 : Nat) < coordinateBitCount := by decide
  let first : Fin coordinateBitCount := ⟨0, zeroIndex⟩
  have hiddenAt : gadgetAt output .x first = hiddenIdx input (.inr output) := rfl
  have atHidden : w (gadgetAt output .x first) = 0 := by
    rw [hiddenAt]
    exact zeroHidden_of_hidden input _ _
  have restX : ∀ index : Fin coordinateBitCount, index ≠ first →
      w (gadgetAt output .x index) = v (gadgetAt output .x index) := fun index off =>
    zeroHidden_of_rest input v _ (gadget_not_hidden input output .x index
      (fun h => off (Fin.ext h.2)))
  have restY : ∀ index : Fin coordinateBitCount,
      w (gadgetAt output .y index) = v (gadgetAt output .y index) := fun index =>
    zeroHidden_of_rest input v _ (gadget_not_hidden input output .y index (fun h => by cases h.1))
  unfold digest
  rw [xorFold_split first, xorFold_split first (fun index => w (gadgetAt output .x index) ^^^ _),
    Programs.xorFoldExcept_congr first (fun index => w (gadgetAt output .x index) ^^^ _)
      (fun index => v (gadgetAt output .x index) ^^^ mac.x.get index)
      (fun index off => by rw [restX index off])]
  simp only [atHidden, restY, ← hiddenAt]
  refine xor_bits _ _ fun i => ?_
  simp only [BitVec.getLsbD_xor]
  cases (v (gadgetAt output .x first)).getLsbD i <;> simp

end Hidden

/-! ### 4. The gadget on a table -/

section Gadget

theorem gadgetDigestM_table (v : OtherIndex → Block) (T : Tape) (output : Fin digitCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    (Programs.gadgetDigestM output coordinate mac).eval (tableAnswer (fixedTable v T)) =
      xorFold (fun index : Fin coordinateBitCount =>
        v (gadgetAt output (Pipeline.gadgetCoord coordinate) index) ^^^ mac.get index) := by
  simp only [Programs.gadgetDigestM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn]
  show Fin.foldl coordinateBitCount (fun acc index => acc ^^^
    (Programs.hashM (gadgetAt output (Pipeline.gadgetCoord coordinate) index).1 (mac.get index)).eval
      (tableAnswer (fixedTable v T))) 0 = _
  simp only [hashM_table_other]
  rfl

/-- A digit's gadget entry from the other answers. -/
def entryOf (v : OtherIndex → Block) (output : Fin digitCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pad
  | some phi => Exception.writeEntry pad
      (Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
      (Exception.lowByte (digest v output
        (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates))) ^^^
        Exception.digitCode key.digit)

theorem garbleEntryM_table (v : OtherIndex → Block) (T : Tape) (output : Fin digitCount)
    (key : OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (Programs.garbleEntryM output key inputKey pad).eval (tableAnswer (fixedTable v T)) =
      entryOf v output key inputKey pad := by
  unfold Programs.garbleEntryM entryOf
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, Programs.gadgetMaskM,
        gadgetDigestM_table]
      rfl

end Gadget

/-! ### 5. The lanes' offsets and joins are F4's -/

section Elements

variable (v : OtherIndex → Block) (T : Tape)

theorem maskSiteEquiv_curveX (masks : MaskSite → BaseField) (element : CurveXElement)
    (cs : ChunkSwitch) :
    (maskSiteEquiv masks).2 (.inl element) cs = masks ⟨.curveX, cs.1, cs.2, curveXSlots element⟩ := by
  simp [maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply]

theorem maskSiteEquiv_curveY (masks : MaskSite → BaseField) (element : CurveYElement)
    (cs : ChunkSwitch) :
    (maskSiteEquiv masks).2 (.inr element) cs = masks ⟨.curveY, cs.1, cs.2, curveYSlots element⟩ := by
  simp [maskSiteEquiv, maskSiteSplit, laneSlots, Equiv.arrowCongr_apply]

/-- **The curve lanes' offsets are F4's curve offsets.** -/
theorem curveValues_fixed (dx dy : Block) (kx ky : Fin coordinateBitCount → Block × Block) :
    Pipeline.curveValues
        (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountX .curveX dx kx).offsets
        (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountY .curveY dy ky).offsets =
      curveOffsets (maskSiteEquiv (masksOf T)).2 := by
  funext element
  rcases element with e | e
  · refine (laneOffsets_fixed v T .curveX dx kx (curveXSlots e)).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (masksOf T)).2 (.inl e) ⟨c, j⟩
    simp only [maskSiteEquiv_curveX]
  · refine (laneOffsets_fixed v T .curveY dy ky (curveYSlots e)).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (masksOf T)).2 (.inr e) ⟨c, j⟩
    simp only [maskSiteEquiv_curveY]

/-- **The point lanes' offsets are F4's digit offsets.** -/
theorem digitValues_fixed (dx dy : Block) (kx ky : Fin coordinateBitCount → Block × Block)
    (d : Fin digitCount) :
    Pipeline.digitValues
        (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountX .pointX dx kx).offsets
        (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountY .pointY dy ky).offsets d =
      digitOffsets ((maskSiteEquiv (masksOf T)).1 d) := by
  funext element
  rcases element with e | e
  · refine (laneOffsets_fixed v T .pointX dx kx (pointXSlots (d, e))).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (masksOf T)).1 d (.inl e) ⟨c, j⟩
    simp only [maskSiteEquiv_pointX]
    rfl
  · refine (laneOffsets_fixed v T .pointY dy ky (pointYSlots (d, e))).trans ?_
    show _ = ∑ c : Fin chunkCount, ∑ j : Fin (2 ^ chunkWidth c),
      iota _ j * (maskSiteEquiv (masksOf T)).1 d (.inr e) ⟨c, j⟩
    simp only [maskSiteEquiv_pointY]
    rfl

theorem pointXJoins_fixed (dx : Block) (kx : Fin coordinateBitCount → Block × Block)
    (rand : Fin digitCount → RowRand) (slopes : Fin digitCount → Biquadratic.Values)
    (hs : ∀ d, slopes d = digitSlopes ((maskSiteEquiv (masksOf T)).1 d) (rand d))
    (chunk : Fin chunkCount) (slot : Fin pointElementCountX) :
    (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountX .pointX dx kx).scaleJoins
        (Pipeline.pointXAssemble slopes) chunk slot =
      digitJoins ((maskSiteEquiv (masksOf T)).1 (pointXSlots.symm slot).1)
        (rand (pointXSlots.symm slot).1) (.inl (pointXSlots.symm slot).2) chunk := by
  obtain ⟨⟨d, e⟩, rfl⟩ := pointXSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .pointX dx kx _ chunk (pointXSlots (d, e))).trans ?_
  have slope : Pipeline.pointXAssemble slopes (pointXSlots (d, e)) = slopes d (.inl e) :=
    Pipeline.pointXAssemble_digit slopes d e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk), (maskSiteEquiv (masksOf T)).1 d (.inl e) ⟨chunk, j⟩) +
    digitSlopes ((maskSiteEquiv (masksOf T)).1 d) (rand d) (.inl e) * weight chunk
  rw [slope, hs d]
  simp only [maskSiteEquiv_pointX]
  rfl

theorem pointYJoins_fixed (dy : Block) (ky : Fin coordinateBitCount → Block × Block)
    (rand : Fin digitCount → RowRand) (slopes : Fin digitCount → Biquadratic.Values)
    (hs : ∀ d, slopes d = digitSlopes ((maskSiteEquiv (masksOf T)).1 d) (rand d))
    (chunk : Fin chunkCount) (slot : Fin pointElementCountY) :
    (Programs.laneTables (tableOracle (fixedTable v T)) pointElementCountY .pointY dy ky).scaleJoins
        (Pipeline.pointYAssemble slopes) chunk slot =
      digitJoins ((maskSiteEquiv (masksOf T)).1 (pointYSlots.symm slot).1)
        (rand (pointYSlots.symm slot).1) (.inr (pointYSlots.symm slot).2) chunk := by
  obtain ⟨⟨d, e⟩, rfl⟩ := pointYSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .pointY dy ky _ chunk (pointYSlots (d, e))).trans ?_
  have slope : Pipeline.pointYAssemble slopes (pointYSlots (d, e)) = slopes d (.inr e) :=
    Pipeline.pointYAssemble_digit slopes d e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk), (maskSiteEquiv (masksOf T)).1 d (.inr e) ⟨chunk, j⟩) +
    digitSlopes ((maskSiteEquiv (masksOf T)).1 d) (rand d) (.inr e) * weight chunk
  rw [slope, hs d]
  simp only [maskSiteEquiv_pointY]
  rfl

theorem curveXJoins_fixed (dx : Block) (kx : Fin coordinateBitCount → Block × Block)
    (r1 r2 : BaseField) (slopes : CurveMembership.Values)
    (hs : slopes = curveSlopes (maskSiteEquiv (masksOf T)).2 r1 r2)
    (chunk : Fin chunkCount) (slot : Fin curveElementCountX) :
    (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountX .curveX dx kx).scaleJoins
        (Pipeline.curveXAssemble slopes) chunk slot =
      curveJoins (maskSiteEquiv (masksOf T)).2 r1 r2 (.inl (curveXSlots.symm slot)) chunk := by
  obtain ⟨e, rfl⟩ := curveXSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .curveX dx kx _ chunk (curveXSlots e)).trans ?_
  have slope : Pipeline.curveXAssemble slopes (curveXSlots e) = slopes (.inl e) :=
    Pipeline.curveXAssemble_slot slopes e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk), (maskSiteEquiv (masksOf T)).2 (.inl e) ⟨chunk, j⟩) +
    curveSlopes (maskSiteEquiv (masksOf T)).2 r1 r2 (.inl e) * weight chunk
  rw [slope, hs]
  simp only [maskSiteEquiv_curveX]

theorem curveYJoins_fixed (dy : Block) (ky : Fin coordinateBitCount → Block × Block)
    (r1 r2 : BaseField) (slopes : CurveMembership.Values)
    (hs : slopes = curveSlopes (maskSiteEquiv (masksOf T)).2 r1 r2)
    (chunk : Fin chunkCount) (slot : Fin curveElementCountY) :
    (Programs.laneTables (tableOracle (fixedTable v T)) curveElementCountY .curveY dy ky).scaleJoins
        (Pipeline.curveYAssemble slopes) chunk slot =
      curveJoins (maskSiteEquiv (masksOf T)).2 r1 r2 (.inr (curveYSlots.symm slot)) chunk := by
  obtain ⟨e, rfl⟩ := curveYSlots.surjective slot
  rw [Equiv.symm_apply_apply]
  refine (laneScaleJoins_fixed v T .curveY dy ky _ chunk (curveYSlots e)).trans ?_
  have slope : Pipeline.curveYAssemble slopes (curveYSlots e) = slopes (.inr e) :=
    Pipeline.curveYAssemble_slot slopes e
  show _ = (∑ j : Fin (2 ^ chunkWidth chunk), (maskSiteEquiv (masksOf T)).2 (.inr e) ⟨chunk, j⟩) +
    curveSlopes (maskSiteEquiv (masksOf T)).2 r1 r2 (.inr e) * weight chunk
  rw [slope, hs]
  simp only [maskSiteEquiv_curveY]

end Elements

/-! ### 6. F4's context off the curve, and the matching -/

section Context

variable (input : AffineInput) (pads : Programs.Pads)

/-- The label pairs of some zero labels and offsets (the coins' `inputMacKey`). -/
def labelKey (Z : Coord → Fin coordinateBitCount → Block) (Δ : Coord → Block) : InputMacKey where
  x := Vector.ofFn fun position => { falseLabel := Z .x position, trueLabel := Z .x position ^^^ Δ .x }
  y := Vector.ofFn fun position => { falseLabel := Z .y position, trueLabel := Z .y position ^^^ Δ .y }

/-- A lane's bit keys. -/
def laneKey (key : InputMacKey) : Lane → Fin coordinateBitCount → Block × Block
  | .curveX => Pipeline.bitKeyOf key .x
  | .curveY => Pipeline.bitKeyOf key .y
  | .pointX => Pipeline.bitKeyOf (Programs.whitenKeyOf pads key) .x
  | .pointY => Pipeline.bitKeyOf (Programs.whitenKeyOf pads key) .y

/-- **F4's context off the curve**, from the output keys and the rest: the true rows and `ρ`, the
fold joins and the digests with the hidden answers zeroed, the gadget slots and codes. (The keys
are a parameter so that no proof ever unfolds the scalar's digits.) -/
def offContext (keys : OutputKeys) (o : Outer input) : JointContext where
  rows d := Coordinates.rows (keys.get d).offset.coordinates
    (digitEndomorphismBase (keys.get d).digit) (o.2.1 d).value
  rho d := o.2.1 d
  foldVisible _ lane chunk := foldJoin (zeroHidden input o.2.2.2.2) lane chunk
    (zeroOne (laneKey pads (labelKey o.2.2.1 o.2.2.2.1) lane) chunk)
  gadgetVisible _ d := match digitEndomorphismBase (keys.get d).digit with
    | none => 0
    | some phi => digest (zeroHidden input o.2.2.2.2) d
        ((Programs.transformKeyOf pads (labelKey o.2.2.1 o.2.2.2.1)).encodeAffine
          (Exception.exceptionalInput phi (keys.get d).offset.coordinates))
  gadgetSlot d := (digitEndomorphismBase (keys.get d).digit).map fun phi =>
    Exception.exceptionIndex (Exception.exceptionalInput phi (keys.get d).offset.coordinates)
  gadgetCode d := Exception.digitCode (keys.get d).digit

theorem public_ext {a b : Public} (curve : a.curve = b.curve) (rows : a.rows = b.rows)
    (exception : a.exception = b.exception) (cx : a.curveXHot = b.curveXHot)
    (cy : a.curveYHot = b.curveYHot) (px : a.pointXHot = b.pointXHot) (py : a.pointYHot = b.pointYHot)
    (scale : a.scale = b.scale) : a = b := by
  cases a
  cases b
  simp only at curve rows exception cx cy px py scale
  subst curve rows exception cx cy px py scale
  rfl

theorem entryOf_gadgetEntry (v : OtherIndex → Block) (d : Fin digitCount) (key : OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) :
    entryOf v d key inputKey pad = gadgetEntry
      ((digitEndomorphismBase key.digit).map fun phi =>
        Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
      (Exception.digitCode key.digit)
      (match digitEndomorphismBase key.digit with
        | none => 0
        | some phi => digest (zeroHidden input (splitAlong (hiddenIdx input)
            (hiddenIdx_injective input) v).2) d
              (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates)))
      pad (v (hiddenIdx input (.inr d))) := by
  unfold entryOf
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      show Exception.writeEntry pad _ (Exception.lowByte (digest v d _) ^^^ _) =
        Exception.writeEntry pad _ (Exception.lowByte (_ ^^^ _) ^^^ _)
      rw [digest_split input v d]

theorem cellsSource_exception (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.exception = Vector.ofFn cells.2.2.2 := rfl

theorem cellsSource_hot (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.curveXHot = foldVector (cells.2.2.1 .curveX) ∧
    (cellsSource cells key).publicValue.curveYHot = foldVector (cells.2.2.1 .curveY) ∧
    (cellsSource cells key).publicValue.pointXHot = foldVector (cells.2.2.1 .pointX) ∧
    (cellsSource cells key).publicValue.pointYHot = foldVector (cells.2.2.1 .pointY) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem cellsSource_scale (cells : PublicCells) (key : InputMacKey) :
    (cellsSource cells key).publicValue.scale =
      Vector.ofFn fun chunk => pack (cellsJoins cells chunk) := rfl

theorem assemble_exception (keys : OutputKeys) (pR : Randomness) (t : BaseField) (mask : NonZeroBase)
    (r1 r2 : BaseField) (cx : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY) (g : Vector Exception.Entry outputMacCount) :
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).exception = g := rfl

theorem assemble_hot (keys : OutputKeys) (pR : Randomness) (t : BaseField) (mask : NonZeroBase)
    (r1 r2 : BaseField) (cx : Programs.LaneTables curveElementCountX)
    (cy : Programs.LaneTables curveElementCountY) (px : Programs.LaneTables pointElementCountX)
    (py : Programs.LaneTables pointElementCountY) (g : Vector Exception.Entry outputMacCount) :
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).curveXHot = cx.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).curveYHot = cy.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).pointXHot = px.hotJoins ∧
    (Programs.assemble keys pR t mask r1 r2 cx cy px py g).pointYHot = py.hotJoins :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The garbler's published value on a table is the source of F4's published cells.** -/
theorem tablePub_cells (coins : Coins) (v : OtherIndex → Block) (T : Tape) (key : InputMacKey)
    (keys : OutputKeys) (keysEq : FieldMacToECMac.outputKeys construction scalar.value coins.offsets = keys) :
    tablePub scalar coins pads v T =
      (cellsSource (publicOf (offContext input pads keys (omegaEquiv input (coins, v, masksOf T)).1)
        (omegaEquiv input (coins, v, masksOf T)).2) key).publicValue := by
  unfold tablePub
  rw [keysEq]
  have outerEq : (omegaEquiv input (coins, v, masksOf T)).1 =
      (⟨coins.offsets, coins.offsetsClamped⟩, fun d => (coins.pointRandomness.get d).rho,
        coins.inputZero, coins.inputDelta,
        (splitAlong (hiddenIdx input) (hiddenIdx_injective input) v).2) := rfl
  have coinsEq : (omegaEquiv input (coins, v, masksOf T)).2 =
      (fun d => ((maskSiteEquiv (masksOf T)).1 d, ((coins.pointRandomness.get d).x,
          (coins.pointRandomness.get d).y, (coins.pointRandomness.get d).z)),
        ((maskSiteEquiv (masksOf T)).2, coins.bridgeKey,
          ⟨coins.curveMask.value, coins.curveMask.nonzero⟩, coins.curveR1, coins.curveR2),
        (fun ℓ c => v (hiddenIdx input (.inl (ℓ, c))),
          fun d => (coins.exceptionPad.get d, v (hiddenIdx input (.inr d))))) := rfl
  rw [outerEq, coinsEq]
  have keyEq : labelKey coins.inputZero coins.inputDelta = coins.inputMacKey := rfl
  set O := tableOracle (fixedTable v T)
  set m := masksOf T
  set PX := Programs.laneTables O pointElementCountX .pointX (coins.inputDelta .x)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .x)
  set PY := Programs.laneTables O pointElementCountY .pointY (coins.inputDelta .y)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf pads coins.inputMacKey) .y)
  have digitK : ∀ d, Pipeline.digitValues PX.offsets PY.offsets d =
      digitOffsets ((maskSiteEquiv m).1 d) := fun d => digitValues_fixed v T _ _ _ _ d
  have curveK := curveValues_fixed v T (coins.inputDelta .x) (coins.inputDelta .y)
    (Pipeline.bitKeyOf coins.inputMacKey .x) (Pipeline.bitKeyOf coins.inputMacKey .y)
  apply public_ext
  · change CurveMembership.garble _ _ _ _ _ = CurveMembership.garble _ _ _ _ _
    rw [curveK]
  · change Vector.ofFn _ = Vector.ofFn _
    refine congrArg Vector.ofFn (funext fun d => ?_)
    change garbleRow _ _ _ = garbleRow _ _ _
    beta_reduce
    rw [digitK]
    have rowsGet : ∀ i : Fin outputMacCount,
        (FieldMacToECMac.rowsForOutputKeys keys coins.pointRandomness).get i =
          Coordinates.rows (keys.get i).offset.coordinates (digitEndomorphismBase (keys.get i).digit)
            (coins.pointRandomness.get i).rho.value := by
      intro i
      unfold FieldMacToECMac.rowsForOutputKeys
      exact Vector.get_ofFn _ i
    rw [rowsGet d]
    rfl
  · rw [assemble_exception, cellsSource_exception]
    unfold Programs.gadgetM
    rw [FreeQuery.eval_vector]
    refine ofFn_congr_digit _ _ fun d => ?_
    rw [garbleEntryM_table, entryOf_gadgetEntry input v d]
    rfl
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).1, (cellsSource_hot _ _).1, laneHotJoins_fixed]
    exact congrArg foldVector (funext fun c => foldJoin_split input v .curveX c _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.1, (cellsSource_hot _ _).2.1, laneHotJoins_fixed]
    exact congrArg foldVector (funext fun c => foldJoin_split input v .curveY c _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.1, (cellsSource_hot _ _).2.2.1, laneHotJoins_fixed]
    exact congrArg foldVector (funext fun c => foldJoin_split input v .pointX c _)
  · rw [(assemble_hot _ _ _ _ _ _ _ _ _ _ _).2.2.2, (cellsSource_hot _ _).2.2.2, laneHotJoins_fixed]
    exact congrArg foldVector (funext fun c => foldJoin_split input v .pointY c _)
  · have pointSlopes : ∀ d : Fin digitCount, Biquadratic.slopes (coins.pointRandomness.get d).x
        (coins.pointRandomness.get d).y (coins.pointRandomness.get d).z
          (Pipeline.digitValues PX.offsets PY.offsets d) =
        digitSlopes ((maskSiteEquiv m).1 d) ((coins.pointRandomness.get d).x,
          (coins.pointRandomness.get d).y, (coins.pointRandomness.get d).z) := by
      intro d
      rw [digitK]
      rfl
    have curveSlopesEq : CurveMembership.slopes coins.curveR1 coins.curveR2
        (Pipeline.curveValues
          (Programs.laneTables O curveElementCountX .curveX (coins.inputDelta .x)
            (Pipeline.bitKeyOf coins.inputMacKey .x)).offsets
          (Programs.laneTables O curveElementCountY .curveY (coins.inputDelta .y)
            (Pipeline.bitKeyOf coins.inputMacKey .y)).offsets) =
        curveSlopes (maskSiteEquiv m).2 coins.curveR1 coins.curveR2 := by
      rw [curveK]
      rfl
    change Vector.ofFn _ = Vector.ofFn _
    refine congrArg Vector.ofFn (funext fun chunk => congrArg pack ?_)
    show Pipeline.assembleWord _ _ _ _ = Pipeline.assembleWord _ _ _ _
    congr 1 <;> funext slot
    · exact pointXJoins_fixed v T _ _ _ _ pointSlopes chunk slot
    · exact curveXJoins_fixed v T _ _ _ _ _ curveSlopesEq chunk slot
    · exact pointYJoins_fixed v T _ _ _ _ pointSlopes chunk slot
    · exact curveYJoins_fixed v T _ _ _ _ _ curveSlopesEq chunk slot

end Context

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
