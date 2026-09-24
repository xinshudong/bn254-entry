/-
**Phase 3, P1e — the gadget's label collision (a counter-shape to P1d's per-shape core).**

P1d's plan for the middle game `M` of `G1U → HW` flags a stage-1 touch or the **doubling** event
(`u` is a nonzero digit's exceptional input) and otherwise asks the per-shape core to identify
`G1U`'s stage-2 entry map, *as a lookup map*, with the simulator's path and a shadow. That core is
false: `G1U`'s visible set (`visibleEntries`: the garbler's entries whose query the evaluator's
reach asks, on the tape) also contains **collision** entries, and one family of them reveals the
digit off the doubling event.

**The collision.** The gadget labels are *bit-dependent* transforms of the Lamport labels
(`transformKeyOf`, `EncPRF.transformAt`): at position `i` the bit-`b` label is
`pad_b(i) xor Z_i xor b·Δ` with `pad_b(i) = π_i(k1 xor b) xor k2`. When
`pad_0(i) xor pad_1(i) = Δ` — that is `π_i(k1) xor π_i(k1 xor 1) = Δ`
(`evenMansourPad_xor`), mass `1/(2^128−1)` per position for `Δ ≠ 0` — the two labels of position `i`
**coincide** (`transformKey_label_collide`). Then:

* the evaluator's gadget labels at any input `u` that differs from the exceptional input `exc_d`
  only at colliding positions **are** the garbler's labels of `exc_d`
  (`transformKey_encode_eq_of_collision`, `transformMac_eq_of_collision`): all `508` gadget queries
  of digit `d` are visible and installed in `G1U`, exactly as at the exceptional input;
* the evaluator's mask is then the garbler's, and the exceptional slot of the published entry
  unlocks `k_d` (`garbleEntry_unlock_of_encode_eq`) — the adversary reads all six slots, so the
  slot of `u` itself is irrelevant.

`HW` never reveals `k_d` (its published gadget is uniform and never read by the simulator). So the
flag of any middle game must contain the **generalised exceptional event**
`∃ nonzero d, ∀ i, u_i = exc_{d,i} ∨ collide_i`, not only the doubling event — the model form is
`PublicFirst.plan_not_flagMono` (in `PublicFirst.lean`). Off that event the collisions still add
visible gadget entries (mass `≈ 508/2^128 ≫ 182/(r−1)`), which `M` must *mirror* (a coupled `Δ`),
not flag.
-/

import Construction.OraclePrograms

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography Kriterion.ArgoMAC

/-- **The Even–Mansour pads of the two bits differ by the two permutation images**: the whitening
key `k2` cancels, so the pads collide with `Δ` exactly when `π_i(k1) xor π_i(k1 xor 1) = Δ`. -/
theorem evenMansourPad_xor (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    EncPRF.evenMansourPad oracle keys { coordinate, index, bit := false }
        ^^^ EncPRF.evenMansourPad oracle keys { coordinate, index, bit := true }
      = oracle.permutation (coordinate, index) (encodeBit false ^^^ keys.first)
        ^^^ oracle.permutation (coordinate, index) (encodeBit true ^^^ keys.first) := by
  simp only [EncPRF.evenMansourPad, evenMansour, Cryptography.xor]
  generalize oracle.permutation (coordinate, index) (encodeBit false ^^^ keys.first) = first
  generalize oracle.permutation (coordinate, index) (encodeBit true ^^^ keys.first) = second
  refine BitVec.eq_of_getLsbD_eq fun position _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases first.getLsbD position <;> cases second.getLsbD position <;>
    cases keys.second.getLsbD position <;> rfl

/-- **The collision of one position**: pads differing by `Δ` send the two labels of a
`Δ`-structured pair to the same transformed label. -/
theorem encrypt_collide (padFalse padTrue label delta : Block)
    (collide : padFalse ^^^ padTrue = delta) :
    encrypt padFalse label = encrypt padTrue (label ^^^ delta) := by
  subst collide
  simp only [encrypt, Cryptography.xor]
  refine BitVec.eq_of_getLsbD_eq fun position _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases padFalse.getLsbD position <;> cases padTrue.getLsbD position <;>
    cases label.getLsbD position <;> rfl

/-- A `Δ`-structured coordinate key (the construction's `Coins.inputMacKey`: `(Z_i, Z_i xor Δ)`). -/
def Structured (key : CoordinateMacKey) (delta : Block) : Prop :=
  ∀ index : Fin coordinateBitCount, key[index.val].trueLabel = key[index.val].falseLabel ^^^ delta

/-- The construction's label pairs are `Δ`-structured (`Scheme.Coins.inputMacKey`). -/
theorem coins_structured_x (coins : Scheme.Coins) :
    Structured coins.inputMacKey.x (coins.inputDelta .x) := by
  intro index
  simp [Scheme.Coins.inputMacKey]

theorem coins_structured_y (coins : Scheme.Coins) :
    Structured coins.inputMacKey.y (coins.inputDelta .y) := by
  intro index
  simp [Scheme.Coins.inputMacKey]

/-- The transformed labels of one coordinate (`Programs.transformKeyOf`, one coordinate). -/
theorem transformKeyOf_x (pads : Programs.Pads) (key : InputMacKey) (index : Fin coordinateBitCount) :
    (Programs.transformKeyOf pads key).x[index.val] =
      { falseLabel := encrypt (pads .x index false) key.x[index.val].falseLabel
        trueLabel := encrypt (pads .x index true) key.x[index.val].trueLabel } := by
  simp [Programs.transformKeyOf]

theorem transformKeyOf_y (pads : Programs.Pads) (key : InputMacKey) (index : Fin coordinateBitCount) :
    (Programs.transformKeyOf pads key).y[index.val] =
      { falseLabel := encrypt (pads .y index false) key.y[index.val].falseLabel
        trueLabel := encrypt (pads .y index true) key.y[index.val].trueLabel } := by
  simp [Programs.transformKeyOf]

/-- **The two transformed labels of a colliding position coincide.** -/
theorem transformKey_label_collide (padFalse padTrue delta : Block) (label : BitAdaptor.Key)
    (structured : label.trueLabel = label.falseLabel ^^^ delta)
    (collide : padFalse ^^^ padTrue = delta) :
    encrypt padFalse label.falseLabel = encrypt padTrue label.trueLabel := by
  rw [structured]
  exact encrypt_collide padFalse padTrue label.falseLabel delta collide

/-- Two bit words select the same labels of a coordinate key when every differing position has
equal labels. -/
theorem encodeCoordinate_eq (key : CoordinateMacKey) (first second : BitVec coordinateBitCount)
    (same : ∀ index : Fin coordinateBitCount, first.getLsb index ≠ second.getLsb index →
      key[index.val].falseLabel = key[index.val].trueLabel) :
    encodeCoordinate key first = encodeCoordinate key second := by
  apply Vector.ext
  intro index bound
  simp only [encodeCoordinate, Vector.getElem_ofFn]
  by_cases agree : first.getLsb ⟨index, bound⟩ = second.getLsb ⟨index, bound⟩
  · rw [agree]
  · have labels := same ⟨index, bound⟩ agree
    unfold BitAdaptor.encode
    cases hf : first.getLsb ⟨index, bound⟩ <;> cases hs : second.getLsb ⟨index, bound⟩ <;>
      simp_all

/-- **The gadget labels of two inputs coincide** when they differ only at colliding positions:
the evaluator at `second` asks exactly the garbler's gadget queries at `first`. -/
theorem transformKey_encode_eq_of_collision (pads : Programs.Pads) (key : InputMacKey)
    (deltaX deltaY : Block) (structuredX : Structured key.x deltaX)
    (structuredY : Structured key.y deltaY) (first second : BitInput)
    (collideX : ∀ index : Fin coordinateBitCount, first.xBits.getLsb index ≠ second.xBits.getLsb index →
      pads .x index false ^^^ pads .x index true = deltaX)
    (collideY : ∀ index : Fin coordinateBitCount, first.yBits.getLsb index ≠ second.yBits.getLsb index →
      pads .y index false ^^^ pads .y index true = deltaY) :
    (Programs.transformKeyOf pads key).encode first = (Programs.transformKeyOf pads key).encode second := by
  apply InputMac.ext
  · refine encodeCoordinate_eq _ _ _ fun index differ => ?_
    rw [transformKeyOf_x]
    exact transformKey_label_collide _ _ deltaX _ (structuredX index) (collideX index differ)
  · refine encodeCoordinate_eq _ _ _ fun index differ => ?_
    rw [transformKeyOf_y]
    exact transformKey_label_collide _ _ deltaY _ (structuredY index) (collideY index differ)

/-- **The evaluator's transformed labels are the garbler's labels of a colliding input**: at the
real pads, the evaluator's `transformMac` of its selected labels at `second` equals the garbler's
transformed key encoded at `first` (the construction's own `EncPRF.transformEncode`). -/
theorem transformMac_eq_of_collision (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) (deltaX deltaY : Block)
    (structuredX : Structured key.x deltaX) (structuredY : Structured key.y deltaY)
    (first second : BitInput)
    (collideX : ∀ index : Fin coordinateBitCount, first.xBits.getLsb index ≠ second.xBits.getLsb index →
      oracle.permutation (.x, index) (encodeBit false ^^^ keys.first)
        ^^^ oracle.permutation (.x, index) (encodeBit true ^^^ keys.first) = deltaX)
    (collideY : ∀ index : Fin coordinateBitCount, first.yBits.getLsb index ≠ second.yBits.getLsb index →
      oracle.permutation (.y, index) (encodeBit false ^^^ keys.first)
        ^^^ oracle.permutation (.y, index) (encodeBit true ^^^ keys.first) = deltaY) :
    EncPRF.transformMac oracle keys second (key.encode second)
      = (EncPRF.transformKey oracle keys key).encode first := by
  rw [EncPRF.transformEncode, ← Programs.transformKeyOf_realPads]
  refine (transformKey_encode_eq_of_collision _ key deltaX deltaY structuredX structuredY first
    second (fun index differ => ?_) (fun index differ => ?_)).symm
  · simp only [Programs.realPads]
    rw [evenMansourPad_xor]
    exact collideX index differ
  · simp only [Programs.realPads]
    rw [evenMansourPad_xor]
    exact collideY index differ

/-- **The gadget unlocks the digit at a colliding input**: when the evaluator's gadget labels at
`u` are the garbler's labels at the exceptional input, its mask is the garbler's, and the
exceptional slot of the published entry decodes to `k_d`. -/
theorem garbleEntry_unlock_of_encode_eq [FieldCertificate] (perms : FieldMacToECMac.GadgetPermutations)
    (output : Fin FieldMacToECMac.outputMacCount) (key : FieldMacToECMac.OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) (phi : BaseField)
    (selected : digitEndomorphismBase key.digit = some phi) (input : AffineInput)
    (same : inputKey.encodeAffine input
      = inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates)) :
    Exception.unlock (FieldMacToECMac.gadgetMask perms output (inputKey.encodeAffine input))
        (FieldMacToECMac.garbleEntry perms output key inputKey pad)
        (Exception.exceptionalInput phi key.offset.coordinates)
      = key.digit := by
  rw [same]
  simp only [FieldMacToECMac.garbleEntry, selected]
  exact Exception.unlock_writeEntry _ _ _ _

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
