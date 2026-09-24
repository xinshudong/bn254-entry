/-
**The replay, the designated chunk** — the designated prefix (`rtree_designatedPrefix`):
`j* = α ⊕ 1` to `tmpJStar`, `E* = E_{j*}` to `hotLabelBase + 4`, `κ = 1 − 2 · bit₀` to
`tmpKappa`; and `κ` is P3's `kappa` (`kappa_eq`).
-/

import Proof.Simulator.ReplayDesSwitch

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- `ι(α ⊕ 1) − ι(α) = 1 − 2 · (α mod 2)` for a two-bit switch. -/
theorem kappa_value (alpha : Nat) (small : alpha < 4) :
    ((alpha ^^^ 1 : Nat) : BaseField) - (alpha : BaseField) =
      1 - (((alpha % 2 : Nat) : BaseField) + ((alpha % 2 : Nat) : BaseField)) := by
  interval_cases alpha <;>
    simp only [show (0 : Nat) ^^^ 1 = 1 from rfl, show (1 : Nat) ^^^ 1 = 0 from rfl,
      show (2 : Nat) ^^^ 1 = 3 from rfl, show (3 : Nat) ^^^ 1 = 2 from rfl] <;> norm_num

theorem word_xor_one (alpha : Nat) (small : alpha < 4) :
    Arithmetic.xor.eval (word alpha) (word 1) = word (alpha ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  have xorSmall : alpha ^^^ 1 < 2 ^ 256 := lt_trans (Nat.xor_lt_two_pow (show alpha < 2 ^ 2 by omega)
    (by norm_num)) (by norm_num)
  simp only [Arithmetic.eval, BitVec.toNat_xor, word_small (show alpha < 2 ^ 256 by omega),
    word_small (show 1 < 2 ^ 256 by norm_num), word_small xorSmall]

theorem word_add_small (first second : Nat) (small : first + second < 2 ^ 256) :
    Arithmetic.add.eval (word first) (word second) = word (first + second) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_add, word_small small,
    word_small (show first < 2 ^ 256 by omega), word_small (show second < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt small]

theorem rtree_load_seq (target address : Register) (rest : Prog) (memory : Memory) :
    rtree (.seq (.op (.load target address)) rest) memory =
      rtree rest (setReg memory target (memory.ram (memory.registers address))) := rfl

/-- What the designated prefix leaves. -/
def DesPrefixPost (memory : Memory) (jstar : Nat) (star : Block) (kappaValue : BaseField)
    (after : Memory) : Prop :=
  after.ram = Function.update (Function.update (Function.update memory.ram (word tmpJStar)
      (word jstar)) (word (hotLabelBase + 4)) (blockWord star)) (word tmpKappa) (fieldWord kappaValue) ∧
    after.bits = memory.bits

/-- **The designated prefix.** -/
theorem rtree_designatedPrefix (memory : Memory) (alpha : Nat) (alphaSmall : alpha < 4)
    (star : Block) (alphaCell : memory.ram (word tmpAlpha) = word alpha)
    (bitCell : memory.ram (word tmpBit0) = word (alpha % 2))
    (starCell : memory.ram (word (hotLabelBase + (alpha ^^^ 1))) = blockWord star) :
    ∃ after, rtree Replay.designatedPrefix memory = .pure (some after) ∧
      DesPrefixPost memory (alpha ^^^ 1) star
        (1 - (((alpha % 2 : Nat) : BaseField) + ((alpha % 2 : Nat) : BaseField))) after := by
  have xorSmall : alpha ^^^ 1 < 4 := Nat.xor_lt_two_pow (show alpha < 2 ^ 2 by omega) (by norm_num)
  have jstarHot : word tmpJStar ≠ word (hotLabelBase + (alpha ^^^ 1)) :=
    (hotLabel_ne_tmp (alpha ^^^ 1) 6 (by omega) (by omega)).symm
  have bitAway1 : word tmpBit0 ≠ word tmpJStar := tmp_ne 1 6 (by omega) (by omega) (by omega)
  have bitAway2 : word tmpBit0 ≠ word (hotLabelBase + 4) :=
    (hotLabel_ne_tmp 4 1 (by omega) (by omega)).symm
  unfold Replay.designatedPrefix
  rw [rtree_loadAt_seq, alphaCell, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word alpha) (word 1) (by rw [reg_ne _ _ _ _ (by decide), reg_same])
      (reg_same _ _ _), word_xor_one alpha alphaSmall,
    rtree_storeAt_seq _ _ _ _ (by decide), reg_same, rtree_cst_seq,
    rtree_ar_val _ _ _ _ _ _ (word (alpha ^^^ 1)) (word hotLabelBase)
      (by rw [reg_ne _ _ _ _ (by decide), storeRam_registers, reg_ne _ _ _ _ (by decide), reg_same])
      (reg_same _ _ _),
    word_add_small _ _ (by unfold hotLabelBase; omega), rtree_load_seq, reg_same]
  simp only [setReg_ram, storeRam_ram]
  have starCell' : memory.ram (word ((alpha ^^^ 1) + hotLabelBase)) = blockWord star := by
    rw [Nat.add_comm]; exact starCell
  have jstarHot' : word ((alpha ^^^ 1) + hotLabelBase) ≠ word tmpJStar := by
    rw [Nat.add_comm]; exact jstarHot.symm
  rw [Function.update_of_ne jstarHot', starCell',
    rtree_storeAt_seq _ _ _ _ (by decide), reg_same, rtree_cst_seq, rtree_loadAt_seq]
  simp only [setReg_ram, storeRam_ram]
  rw [Function.update_of_ne bitAway2, Function.update_of_ne bitAway1, bitCell,
    rtree_ar_val _ _ _ _ _ _ (word (alpha % 2)) (word (alpha % 2)) (reg_same _ _ _) (reg_same _ _ _),
    eval_fieldAdd, word_small (show alpha % 2 < 2 ^ 256 by omega),
    rtree_ar_val _ _ _ _ _ _ (word 1) (fieldWord (((alpha % 2 : Nat) : BaseField) +
      ((alpha % 2 : Nat) : BaseField)))
      (by rw [reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide), reg_ne _ _ _ _ (by decide),
        reg_same]) (reg_same _ _ _),
    eval_fieldSub, word_small (show 1 < 2 ^ 256 by norm_num), fieldWord_cast, Nat.cast_one,
    rtree_storeAt _ _ _ (by decide), reg_same]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [storeRam_ram, setReg_ram]
  · simp only [storeRam_bits, setReg_bits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
