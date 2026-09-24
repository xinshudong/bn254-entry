/-
**The replay, the designated chunk** — one switch step (`agree_desSwitchStep`): skipped at `α`,
otherwise the switch's label and coefficient are loaded and its `455` guarded elements run.
-/

import Proof.Simulator.ReplayGuarded

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What one designated-chunk switch step leaves. -/
def DesSwitchPost (bits : BitInput) (switch : Nat) (label : Block) (acc1 : Nat → BaseField)
    (coef : BaseField) (start : Memory) (record : Record)
    (result : (Fin pointElementCountX → BaseField) × Record) (after : Memory) : Prop :=
  (∀ e : Fin pointElementCountX,
      after.ram (accCell Replay.pointXSpec e) = fieldWord (acc1 e + coef * result.1 e)) ∧
    (∀ address, (∀ e, e < pointElementCountX → address ≠ accCell Replay.pointXSpec e) →
      after.ram address = start.ram address) ∧ after.bits = start.bits ∧
    (switch ≠ (designatedSwitch bits).val → result.2 = record) ∧
    (switch = (designatedSwitch bits).val → RecordUpTo bits label pointElementCountX result.2)

/-- **One switch step of the designated chunk.** -/
theorem agree_desSwitchStep [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (alpha switch : Fin (2 ^ 2)) (hot : Fin (2 ^ 2) → Block) (memory : Memory) (record : Record)
    (acc1 : Nat → BaseField) (notStar : alpha.val ≠ (designatedSwitch bits).val)
    (alphaCell : memory.ram (word tmpAlpha) = word alpha.val)
    (hotCell : memory.ram (word (hotLabelBase + switch.val)) = blockWord (hot switch))
    (jstarCell : memory.ram (word tmpJStar) = word (designatedSwitch bits).val)
    (cells : ∀ e, e < pointElementCountX →
      memory.ram (accCell Replay.pointXSpec e) = fieldWord (acc1 e)) :
    Agree (DesSwitchPost bits switch.val (hot switch) acc1
        ((switch.val : BaseField) - (alpha.val : BaseField)) memory record)
      (rtree (Replay.switchStep ordF0 Replay.pointXSpec true 0 switch.val) memory)
      (interceptT bits (if switch = alpha then FreeQuery.pure (fun _ => 0) else
        FreeQuery.bind (FreeQuery.vector pointElementCountX fun e =>
          elemProg (desIdx switch.val e) (hot switch)) fun values => .pure values.get) record) := by
  have alphaSmall : alpha.val < 2 ^ 256 := lt_trans alpha.isLt (by norm_num)
  have switchSmall : switch.val < 2 ^ 256 := lt_trans switch.isLt (by norm_num)
  have fits : Replay.pointXSpec.slot + pointElementCountX ≤ 824 := by decide
  unfold Replay.switchStep
  rw [rtree_loadAt_seq, rtree_cst_seq, rtree_ar_val _ _ _ _ _ _ (word alpha.val) (word switch.val)
    (by rw [reg_ne _ _ _ _ (by decide), reg_same, alphaCell]) (reg_same _ _ _), rtree_ite, reg_same,
    eval_xor]
  by_cases same : switch = alpha
  · subst same
    rw [if_pos ((word_xor_eq_zero switchSmall switchSmall).mpr rfl), if_pos rfl, rtree_skip]
    refine .leaf ⟨fun e => ?_, fun _ _ => rfl, rfl, fun _ => rfl, fun isStar => absurd isStar notStar⟩
    simp only [setReg_ram, sub_self, zero_mul, add_zero]
    exact cells e.val e.isLt
  · have different : switch.val ≠ alpha.val := fun equal => same (Fin.ext equal)
    rw [if_neg (fun zero => different ((word_xor_eq_zero alphaSmall switchSmall).mp zero).symm),
      if_neg same]
    unfold Replay.switchBody Replay.switchElements
    rw [if_pos rfl, rtree_loadAt_seq, rtree_loadAt_seq, rtree_cst_seq,
      rtree_ar_val _ _ _ _ _ _ (word switch.val) (word alpha.val) (reg_same _ _ _)
        (by rw [reg_ne _ _ _ _ (by decide), reg_same]; simp only [setReg_ram, alphaCell]),
      rtree_designatedElements, interceptT_bind]
    have finish : ∀ start : Memory, start.ram = memory.ram → start.bits = memory.bits →
        start.registers rInput = blockWord (hot switch) →
        start.registers rF = fieldWord ((switch.val : BaseField) - (alpha.val : BaseField)) →
        Agree (DesSwitchPost bits switch.val (hot switch) acc1
            ((switch.val : BaseField) - (alpha.val : BaseField)) memory record)
          (rtree (Prog.rep (5 * 91) fun index =>
            Replay.guardedElement ordF0 Replay.pointXSpec 0 switch.val index) start)
          (FreeQuery.bind (interceptT bits (FreeQuery.vector pointElementCountX fun e =>
              elemProg (desIdx switch.val e) (hot switch)) record)
            fun result => interceptT bits (.pure result.1.get) result.2) := by
      intro start sameRam sameBits input factor
      have loop := agree_designatedElements bits switch.val (by have := switch.isLt; omega) start
        record (hot switch) ((switch.val : BaseField) - (alpha.val : BaseField)) acc1 input factor
        (by rw [sameRam]; exact jstarCell) (fun e bound => by rw [sameRam]; exact cells e bound)
      have mapped := Agree.map (Post' := DesSwitchPost bits switch.val (hot switch) acc1
          ((switch.val : BaseField) - (alpha.val : BaseField)) memory record)
        (fun (state : Vector BaseField pointElementCountX × Record) => (state.1.get, state.2))
        (fun state after holds => by
          obtain ⟨accs, frame, bitsSame, _, _, offStar, atStar⟩ := holds
          refine ⟨fun e => ?_, fun address outside => ?_, bitsSame.trans sameBits, offStar, atStar⟩
          · rw [accs e.val e.isLt]
            rfl
          · rw [frame address outside, sameRam]) loop
      exact mapped
    exact finish _ (by simp only [setReg_ram]) rfl
      (by simp only [setReg_registers, setReg_ram, hotCell]; simp (config := {decide := true}))
      (by simp only [setReg_registers, if_true, eval_fieldSub, word_small switchSmall,
        word_small alphaSmall])

/-! ### The four switch steps of the designated chunk -/

/-- The invariant of the designated chunk's switch loop. -/
def DesSwInv (bits : BitInput) (jstar : Fin (2 ^ 2)) (hot : Fin (2 ^ 2) → Block)
    (acc0 : Nat → BaseField) (alpha : Nat) (start : Memory) (record0 : Record) (count : Nat)
    (state : Vector (Fin pointElementCountX → BaseField) count × Record) (memory : Memory) : Prop :=
  (∀ e : Fin pointElementCountX, memory.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e +
      ∑ switch : Fin count, ((switch.val : BaseField) - (alpha : BaseField)) * state.1[switch] e)) ∧
    (∀ address, (∀ e, e < pointElementCountX → address ≠ accCell Replay.pointXSpec e) →
      memory.ram address = start.ram address) ∧ memory.bits = start.bits ∧
    (jstar.val < count → RecordUpTo bits (hot jstar) pointElementCountX state.2) ∧
    (count ≤ jstar.val → state.2 = record0)

/-- **The switch loop of the designated chunk.** -/
theorem agree_desSwitches [DecidableEq PlanB.FixedIndex] (bits : BitInput) (alpha jstar : Fin (2 ^ 2))
    (jstarValue : jstar.val = (designatedSwitch bits).val) (notStar : alpha ≠ jstar)
    (hot : Fin (2 ^ 2) → Block) (start : Memory) (record0 : Record) (acc0 : Nat → BaseField)
    (alphaCell : start.ram (word tmpAlpha) = word alpha.val)
    (hotCells : ∀ switch : Fin (2 ^ 2),
      start.ram (word (hotLabelBase + switch.val)) = blockWord (hot switch))
    (jstarCell : start.ram (word tmpJStar) = word (designatedSwitch bits).val)
    (cells : ∀ e, e < pointElementCountX →
      start.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e)) :
    Agree (DesSwInv bits jstar hot acc0 alpha.val start record0 (2 ^ 2))
      (rtree (Prog.rep (2 ^ 2) fun switch => Replay.switchStep ordF0 Replay.pointXSpec true 0 switch)
        start)
      (interceptT bits (FreeQuery.vector (2 ^ 2) fun switch =>
        if switch = alpha then FreeQuery.pure (fun _ => 0) else
          FreeQuery.bind (FreeQuery.vector pointElementCountX fun e =>
            elemProg (desIdx switch.val e) (hot switch)) fun values => .pure values.get) record0) := by
  have fits : Replay.pointXSpec.slot + pointElementCountX ≤ 824 := by decide
  refine agree_rep_vector bits _ (DesSwInv bits jstar hot acc0 alpha.val start record0) (2 ^ 2) _ ?_
    record0 start ⟨fun e => (by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact cells e e.isLt), fun _ _ => rfl, rfl, fun small => absurd small (Nat.not_lt_zero _),
      fun _ => rfl⟩
  intro switch masks record memory holds
  obtain ⟨accs, frame, bitsSame, done, untouched⟩ := holds
  have agree := agree_desSwitchStep bits alpha switch hot memory record
    (fun e => if bound : e < pointElementCountX then acc0 e + ∑ earlier : Fin switch.val,
      ((earlier.val : BaseField) - (alpha.val : BaseField)) * masks[earlier] ⟨e, bound⟩ else 0)
    (fun equal => notStar (Fin.ext (equal.trans jstarValue.symm)))
    (by rw [frame (word tmpAlpha) fun e bound => tmp_ne_acc Replay.pointXSpec fits 0 (by omega) e bound,
      alphaCell])
    (by rw [frame _ fun e bound => hotLabel_ne_acc Replay.pointXSpec fits switch.val (by omega) e bound,
      hotCells])
    (by rw [frame (word tmpJStar) fun e bound => tmp_ne_acc Replay.pointXSpec fits 6 (by omega) e bound,
      jstarCell])
    (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩)
  refine agree.mono fun result after post => ?_
  obtain ⟨accsAfter, frameAfter, bitsAfter, offStar, atStar⟩ := post
  refine ⟨fun e => ?_, fun address outside => ?_, bitsAfter.trans bitsSame, fun below => ?_,
    fun above => ?_⟩
  · rw [accsAfter e]
    simp only [dif_pos e.isLt]
    rw [Fin.sum_univ_castSucc]
    try simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun earlier _ => ?_
      simp only [Fin.getElem_fin, Fin.coe_castSucc, Vector.getElem_push_lt earlier.isLt]
    · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
  · rw [frameAfter address outside, frame address outside]
  · by_cases isStar : switch = jstar
    · subst isStar
      exact atStar jstarValue
    · have earlier : jstar.val < switch.val := by
        have : switch.val ≠ jstar.val := fun equal => isStar (Fin.ext equal)
        omega
      rw [offStar (fun equal => isStar (Fin.ext (equal.trans jstarValue.symm)))]
      exact done earlier
  · have notHere : switch.val ≠ (designatedSwitch bits).val := by omega
    rw [offStar notHere]
    exact untouched (by omega)

end

end Kriterion.ArgoMAC.PlanB.SimMachine