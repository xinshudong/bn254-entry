/-
**The replay, the designated chunk** (`agree_desChunkBody`): the chunk prefix, the designated
prefix (`j*`, `E*`, `κ`), the four designated switches (the collectors at `j*` answered inline and
recorded), the published-join terms.
-/

import Proof.Simulator.ReplayDesPrefix

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- What the designated chunk leaves. -/
def DesChunkPost (bits : BitInput) (acc0 : Nat → BaseField) (start : Memory) (jstar : Nat)
    (star : Block) (kappaValue : BaseField) (result : (Fin pointElementCountX → BaseField) × Record)
    (after : Memory) : Prop :=
  (∀ e : Fin pointElementCountX,
      after.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e + result.1 e)) ∧
    (∀ address, OffChunk Replay.pointXSpec address → address ≠ word tmpJStar →
      address ≠ word (hotLabelBase + 4) → address ≠ word tmpKappa →
      after.ram address = start.ram address) ∧
    after.ram (word tmpJStar) = word jstar ∧ after.ram (word (hotLabelBase + 4)) = blockWord star ∧
    after.ram (word tmpKappa) = fieldWord kappaValue ∧ after.bits = start.bits ∧
    RecordUpTo bits star pointElementCountX result.2

/-- **The designated chunk.** -/
theorem agree_desChunkBody [DecidableEq PlanB.FixedIndex] (bits : BitInput)
    (chunk : Fin chunkCount) (chunkZeroIs : chunk.val = 0)
    (width : Nat) (twoWide : width = 2) (alpha : Fin (2 ^ width))
    (activeIs : (activeSwitch bits).val = alpha.val)
    (bitLabel join : Nat → Block) (scaleJ : Fin pointElementCountX → BaseField)
    (memory : Memory) (record : Record) (acc0 : Nat → BaseField)
    (coord : Nat) (coordSmall : coord < 2 ^ 254) (L0 L1 J : Block)
    (alphaValue : alpha.val = coord % 4)
    (label0Is : bitLabel 0 = L0) (label1Is : bitLabel 1 = L1) (free : join 0 = 0) (joinIs : join 1 = J)
    (coordCell : memory.ram (word Replay.pointXSpec.coordinate) = word coord)
    (label0 : memory.ram (word (Replay.pointXSpec.labels + 2 * chunk.val)) = blockWord L0)
    (label1 : memory.ram (word (Replay.pointXSpec.labels + 2 * chunk.val + 1)) = blockWord L1)
    (joinCell : memory.ram (word (hotBase + 127 * Replay.pointXSpec.hotRow + chunk.val)) = blockWord J)
    (off0 : OffScratch (word (Replay.pointXSpec.labels + 2 * chunk.val)))
    (off1 : OffScratch (word (Replay.pointXSpec.labels + 2 * chunk.val + 1)))
    (offJ : OffScratch (word (hotBase + 127 * Replay.pointXSpec.hotRow + chunk.val)))
    (cells : ∀ e, e < pointElementCountX → memory.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e))
    (joins : ∀ e : Fin pointElementCountX,
      memory.ram (word (scaleCellBase + 824 * chunk.val + Replay.pointXSpec.slot + e.val)) =
        fieldWord (scaleJ e))
    (joinAway : ∀ e first, e < pointElementCountX → first < pointElementCountX →
      word (scaleCellBase + 824 * chunk.val + Replay.pointXSpec.slot + e) ≠ accCell Replay.pointXSpec first)
    (joinOff : ∀ e, e < pointElementCountX →
      OffScratch (word (scaleCellBase + 824 * chunk.val + Replay.pointXSpec.slot + e))) :
    Agree (fun (result : (Fin pointElementCountX → BaseField) × Record) after =>
        ∃ star : Block, DesChunkPost bits acc0 memory (designatedSwitch bits).val star
          (kappa bits) result after)
      (rtree (Replay.chunkBody ordF0 Replay.pointXSpec true chunk.val) memory)
      (interceptT bits (FreeQuery.bind (Programs.evalFoldM .pointX chunk alpha.val bitLabel join width)
        fun hot => FreeQuery.bind (Programs.evalMasksM pointElementCountX .pointX chunk width hot alpha)
          fun masks => .pure (Programs.evalScaleOf width masks alpha scaleJ)) record) := by
  obtain rfl : chunk = chunkZero := Fin.ext chunkZeroIs
  subst twoWide
  have coordShift : coord >>> (2 * chunkZero.val) = coord := by
    show coord >>> (2 * 0) = coord
    rw [Nat.mul_zero, Nat.shiftRight_zero]
  rw [interceptT_bind, interceptT_clean bits record (clean_evalFoldM bits _ _ _ _ _ 2),
    evalFold_two _ _ _ _ _ free, label0Is, label1Is, joinIs, alphaValue]
  unfold Replay.chunkBody
  rw [rtree_seq]
  have alphaSmall : alpha.val < 4 := alpha.isLt
  have fits : Replay.pointXSpec.slot + pointElementCountX ≤ 824 := by decide
  refine Agree.bindOpt (fun result afterFold foldPost => ?_)
    ((agree_chunkPrefix Replay.pointXSpec chunkZero memory coord coordSmall L0 L1 J coordCell label0
      label1 joinCell off0 off1 offJ).map (Post' := fun result after =>
        FoldPost memory ((coord >>> (2 * chunkZero.val)) % 4) result.1 after ∧ result.2 = record)
      (fun hot => (hot, record)) fun hot after holds => ⟨holds, rfl⟩)
  obtain ⟨⟨hots, alphaCell, bitCell, foldFrame, foldBits⟩, recordSame⟩ := foldPost
  rw [coordShift, ← alphaValue] at alphaCell bitCell
  rw [recordSame]
  have starIs : (designatedSwitch bits).val = alpha.val ^^^ 1 := by
    show (activeSwitch bits).val ^^^ 1 = _
    rw [activeIs]
  have jSmall : alpha.val ^^^ 1 < 4 := Nat.xor_lt_two_pow (show alpha.val < 2 ^ 2 from alpha.isLt)
    (by norm_num)
  set jstar : Fin (2 ^ 2) := ⟨alpha.val ^^^ 1, jSmall⟩ with jstarDef
  have jstarValue : jstar.val = (designatedSwitch bits).val := starIs.symm
  have notStar : alpha ≠ jstar := fun equal => by
    have same : alpha.val = alpha.val ^^^ 1 := congrArg Fin.val equal
    revert same
    generalize alpha.val = a at alphaSmall ⊢
    interval_cases a <;> decide
  simp only [if_true, rtree_seq]
  obtain ⟨afterPrefix, runPrefix, prefixRam, prefixBits⟩ := rtree_designatedPrefix afterFold alpha.val
    alphaSmall (result.1 jstar) alphaCell bitCell (hots jstar)
  rw [runPrefix, bindOpt_pure]
  simp only [Programs.evalMasksM, TreeLaws.monad_bind, interceptT_bind, TreeLaws.bind_assoc]
  have tmpAlphaNe : ∀ k, k = 5 ∨ k = 6 → word tmpAlpha ≠ word (tmpBase + k) := by
    rintro k (rfl | rfl)
    · exact tmp_ne 0 5 (by omega) (by omega) (by omega)
    · exact tmp_ne 0 6 (by omega) (by omega) (by omega)
  have prefixKeep : ∀ address, address ≠ word tmpJStar → address ≠ word (hotLabelBase + 4) →
      address ≠ word tmpKappa → afterPrefix.ram address = afterFold.ram address := by
    intro address a b c
    rw [prefixRam, Function.update_of_ne c, Function.update_of_ne b, Function.update_of_ne a]
  have accsPrefix : ∀ e, e < pointElementCountX →
      afterPrefix.ram (accCell Replay.pointXSpec e) = fieldWord (acc0 e) := by
    intro e bound
    rw [prefixKeep _ (tmp_ne_acc Replay.pointXSpec fits 6 (by omega) e bound).symm
      (hotLabel_ne_acc Replay.pointXSpec fits 4 (by omega) e bound).symm
      (tmp_ne_acc Replay.pointXSpec fits 5 (by omega) e bound).symm,
      foldFrame _ (fun j small => (hotLabel_ne_acc Replay.pointXSpec fits j (by omega) e bound).symm)
      (tmp_ne_acc Replay.pointXSpec fits 0 (by omega) e bound).symm
      (tmp_ne_acc Replay.pointXSpec fits 1 (by omega) e bound).symm, cells e bound]
  refine Agree.bindOpt (fun state afterSwitches switchPost => ?_)
    (agree_desSwitches bits alpha jstar jstarValue notStar result.1 afterPrefix record acc0
      (by rw [prefixKeep _ (tmpAlphaNe 6 (Or.inr rfl)) (hotLabel_ne_tmp 4 0 (by omega) (by omega)).symm
        (tmpAlphaNe 5 (Or.inl rfl)), alphaCell])
      (fun switch => by
        rw [prefixKeep _ (hotLabel_ne_tmp switch.val 6 (by omega) (by omega))
          (hotLabel_ne switch.val 4 (by omega) (by omega) (by omega))
          (hotLabel_ne_tmp switch.val 5 (by omega) (by omega)), hots switch])
      (by rw [prefixRam, Function.update_of_ne (show word tmpJStar ≠ word tmpKappa from
          tmp_ne 6 5 (by omega) (by omega) (by omega)),
        Function.update_of_ne (show word tmpJStar ≠ word (hotLabelBase + 4) from
          (hotLabel_ne_tmp 4 6 (by omega) (by omega)).symm), Function.update_self, starIs])
      accsPrefix)
  obtain ⟨switchAccs, switchFrame, switchBits, switchRecord, _⟩ := switchPost
  show Agree _ (rtree (.seq (loadAt rF tmpAlpha) (Prog.rep Replay.pointXSpec.count fun index =>
    Replay.joinTerm Replay.pointXSpec chunkZero.val index)) afterSwitches) _
  rw [rtree_loadAt_seq]
  have alphaAfter : afterSwitches.ram (word tmpAlpha) = word alpha.val := by
    rw [switchFrame (word tmpAlpha) fun e bound =>
        tmp_ne_acc Replay.pointXSpec fits 0 (by omega) e bound,
      prefixKeep _ (tmpAlphaNe 6 (Or.inr rfl)) (hotLabel_ne_tmp 4 0 (by omega) (by omega)).symm
        (tmpAlphaNe 5 (Or.inl rfl)), alphaCell]
  obtain ⟨final, run, finalAccs, finalFrame, finalBits, _⟩ := rtree_joinTerms Replay.pointXSpec fits
    chunkZero.val (alpha.val : BaseField)
    (fun e => if bound : e < pointElementCountX then scaleJ ⟨e, bound⟩ else 0)
    (setReg (setReg afterSwitches rAddr (word tmpAlpha)) rF (afterSwitches.ram (word tmpAlpha)))
    (by
      rw [reg_same, alphaAfter]
      unfold fieldWord
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold baseFieldModulus; omega)])
    (fun e bound => by
      simp only [setReg_ram, dif_pos (show e < pointElementCountX from bound)]
      have off := joinOff e bound
      rw [switchFrame _ fun first firstBound => joinAway e first bound firstBound,
        prefixKeep _ (off.2 6 (by omega)) (off.1 4 (by omega)) (off.2 5 (by omega)),
        foldFrame _ (fun j small => off.1 j (by omega)) (off.2 0 (by omega)) (off.2 1 (by omega))]
      exact joins ⟨e, bound⟩)
    joinAway (fun e => acc0 e + ∑ switch : Fin (2 ^ 2),
      ((switch.val : BaseField) - (alpha.val : BaseField)) *
        (if bound : e < pointElementCountX then state.1[switch] ⟨e, bound⟩ else 0))
    (fun e bound => by
      simp only [setReg_ram, dif_pos (show e < pointElementCountX from bound)]
      exact switchAccs ⟨e, bound⟩)
    Replay.pointXSpec.count le_rfl
  rw [run]
  have keepThree : ∀ address, (∀ e, e < pointElementCountX → address ≠ accCell Replay.pointXSpec e) →
      final.ram address = afterPrefix.ram address := by
    intro address outside
    rw [finalFrame address outside]
    simp only [setReg_ram]
    rw [switchFrame address outside]
  refine .leaf ⟨result.1 jstar, fun e => ?_, fun address off a b c => ?_, ?_, ?_, ?_, ?_,
    switchRecord (by omega)⟩
  · rw [finalAccs e.val e.isLt]
    simp only [dif_pos e.isLt]
    rw [evalScaleOf_eq, add_assoc]
    rfl
  · rw [keepThree address off.1, prefixKeep address a b c,
      foldFrame address off.2.1 off.2.2.1 off.2.2.2]
  · rw [keepThree (word tmpJStar) fun e bound => tmp_ne_acc Replay.pointXSpec fits 6 (by omega) e bound,
      prefixRam, Function.update_of_ne (show word tmpJStar ≠ word tmpKappa from
        tmp_ne 6 5 (by omega) (by omega) (by omega)),
      Function.update_of_ne (show word tmpJStar ≠ word (hotLabelBase + 4) from
        (hotLabel_ne_tmp 4 6 (by omega) (by omega)).symm), Function.update_self, starIs]
  · rw [keepThree _ fun e bound => hotLabel_ne_acc Replay.pointXSpec fits 4 (by omega) e bound,
      prefixRam, Function.update_of_ne (show word (hotLabelBase + 4) ≠ word tmpKappa from
        hotLabel_ne_tmp 4 5 (by omega) (by omega)), Function.update_self]
  · rw [keepThree (word tmpKappa) fun e bound => tmp_ne_acc Replay.pointXSpec fits 5 (by omega) e bound,
      prefixRam, Function.update_self]
    congr 1
    unfold kappa iota
    rw [starIs, activeIs, kappa_value _ alphaSmall]
  · rw [finalBits]
    simp only [setReg_bits]
    rw [switchBits, prefixBits, foldBits]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
