/-
**The replay, one plain chunk**: `chunkBody` (not the designated chunk) against the evaluator's
`evalChunkM` body (`agree_chunkBody`): the fold, the four switches, the published-join terms.
-/

import Proof.Simulator.ReplayChunk

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-- An address a plain chunk of a lane leaves alone. -/
def OffChunk (spec : Replay.LaneSpec) (address : Word) : Prop :=
  (∀ e, e < spec.count → address ≠ accCell spec e) ∧ (∀ j, j < 4 → address ≠ word (hotLabelBase + j)) ∧
    address ≠ word tmpAlpha ∧ address ≠ word tmpBit0

/-- What a plain chunk leaves: every accumulator cell advanced by the chunk's free fold. -/
def ChunkPost (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory) (record : Record)
    (result : (Fin spec.count → BaseField) × Record) (after : Memory) : Prop :=
  (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
    (∀ address, OffChunk spec address → after.ram address = start.ram address) ∧
    after.bits = start.bits ∧ result.2 = record

/-- **One plain chunk.** The abstract side is the body of `evalChunkM`, at a width `w = 2`. -/
theorem agree_chunkBody [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (fits : spec.slot + spec.count ≤ 824) (small : spec.count ≤ elementCountX)
    (chunk : Fin chunkCount) (width : Nat) (twoWide : width = 2) (alpha : Fin (2 ^ width))
    (bitLabel join : Nat → Block) (scaleJ : Fin spec.count → BaseField)
    (memory : Memory) (record : Record) (acc0 : Nat → BaseField)
    (coord : Nat) (coordSmall : coord < 2 ^ 254) (L0 L1 J : Block)
    (alphaValue : alpha.val = (coord >>> (2 * chunk.val)) % 4)
    (label0Is : bitLabel 0 = L0) (label1Is : bitLabel 1 = L1) (free : join 0 = 0) (joinIs : join 1 = J)
    (coordCell : memory.ram (word spec.coordinate) = word coord)
    (label0 : memory.ram (word (spec.labels + 2 * chunk.val)) = blockWord L0)
    (label1 : memory.ram (word (spec.labels + 2 * chunk.val + 1)) = blockWord L1)
    (joinCell : memory.ram (word (hotBase + 127 * spec.hotRow + chunk.val)) = blockWord J)
    (off0 : OffScratch (word (spec.labels + 2 * chunk.val)))
    (off1 : OffScratch (word (spec.labels + 2 * chunk.val + 1)))
    (offJ : OffScratch (word (hotBase + 127 * spec.hotRow + chunk.val)))
    (cells : ∀ e, e < spec.count → memory.ram (accCell spec e) = fieldWord (acc0 e))
    (joins : ∀ e : Fin spec.count,
      memory.ram (word (scaleCellBase + 824 * chunk.val + spec.slot + e.val)) = fieldWord (scaleJ e))
    (joinAway : ∀ e first, e < spec.count → first < spec.count →
      word (scaleCellBase + 824 * chunk.val + spec.slot + e) ≠ accCell spec first)
    (joinOff : ∀ e, e < spec.count →
      OffScratch (word (scaleCellBase + 824 * chunk.val + spec.slot + e)))
    (clean : ∀ (switch : Fin (2 ^ 2)) (e : Fin spec.count) block,
      ¬ IsDesignated bits (scaleIndexOf spec.lane chunk switch.val e block)) :
    Agree (ChunkPost spec acc0 memory record) (rtree (Replay.chunkBody ordF0 spec false chunk.val) memory)
      (interceptT bits (FreeQuery.bind (Programs.evalFoldM spec.lane chunk alpha.val bitLabel join width)
        fun hot => FreeQuery.bind (Programs.evalMasksM spec.count spec.lane chunk width hot alpha)
          fun masks => .pure (Programs.evalScaleOf width masks alpha scaleJ)) record) := by
  subst twoWide
  rw [interceptT_bind, interceptT_clean bits record (clean_evalFoldM bits _ _ _ _ _ 2),
    evalFold_two _ _ _ _ _ free, label0Is, label1Is, joinIs, alphaValue]
  unfold Replay.chunkBody
  rw [rtree_seq]
  have alphaSmall : alpha.val < 4 := alpha.isLt
  refine Agree.bindOpt (fun result afterFold foldPost => ?_)
    ((agree_chunkPrefix spec chunk memory coord coordSmall L0 L1 J coordCell label0 label1 joinCell
      off0 off1 offJ).map (Post' := fun result after =>
        FoldPost memory ((coord >>> (2 * chunk.val)) % 4) result.1 after ∧ result.2 = record)
      (fun hot => (hot, record)) fun hot after holds => ⟨holds, rfl⟩)
  obtain ⟨⟨hots, alphaCell, _, foldFrame, foldBits⟩, recordSame⟩ := foldPost
  rw [← alphaValue] at alphaCell
  rw [recordSame]
  simp only [if_neg (by decide : ¬ (false = true)), rtree_seq, rtree_skip, bindOpt_pure]
  simp only [Programs.evalMasksM, TreeLaws.monad_bind, interceptT_bind, TreeLaws.bind_assoc]
  have accsFold : ∀ e, e < spec.count → afterFold.ram (accCell spec e) = fieldWord (acc0 e) := by
    intro e bound
    rw [foldFrame _ (fun j small => (hotLabel_ne_acc spec fits j (by omega) e bound).symm)
      (tmp_ne_acc spec fits 0 (by omega) e bound).symm (tmp_ne_acc spec fits 1 (by omega) e bound).symm,
      cells e bound]
  refine Agree.bindOpt (fun state afterSwitches switchPost => ?_) (agree_switches bits spec fits small
    chunk alpha result.1 afterFold record acc0 clean alphaCell (fun switch => hots switch) accsFold)
  obtain ⟨switchAccs, switchFrame, switchBits, switchRecord⟩ := switchPost
  rw [rtree_loadAt_seq]
  have alphaAfter : afterSwitches.ram (word tmpAlpha) = word alpha.val := by
    rw [switchFrame (word tmpAlpha) fun e bound => tmp_ne_acc spec fits 0 (by omega) e bound,
      alphaCell]
  obtain ⟨final, run, finalAccs, finalFrame, finalBits, _⟩ := rtree_joinTerms spec fits chunk.val
    (alpha.val : BaseField) (fun e => if bound : e < spec.count then scaleJ ⟨e, bound⟩ else 0)
    (setReg (setReg afterSwitches rAddr (word tmpAlpha)) rF (afterSwitches.ram (word tmpAlpha)))
    (by
      rw [reg_same, alphaAfter]
      unfold fieldWord
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold baseFieldModulus; omega)])
    (fun e bound => by
      simp only [setReg_ram, dif_pos bound]
      rw [switchFrame _ fun first firstBound => joinAway e first bound firstBound,
        foldFrame _ (fun j small => (joinOff e bound).1 j (by omega))
          ((joinOff e bound).2 0 (by omega)) ((joinOff e bound).2 1 (by omega))]
      exact joins ⟨e, bound⟩)
    joinAway (fun e => acc0 e + ∑ switch : Fin (2 ^ 2),
      ((switch.val : BaseField) - (alpha.val : BaseField)) *
        (if bound : e < spec.count then state.1[switch] ⟨e, bound⟩ else 0))
    (fun e bound => by simp only [setReg_ram, dif_pos bound]; exact switchAccs ⟨e, bound⟩)
    spec.count le_rfl
  rw [run]
  refine .leaf ⟨fun e => ?_, fun address off => ?_, ?_, switchRecord⟩
  · rw [finalAccs e.val e.isLt]
    simp only [dif_pos e.isLt]
    rw [evalScaleOf_eq, add_assoc]
    rfl
  · rw [finalFrame address off.1]
    simp only [setReg_ram]
    rw [switchFrame address off.1, foldFrame address off.2.1 off.2.2.1 off.2.2.2]
  · rw [finalBits]
    simp only [setReg_bits]
    rw [switchBits, foldBits]

/-! ### A lane -/

/-- The invariant of a lane's chunk loop. -/
def LaneInv (spec : Replay.LaneSpec) (acc0 : Nat → BaseField) (start : Memory)
    (recordInv : Nat → Record → Prop) (count : Nat)
    (state : Vector (Fin spec.count → BaseField) count × Record) (memory : Memory) : Prop :=
  (∀ e : Fin spec.count, memory.ram (accCell spec e) = fieldWord (acc0 e +
      ∑ chunk : Fin count, state.1[chunk] e)) ∧
    (∀ address, OffChunk spec address → memory.ram address = start.ram address) ∧
    memory.bits = start.bits ∧ recordInv count state.2

/-- **A lane's chunk loop**, from the per-chunk agreements. -/
theorem agree_lane [DecidableEq PlanB.FixedIndex] (bits : BitInput) (spec : Replay.LaneSpec)
    (bodies : Nat → Prog) (chunkProg : Fin chunkCount → FreeQuery Programs.Spec (Fin spec.count → BaseField))
    (recordInv : Nat → Record → Prop) (start : Memory) (record0 : Record) (acc0 : Nat → BaseField)
    (step : ∀ (chunk : Fin chunkCount) (memory : Memory) (record : Record) (accNow : Nat → BaseField),
      recordInv chunk.val record →
      (∀ e, e < spec.count → memory.ram (accCell spec e) = fieldWord (accNow e)) →
      (∀ address, OffChunk spec address → memory.ram address = start.ram address) →
      memory.bits = start.bits →
      Agree (fun (result : (Fin spec.count → BaseField) × Record) after =>
          (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (accNow e + result.1 e)) ∧
          (∀ address, OffChunk spec address → after.ram address = memory.ram address) ∧
          after.bits = memory.bits ∧ recordInv (chunk.val + 1) result.2)
        (rtree (bodies chunk.val) memory) (interceptT bits (chunkProg chunk) record))
    (recordStart : recordInv 0 record0)
    (cells : ∀ e, e < spec.count → start.ram (accCell spec e) = fieldWord (acc0 e)) :
    Agree (fun (result : (Fin spec.count → BaseField) × Record) after =>
        (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, OffChunk spec address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ recordInv chunkCount result.2)
      (rtree (Prog.rep chunkCount bodies) start)
      (interceptT bits (FreeQuery.bind (FreeQuery.vector chunkCount chunkProg) fun perChunk =>
        .pure fun e => ∑ chunk : Fin chunkCount, perChunk.get chunk e) record0) := by
  rw [interceptT_bind]
  have initial : LaneInv spec acc0 start recordInv 0 (#v[], record0) start := by
    refine ⟨fun e => ?_, fun _ _ => rfl, rfl, recordStart⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact cells e e.isLt
  have loop := agree_rep_vector bits bodies (LaneInv spec acc0 start recordInv) chunkCount chunkProg
    (fun chunk values record memory holds => by
      obtain ⟨accs, frame, bitsSame, recordHolds⟩ := holds
      have agree := step chunk memory record
        (fun e => if bound : e < spec.count then acc0 e + ∑ earlier : Fin chunk.val,
          values[earlier] ⟨e, bound⟩ else 0) recordHolds
        (fun e bound => by rw [dif_pos bound]; exact accs ⟨e, bound⟩) frame bitsSame
      refine agree.mono fun result after post => ?_
      obtain ⟨accsAfter, frameAfter, bitsAfter, recordAfter⟩ := post
      refine ⟨fun e => ?_, fun address off => ?_, bitsAfter.trans bitsSame, recordAfter⟩
      · rw [accsAfter e]
        simp only [dif_pos e.isLt]
        rw [Fin.sum_univ_castSucc]
        try simp only [Fin.coe_castSucc, Fin.val_last]
        rw [add_assoc]
        congr 3
        · refine Finset.sum_congr rfl fun earlier _ => ?_
          simp only [Fin.getElem_fin, Fin.coe_castSucc, Vector.getElem_push_lt earlier.isLt]
        · simp only [Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      · rw [frameAfter address off, frame address off]
      ) record0 start initial
  simp only [interceptT]
  have mapped := Agree.map (Post' := fun (result : (Fin spec.count → BaseField) × Record) after =>
      (∀ e : Fin spec.count, after.ram (accCell spec e) = fieldWord (acc0 e + result.1 e)) ∧
        (∀ address, OffChunk spec address → after.ram address = start.ram address) ∧
        after.bits = start.bits ∧ recordInv chunkCount result.2)
    (fun (state : Vector (Fin spec.count → BaseField) chunkCount × Record) =>
      ((fun e => ∑ chunk : Fin chunkCount, state.1.get chunk e), state.2))
    (fun state after holds => ⟨fun e => by
      rw [holds.1 e]
      simp only [Vector.get_eq_getElem, Fin.getElem_fin], holds.2.1, holds.2.2.1, holds.2.2.2⟩) loop
  exact mapped

end

end Kriterion.ArgoMAC.PlanB.SimMachine