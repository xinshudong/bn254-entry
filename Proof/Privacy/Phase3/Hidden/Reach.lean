/-
**Phase 3, P1h — what the evaluator asks: one lane.**

`Asks ans P q`: the program `P`, run on the answers `ans`, asks the question `q`. It passes to a bind
from either side (`Asks.bind_left`, `Asks.bind_right` at the first stage's value) and to a loop from
any iteration (`Asks.vector`).

**One lane of the evaluator asks every garbler question the evaluator is meant to hold** — on
every tape, with the lane's published fold joins and the selected labels of a free-XOR key:

* `asks_evalLane_hot`: every fold gate of step `1` at an **inactive** parent, at the garbler's own
  level-1 label (`evalFold_garbleFold` at one step: the evaluator's label equals the garbler's off
  the active entry);
* `asks_evalLane_scale`: every block of every element of every **inactive** switch, at the garbler's
  own one-hot label (`evalHot_agrees_off_active`).
-/

import Proof.Privacy.Phase3.Hidden.StageTwoShift
import Proof.Correctness.PGS.Row

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

/-! ### Asked questions -/

/-- `P` asks `q` on the answers `ans`. -/
def Asks {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (P : FreeQuery Programs.Spec α) (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  q ∈ (Hidden.transcriptOf ans P).map Sigma.fst

namespace Asks

variable {α β : Type} {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
  {q : PublicQuery FixedIndex EncPRF.PermutationIndex}

theorem ask' (q : PublicQuery FixedIndex EncPRF.PermutationIndex) :
    Asks ans (FreeQuery.ask (spec := Programs.Spec) q) q := by
  show q ∈ [q]
  exact List.mem_singleton_self q

theorem bind_left {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (asks : Asks ans P q) : Asks ans (P >>= f) q := by
  unfold Asks at *
  rw [transcriptOf_bind, List.map_append]
  exact List.mem_append_left _ asks

theorem bind_right {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (asks : Asks ans (f (P.eval ans)) q) : Asks ans (P >>= f) q := by
  unfold Asks at *
  rw [transcriptOf_bind, List.map_append]
  exact List.mem_append_right _ asks

theorem vector : ∀ (count : Nat) {P : Fin count → FreeQuery Programs.Spec α} (i : Fin count),
    Asks ans (P i) q → Asks ans (FreeQuery.vector count P) q
  | 0, _, i, _ => i.elim0
  | count + 1, P, i, asks => by
      show Asks ans (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value)) q
      by_cases last : i = Fin.last count
      · subst last
        exact bind_right (bind_left asks)
      · have small : i.val < count := by
          have := i.isLt
          have : i.val ≠ count := fun h => last (Fin.ext h)
          omega
        have cast : (⟨i.val, small⟩ : Fin count).castSucc = i := Fin.ext rfl
        refine bind_left (vector count (P := fun index => P index.castSucc) ⟨i.val, small⟩ ?_)
        rw [cast]
        exact asks

/-- A Davies–Meyer gate asks its question. -/
theorem hashM (index : FixedIndex) (label : Block) :
    Asks ans (Programs.hashM index label) (.fixedForward index label) :=
  bind_left (ask' _)

end Asks

/-! ### One chunk of the evaluator -/

theorem labelAt_select_chunk (bitKey : Fin PlanB.coordinateBits → Block × Block) (delta : Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) (step : Nat) (inRange : step < chunkWidth k) :
    labelAt (chunkLabels (selectBits bitKey bits) k) step =
      labelAt (fun position => (chunkKey bitKey k position).1) step ^^^
        (if (chunkValue bits k).toNat.testBit step then delta else 0) := by
  rw [chunkLabels_selectBits]
  have bitEq : (chunkValue bits k)[(⟨step, inRange⟩ : Fin (chunkWidth k))] =
      (chunkValue bits k).toNat.testBit step :=
    BitVec.getElem_eq_testBit_toNat (chunkValue bits k) step inRange
  simp only [labelAt, dif_pos inRange, selectBits, ← bitEq]
  by_cases bit : (chunkValue bits k)[(⟨step, inRange⟩ : Fin (chunkWidth k))] = true
  · rw [if_pos bit, if_pos bit, chunkKey_correlated bitKey delta correlated]
  · rw [if_neg bit, if_neg bit, bxor_zero]

/-- **The evaluator's level-1 labels are the garbler's off the active parent.** -/
theorem evalFold_one_off (O : PermutationOracle FixedIndex Block) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (bits : BitVec PlanB.coordinateBits) (k : Fin chunkCount) (r : Fin (2 ^ 1))
    (off : r.val ≠ (chunkOf bits k).val % 2) :
    evalFold O lane k (chunkValue bits k).toNat (labelAt (chunkLabels (selectBits bitKey bits) k))
        (joinAt (hotSlice (hotJoins O lane delta bitKey) k)) 1 r =
      (garbleFold O lane k delta (labelAt fun p => (chunkKey bitKey k p).1) 1).1 r := by
  rw [evalFold_garbleFold O lane k delta (labelAt fun p => (chunkKey bitKey k p).1)
    (labelAt (chunkLabels (selectBits bitKey bits) k)) (chunkValue bits k).toNat 1
    (joinAt (hotSlice (hotJoins O lane delta bitKey) k))
    (fun step small => labelAt_select_chunk bitKey delta correlated bits k step
      (by rw [chunkWidth_two]; omega))
    (fun step small => by
      obtain rfl : step = 0 := by omega
      rw [garbleFold_join_zero O lane k delta _ 1 (by omega)]
      rfl) r]
  have notHit : ¬ (r.val = (chunkValue bits k).toNat % 2 ^ 1) := by
    rw [chunkValue_toNat]
    exact off
  rw [if_neg notHit, bxor_zero]

/-- The fold of `steps ≥ 2` levels asks every non-active step-1 gate at the evaluator's level-1
label. -/
theorem asks_evalFoldM_one (O : Oracle) (lane : Lane) (k : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (r : Fin (2 ^ 1)) (half : Bool) (off : r ≠ activeAt value 1) :
    ∀ steps, 2 ≤ steps → Asks (publicAnswer O) (Programs.evalFoldM lane k value bitLabel join steps)
      (.fixedForward (hotIndexNat lane k 1 r.val half) (evalFold O.1 lane k value bitLabel join 1 r))
  | 0, small => absurd small (by omega)
  | 1, small => absurd small (by omega)
  | steps + 2, _ => by
      show Asks _ (Programs.evalFoldM lane k value bitLabel join (steps + 1) >>= fun previous =>
          Programs.evalStepM lane k (steps + 1) (bitLabel (steps + 1)) (join (steps + 1))
            (activeAt value (steps + 1)) previous >>= fun right =>
              Pure.pure (extendLevel (steps + 1) previous right)) _
      by_cases one : steps = 0
      · subst one
        show Asks _ (Programs.evalFoldM lane k value bitLabel join 1 >>= fun previous =>
            Programs.evalStepM lane k 1 (bitLabel 1) (join 1) (activeAt value 1) previous >>= fun right =>
              Pure.pure (extendLevel 1 previous right)) _
        refine Asks.bind_right (Asks.bind_left ?_)
        rw [Programs.eval_evalFoldM]
        unfold Programs.evalStepM
        refine Asks.bind_left (Asks.vector _ r ?_)
        simp only [if_neg off]
        unfold Programs.foldMaskM
        cases half
        · exact Asks.bind_left (Asks.hashM _ _)
        · exact Asks.bind_right (Asks.bind_left (Asks.hashM _ _))
      · exact Asks.bind_left (asks_evalFoldM_one O lane k value bitLabel join r half off (steps + 1)
          (by omega))

/-- A switch's mask asks every block of every element at its label. -/
theorem asks_switchMaskM (O : Oracle) (count : Nat) (lane : Lane) (k : Fin chunkCount) (switch : Nat)
    (label : Block) (element : Fin count) (block : Fin 3) :
    Asks (publicAnswer O) (Programs.switchMaskM count lane k switch label)
      (.fixedForward (scaleIndexOf lane k switch element block) label) := by
  unfold Programs.switchMaskM
  refine Asks.bind_left (Asks.vector _ element ?_)
  fin_cases block
  · exact Asks.bind_left (Asks.hashM _ _)
  · exact Asks.bind_right (Asks.bind_left (Asks.hashM _ _))
  · exact Asks.bind_right (Asks.bind_right (Asks.bind_left (Asks.hashM _ _)))

theorem asks_switchMaskM_eq (O : Oracle) (count : Nat) (lane : Lane) (k : Fin chunkCount) (switch : Nat)
    (label target : Block) (element : Fin count) (block : Fin 3) (eq : label = target) :
    Asks (publicAnswer O) (Programs.switchMaskM count lane k switch label)
      (.fixedForward (scaleIndexOf lane k switch element block) target) := by
  subst eq
  exact asks_switchMaskM O count lane k switch label element block

/-- **One chunk asks every inactive step-1 fold gate, at the garbler's point.** -/
theorem asks_evalChunk_hot (O : Oracle) (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (r : Fin (2 ^ 1)) (half : Bool) (off : r.val ≠ (chunkOf bits k).val % 2) :
    Asks (publicAnswer O)
      (Programs.evalChunkM count lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits) k)
      (.fixedForward (hotIndexNat lane k 1 r.val half)
        ((garbleFold O.1 lane k delta (labelAt fun p => (chunkKey bitKey k p).1) 1).1 r)) := by
  unfold Programs.evalChunkM
  refine Asks.bind_left ?_
  have notActive : r ≠ activeAt (chunkValue bits k).toNat 1 := by
    intro same
    apply off
    rw [same]
    show (chunkValue bits k).toNat % 2 ^ 1 = _
    rw [chunkValue_toNat]
    rfl
  have asks := asks_evalFoldM_one O lane k (chunkValue bits k).toNat
    (labelAt (chunkLabels (selectBits bitKey bits) k)) (joinAt (hotSlice (hotJoins O.1 lane delta bitKey) k))
    r half notActive (chunkWidth k) (by rw [chunkWidth_two])
  rw [evalFold_one_off O.1 lane delta bitKey correlated bits k r off] at asks
  exact asks

/-- **One chunk asks every block of every inactive switch, at the garbler's point.** -/
theorem asks_evalChunk_scale (O : Oracle) (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (j : Fin (2 ^ chunkWidth k)) (element : Fin count) (block : Fin 3)
    (off : j ≠ chunkOf bits k) :
    Asks (publicAnswer O)
      (Programs.evalChunkM count lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits) k)
      (.fixedForward (scaleIndexOf lane k j.val element block) ((garbleChunk O.1 lane delta bitKey k).1 j)) := by
  unfold Programs.evalChunkM
  refine Asks.bind_right (Asks.bind_left ?_)
  have hot : (Programs.evalFoldM lane k (chunkValue bits k).toNat
      (labelAt (chunkLabels (selectBits bitKey bits) k)) (joinAt (hotSlice (hotJoins O.1 lane delta bitKey) k))
      (chunkWidth k)).eval (publicAnswer O) j = (garbleChunk O.1 lane delta bitKey k).1 j := by
    rw [Programs.eval_evalFoldM]
    show evalHot O.1 lane k (chunkWidth k) (hotSlice (hotJoins O.1 lane delta bitKey) k)
      (chunkLabels (selectBits bitKey bits) k) (chunkValue bits k) j = _
    rw [hotSlice_hotJoins, chunkLabels_selectBits]
    exact evalHot_agrees_off_active correlated bits k j off
  unfold Programs.evalMasksM
  refine Asks.bind_left (Asks.vector _ j ?_)
  simp only [if_neg off]
  exact asks_switchMaskM_eq O count lane k j.val _ _ element block hot

/-- **One lane asks every inactive step-1 fold gate.** -/
theorem asks_evalLane_hot (O : Oracle) (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (r : Fin (2 ^ 1)) (half : Bool) (off : r.val ≠ (chunkOf bits k).val % 2) :
    Asks (publicAnswer O)
      (Programs.evalLaneM count lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits))
      (.fixedForward (hotIndexNat lane k 1 r.val half)
        ((garbleFold O.1 lane k delta (labelAt fun p => (chunkKey bitKey k p).1) 1).1 r)) :=
  Asks.bind_left (Asks.vector _ k
    (asks_evalChunk_hot O count lane delta bitKey correlated scale bits k r half off))

/-- **One lane asks every block of every inactive switch.** -/
theorem asks_evalLane_scale (O : Oracle) (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec PlanB.coordinateBits)
    (k : Fin chunkCount) (j : Fin (2 ^ chunkWidth k)) (element : Fin count) (block : Fin 3)
    (off : j ≠ chunkOf bits k) :
    Asks (publicAnswer O)
      (Programs.evalLaneM count lane (hotJoins O.1 lane delta bitKey) scale bits (selectBits bitKey bits))
      (.fixedForward (scaleIndexOf lane k j.val element block) ((garbleChunk O.1 lane delta bitKey k).1 j)) :=
  Asks.bind_left (Asks.vector _ k
    (asks_evalChunk_scale O count lane delta bitKey correlated scale bits k j element block off))

end

end Kriterion.ArgoMAC.Security.Phase3
