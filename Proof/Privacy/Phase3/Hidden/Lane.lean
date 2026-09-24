/-
**Phase 3, P1f — shifting the tape: one lane of the garbler, run on a shifted tape.**

A `LaneShift` fixes the shift of the lane's `Δ`, of its 254 zero labels and, per chunk, of the
fold's step materials and gate outputs; `LaneShift.fold c` is chunk `c`'s `FoldShift`. On a tape
whose fold gates are shifted by `FoldShift.hot` and whose scale permutations are conjugated by the
level shift of their switch (`x ↦ π (x ⊕ t) ⊕ t`), `sim_laneM`: the lane run on the shifted `Δ`
and zero labels asks every gate at the shifted point, and its tables have the same masks and the
same published joins.
-/

import Proof.Privacy.Phase3.Hidden.Shift

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.Hidden

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)

noncomputable section

variable {rel : Asked FixedIndex EncPRF.PermutationIndex → Asked FixedIndex EncPRF.PermutationIndex → Prop}

/-- One switch's masks at the conjugated switch permutations: the same masks. -/
theorem sim_switchMaskM (O O' : Oracle) (count : Nat) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Nat) (label t : Block)
    (oracle : ∀ (element : Fin count) (block : Fin 3) (x : Block),
      O'.1.permutation (scaleIndexOf lane chunk switch element block) (x ^^^ t) =
        O.1.permutation (scaleIndexOf lane chunk switch element block) x ^^^ t)
    (entry : ∀ (element : Fin count) (block : Fin 3),
      rel ⟨.fixedForward (scaleIndexOf lane chunk switch element block) label,
          O.1.permutation (scaleIndexOf lane chunk switch element block) label⟩
        ⟨.fixedForward (scaleIndexOf lane chunk switch element block) (label ^^^ t),
          O'.1.permutation (scaleIndexOf lane chunk switch element block) (label ^^^ t)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun v v' => v = switchMask O.1 lane chunk switch label ∧ v' = v)
      (Programs.switchMaskM count lane chunk switch label)
      (Programs.switchMaskM count lane chunk switch (label ^^^ t)) := by
  unfold Programs.switchMaskM
  refine Sim.bind (Sim.vector count
      (R := fun element v v' => v = switchMask O.1 lane chunk switch label element ∧ v' = v) _ _
      fun element => ?_) fun values values' related => Sim.pure' ⟨?_, ?_⟩
  · refine Sim.bind (sim_hashM O O' _ label t t (oracle element 0 label) (entry element 0))
      fun first first' hfirst => Sim.bind (sim_hashM O O' _ label t t (oracle element 1 label)
        (entry element 1)) fun second second' hsecond => Sim.bind (sim_hashM O O' _ label t t
          (oracle element 2 label) (entry element 2)) fun third third' hthird => Sim.pure' ⟨?_, ?_⟩
    · rw [hfirst.1, hsecond.1, hthird.1]
      rfl
    · rw [hfirst.2, hsecond.2, hthird.2, xor_cancel_right, xor_cancel_right, xor_cancel_right]
  · funext element
    exact (related element).1
  · funext element
    exact (related element).2

/-- The shift of one lane. -/
structure LaneShift where
  /-- The shift of the lane's `Δ`. -/
  delta : Block
  /-- The shift of each zero label. -/
  zero : Fin PlanB.coordinateBits → Block
  /-- Per chunk, the shift of each paid step material. -/
  m : Fin chunkCount → Nat → Nat → Block
  /-- Per chunk, the shift of both outputs of each fold gate. -/
  o : Fin chunkCount → Nat → Nat → Block

/-- Chunk `c`'s fold shift. -/
def LaneShift.fold (L : LaneShift) (c : Fin chunkCount) : FoldShift where
  delta := L.delta
  zero := labelAt fun position : Fin (chunkWidth c) => L.zero (chunkBitIndex c position)
  m := L.m c
  o := L.o c

/-- Every chunk keeps its joins. -/
def LaneShift.Valid (L : LaneShift) : Prop := ∀ c, (L.fold c).Valid (chunkWidth c)

theorem labelAt_shift {width : Nat} (labels shift : Fin width → Block) (n : Nat) :
    labelAt (fun position => labels position ^^^ shift position) n = labelAt labels n ^^^ labelAt shift n := by
  unfold labelAt
  split
  · rfl
  · exact BitVec.xor_self.symm

/-- **One chunk's fold on the shifted tape.** -/
theorem sim_garbleChunkM (O O' : Oracle) (L : LaneShift) (valid : L.Valid) (lane : Lane)
    (delta : Block) (bitKey bitKey' : Fin PlanB.coordinateBits → Block × Block)
    (keys : ∀ position, (bitKey' position).1 = (bitKey position).1 ^^^ L.zero position)
    (c : Fin chunkCount)
    (oracle : ∀ (n r : Nat) (half : Bool) (x : Block), n < chunkWidth c → r < 2 ^ n →
      O'.1.permutation (hotIndexNat lane c n r half) (x ^^^ ((L.fold c).hot n r half).1) =
        O.1.permutation (hotIndexNat lane c n r half) x ^^^ ((L.fold c).hot n r half).2)
    (entry : ∀ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < chunkWidth c → n ≠ 0 →
      rel ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r),
        O.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r)⟩
        ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val),
        O'.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun chunk chunk' => chunk = garbleChunk O.1 lane delta bitKey c ∧
        (∀ j : Fin (2 ^ chunkWidth c), chunk'.1 j = chunk.1 j ^^^ (L.fold c).level (chunkWidth c) j.val) ∧
        chunk'.2 = chunk.2)
      (Programs.garbleChunkM lane delta bitKey c)
      (Programs.garbleChunkM lane (delta ^^^ L.delta) bitKey' c) := by
  unfold Programs.garbleChunkM
  have zeros : (labelAt fun position : Fin (chunkWidth c) => (chunkKey bitKey' c position).1) =
      fun n => (labelAt fun position : Fin (chunkWidth c) => (chunkKey bitKey c position).1) n ^^^
        (L.fold c).zero n := by
    funext n
    show _ = _ ^^^ labelAt (fun position : Fin (chunkWidth c) => L.zero (chunkBitIndex c position)) n
    rw [← labelAt_shift]
    congr 1
    funext position
    exact keys _
  rw [zeros]
  refine Sim.bind (sim_garbleFoldM O O' (L.fold c) lane c delta _ (chunkWidth c) (valid c) oracle entry)
    fun folded folded' related => Sim.pure' ⟨?_, related.2.1, ?_⟩
  · rw [related.1]
    rfl
  · rw [related.2.2]

/-- **One chunk's tables on the shifted tape.** -/
theorem sim_chunkTablesM (O O' : Oracle) (L : LaneShift) (valid : L.Valid) (count : Nat)
    (lane : Lane) (delta : Block) (bitKey bitKey' : Fin PlanB.coordinateBits → Block × Block)
    (keys : ∀ position, (bitKey' position).1 = (bitKey position).1 ^^^ L.zero position)
    (c : Fin chunkCount)
    (hotOracle : ∀ (n r : Nat) (half : Bool) (x : Block), n < chunkWidth c → r < 2 ^ n →
      O'.1.permutation (hotIndexNat lane c n r half) (x ^^^ ((L.fold c).hot n r half).1) =
        O.1.permutation (hotIndexNat lane c n r half) x ^^^ ((L.fold c).hot n r half).2)
    (scaleOracle : ∀ (j : Nat) (element : Fin count) (block : Fin 3) (x : Block),
      j < 2 ^ chunkWidth c →
      O'.1.permutation (scaleIndexOf lane c j element block)
          (x ^^^ (L.fold c).level (chunkWidth c) j) =
        O.1.permutation (scaleIndexOf lane c j element block) x ^^^
          (L.fold c).level (chunkWidth c) j)
    (hotEntry : ∀ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < chunkWidth c → n ≠ 0 →
      rel ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r),
        O.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r)⟩
        ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val),
        O'.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val)⟩)
    (scaleEntry : ∀ (j : Fin (2 ^ chunkWidth c)) (element : Fin count) (block : Fin 3),
      rel ⟨.fixedForward (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j),
        O.1.permutation (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j)⟩
        ⟨.fixedForward (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j ^^^ (L.fold c).level (chunkWidth c) j.val),
        O'.1.permutation (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j ^^^ (L.fold c).level (chunkWidth c) j.val)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun tables tables' => tables.1 = garbleChunk O.1 lane delta bitKey c ∧
        tables.2 = (fun switch => switchMask O.1 lane c switch.val
          ((garbleChunk O.1 lane delta bitKey c).1 switch)) ∧
        tables'.1.2 = tables.1.2 ∧ tables'.2 = tables.2)
      (Programs.chunkTablesM count lane delta bitKey c)
      (Programs.chunkTablesM count lane (delta ^^^ L.delta) bitKey' c) := by
  unfold Programs.chunkTablesM
  refine Sim.bind (sim_garbleChunkM O O' L valid lane delta bitKey bitKey' keys c hotOracle hotEntry)
    fun chunk chunk' related => ?_
  obtain ⟨rfl, labels, joins⟩ := related
  have shifted : (fun switch : Fin (2 ^ chunkWidth c) =>
      Programs.switchMaskM count lane c switch.val (chunk'.1 switch)) =
      fun switch => Programs.switchMaskM count lane c switch.val
        ((garbleChunk O.1 lane delta bitKey c).1 switch ^^^ (L.fold c).level (chunkWidth c) switch.val) := by
    funext switch
    rw [labels switch]
  rw [shifted]
  refine Sim.bind (Sim.vector (2 ^ chunkWidth c) _ _ fun switch =>
    sim_switchMaskM O O' count lane c switch.val _ _
      (fun element block x => scaleOracle switch.val element block x switch.isLt)
      (fun element block => scaleEntry switch element block))
    fun masks masks' related => Sim.pure' ⟨rfl, ?_, joins, ?_⟩
  · funext switch
    exact (related switch).1
  · funext switch
    exact (related switch).2

/-- **One lane on the shifted tape.** -/
theorem sim_laneM (O O' : Oracle) (L : LaneShift) (valid : L.Valid) (count : Nat)
    (lane : Lane) (delta : Block) (bitKey bitKey' : Fin PlanB.coordinateBits → Block × Block)
    (keys : ∀ position, (bitKey' position).1 = (bitKey position).1 ^^^ L.zero position)
    (hotOracle : ∀ (c : Fin chunkCount) (n r : Nat) (half : Bool) (x : Block), n < chunkWidth c →
      r < 2 ^ n →
      O'.1.permutation (hotIndexNat lane c n r half) (x ^^^ ((L.fold c).hot n r half).1) =
        O.1.permutation (hotIndexNat lane c n r half) x ^^^ ((L.fold c).hot n r half).2)
    (scaleOracle : ∀ (c : Fin chunkCount) (j : Nat) (element : Fin count) (block : Fin 3) (x : Block),
      j < 2 ^ chunkWidth c →
      O'.1.permutation (scaleIndexOf lane c j element block)
          (x ^^^ (L.fold c).level (chunkWidth c) j) =
        O.1.permutation (scaleIndexOf lane c j element block) x ^^^
          (L.fold c).level (chunkWidth c) j)
    (hotEntry : ∀ (c : Fin chunkCount) (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < chunkWidth c →
      n ≠ 0 →
      rel ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r),
        O.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r)⟩
        ⟨.fixedForward (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val),
        O'.1.permutation (hotIndexNat lane c n r.val half)
          ((garbleFold O.1 lane c delta (labelAt fun p => (chunkKey bitKey c p).1) n).1 r ^^^
            (L.fold c).level n r.val)⟩)
    (scaleEntry : ∀ (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c)) (element : Fin count)
      (block : Fin 3),
      rel ⟨.fixedForward (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j),
        O.1.permutation (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j)⟩
        ⟨.fixedForward (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j ^^^ (L.fold c).level (chunkWidth c) j.val),
        O'.1.permutation (scaleIndexOf lane c j.val element block)
          ((garbleChunk O.1 lane delta bitKey c).1 j ^^^ (L.fold c).level (chunkWidth c) j.val)⟩) :
    Sim (publicAnswer O) (publicAnswer O') rel
      (fun tables tables' => tables = Programs.laneTables O.1 count lane delta bitKey ∧
        tables'.masks = tables.masks ∧ ∀ c, (tables'.hot c).2 = (tables.hot c).2)
      (Programs.laneM count lane delta bitKey)
      (Programs.laneM count lane (delta ^^^ L.delta) bitKey') := by
  unfold Programs.laneM
  refine Sim.bind (Sim.pi chunkCount _ _ fun c => sim_chunkTablesM O O' L valid count lane delta
    bitKey bitKey' keys c (hotOracle c) (scaleOracle c) (hotEntry c) (scaleEntry c))
    fun tables tables' related => Sim.pure' ⟨?_, ?_, fun c => (related c).2.2.1⟩
  · unfold Programs.laneTables
    congr 1
    · funext c
      exact (related c).1
    · funext c
      rw [(related c).2.1]
  · show (fun c => (tables' c).2) = fun c => (tables c).2
    funext c
    exact (related c).2.2.2

end

end Kriterion.ArgoMAC.Security.Phase3.Hidden
