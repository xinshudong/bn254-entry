/-
**Phase 3, P1n — the off-curve law, step (i): the garbler's entries on an answer table.**

After `LawsTable.swapped_reduce` the garbler of `G1U°` runs on an answer table `A`. Off the curve
the entries `LawOff` plants are its EncPRF entries and its designed entries; on a table both are
transcripts of the evaluator's own programs:

* **the EncPRF entries are the pads' transcript at `k₁`** (`garbler_enc`): the EncPRF part of the
  garbler's transcript is `padsM`'s at the hash value of the bridge key (`enc_split` for any answer
  function), and the pads' questions read only the first whitening key (`padsM_first`);
* **the designed entries are system A's transcript** (`garbler_designed`): off the curve the
  designed entries are the curve lanes' inactive fold gates and switches (the filter of the two
  curve lanes' transcripts, `designedEntries_offCurve`'s argument for any answer function), and
  on a table the evaluator run on the published fold joins and the selected labels asks exactly
  those questions, in the same order, at the same inputs (correctness on the table).

Correctness on a table is read off the real-oracle lemmas (`Reach.evalFold_one_off`,
`evalHot_agrees_off_active`) through **the table's oracle** (`tableOracle`): at a mask cell the
translation by its limb, elsewhere the translation by its entry. Its Davies–Meyer values are the
table's limbs and entries, so its fold materials and switch masks are the table's
(`foldMaskM_table`, `switchMaskM_table`), whatever the labels.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsPrivate
import Proof.Privacy.Phase3.Hidden.Reach
import Proof.Privacy.Phase3.Hidden.CurveDesigned

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape)
open scoped ENNReal

noncomputable section

/-! ### 1. Transcripts of binds and loops -/

section Loops

variable (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)

theorem transcript_bind' {α β : Type} (P : FreeQuery Programs.Spec α)
    (f : α → FreeQuery Programs.Spec β) :
    transcript ans (P >>= f) = transcript ans P ++ transcript ans (f (P.eval ans)) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, transcript_eq_transcriptOf]
  exact Hidden.transcriptOf_bind ans P f

theorem transcript_pure' {α : Type} (value : α) :
    transcript ans (Pure.pure value : FreeQuery Programs.Spec α) = [] := rfl

theorem transcript_vector' {α : Type} : ∀ (count : Nat) (P : Fin count → FreeQuery Programs.Spec α),
    transcript ans (FreeQuery.vector count P) = (List.ofFn fun i => transcript ans (P i)).flatten
  | 0, _ => rfl
  | count + 1, P => by
      show transcript ans (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value)) = _
      rw [transcript_bind', transcript_bind', transcript_pure', transcript_vector' count,
        List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.append_nil]
      simp

theorem transcript_pi' : ∀ (count : Nat) {β : Fin count → Type}
    (P : (index : Fin count) → FreeQuery Programs.Spec (β index)),
    transcript ans (FreeQuery.pi count P) = (List.ofFn fun i => transcript ans (P i)).flatten
  | 0, _, _ => rfl
  | count + 1, _, P => by
      show transcript ans (P 0 >>= fun head => FreeQuery.pi count (fun index => P index.succ) >>=
          fun tail => Pure.pure (Fin.cons head tail)) = _
      rw [transcript_bind', transcript_bind', transcript_pure', transcript_pi' count,
        List.ofFn_succ, List.flatten_cons, List.append_nil]

/-- A filter of a flattened family is the flattened family of filters. -/
theorem filter_flatten_ofFn {α : Type} {count : Nat} (keep : α → Bool) (f : Fin count → List α) :
    (List.ofFn f).flatten.filter keep = (List.ofFn fun i => (f i).filter keep).flatten := by
  rw [List.filter_flatten, List.map_ofFn]
  rfl

/-- Two flattened families agree if they agree entrywise. -/
theorem flatten_ofFn_congr {α : Type} {count : Nat} {f g : Fin count → List α}
    (same : ∀ i, f i = g i) : (List.ofFn f).flatten = (List.ofFn g).flatten := by
  rw [funext same]

end Loops

/-! ### 2. The table's oracle -/

/-- Translation by a block, as a permutation. -/
def xorPerm (c : Block) : Equiv.Perm Block where
  toFun x := x ^^^ c
  invFun x := x ^^^ c
  left_inv x := by
    show (x ^^^ c) ^^^ c = x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv x := by
    show (x ^^^ c) ^^^ c = x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **The table's oracle**: at a mask cell the translation by its limb, elsewhere the translation
by its entry. -/
def tableOracle (A : Table) : PermutationOracle FixedIndex Block :=
  ⟨fun index => @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
    (fun hit => xorPerm (A.2.2.2 (Classical.choose hit))) (fun hit => xorPerm (A.2.2.1 ⟨index, hit⟩))⟩

theorem xor_xor_cancel (a b : Block) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_cancel_pair (a b x : Block) : (a ^^^ x) ^^^ (b ^^^ x) = a ^^^ b := by
  rw [BitVec.xor_assoc, BitVec.xor_comm b x, ← BitVec.xor_assoc x x b, BitVec.xor_self,
    BitVec.zero_xor]

theorem hash_tableOracle_site (A : Table) (cell : Cell) (x : Block) :
    hash (tableOracle A) (siteIndex cell) x = A.2.2.2 cell := by
  have hit : siteIndex cell ∈ Set.range siteIndex := ⟨cell, rfl⟩
  show ((@dite _ (siteIndex cell ∈ Set.range siteIndex) (Classical.propDecidable _)
    (fun hit => xorPerm (A.2.2.2 (Classical.choose hit)))
    (fun hit => xorPerm (A.2.2.1 ⟨siteIndex cell, hit⟩))) x) ^^^ x = _
  rw [dif_pos hit, siteIndex_injective (Classical.choose_spec hit)]
  show (x ^^^ A.2.2.2 cell) ^^^ x = _
  rw [BitVec.xor_comm x, xor_xor_cancel]

theorem hash_tableOracle_other (A : Table) (o : OtherIndex) (x : Block) :
    hash (tableOracle A) o.1 x = A.2.2.1 o := by
  show ((@dite _ (o.1 ∈ Set.range siteIndex) (Classical.propDecidable _)
    (fun hit => xorPerm (A.2.2.2 (Classical.choose hit)))
    (fun hit => xorPerm (A.2.2.1 ⟨o.1, hit⟩))) x) ^^^ x = _
  rw [dif_neg o.2]
  show (x ^^^ A.2.2.1 o) ^^^ x = _
  rw [BitVec.xor_comm x, xor_xor_cancel]

theorem hashM_eval (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (index : FixedIndex) (x : Block) :
    (Programs.hashM index x).eval ans = @id Block (ans (.fixedForward index x)) ^^^ x := rfl

theorem hashM_table_site (A : Table) (cell : Cell) (x : Block) :
    (Programs.hashM (siteIndex cell) x).eval (tableAnswer A) = A.2.2.2 cell := by
  rw [hashM_eval, tableAnswer_site, id, xor_xor_cancel]

theorem hashM_table_other (A : Table) (o : OtherIndex) (x : Block) :
    (Programs.hashM o.1 x).eval (tableAnswer A) = A.2.2.1 o ^^^ x := by
  rw [hashM_eval, tableAnswer_other, id]

/-- The fold gates are not mask cells. -/
def hotOther (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (half : Bool) : OtherIndex :=
  ⟨hotIndexNat lane chunk step entry half, hot_not_site _ _ _ _ _⟩

/-- **On a table the fold material is the table's, whatever the label.** -/
theorem foldMaskM_table (A : Table) (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) :
    (Programs.foldMaskM lane chunk step entry label).eval (tableAnswer A) =
      foldMask (tableOracle A) lane chunk step entry label := by
  show (Programs.hashM (hotOther lane chunk step entry false).1 label).eval (tableAnswer A) ^^^
      (Programs.hashM (hotOther lane chunk step entry true).1 label).eval (tableAnswer A) =
    hash (tableOracle A) (hotOther lane chunk step entry false).1 label ^^^
      hash (tableOracle A) (hotOther lane chunk step entry true).1 label
  rw [hashM_table_other, hashM_table_other, hash_tableOracle_other, hash_tableOracle_other,
    xor_cancel_pair]

/-- The mask cell of a lane's scale gate. -/
def laneCell (lane : Lane) (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (element : Fin (laneCount lane)) (block : Fin 3) : Cell :=
  (⟨lane, chunk, switch, element⟩, block)

theorem laneCell_index (lane : Lane) (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (element : Fin (laneCount lane)) (block : Fin 3) :
    siteIndex (laneCell lane chunk switch element block) =
      scaleIndexOf lane chunk switch.val element block := rfl

/-- **On a table a lane's switch mask is the masks of the table's limbs, whatever the label.** -/
theorem switchMaskM_table (A : Table) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (label : Block) :
    (Programs.switchMaskM (laneCount lane) lane chunk switch.val label).eval (tableAnswer A) =
      switchMask (tableOracle A) lane chunk switch.val label := by
  funext element
  simp only [Programs.switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn]
  show sampleFp ((Programs.hashM (siteIndex (laneCell lane chunk switch element 0)) label).eval
      (tableAnswer A)) ((Programs.hashM (siteIndex (laneCell lane chunk switch element 1)) label).eval
      (tableAnswer A)) ((Programs.hashM (siteIndex (laneCell lane chunk switch element 2)) label).eval
      (tableAnswer A)) =
    sampleFp (hash (tableOracle A) (siteIndex (laneCell lane chunk switch element 0)) label)
      (hash (tableOracle A) (siteIndex (laneCell lane chunk switch element 1)) label)
      (hash (tableOracle A) (siteIndex (laneCell lane chunk switch element 2)) label)
  rw [hashM_table_site, hashM_table_site, hashM_table_site, hash_tableOracle_site,
    hash_tableOracle_site, hash_tableOracle_site]

/-! ### 3. The lanes on a table are the lanes on the table's oracle -/

section Eval

variable (A : Table) (lane : Lane) (chunk : Fin chunkCount)

theorem garbleStepM_table (step : Nat) (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (Programs.garbleStepM lane chunk step zeroLabel parent).eval (tableAnswer A) =
      garbleStep (tableOracle A) lane chunk step zeroLabel parent := by
  funext entry
  by_cases zero : step = 0
  · rw [Programs.garbleStepM, if_pos zero]
    simp only [garbleStep, if_pos zero, FreeQuery.eval_pure]
  · rw [Programs.garbleStepM, if_neg zero]
    simp only [garbleStep, if_neg zero, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn, foldMaskM_table]

theorem garbleFoldM_table (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    (Programs.garbleFoldM lane chunk delta zeroLabel steps).eval (tableAnswer A) =
      garbleFold (tableOracle A) lane chunk delta zeroLabel steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [Programs.garbleFoldM, garbleFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        garbleStepM_table]

theorem garbleChunkM_table (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (Programs.garbleChunkM lane delta bitKey chunk).eval (tableAnswer A) =
      garbleChunk (tableOracle A) lane delta bitKey chunk := by
  simp only [Programs.garbleChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure, garbleFoldM_table]
  rfl

/-- **A lane on a table is the lane on the table's oracle.** -/
theorem laneM_table (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (Programs.laneM (laneCount lane) lane delta bitKey).eval (tableAnswer A) =
      Programs.laneTables (tableOracle A) (laneCount lane) lane delta bitKey := by
  simp only [Programs.laneM, Programs.chunkTablesM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_pi, FreeQuery.eval_vector, garbleChunkM_table, switchMaskM_table]
  unfold Programs.laneTables
  congr 1
  funext c switch
  rw [Vector.get_ofFn]

theorem evalStepM_table (step : Nat) (bitLabel join : Block) (active : Fin (2 ^ step))
    (parent : Fin (2 ^ step) → Block) :
    (Programs.evalStepM lane chunk step bitLabel join active parent).eval (tableAnswer A) =
      evalStep (tableOracle A) lane chunk step bitLabel join active parent := by
  funext entry
  simp only [Programs.evalStepM, evalStep, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector]
  by_cases same : entry = active
  · rw [if_pos same, if_pos same]
    congr 1
    apply Programs.xorFoldExcept_congr
    intro other different
    simp only [Vector.get_ofFn, if_neg different, foldMaskM_table]
  · simp only [if_neg same, Vector.get_ofFn, foldMaskM_table]

theorem evalFoldM_table (value : Nat) (bitLabel join : Nat → Block) (steps : Nat) :
    (Programs.evalFoldM lane chunk value bitLabel join steps).eval (tableAnswer A) =
      evalFold (tableOracle A) lane chunk value bitLabel join steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [Programs.evalFoldM, evalFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        evalStepM_table]

end Eval

/-! ### 4. The shape of one chunk's transcripts -/

section Shape

variable (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (lane : Lane)
  (chunk : Fin chunkCount)

theorem transcript_ite {α : Type} (p : Prop) [Decidable p] (a b : FreeQuery Programs.Spec α) :
    transcript ans (if p then a else b) = if p then transcript ans a else transcript ans b := by
  split <;> rfl

theorem transcript_garbleFoldM_succ (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel (steps + 1)) =
      transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel steps) ++
        transcript ans (Programs.garbleStepM lane chunk steps (zeroLabel steps)
          ((Programs.garbleFoldM lane chunk delta zeroLabel steps).eval ans).1) := by
  show transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel steps >>= _) = _
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil]

theorem transcript_evalFoldM_succ (value : Nat) (bitLabel join : Nat → Block) (steps : Nat) :
    transcript ans (Programs.evalFoldM lane chunk value bitLabel join (steps + 1)) =
      transcript ans (Programs.evalFoldM lane chunk value bitLabel join steps) ++
        transcript ans (Programs.evalStepM lane chunk steps (bitLabel steps) (join steps)
          (activeAt value steps) ((Programs.evalFoldM lane chunk value bitLabel join steps).eval ans)) := by
  show transcript ans (Programs.evalFoldM lane chunk value bitLabel join steps >>= _) = _
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil]

/-- The garbler's fold of width two asks the four gates of step `1`. -/
theorem transcript_garbleFoldM_two (delta : Block) (zeroLabel : Nat → Block) :
    transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel 2) =
      (List.ofFn fun r : Fin (2 ^ 1) => transcript ans (Programs.foldMaskM lane chunk 1 r.val
        (((Programs.garbleFoldM lane chunk delta zeroLabel 1).eval ans).1 r))).flatten := by
  rw [transcript_garbleFoldM_succ ans lane chunk delta zeroLabel 1,
    transcript_garbleFoldM_succ ans lane chunk delta zeroLabel 0]
  unfold Programs.garbleStepM
  rw [if_pos rfl, if_neg (by decide), transcript_bind', transcript_vector']
  simp only [transcript_pure', List.append_nil]
  rfl

/-- The evaluator's fold of width two asks the two gates of step `1` at the inactive parent. -/
theorem transcript_evalFoldM_two (value : Nat) (bitLabel join : Nat → Block) :
    transcript ans (Programs.evalFoldM lane chunk value bitLabel join 2) =
      (List.ofFn fun r : Fin (2 ^ 1) => if r = activeAt value 1 then [] else
        transcript ans (Programs.foldMaskM lane chunk 1 r.val
          (((Programs.evalFoldM lane chunk value bitLabel join 1).eval ans) r))).flatten := by
  rw [transcript_evalFoldM_succ ans lane chunk value bitLabel join 1,
    transcript_evalFoldM_succ ans lane chunk value bitLabel join 0]
  have zero : transcript ans (Programs.evalStepM lane chunk 0 (bitLabel 0) (join 0) (activeAt value 0)
      ((Programs.evalFoldM lane chunk value bitLabel join 0).eval ans)) = [] := by
    unfold Programs.evalStepM
    rw [transcript_bind', transcript_vector']
    simp only [transcript_pure', List.append_nil]
    rw [List.ofFn_succ, List.ofFn_zero]
    rw [if_pos (Fin.ext (by simp [activeAt]))]
    rfl
  rw [zero]
  unfold Programs.evalStepM
  rw [transcript_bind', transcript_vector']
  simp only [transcript_pure', List.append_nil, transcript_ite]
  rfl

theorem transcript_garbleChunkM (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    transcript ans (Programs.garbleChunkM lane delta bitKey chunk) =
      transcript ans (Programs.garbleFoldM lane chunk delta
        (labelAt fun position => (chunkKey bitKey chunk position).1) (chunkWidth chunk)) := by
  unfold Programs.garbleChunkM
  rw [transcript_bind', transcript_pure', List.append_nil]

theorem transcript_chunkTablesM (count : Nat) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    transcript ans (Programs.chunkTablesM count lane delta bitKey chunk) =
      transcript ans (Programs.garbleFoldM lane chunk delta
        (labelAt fun position => (chunkKey bitKey chunk position).1) (chunkWidth chunk)) ++
      (List.ofFn fun switch : Fin (2 ^ chunkWidth chunk) =>
        transcript ans (Programs.switchMaskM count lane chunk switch.val
          (((Programs.garbleChunkM lane delta bitKey chunk).eval ans).1 switch))).flatten := by
  unfold Programs.chunkTablesM
  rw [transcript_bind', transcript_garbleChunkM, transcript_bind', transcript_vector',
    transcript_pure', List.append_nil]

theorem transcript_evalChunkM (count : Nat) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    transcript ans (Programs.evalChunkM count lane joins scale bits labels chunk) =
      transcript ans (Programs.evalFoldM lane chunk (chunkValue bits chunk).toNat
        (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk)) (chunkWidth chunk)) ++
      (List.ofFn fun switch : Fin (2 ^ chunkWidth chunk) => if switch = chunkOf bits chunk then [] else
        transcript ans (Programs.switchMaskM count lane chunk switch.val
          (((Programs.evalFoldM lane chunk (chunkValue bits chunk).toNat
            (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk))
            (chunkWidth chunk)).eval ans) switch))).flatten := by
  unfold Programs.evalChunkM Programs.evalMasksM
  rw [transcript_bind', transcript_bind', transcript_bind', transcript_vector']
  simp only [transcript_pure', List.append_nil, transcript_ite]

theorem hashM_only {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} (index : FixedIndex)
    (label : Block) (holds : S (.fixedForward index label)) :
    Hidden.QueryOnly S (Programs.hashM index label) :=
  Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ holds) fun _ => Hidden.QueryOnly.pure' _

/-- A transcript all of whose questions a filter decides alike is kept whole or dropped. -/
theorem filter_transcript_const {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    {P : FreeQuery Programs.Spec α} (only : Hidden.QueryOnly S P)
    (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool) (b : Bool)
    (value : ∀ e : Entry FixedIndex EncPRF.PermutationIndex, S e.1 → keep e = b) :
    (transcript ans P).filter keep = if b = true then transcript ans P else [] := by
  have mem : ∀ e ∈ transcript ans P, keep e = b := fun e member =>
    value e (only.mem ans e (by rw [← transcript_eq_transcriptOf]; exact member))
  cases b
  · rw [if_neg Bool.false_ne_true]
    exact List.filter_eq_nil_iff.mpr fun e member => by simp [mem e member]
  · rw [if_pos rfl]
    exact List.filter_eq_self.mpr fun e member => mem e member

/-- **The fold of width two, filtered to the inactive parent, is the evaluator's fold** — when the
filter keeps exactly the inactive parent's gates and the level-1 labels agree off the active
parent. -/
theorem fold_filter_two (keep : Entry FixedIndex EncPRF.PermutationIndex → Bool) (delta : Block)
    (zeroLabel : Nat → Block) (value : Nat) (bitLabel join : Nat → Block)
    (keepHot : ∀ (r : Fin (2 ^ 1)) (half : Bool) (x : Block)
      (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex)
        (hotIndexNat lane chunk 1 r.val half) x).Answer),
      keep ⟨.fixedForward (hotIndexNat lane chunk 1 r.val half) x, y⟩ = decide (r ≠ activeAt value 1))
    (level : ∀ r : Fin (2 ^ 1), r ≠ activeAt value 1 →
      (Programs.evalFoldM lane chunk value bitLabel join 1).eval ans r =
        ((Programs.garbleFoldM lane chunk delta zeroLabel 1).eval ans).1 r) :
    ∀ n, n = 2 → (transcript ans (Programs.garbleFoldM lane chunk delta zeroLabel n)).filter keep =
      transcript ans (Programs.evalFoldM lane chunk value bitLabel join n) := by
  intro n hn
  subst hn
  rw [transcript_garbleFoldM_two, transcript_evalFoldM_two, filter_flatten_ofFn]
  refine flatten_ofFn_congr fun r => ?_
  have only : Hidden.QueryOnly (fun q => ∃ half x, q = .fixedForward (hotIndexNat lane chunk 1 r.val half) x)
      (Programs.foldMaskM lane chunk 1 r.val
        (((Programs.garbleFoldM lane chunk delta zeroLabel 1).eval ans).1 r)) :=
    Hidden.QueryOnly.bind (hashM_only _ _ ⟨false, _, rfl⟩) fun _ =>
      Hidden.QueryOnly.bind (hashM_only _ _ ⟨true, _, rfl⟩) fun _ => Hidden.QueryOnly.pure' _
  rw [filter_transcript_const ans only keep (decide (r ≠ activeAt value 1)) (by
    rintro ⟨q, y⟩ ⟨half, x, rfl⟩
    exact keepHot r half x y)]
  by_cases active : r = activeAt value 1
  · rw [if_pos active]
    simp [active]
  · rw [if_neg active, if_pos (decide_eq_true active), level r active]

end Shape

/-! ### 5. One chunk, one curve lane: the designed entries are the evaluator's questions -/

section Chunk

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (tape : Coins × Oracle)
  (input : AffineInput)

theorem keep_hot (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount) (r : Nat)
    (small : r < 2) (half : Bool) (x : Block)
    (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex)
      (hotIndexNat lane chunk 1 r half) x).Answer) :
    designedKeep scalar tape input ⟨.fixedForward (hotIndexNat lane chunk 1 r half) x, y⟩ =
      decide (r ≠ (chunkOf (inputBits input lane.coord) chunk).val % 2) := by
  have four : r % 2 ^ chunkBits = r := Nat.mod_eq_of_lt (by unfold chunkBits; omega)
  simp only [designedKeep, designedRule, designedIndex, hotIndexNat, Entry.IsEnc, curve,
    Bool.true_or, Bool.and_true, Bool.not_false, Bool.true_and, four]
  rfl

theorem keep_scale (lane : Lane) (curve : laneIsCurve lane = true) (chunk : Fin chunkCount)
    (switch : Fin (2 ^ chunkWidth chunk)) (element : Fin (laneCount lane)) (block : Fin 3) (x : Block)
    (y : (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex)
      (scaleIndexOf lane chunk switch.val element block) x).Answer) :
    designedKeep scalar tape input ⟨.fixedForward (scaleIndexOf lane chunk switch.val element block) x, y⟩ =
      decide (switch ≠ chunkOf (inputBits input lane.coord) chunk) := by
  have small : switch.val % 2 ^ chunkBits = switch.val :=
    Nat.mod_eq_of_lt (Pipeline.switch_lt_twoPowChunkBits chunk switch)
  simp only [designedKeep, designedRule, designedIndex, scaleIndexOf, scaleIndexNat, Entry.IsEnc,
    curve, Bool.true_or, Bool.and_true, Bool.not_false, Bool.true_and, small]
  simp only [ne_eq, decide_not, Fin.ext_iff]

/-- A lane's switch mask asks only that switch's scale gates. -/
theorem switchMaskM_only (lane : Lane) (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk))
    (label : Block) :
    Hidden.QueryOnly (fun q => ∃ (element : Fin (laneCount lane)) (block : Fin 3) (x : Block),
        q = .fixedForward (scaleIndexOf lane chunk switch.val element block) x)
      (Programs.switchMaskM (laneCount lane) lane chunk switch.val label) :=
  Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun element =>
    Hidden.QueryOnly.bind (hashM_only _ _ ⟨element, 0, _, rfl⟩) fun _ =>
      Hidden.QueryOnly.bind (hashM_only _ _ ⟨element, 1, _, rfl⟩) fun _ =>
        Hidden.QueryOnly.bind (hashM_only _ _ ⟨element, 2, _, rfl⟩) fun _ =>
          Hidden.QueryOnly.pure' _) fun _ => Hidden.QueryOnly.pure' _

/-- **One chunk of a curve lane, on a table**: the designed part of the garbler's questions is
the evaluator's questions, run on the lane's published fold joins and the selected labels. -/
theorem chunk_designed (A : Table) (lane : Lane) (curve : laneIsCurve lane = true) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (bitsEq : inputBits input lane.coord = bits) (chunk : Fin chunkCount) :
    (transcript (tableAnswer A) (Programs.chunkTablesM (laneCount lane) lane delta bitKey chunk)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (Programs.evalChunkM (laneCount lane) lane
        (hotJoins (tableOracle A) lane delta bitKey) scale bits (selectBits bitKey bits) chunk) := by
  rw [transcript_chunkTablesM, transcript_evalChunkM, List.filter_append, filter_flatten_ofFn]
  congr 1
  · refine fold_filter_two (tableAnswer A) lane chunk _ delta _ _ _ _ ?_ ?_ (chunkWidth chunk)
      (Hidden.chunkWidth_eq_two chunk)
    · intro r half x y
      rw [keep_hot scalar tape input lane curve chunk r.val (by have := r.isLt; omega) half x y,
        bitsEq]
      congr 1
      simp only [ne_eq, eq_iff_iff]
      rw [Fin.ext_iff]
      have value : (chunkValue bits chunk).toNat = (chunkOf bits chunk).val := chunkValue_toNat _ _
      show ¬ r.val = (chunkOf bits chunk).val % 2 ↔ ¬ r.val = (chunkValue bits chunk).toNat % 2 ^ 1
      rw [value]
      rfl
    · intro r off
      rw [evalFoldM_table, garbleFoldM_table]
      have value : (chunkValue bits chunk).toNat = (chunkOf bits chunk).val := chunkValue_toNat _ _
      refine evalFold_one_off (tableOracle A) lane delta bitKey correlated bits chunk r ?_
      intro same
      apply off
      refine Fin.ext ?_
      show r.val = (chunkValue bits chunk).toNat % 2 ^ 1
      rw [value]
      exact same
  · refine flatten_ofFn_congr fun switch => ?_
    rw [filter_transcript_const (tableAnswer A) (switchMaskM_only lane chunk switch _) _
      (decide (switch ≠ chunkOf bits chunk)) (by
        rintro ⟨q, y⟩ ⟨element, block, x, rfl⟩
        rw [keep_scale scalar tape input lane curve chunk switch element block x y, bitsEq])]
    by_cases active : switch = chunkOf bits chunk
    · rw [if_pos active]
      simp [active]
    · rw [if_neg active, if_pos (decide_eq_true active)]
      congr 2
      rw [garbleChunkM_table, evalFoldM_table]
      show _ = evalHot (tableOracle A) lane chunk (chunkWidth chunk)
        (hotSlice (hotJoins (tableOracle A) lane delta bitKey) chunk)
        (chunkLabels (selectBits bitKey bits) chunk) (chunkValue bits chunk) switch
      have slices := hotSlice_hotJoins (tableOracle A) lane delta bitKey chunk
      have labels := chunkLabels_selectBits bitKey bits chunk
      have agrees := evalHot_agrees_off_active (oracle := tableOracle A) (lane := lane) correlated
        bits chunk switch active
      exact agrees.symm.trans (congrArg₂ (fun joins held => evalHot (tableOracle A) lane chunk
        (chunkWidth chunk) joins held (chunkValue bits chunk) switch) slices.symm labels.symm)

/-- **One curve lane, on a table**: its designed questions are the evaluator's. -/
theorem lane_designed (A : Table) (lane : Lane) (curve : laneIsCurve lane = true) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block)
    (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField) (bits : BitVec coordinateBitCount)
    (bitsEq : inputBits input lane.coord = bits) :
    (transcript (tableAnswer A) (Programs.laneM (laneCount lane) lane delta bitKey)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (Programs.evalLaneM (laneCount lane) lane
        (hotJoins (tableOracle A) lane delta bitKey) scale bits (selectBits bitKey bits)) := by
  unfold Programs.laneM Programs.evalLaneM
  rw [transcript_bind', transcript_bind', transcript_pi', transcript_vector', transcript_pure',
    transcript_pure', List.append_nil, List.append_nil, filter_flatten_ofFn]
  exact flatten_ofFn_congr fun chunk => chunk_designed scalar tape input A lane curve delta bitKey
    correlated scale bits bitsEq chunk

/-- **Off the curve the designed entries are the curve lanes'**, on any answers. -/
theorem garbler_designed_lanes (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (coins : Coins) (invalid : validate input = false) :
    (transcript ans (Programs.garbleM scalar coins)).filter (designedKeep scalar tape input) =
      (transcript ans (Programs.laneM curveElementCountX .curveX (coins.inputDelta .x)
          (Pipeline.bitKeyOf coins.inputMacKey .x))).filter (designedKeep scalar tape input) ++
      (transcript ans (Programs.laneM curveElementCountY .curveY (coins.inputDelta .y)
          (Pipeline.bitKeyOf coins.inputMacKey .y))).filter (designedKeep scalar tape input) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, transcript_eq_transcriptOf]
  unfold Programs.garbleM
  simp only [Hidden.transcriptOf_bind, List.filter_append]
  have hashNil : ∀ value, (Hidden.transcriptOf ans (Programs.askHash value)).filter
      (designedKeep scalar tape input) = [] := fun value => by
    show [(⟨.hash value, ans (.hash value)⟩ : Entry FixedIndex EncPRF.PermutationIndex)].filter _ = []
    simp [designedKeep, designedRule, invalid, Entry.IsEnc]
  have padsNil : ∀ keys, (Hidden.transcriptOf ans (Programs.padsM keys)).filter
      (designedKeep scalar tape input) = [] := fun keys =>
    filter_nil_of_only (Hidden.padsM_encOnly keys) _ _ (keep_enc scalar tape input)
  have pointNil : ∀ count ℓ delta bitKey, laneIsCurve ℓ = false →
      (Hidden.transcriptOf ans (Programs.laneM count ℓ delta bitKey)).filter
        (designedKeep scalar tape input) = [] := fun count ℓ delta bitKey point =>
    filter_nil_of_only (laneM_laneOnly count ℓ delta bitKey) _ _
      (keep_point scalar tape input invalid ℓ point)
  have gadgetNil : ∀ keys inputKey pads,
      (Hidden.transcriptOf ans (Programs.gadgetM keys inputKey pads)).filter
        (designedKeep scalar tape input) = [] := fun keys inputKey pads =>
    filter_nil_of_only (gadgetM_gadgetOnly keys inputKey pads) _ _
      (keep_gadget scalar tape input invalid)
  have pureNil : ∀ {β : Type} (value : β), (Hidden.transcriptOf ans
      (Pure.pure value : FreeQuery Programs.Spec β)).filter (designedKeep scalar tape input) = [] :=
    fun _ => rfl
  rw [hashNil, padsNil, pointNil _ .pointX _ _ rfl, pointNil _ .pointY _ _ rfl, gadgetNil, pureNil]
  simp only [List.nil_append, List.append_nil]

end Chunk

/-! ### 6. The EncPRF entries -/

section Enc

variable [FieldCertificate] [GroupCertificate]
  (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)

/-- The EncPRF part of a hash-then-pads-then-fixed-key program is the pads' transcript, on any
answers. -/
theorem enc_split' {β : Type} (t : BaseField)
    (R : Block × Block → Programs.Pads → FreeQuery Programs.Spec β)
    (only : ∀ h p, Hidden.QueryOnly Hidden.IsFixedForward (R h p)) :
    (transcript ans (Programs.askHash t >>= fun h =>
        Programs.padsM ⟨h.1, h.2⟩ >>= fun p => R h p)).filter Entry.IsEnc =
      transcript ans (Programs.padsM ⟨((Programs.askHash t).eval ans).1,
        ((Programs.askHash t).eval ans).2⟩) := by
  rw [transcript_eq_transcriptOf, transcript_eq_transcriptOf, Hidden.transcriptOf_bind,
    Hidden.transcriptOf_bind]
  have hashHead : Hidden.transcriptOf ans (Programs.askHash t) = [⟨.hash t, ans (.hash t)⟩] := rfl
  rw [hashHead, List.filter_append, List.filter_append,
    filter_none _ [_] (fun a member => by rcases List.mem_singleton.mp member with rfl; rfl),
    filter_all _ _ fun a member => isEnc_of_encForward a ((Hidden.padsM_encOnly _).mem _ a member),
    filter_none _ _ fun a member => isEnc_of_fixedForward a ((only _ _).mem _ a member),
    List.nil_append, List.append_nil]

theorem transcript_padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    transcript ans (Programs.padM keys coordinate index bit) =
      transcript ans (Programs.askEnc (coordinate, index) (encodeBit bit ^^^ keys.first)) := by
  unfold Programs.padM
  rw [transcript_bind', transcript_pure', List.append_nil]

/-- **The pads' questions read only the first whitening key.** -/
theorem padsM_first (keys : WhiteningKeys) :
    transcript ans (Programs.padsM keys) = transcript ans (Programs.padsM ⟨keys.first, 0⟩) := by
  unfold Programs.padsM
  simp only [transcript_bind', transcript_vector', transcript_pure', List.append_nil,
    transcript_padM]

/-- The pads of a table, at the table's hash value of the bridge key. -/
def tablePads (A : Table) (coins : Coins) : Programs.Pads :=
  (Programs.padsM ⟨(A.2.1 coins.bridgeKey).1, (A.2.1 coins.bridgeKey).2⟩).eval (tableAnswer A)

/-- **The garbler's EncPRF entries are the pads' transcript at `k₁`.** -/
theorem garbler_enc (scalar : NonZeroScalar) (coins : Coins) :
    (transcript ans (Programs.garbleM scalar coins)).filter Entry.IsEnc =
      transcript ans (Programs.padsM ⟨((Programs.askHash coins.bridgeKey).eval ans).1, 0⟩) := by
  unfold Programs.garbleM
  refine (enc_split' ans coins.bridgeKey _ fun _ _ => ?_).trans (padsM_first ans _)
  exact Hidden.QueryOnly.bind (Hidden.laneM_fixedOnly _ _ _ _) fun _ =>
    Hidden.QueryOnly.bind (Hidden.laneM_fixedOnly _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.laneM_fixedOnly _ _ _ _) fun _ =>
        Hidden.QueryOnly.bind (Hidden.laneM_fixedOnly _ _ _ _) fun _ =>
          Hidden.QueryOnly.bind (Hidden.gadgetM_fixedOnly _ _ _) fun _ => Hidden.QueryOnly.pure' _

/-- **The garbler on a table**: the assembly of the lanes on the table's oracle, the table's pads
and the gadget on the table. -/
theorem garbleM_table (scalar : NonZeroScalar) (A : Table) (coins : Coins) :
    (Programs.garbleM scalar coins).eval (tableAnswer A) =
      (Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
        coins.pointRandomness coins.bridgeKey coins.curveMask coins.curveR1 coins.curveR2
        (Programs.laneTables (tableOracle A) curveElementCountX .curveX (coins.inputDelta .x)
          (Pipeline.bitKeyOf coins.inputMacKey .x))
        (Programs.laneTables (tableOracle A) curveElementCountY .curveY (coins.inputDelta .y)
          (Pipeline.bitKeyOf coins.inputMacKey .y))
        (Programs.laneTables (tableOracle A) pointElementCountX .pointX (coins.inputDelta .x)
          (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .x))
        (Programs.laneTables (tableOracle A) pointElementCountY .pointY (coins.inputDelta .y)
          (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .y))
        ((Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
          (Programs.transformKeyOf (tablePads A coins) coins.inputMacKey) coins.exceptionPad).eval
            (tableAnswer A)),
       coins.inputMacKey) := by
  have cx := laneM_table A .curveX (coins.inputDelta .x) (Pipeline.bitKeyOf coins.inputMacKey .x)
  have cy := laneM_table A .curveY (coins.inputDelta .y) (Pipeline.bitKeyOf coins.inputMacKey .y)
  have px := laneM_table A .pointX (coins.inputDelta .x)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .x)
  have py := laneM_table A .pointY (coins.inputDelta .y)
    (Pipeline.bitKeyOf (Programs.whitenKeyOf (tablePads A coins) coins.inputMacKey) .y)
  simp only [laneCount] at cx cy px py
  unfold tablePads at px py ⊢
  have hashEq : (Programs.askHash coins.bridgeKey).eval (tableAnswer A) = A.2.1 coins.bridgeKey := rfl
  simp only [Programs.garbleM, FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [hashEq, cx, cy, px, py]

end Enc

/-! ### 7. The garbler's planted entries on a table, off the curve -/

section Designed

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (tape : Coins × Oracle)
  (input : AffineInput)

/-- The coins' label pairs are free-XOR correlated. -/
theorem correlated_coins (coins : Coins) (coord : Coord) :
    ∀ position, (Pipeline.bitKeyOf coins.inputMacKey coord position).2 =
      (Pipeline.bitKeyOf coins.inputMacKey coord position).1 ^^^ coins.inputDelta coord := by
  intro position
  cases coord <;>
    simp [Pipeline.bitKeyOf, Kriterion.ArgoMAC.Scheme.Coins.inputMacKey, Vector.get_ofFn]

/-- **Off the curve, on a table, the designed entries are system A's questions** on the published
value and the selected labels. -/
theorem garbler_designed (A : Table) (coins : Coins) (invalid : validate input = false) :
    (transcript (tableAnswer A) (Programs.garbleM scalar coins)).filter
        (designedKeep scalar tape input) =
      transcript (tableAnswer A) (systemAM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (BitInput.ofAffine input) (coins.inputMacKey.encode (BitInput.ofAffine input))) := by
  rw [garbler_designed_lanes scalar tape input _ coins invalid, garbleM_table]
  unfold systemAM
  rw [transcript_bind', transcript_bind', transcript_pure', List.append_nil,
    Pipeline.macLabels_encode, Pipeline.macLabels_encode]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact lane_designed scalar tape input A .curveX rfl (coins.inputDelta .x)
      (Pipeline.bitKeyOf coins.inputMacKey .x) (correlated_coins coins .x) _ _ rfl
  · exact lane_designed scalar tape input A .curveY rfl (coins.inputDelta .y)
      (Pipeline.bitKeyOf coins.inputMacKey .y) (correlated_coins coins .y) _ _ rfl

end Designed

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
