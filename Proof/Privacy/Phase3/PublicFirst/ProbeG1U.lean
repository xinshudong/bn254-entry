/-
**Phase 3, P1g — the off-curve probe, and its law in `G1U`.**

The probe adversary (`probeAdversary`) makes no stage-1 query and selects the off-curve input
`(0, 0)`. In stage 2 it runs the honest evaluator's system A on chunk `0` of the `curveX` lane —
the width-2 fold (two fixed-key questions) and the three Davies–Meyer blocks of one element of the
inactive switch `1` — and reports whether the resulting mask is below `R = 2^384 mod p`
(`probeM`, five questions).

**In `G1U`** every question of the probe is a garbler entry the reach also asks — the evaluator's
fold labels agree with the garbler's off the active entry (`evalHot_agrees_off_active`,
`evalFold_garbleFold`) — so it is installed with the tape's answer (`plantAll_stored`), and the
probe reads the garbler's own swapped mask at the site `(curveX, 0, 1, 0)`
(`hiddenDeleted_probe`): `G1U` outputs `true` with mass exactly `R/p`
(`hiddenDeleted_probe_true`, from `MaskSwap.swappedTape_garblerMasks`).
-/

import Proof.Privacy.Phase3.PublicFirst.Probe
import Proof.Privacy.Phase3.Lazy.ChunkZero
import Proof.Correctness.PGS.AffineFp

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary chunkZero)
open Kriterion.ArgoMAC.Phase3.Lazy (LState inactiveEntry foldLabels)
open scoped ENNReal

noncomputable section

/-! ### 1. The probe -/

/-- The off-curve input `(0, 0)`. -/
def offInput : AffineInput := ⟨0, 0⟩

theorem three_ne_zero_base : (3 : BaseField) ≠ 0 := by
  have cast : ((3 : ℕ) : BaseField) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 3 baseFieldModulus).not.mpr (by decide)
  exact_mod_cast cast

/-- `(0, 0)` is off the curve: `0 ≠ 0³ + 3`. -/
theorem offInput_offCurve : ¬ OnCurve offInput := by
  unfold OnCurve offInput
  intro equal
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at equal
  exact three_ne_zero_base equal.symm

/-- The scalar-multiplication function refuses `(0, 0)`. -/
theorem function_offInput [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) :
    Scheme.scheme.function scalar offInput = none := by
  have refused : decodePoint offInput = none := by
    by_contra defined
    exact offInput_offCurve ((decodePoint_defined offInput).mp defined)
  show checkedScalarMultiplication scalar.value offInput = none
  unfold checkedScalarMultiplication
  rw [refused]
  rfl

/-- The inactive switch the probe reads (the active switch of `(0, 0)` is `0`). -/
def probeSwitch : Fin (2 ^ chunkWidth chunkZero) := ⟨1, by decide⟩

/-- The element the probe reads. -/
def probeElement : Fin curveElementCountX := ⟨0, by decide⟩

/-- The three blocks of the probed mask, at a label, and the low-mask test. -/
def probeMaskM (label : Block) : Programs.M Bool :=
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 0) label >>=
    fun first =>
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 1) label >>=
    fun second =>
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 2) label >>=
    fun third => Pure.pure (lowMask (sampleFp first second third))

/-- The chunk value the evaluator folds (that of `(0, 0)`). -/
abbrev probeValue (labels : LamportSignature) : ℕ :=
  (chunkValue (Pipeline.coordBits (Lamport.restore offInput labels).input .x) chunkZero).toNat

/-- The bit labels the evaluator folds. -/
abbrev probeBitLabel (labels : LamportSignature) : ℕ → Block :=
  labelAt (chunkLabels (Pipeline.macLabels (Lamport.restore offInput labels).inputMac .x) chunkZero)

/-- The published fold joins the evaluator reads. -/
abbrev probeJoin (table : Public) : ℕ → Block := joinAt (hotSlice table.curveXHot chunkZero)

/-- The evaluator's fold of chunk `0` of `curveX`, from the published table and the labels. -/
def probeFoldM (table : Public) (labels : LamportSignature) :
    Programs.M (Fin (2 ^ chunkWidth chunkZero) → Block) :=
  Programs.evalFoldM .curveX chunkZero (probeValue labels) (probeBitLabel labels) (probeJoin table)
    (chunkWidth chunkZero)

/-- **The probe**: the fold, then the probed mask at the inactive switch's label. -/
def probeM (table : Public) (labels : LamportSignature) : Programs.M Bool :=
  probeFoldM table labels >>= fun hot => probeMaskM (hot probeSwitch)

theorem probeMaskM_bounded (label : Block) : FreeQuery.Bounded (probeMaskM label) 3 :=
  (FreeQuery.Bounded.bind (Programs.bounded_hashM _ _) fun _ =>
    FreeQuery.Bounded.bind (Programs.bounded_hashM _ _) fun _ =>
      FreeQuery.Bounded.bind (Programs.bounded_hashM _ _) fun _ =>
        FreeQuery.Bounded.pure' _ 0).of_eq (by norm_num)

theorem probeM_bounded (table : Public) (labels : LamportSignature) :
    FreeQuery.Bounded (probeM table labels) 5 :=
  (FreeQuery.Bounded.bind (Programs.bounded_evalFoldM _ _ _ _ _ _) fun _ =>
    probeMaskM_bounded _).of_eq (by decide)

/-- **The probe adversary**: no stage-1 query, the input `(0, 0)`, five stage-2 questions. -/
def probeAdversary : PlanBAdversary Unit where
  State := Unit
  firstQueryBudget _ := 0
  secondQueryBudget _ := 5
  chooseInput _ _ _ := .pure (PMF.pure (offInput, ()))
  decide _ table labels _ _ := freeOracle (probeM table labels) 5 (probeM_bounded table labels)

/-! ### 2. Transcripts of the probe's pieces -/

section Transcripts

variable (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer)

theorem transcript_hashM_bind {β : Type} (index : FixedIndex) (label : Block)
    (f : Block → FreeQuery Programs.Spec β) :
    transcript answer (Programs.hashM index label >>= f) =
      ⟨.fixedForward index label, answer (.fixedForward index label)⟩ ::
        transcript answer (f ((show Block from answer (.fixedForward index label)) ^^^ label)) := by
  unfold Programs.hashM
  rw [Kriterion.ArgoMAC.Phase3.Lazy.fq_bind_assoc]
  rfl

/-- The switch-mask loop's body at one element, as `switchMaskM` writes it. -/
def elementMaskM (label : Block) : Programs.M BaseField :=
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 0) label >>=
    fun first =>
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 1) label >>=
    fun second =>
  Programs.hashM (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement 2) label >>=
    fun third => Pure.pure (sampleFp first second third)

theorem transcript_probeMaskM (label : Block) :
    transcript answer (probeMaskM label) = transcript answer (elementMaskM label) := by
  unfold probeMaskM elementMaskM
  simp only [transcript_hashM_bind]
  rfl

end Transcripts

/-! ### 3. The tape's garbling -/

section Garbling

variable [FieldCertificate] [GroupCertificate]

/-- The challenge's garbling is the program's: the Plan B garbler on the tape. -/
theorem scheme_garble_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    Scheme.scheme.garble parameter scalar tape =
      (Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value tape.1.offsets)
        tape.1.pointRandomness tape.1.exceptionPad tape.1.bridgeKey tape.1.curveMask
        tape.1.curveR1 tape.1.curveR2 tape.2.1 tape.2.2.1 tape.2.2.2 tape.1.inputDelta
        tape.1.inputMacKey, tape.1.inputMacKey) := by
  rw [← Programs.garbleProgram_correct parameter scalar tape.1 tape.2, Programs.garbleProgram,
    FreeQuery.eval_toProgram, Programs.eval_garbleM]

/-- The published `curveX` fold joins are the garbler's. -/
theorem garble_curveXHot (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar tape).1.curveXHot =
      hotJoins tape.2.1 .curveX (tape.1.inputDelta .x) (Pipeline.bitKeyOf tape.1.inputMacKey .x) := by
  rw [scheme_garble_eq]
  rfl

/-- The wire adapter restores the selected labels. -/
theorem probe_restore (key : InputMacKey) :
    Lamport.restore offInput (Scheme.scheme.encode key offInput) =
      ⟨BitInput.ofAffine offInput, key.encode (BitInput.ofAffine offInput)⟩ := by
  show Lamport.restore offInput
      (Lamport.selectedLabels (key.encode (BitInput.ofAffine offInput))) = _
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine offInput))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [Lamport.restore, Lamport.selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

end Garbling

/-- The coins' label pairs are `Δ`-correlated. -/
theorem coins_correlated (coins : Coins) :
    ∀ position, (Pipeline.bitKeyOf coins.inputMacKey .x position).2 =
      (Pipeline.bitKeyOf coins.inputMacKey .x position).1 ^^^ coins.inputDelta .x := by
  intro position
  simp [Pipeline.bitKeyOf, Scheme.Coins.inputMacKey]

/-- The chunk-`0` value of `(0, 0)`'s `x` word is `0`. -/
theorem probe_chunkOf :
    chunkOf (Pipeline.coordBits (BitInput.ofAffine offInput) .x) chunkZero = ⟨0, by decide⟩ := by
  apply Fin.ext
  show (Pipeline.coordBits (BitInput.ofAffine offInput) .x).toNat >>> chunkOffset chunkZero
      % 2 ^ chunkWidth chunkZero = 0
  have zero : (Pipeline.coordBits (BitInput.ofAffine offInput) .x).toNat = 0 := by
    show (Kriterion.ArgoMAC.coordinateBits (0 : BaseField)).toNat = 0
    rw [coordinateBitsToNat, ZMod.val_zero]
  rw [zero]
  rfl

theorem probeSwitch_inactive :
    probeSwitch ≠ chunkOf (Pipeline.coordBits (BitInput.ofAffine offInput) .x) chunkZero := by
  rw [probe_chunkOf]
  decide

/-! ### 4. The fold labels agree with the garbler's -/

theorem xor_zero_block (a : Block) : a ^^^ (0 : Block) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro index _
  simp

section Labels

variable (oracle : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
  (delta : Block) (bitKey : Fin PlanB.coordinateBits → Block × Block)
  (correlated : ∀ position, (bitKey position).2 = (bitKey position).1 ^^^ delta)
  (bits : BitVec PlanB.coordinateBits)

include correlated in
/-- The selected bit labels of a chunk are the zero labels, complemented by `Δ` at set bits. -/
theorem chunk_bitLabel (step : ℕ) (inRange : step < chunkWidth c) :
    labelAt (selectBits (chunkKey bitKey c) (chunkValue bits c)) step
      = labelAt (fun position => (chunkKey bitKey c position).1) step
        ^^^ (if (chunkValue bits c).toNat.testBit step then delta else 0) := by
  have bitEq : (chunkValue bits c)[(⟨step, inRange⟩ : Fin (chunkWidth c))]
      = (chunkValue bits c).toNat.testBit step :=
    BitVec.getElem_eq_testBit_toNat (chunkValue bits c) step inRange
  simp only [labelAt, dif_pos inRange, selectBits, ← bitEq]
  by_cases bit : (chunkValue bits c)[(⟨step, inRange⟩ : Fin (chunkWidth c))] = true
  · rw [if_pos bit, if_pos bit, chunkKey_correlated bitKey delta correlated c]
  · rw [if_neg bit, if_neg bit, xor_zero_block]

include correlated in
/-- **The level-1 label of the inactive gate is the garbler's.** -/
theorem level_one_agrees
    (tail : PermutationOracle EncPRF.PermutationIndex Block × (BaseField → Block × Block))
    (join : ℕ → Block) (joinZero : join 0 = 0)
    (width : 0 < chunkWidth c) :
    (garbleFold oracle lane c delta (labelAt fun position => (chunkKey bitKey c position).1) 1).1
        ⟨inactiveEntry (chunkValue bits c).toNat, by
          unfold inactiveEntry; have := Nat.mod_lt (chunkValue bits c).toNat two_pos; omega⟩
      = join 0 ^^^ labelAt (selectBits (chunkKey bitKey c) (chunkValue bits c)) 0 := by
  set value := (chunkValue bits c).toNat
  set zeroLabel := labelAt fun position => (chunkKey bitKey c position).1
  set bitLabel := labelAt (selectBits (chunkKey bitKey c) (chunkValue bits c))
  have hbit : ∀ step, step < 1 →
      bitLabel step = zeroLabel step ^^^ (if value.testBit step then delta else 0) :=
    fun step small => chunk_bitLabel c delta bitKey correlated bits step (by omega)
  have hjoin : ∀ step, step < 1 → join step = (garbleFold oracle lane c delta zeroLabel 1).2 step := by
    intro step small
    have zero : step = 0 := by omega
    subst zero
    rw [joinZero, garbleFold_join_zero oracle lane c delta zeroLabel 1 one_pos]
  have main := evalFold_garbleFold oracle lane c delta zeroLabel bitLabel value 1 join hbit hjoin
    ⟨inactiveEntry value, by unfold inactiveEntry; have := Nat.mod_lt value two_pos; omega⟩
  have offActive : ¬ (inactiveEntry value = value % 2 ^ 1) := by
    unfold inactiveEntry
    have := Nat.mod_lt value two_pos
    rw [pow_one]
    omega
  rw [if_neg offActive, xor_zero_block] at main
  rw [← main]
  have evaluated := Programs.eval_evalFoldM (oracle, tail) lane c value bitLabel join 1
  rw [Kriterion.ArgoMAC.Phase3.Lazy.evalFoldM_one] at evaluated
  rw [← evaluated]
  rfl

end Labels

/-! ### 5. Where the probe's questions live: the garbler's transcript and the reach -/

section Membership

/-- The last level of a fold is part of it. -/
theorem mem_garbleFoldM_succ (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex,
      query.Answer) (lane : Lane) (c : Fin chunkCount) (delta : Block) (zeroLabel : ℕ → Block)
    (steps : ℕ) {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (Programs.garbleStepM lane c steps (zeroLabel steps)
      (FreeQuery.eval answer (Programs.garbleFoldM lane c delta zeroLabel steps)).1)) :
    entry ∈ transcript answer (Programs.garbleFoldM lane c delta zeroLabel (steps + 1)) := by
  show entry ∈ transcript answer (Programs.garbleFoldM lane c delta zeroLabel steps >>=
    fun previous => Programs.garbleStepM lane c steps (zeroLabel steps) previous.1 >>=
      fun right => Pure.pure (extendLevel steps previous.1 right,
        fun step => if step = steps then stepJoin steps (zeroLabel steps) right
          else previous.2 step))
  exact mem_transcript_right _ (mem_transcript_left _ member)

/-- The fold gates of chunk `0`'s level `1` are in the chunk's garbling, at the garbler's labels. -/
theorem chunkTables_fold_mem (oracle : Oracle) (count : ℕ) (lane : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) (gate : Fin (2 ^ 1)) (half : Bool) :
    (⟨.fixedForward (hotIndexNat lane chunkZero 1 gate.val half)
        ((garbleFold oracle.1 lane chunkZero delta
          (labelAt fun position => (chunkKey bitKey chunkZero position).1) 1).1 gate),
      publicAnswer oracle (.fixedForward (hotIndexNat lane chunkZero 1 gate.val half)
        ((garbleFold oracle.1 lane chunkZero delta
          (labelAt fun position => (chunkKey bitKey chunkZero position).1) 1).1 gate))⟩ :
        Entry FixedIndex EncPRF.PermutationIndex) ∈
      transcript (publicAnswer oracle) (Programs.chunkTablesM count lane delta bitKey chunkZero) := by
  unfold Programs.chunkTablesM Programs.garbleChunkM
  refine mem_transcript_left _ (mem_transcript_left _ ?_)
  refine mem_garbleFoldM_succ _ lane chunkZero delta _ 1 ?_
  simp only [Programs.eval_garbleFoldM]
  unfold Programs.garbleStepM
  rw [if_neg one_ne_zero]
  refine mem_transcript_left _ (mem_transcript_vector _ _ _ gate ?_)
  unfold Programs.foldMaskM
  cases half
  · exact mem_transcript_left _ (mem_transcript_left _ (by
      rw [transcript_askFixed]; exact List.mem_singleton_self _))
  · exact mem_transcript_right _ (mem_transcript_left _ (mem_transcript_left _ (by
      rw [transcript_askFixed]; exact List.mem_singleton_self _)))

/-- The probed element's blocks are in the chunk's garbling, at the garbler's switch label. -/
theorem chunkTables_scale_mem (oracle : Oracle) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript (publicAnswer oracle)
      (elementMaskM ((garbleChunk oracle.1 .curveX delta bitKey chunkZero).1 probeSwitch))) :
    entry ∈ transcript (publicAnswer oracle)
      (Programs.chunkTablesM curveElementCountX .curveX delta bitKey chunkZero) := by
  unfold Programs.chunkTablesM
  refine mem_transcript_right _ ?_
  rw [Programs.eval_garbleChunkM oracle .curveX delta bitKey chunkZero]
  refine mem_transcript_left _ (mem_transcript_vector _ _ _ probeSwitch ?_)
  unfold Programs.switchMaskM
  exact mem_transcript_left _ (mem_transcript_vector _ _ _ probeElement member)

variable [FieldCertificate] [GroupCertificate]

/-- The `curveX` lane's garbling is part of the garbler's transcript. -/
theorem garbler_of_curveX (scalar : NonZeroScalar) (tape : Coins × Oracle)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript (publicAnswer tape.2)
      (Programs.chunkTablesM curveElementCountX .curveX (tape.1.inputDelta .x)
        (Pipeline.bitKeyOf tape.1.inputMacKey .x) chunkZero)) :
    entry ∈ garblerTranscript scalar tape := by
  unfold garblerTranscript Programs.garbleM
  dsimp only
  refine mem_transcript_right _ (mem_transcript_right _ (mem_transcript_left _ ?_))
  unfold Programs.laneM
  exact mem_transcript_left _ (mem_transcript_pi _ _ _ chunkZero member)

/-- Chunk `0` of the `curveX` lane's evaluation is part of the reach. -/
theorem reach_of_chunk (table : Public) (labels : LamportSignature) (tape : Coins × Oracle)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript (publicAnswer tape.2)
      (Programs.evalChunkM curveElementCountX .curveX table.curveXHot
        (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
        (Pipeline.coordBits (Lamport.restore offInput labels).input .x)
        (Pipeline.macLabels (Lamport.restore offInput labels).inputMac .x) chunkZero)) :
    entry ∈ reachTranscript table offInput labels tape := by
  unfold reachTranscript Programs.onCurveM
  refine mem_transcript_left _ ?_
  unfold Programs.evalLaneM
  exact mem_transcript_left _ (mem_transcript_vector _ _ _ chunkZero member)

/-- The probe's fold is the reach's. -/
theorem reach_fold_mem (table : Public) (labels : LamportSignature) (tape : Coins × Oracle)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript (publicAnswer tape.2) (probeFoldM table labels)) :
    entry ∈ reachTranscript table offInput labels tape := by
  refine reach_of_chunk table labels tape ?_
  unfold Programs.evalChunkM
  exact mem_transcript_left _ member

/-- The probe's blocks are the reach's, at the inactive switch. -/
theorem reach_scale_mem (table : Public) (labels : LamportSignature) (tape : Coins × Oracle)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript (publicAnswer tape.2)
      (elementMaskM (FreeQuery.eval (publicAnswer tape.2) (probeFoldM table labels) probeSwitch))) :
    entry ∈ reachTranscript table offInput labels tape := by
  refine reach_of_chunk table labels tape ?_
  unfold Programs.evalChunkM
  refine mem_transcript_right _ (mem_transcript_left _ ?_)
  unfold Programs.evalMasksM
  refine mem_transcript_left _ (mem_transcript_vector _ _ _ probeSwitch ?_)
  have inactive : probeSwitch ≠
      chunkOf (Pipeline.coordBits (Lamport.restore offInput labels).input .x) chunkZero :=
    probeSwitch_inactive
  rw [if_neg inactive]
  unfold Programs.switchMaskM
  exact mem_transcript_left _ (mem_transcript_vector _ _ _ probeElement member)

/-- A garbler entry the reach also asks, not an EncPRF entry, is visible. -/
theorem mem_visible {scalar : NonZeroScalar} {tape : Coins × Oracle} {table : Public}
    {input : AffineInput} {labels : LamportSignature}
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (garbler : entry ∈ garblerTranscript scalar tape)
    (reach : entry ∈ reachTranscript table input labels tape) (notEnc : entry.IsEnc = false) :
    entry ∈ visibleEntries scalar tape table input labels := by
  unfold visibleEntries
  rw [List.mem_filter]
  refine ⟨garbler, ?_⟩
  simp only [notEnc, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  exact List.mem_map_of_mem reach

end Membership

/-! ### 6. The probe's questions, one by one -/

section Entries

variable (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex, query.Answer)

theorem not_mem_transcript_pure {α : Type} (value : α)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (Pure.pure value : FreeQuery Programs.Spec α)) : False := by
  change entry ∈ ([] : List (Entry FixedIndex EncPRF.PermutationIndex)) at member
  exact List.not_mem_nil member

/-- A fold gate asks its two halves at its label. -/
theorem foldMaskM_entries (lane : Lane) (c : Fin chunkCount) (step gate : ℕ) (label : Block)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (Programs.foldMaskM lane c step gate label)) :
    ∃ half, entry = ⟨.fixedForward (hotIndexNat lane c step gate half) label,
      answer (.fixedForward (hotIndexNat lane c step gate half) label)⟩ := by
  unfold Programs.foldMaskM at member
  rw [transcript_hashM_bind, transcript_hashM_bind] at member
  rcases List.mem_cons.mp member with same | rest
  · exact ⟨false, same⟩
  · rcases List.mem_cons.mp rest with same | rest
    · exact ⟨true, same⟩
    · exact (not_mem_transcript_pure answer _ rest).elim

/-- The probed element asks its three blocks at its label. -/
theorem elementMaskM_entries (label : Block) {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (elementMaskM label)) :
    ∃ block : Fin 3, entry =
      ⟨.fixedForward (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement block) label,
        answer (.fixedForward (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement block)
          label)⟩ := by
  unfold elementMaskM at member
  rw [transcript_hashM_bind, transcript_hashM_bind, transcript_hashM_bind] at member
  rcases List.mem_cons.mp member with same | rest
  · exact ⟨0, same⟩
  · rcases List.mem_cons.mp rest with same | rest
    · exact ⟨1, same⟩
    · rcases List.mem_cons.mp rest with same | rest
      · exact ⟨2, same⟩
      · exact (not_mem_transcript_pure answer _ rest).elim

/-- The probe's fold, at width `2`: one fold gate at the level-1 label. -/
theorem probeFold_eq (table : Public) (labels : LamportSignature) :
    probeFoldM table labels =
      (Programs.foldMaskM .curveX chunkZero 1 (inactiveEntry (probeValue labels))
          (probeJoin table 0 ^^^ probeBitLabel labels 0) >>= fun material =>
        (Pure.pure (foldLabels (probeValue labels) (probeBitLabel labels) (probeJoin table)
          material) : Programs.M (Fin (2 ^ chunkWidth chunkZero) → Block))) :=
  Kriterion.ArgoMAC.Phase3.Lazy.evalFoldM_two _ _ _ _ _

theorem probeFold_entries (table : Public) (labels : LamportSignature)
    {entry : Entry FixedIndex EncPRF.PermutationIndex}
    (member : entry ∈ transcript answer (probeFoldM table labels)) :
    ∃ half, entry =
      ⟨.fixedForward (hotIndexNat .curveX chunkZero 1 (inactiveEntry (probeValue labels)) half)
          (probeJoin table 0 ^^^ probeBitLabel labels 0),
        answer (.fixedForward (hotIndexNat .curveX chunkZero 1 (inactiveEntry (probeValue labels))
          half) (probeJoin table 0 ^^^ probeBitLabel labels 0))⟩ := by
  rw [probeFold_eq, transcript_bind] at member
  rcases List.mem_append.mp member with fold | rest
  · exact foldMaskM_entries answer _ _ _ _ _ fold
  · exact (not_mem_transcript_pure answer _ rest).elim

end Entries

/-! ### 7. In `G1U`, the probe reads the garbler's swapped mask -/

section Hidden

variable [FieldCertificate] [GroupCertificate]

theorem garble_key (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar tape).2 = tape.1.inputMacKey := by
  rw [scheme_garble_eq]

/-- **The probe's switch label is the garbler's.** -/
theorem probe_hot (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    FreeQuery.eval (publicAnswer tape.2)
        (probeFoldM (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput))
        probeSwitch
      = (garbleChunk tape.2.1 .curveX (tape.1.inputDelta .x)
          (Pipeline.bitKeyOf tape.1.inputMacKey .x) chunkZero).1 probeSwitch := by
  unfold probeFoldM probeValue probeBitLabel probeJoin
  rw [Programs.eval_evalFoldM, probe_restore, garble_curveXHot]
  erw [hotSlice_hotJoins]
  rw [garble_key]
  dsimp only
  rw [Pipeline.macLabels_encode]
  erw [chunkLabels_selectBits]
  exact evalHot_agrees_off_active (coins_correlated tape.1) _ chunkZero probeSwitch
    probeSwitch_inactive

/-- **The probe's level-1 label is the garbler's.** -/
theorem probe_level_one (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    probeJoin (Scheme.scheme.garble parameter scalar tape).1 0 ^^^
        probeBitLabel (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2
          offInput) 0
      = (garbleFold tape.2.1 .curveX chunkZero (tape.1.inputDelta .x)
          (labelAt fun position => (chunkKey (Pipeline.bitKeyOf tape.1.inputMacKey .x) chunkZero
            position).1) 1).1
          ⟨inactiveEntry (probeValue (Scheme.scheme.encode
            (Scheme.scheme.garble parameter scalar tape).2 offInput)), by
            unfold inactiveEntry
            have := Nat.mod_lt (probeValue (Scheme.scheme.encode
              (Scheme.scheme.garble parameter scalar tape).2 offInput)) two_pos
            omega⟩ := by
  unfold probeValue probeBitLabel
  simp only [probe_restore, garble_key]
  rw [Pipeline.macLabels_encode]
  erw [chunkLabels_selectBits]
  exact (level_one_agrees tape.2.1 .curveX chunkZero (tape.1.inputDelta .x)
    (Pipeline.bitKeyOf tape.1.inputMacKey .x) (coins_correlated tape.1)
    (Pipeline.coordBits (BitInput.ofAffine offInput) .x) tape.2.2
    (probeJoin (Scheme.scheme.garble parameter scalar tape).1) rfl (by decide)).symm

end Hidden

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
