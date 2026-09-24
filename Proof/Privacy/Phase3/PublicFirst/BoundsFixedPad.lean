/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: inputs that pass through an EncPRF pad.**

System B's fold indices are asked at a whitened label `pad₀ ⊕ L` and the gadget at a transformed
label `pad_u ⊕ L`; each pad is `π_j(u ⊕ k₁) ⊕ k₂` for the prefix's keys `k`. The potential
`padF` is chosen after the prefix (`prefixSplit`), where the EncPRF part is still empty:

* `pad_le` — an event that forces the final answer of `π_j` at `u ⊕ k₁` to a target read from
  `k` has mass `≤ 1/(2^128 − 1)`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPoint

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests designatedIndex)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt FixedAt IndexAt
  runRefill cellOf runRefillT dropTouched uniformMaskTape queriesAlong queriesAlong_bind
  runRefill_eq_runRefillT fq_bind_assoc)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

theorem mem_queriesAlong_of_transcript {α : Type} (ans : (request : Request) → request.Answer)
    (c : FreeQuery Programs.Spec α) (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (member : entry ∈ transcript ans c) : entry.1 ∈ queriesAlong ans c := by
  induction c with
  | pure value => cases member
  | query request next ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ member)

/-- A stored forward EncPRF pair, as a lookup. -/
theorem stored_enc_lk {state : LState} {j : EncPRF.PermutationIndex} {x a : Block}
    (stored : StoredAs state ⟨.encForward j x, a⟩) :
    lk (state.enc j) x.toFin = some a.toFin := by
  change (lk (state.enc j) x.toFin).map BitVec.ofFin = some a at stored
  cases hk : lk (state.enc j) x.toFin with
  | none => rw [hk] at stored; cases stored
  | some y =>
    rw [hk] at stored
    simp only [Option.map_some, Option.some.injEq] at stored
    rw [← stored]

/-! ### The split after the prefix -/

section Prefix

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

/-- The opening after its prefix. -/
abbrev prefixRest (hashed : Block × Block) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  whitePadsM ⟨hashed.1, hashed.2⟩ >>= padsRest table bits mac

theorem openingQueriesM_prefixSplit :
    openingQueriesM table bits mac = curvePrefixM table bits mac >>= prefixRest table bits mac :=
  openingQueriesM_eq_prefix table bits mac

theorem prefixRest_forward (hashed : Block × Block) :
    AllQ ForwardOnly (prefixRest table bits mac hashed) :=
  (whitePadsM_forwardOnly _).bind fun pads => padsRest_forward table bits mac pads

end Prefix

/-! ### Pads at the final state -/

section Final

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)
  (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState)
  (resultMember : result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
    (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
      ran.2.2 blocks) ran.2.1)).support)

include member resultMember

/-- The final state reads the opening's keys. -/
theorem kOf_final :
    kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf result.2) =
      kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  have grow := final_grows source input tape ran member blocks result resultMember
  show answerOf result.2 (.hash (tOf _ _ _ (answerOf result.2))) = _
  rw [tOf_agree source input tape ran member result.2 grow]
  exact opening_agree source input tape ran member result.2 grow _ (hash_mem_opening _ _ _ _) rfl

/-- **Both pads of every position are stored at the final state, at the opening's keys.** -/
theorem pad_final (j : EncPRF.PermutationIndex) (bit : Bool) :
    StoredAs result.2 ⟨.encForward j (encodeBit bit ^^^
      (kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1)).1),
      answerOf result.2 (.encForward j (encodeBit bit ^^^
        (kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1))⟩ := by
  have grow := final_grows source input tape ran member blocks result resultMember
  cases bit with
  | false =>
    have onPath := whitePads_mem_opening source.publicValue (restoredBits source input)
      (restoredMac source input) (refillAns (restoredBits source input) ran.2.1) _
      (mem_queriesAlong_of_transcript (refillAns (restoredBits source input) ran.2.1)
        (whitePadsM ⟨(kOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) ran.2.1)).1, (kOf source.publicValue
            (restoredBits source input) (restoredMac source input)
              (refillAns (restoredBits source input) ran.2.1)).2⟩) _
        (whitePad_mem_transcript (refillAns (restoredBits source input) ran.2.1)
          ⟨(kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).1, (kOf source.publicValue
              (restoredBits source input) (restoredMac source input)
                (refillAns (restoredBits source input) ran.2.1)).2⟩ j))
    obtain ⟨stored, _⟩ := curve_stored_answer source input tape ran member _ onPath rfl
    have later := storedAs_grows grow stored
    rw [answerOf_of_stored later]
    exact later
  | true =>
    obtain ⟨_, storedPath, _⟩ := runLazyQ_stores _ _ result resultMember
    have entry : (⟨.encForward j (encodeBit true ^^^ (FreeQuery.eval (answerOf result.2)
        (curvePrefixM source.publicValue (restoredBits source input)
          (restoredMac source input))).1),
        answerOf result.2 (.encForward j (encodeBit true ^^^ (FreeQuery.eval (answerOf result.2)
          (curvePrefixM source.publicValue (restoredBits source input)
            (restoredMac source input))).1))⟩ : Entry FixedIndex EncPRF.PermutationIndex) ∈
        transcript (answerOf result.2) (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) := by
      unfold shadowOnM
      refine mem_transcript_right (answerOf result.2) ?_
      generalize FreeQuery.eval (answerOf result.2) (curvePrefixM source.publicValue
        (restoredBits source input) (restoredMac source input)) = E
      exact mem_transcript_left (answerOf result.2)
        (truePad_mem_transcript (answerOf result.2) ⟨E.1, E.2⟩ j)
    have inShadow := storedPath _ entry
    rw [eval_curvePrefixM, kOf_final source input tape ran member blocks result resultMember]
      at inShadow
    exact inShadow

/-- **At most two pairs at every EncPRF index of the final state.** -/
theorem enc_final_small (j : EncPRF.PermutationIndex) : (result.2.enc j).used ≤ 2 := by
  obtain ⟨stored, keysSame, exact⟩ := installed_facts source input tape ran member
    (programRequests (restoredBits source input) ran.2.2 blocks)
  rw [← keysSame] at exact
  exact used_le_two _ _ _ (shadow_enc_final _ _ _ _ stored exact result resultMember j)

end Final

/-! ### The pad potential -/

section PadBound

variable [FieldCertificate] [GroupCertificate]

/-- **An event forcing a pad's final answer to a target read from the keys has mass
`≤ 1/(2^128 − 1)`.** -/
theorem pad_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (j : EncPRF.PermutationIndex)
    (bit : Bool) (goal : Block × Block → Block)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks))) →
        (answerOf result.2 (.encForward j (encodeBit bit ^^^
          (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1)).1)) : Block) =
          goal (kOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1))) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ epsOne := by
  refine onCurve_split_le scalar off source input target event
    (curvePrefixM source.publicValue (restoredBits source input) (restoredMac source input))
    (prefixRest source.publicValue (restoredBits source input) (restoredMac source input))
    (openingQueriesM_prefixSplit _ _ _) (prefixRest_forward _ _ _)
    (fun _ k s => padF (encodeBit bit ^^^ k.1).toFin (goal k).toFin (s.enc j))
    (fun _ k request state forward => enc_lift_step j _ (padF_step _ _) request forward state)
    (fun _ k state updated index input' output _ success =>
      enc_programSame j _ state updated index input' output success)
    (fun _ k state updated index input' output _ success =>
      enc_programSame j _ state updated index input' output success) epsOne
    (fun tape mid midMember => ?_) (fun tape mid midMember ranT ranMember openMember blocks
      result resultMember => ?_)
  · -- after the prefix the EncPRF part is empty
    have encEmpty := runRefill_enc_same (restoredBits source input) (fun cell => PMF.pure (tape cell))
      _ (curvePrefixM_encFree _ _ _) _ _ _ _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
    have zero : (mid.2.1.enc j).used = 0 := by
      have := congrArg (fun e => (e j).used) encEmpty
      exact this
    have unknown : ¬ (mid.2.1.enc j).knownInput (encodeBit bit ^^^ mid.1.1).toFin := by
      unfold SparsePermutation.knownInput
      omega
    show padF _ _ _ ≤ epsOne
    unfold padF
    rw [if_neg unknown, if_pos (by omega)]
  · obtain ⟨_, _, value⟩ := mid_facts (restoredBits source input) tape _
      (curvePrefixM_fresh source.publicValue (restoredBits source input) (restoredMac source input))
      (curvePrefixM_forwardOnly _ _ _) _ mid midMember ranT ranMember
    rw [eval_curvePrefixM] at value
    have keyEq : kOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) (dropTouched ranT).2.1) = mid.1 := value
    have stored := pad_final source input tape (dropTouched ranT) openMember blocks result
      resultMember j bit
    rw [keyEq] at stored
    have found := stored_enc_lk stored
    have small := enc_final_small source input tape (dropTouched ranT) openMember blocks result
      resultMember j
    refine le_trans (ind_mono fun hit => ?_) (padF_bound _ _ _ _ found small)
    have same := reduce tape (dropTouched ranT) openMember blocks result resultMember hit
    rw [keyEq] at same
    rw [same]

end PadBound

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
