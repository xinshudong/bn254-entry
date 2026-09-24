/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: system B's masks, split after the pads.**

* `mid_facts` — for a split `openingQueriesM = first >>= rest` of the opening with a fresh
  forward-only first part: the first part's run is described, the state only grows after it, and
  the final answers read the first part's value.
* `pointScale_le` — at a mask index of system B (in particular a designated one), the canonical
  input hits any target (read from the tape and the whitening pads) with mass `≤ 1/2^128`: the
  potential is chosen after the pads, where both fold indices of the chunk are still empty.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedCurve

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
  foldLabels inactiveEntry program_frame hot_not_designated cellOf_hot runRefill_eq_runRefillT
  fq_bind_assoc evalLaneM_allQ whitePadsM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### A first part of the opening -/

section Mid

theorem runRefillT_mem_runRefill (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (c : FreeQuery Programs.Spec α) (oracle : LState) (record : Record) (touched : Set FixedIndex)
    (result : α × LState × Record × Set FixedIndex)
    (member : some result ∈ (runRefillT bits draw c oracle record touched).support) :
    some (dropTouched result) ∈ (runRefill bits draw c oracle record touched).support := by
  rw [runRefill_eq_runRefillT]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, member, rfl⟩

/-- **After a fresh first part**: it is described, the state grows, and the final answers read its
value. -/
theorem mid_facts {β γ : Type} (bits : BitInput) (tape : Tape) (first : Programs.M β)
    (fresh : Fresh bits ∅ first) (forward : AllQ ForwardOnly first) (rest : β → Programs.M γ)
    (mid : β × LState × Record × Set FixedIndex)
    (midMember : some mid ∈ (runRefillT bits (fun cell => PMF.pure (tape cell)) first
      LazyOracle.empty (fun _ => none) ∅).support)
    (ranT : γ × LState × Record × Set FixedIndex)
    (ranMember : some ranT ∈ (runRefillT bits (fun cell => PMF.pure (tape cell)) (rest mid.1)
      mid.2.1 mid.2.2.1 mid.2.2.2).support) :
    Described bits tape first LazyOracle.empty (fun _ => none) (dropTouched mid) ∧
      Grows mid.2.1 ranT.2.1 ∧ FreeQuery.eval (refillAns bits ranT.2.1) first = mid.1 := by
  have d := runRefill_describe bits tape first forward ∅ fresh LazyOracle.empty (fun _ => none) ∅
    (fun _ _ => ⟨fun h => h, rfl⟩) _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
  have grow : Grows mid.2.1 ranT.2.1 :=
    runRefill_grows _ _ _ _ _ _ _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ ranMember)
  refine ⟨d, grow, ?_⟩
  have value : mid.1 = FreeQuery.eval (refillAns bits mid.2.1) first := d.value
  rw [value]
  refine (queriesAlong_congr _ _ _ fun q onPath => ?_).2
  cases intercept : interceptAnswer bits q with
  | some answer => rw [refillAns_intercept intercept, refillAns_intercept intercept]
  | none =>
    rw [refillAns_plain intercept, refillAns_plain intercept]
    exact answerOf_of_stored (storedAs_grows grow (d.stored q onPath intercept))

/-- A permutation with no pair has none used. -/
theorem used_zero_of_none (S : SparsePermutation (2 ^ 128)) (none' : ∀ z, lk S z = none) :
    S.used = 0 := by
  classical
  rw [← card_known]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun z => ?_⟩
  exact (knownInput_iff _ _).mp z.2 (none' z.1)

end Mid

/-! ### The split after the whitening pads -/

section Pads

variable [FieldCertificate] (table : Public) (bits : BitInput) (mac : InputMac)

/-- The prefix and the whitening pads. -/
abbrev padsFirst : Programs.M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  curvePrefixM table bits mac >>= fun hashed => whitePadsM ⟨hashed.1, hashed.2⟩

/-- System B's two lanes, at the whitened labels. -/
abbrev padsRest (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    Programs.M ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) :=
  pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
    pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY => pure (pointX, pointY)

theorem openingQueriesM_padsSplit :
    openingQueriesM table bits mac = padsFirst table bits mac >>= padsRest table bits mac := by
  rw [openingQueriesM_eq_prefix, fq_bind_assoc]

theorem padsRest_forward (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :
    AllQ ForwardOnly (padsRest table bits mac pads) :=
  (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ =>
    (evalLaneM_forwardOnly _ _ _ _ _ _).bind fun _ => .pure _

theorem padsFirst_forward : AllQ ForwardOnly (padsFirst table bits mac) :=
  (curvePrefixM_forwardOnly _ _ _).bind fun _ => whitePadsM_forwardOnly _

theorem curvePrefixM_fresh : Fresh bits ∅ (curvePrefixM table bits mac) := by
  unfold curvePrefixM
  refine Fresh.bind (S := laneSet .curveX)
    (lane_fresh _ _ _ _ _ _ bits (by decide)) (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  refine Fresh.bind (S := laneSet .curveY)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i inside outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  · rcases outside with outside | outside
    · exact outside
    · exact laneSet_ne (by decide) inside outside
  · exact Fresh.of_none (.query _ _ rfl fun _ => .pure _) _

theorem padsFirst_fresh : Fresh bits ∅ (padsFirst table bits mac) := by
  refine Fresh.bind (S := laneSet .curveX ∪ laneSet .curveY) (curvePrefixM_fresh table bits mac)
    ?_ fun _ => Fresh.of_none ((whitePadsM_allQ _).mono fun _ inside =>
      consumedIndex_none_of_encAt inside) _
  unfold curvePrefixM
  exact ((allQ_inIdx_lane _ _ _ _ _ _ bits).mono fun r inside i hi => Or.inl (inside i hi)).bind
    fun _ => ((allQ_inIdx_lane _ _ _ _ _ _ bits).mono fun r inside i hi =>
      Or.inr (inside i hi)).bind fun _ => .query _ _ (fun i hi => by cases hi) fun _ => .pure _

/-- A question of the first part at a fixed index is at one of system A's indices. -/
theorem padsFirst_fixed (ans : (request : Request) → request.Answer) (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (padsFirst table bits mac)) :
    i ∈ laneSet .curveX ∨ i ∈ laneSet .curveY := by
  have inside : ∀ r ∈ queriesAlong ans (padsFirst table bits mac),
      ∀ i x, r = .fixedForward i x → i ∈ laneSet .curveX ∨ i ∈ laneSet .curveY := by
    refine mem_queriesAlong_allQ ans ?_
    show AllQ _ (curvePrefixM table bits mac >>= fun hashed => whitePadsM ⟨hashed.1, hashed.2⟩)
    unfold curvePrefixM
    refine AllQ.bind (AllQ.bind ((evalLaneM_allQ _ _ _ _ _ _).mono fun r at_ i x same => ?_)
      fun _ => AllQ.bind ((evalLaneM_allQ _ _ _ _ _ _).mono fun r at_ i x same => ?_)
        fun _ => .query _ _ (fun i x same => by cases same) fun _ => .pure _) fun _ => ?_
    · subst same
      exact Or.inl at_
    · subst same
      exact Or.inr at_
    · exact (whitePadsM_allQ _).mono fun r at_ i x same => by
        subst same
        exact at_.elim
  exact inside _ member i x rfl

variable [GroupCertificate] in
theorem eval_padsFirst (ans : (request : Request) → request.Answer) :
    FreeQuery.eval ans (padsFirst table bits mac) = wPadsOf table bits mac ans := by
  rw [FreeQuery.eval_bind, eval_curvePrefixM]

end Pads

/-! ### System B's masks -/

section PointScale

variable [FieldCertificate] [GroupCertificate]

theorem foldIdx_laneSet (lane : Lane) (c : Fin chunkCount) (value : ℕ) (half : Bool) :
    foldIdx lane c value half ∈ laneSet lane :=
  ⟨c, Kriterion.ArgoMAC.Phase3.Lazy.hotIndexNat_indexAt lane c 1 _ half⟩

/-- **At a mask index of system B, the canonical input hits any tape-dependent target with mass
`≤ 1/2^128`.** -/
theorem pointScale_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (lane : Lane) (point : lane = .pointX ∨ lane = .pointY)
    (c : Fin chunkCount) (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX) (b : Fin 3)
    (event : Points FixedIndex EncPRF.PermutationIndex → Prop) (z : Tape → Block)
    (reduce : ∀ (tape : Tape)
      (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
        LState × Record), some ran ∈ (openingRun source input tape).support →
      ∀ (blocks : Fin digitCount × Fin 3 → Block × Block × Block) (result : Unit × LState),
        result ∈ (runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input)) (programAllSkip (programRequests (restoredBits source input)
            ran.2.2 blocks) ran.2.1)).support →
        event ((pointsOf result.2).union (requestPoints (programRequests
          (restoredBits source input) ran.2.2 blocks))) →
        inputOf source.publicValue (restoredBits source input) (restoredMac source input)
          (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
            (refillAns (restoredBits source input) ran.2.1))
          (refillAns (restoredBits source input) ran.2.1)
          (Programs.transformMacOf (ePadsOf source.publicValue (restoredBits source input)
            (restoredMac source input) (answerOf result.2)) (restoredMac source input))
          (.scale lane c s e b) = z tape) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind (event (outcomePoints o)) ≤ delta := by
  set value := (chunkValue (laneWord (restoredBits source input) lane) c).toNat with valueDef
  let fixedPart : (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) → Block :=
    fun pads => foldLabels value
      (labelAt (chunkLabels (laneLabels (restoredMac source input) pads lane) c))
      (joinAt (hotSlice (laneJoins source.publicValue lane) c)) 0 ⟨s.val, by
        have := s.isLt; unfold chunkBits at this; exact this⟩
  refine onCurve_split_le scalar off source input target event
    (padsFirst source.publicValue (restoredBits source input) (restoredMac source input))
    (padsRest source.publicValue (restoredBits source input) (restoredMac source input))
    (openingQueriesM_padsSplit _ _ _) (padsRest_forward _ _ _)
    (fun tape pads => chunkFoldPot lane c value (z tape ^^^ fixedPart pads))
    (fun tape pads => chunkFoldPot_step lane c value _)
    (fun tape pads => chunkFoldPot_siteSame lane c value _)
    (fun tape pads => chunkFoldPot_designatedSame _ lane c value _) delta
    (fun tape mid midMember => ?_) (fun tape mid midMember ranT ranMember openMember blocks
      result resultMember => ?_)
  · -- after the pads, the chunk's fold indices are empty
    have d := runRefill_describe (restoredBits source input) tape _
      (padsFirst_forward source.publicValue (restoredBits source input) (restoredMac source input))
      ∅ (padsFirst_fresh _ _ _) LazyOracle.empty (fun _ => none) ∅ (fun _ _ => ⟨fun h => h, rfl⟩)
      _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
    have empty : ∀ half z', lk (mid.2.1.fixed (foldIdx lane c value half)) z' = none := by
      intro half z'
      cases found : lk (mid.2.1.fixed (foldIdx lane c value half)) z' with
      | none => rfl
      | some w =>
        rcases d.fixed _ z' w found with old | ⟨onPath, _, _⟩
        · rw [lk_empty_fixed] at old
          cases old
        · exfalso
          rcases padsFirst_fixed _ _ _ _ _ _ onPath with inside | inside
          · exact laneSet_ne (by rcases point with rfl | rfl <;> decide)
              (foldIdx_laneSet lane c value half) inside
          · exact laneSet_ne (by rcases point with rfl | rfl <;> decide)
              (foldIdx_laneSet lane c value half) inside
    have zero0 := used_zero_of_none _ (empty false)
    have zero1 := used_zero_of_none _ (empty true)
    refine le_of_eq ?_
    show foldF _ _ _ = delta
    unfold foldF
    rw [if_pos ⟨zero0.le.trans zero_le_one, zero1.le.trans zero_le_one⟩, if_neg fun h => by
      rw [zero0] at h
      exact absurd h.1 (by decide)]
  · obtain ⟨_, _, value'⟩ := mid_facts (restoredBits source input) tape _
      (padsFirst_fresh source.publicValue (restoredBits source input) (restoredMac source input))
      (padsFirst_forward _ _ _) _ mid midMember ranT ranMember
    rw [eval_padsFirst] at value'
    obtain ⟨used0, lk0⟩ := fold_final source input tape (dropTouched ranT) openMember blocks result
      resultMember lane c false
    obtain ⟨used1, lk1⟩ := fold_final source input tape (dropTouched ranT) openMember blocks result
      resultMember lane c true
    refine le_trans (ind_mono fun hit => ?_) (foldF_bound _ _ _ used0 used1 _ _ _ _ lk0 lk1)
    have same := reduce tape (dropTouched ranT) openMember blocks result resultMember hit
    rw [inputOf_scale] at same
    rw [BitVec.ofFin_toFin, BitVec.ofFin_toFin]
    have padsEq : wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) (dropTouched ranT).2.1) = mid.1 := value'
    rw [padsEq] at same ⊢
    exact (xor_eq_iff _ _ _).mp same

end PointScale

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
