/-
**Phase 3, P1m — (B1): the hash conjunct, assembled.**

* `opening_hash_key`, `shadow_hash_key` — on the curve the only hash key of `M'`'s private final
  state is the opening's bridge input `tOf … (refillAns …)`.
* `tOf_opening` — that input is `curveMap` of the tape's masks (system A's masks are consumed from
  the tape: `Described.fixed`, `lane_eval_eq`, `laneValue_tapeH`).
* `hash_onCurve_le` — its mass at any key is `≤ 1/p` (`uniform_affine_le`, `curveMap_shift`);
  `hash_off_zero` — off the curve there is no hash key.
* **`designedShadow_hashBound`** — the hash conjunct of `PerPairBound (designedShadow scalar) scalar
  (4/2^128)`.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsHash

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request AllQ EncAt FixedAt IndexAt
  queriesAlong queriesAlong_bind cellOf uniformMaskTape masksOf_surjective evalLaneM_allQ
  cellOf_maskIndex maskIndex whitePadsM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
variable [FieldCertificate] [GroupCertificate]

/-! ### System A along the opening's answers -/

section Lookups

/-- A stored forward pair, as a lookup. -/
theorem stored_fixed_lk {state : LState} {i : FixedIndex} {x a : Block}
    (stored : StoredAs state ⟨.fixedForward i x, a⟩) :
    lk (state.fixed i) x.toFin = some a.toFin := by
  change (lk (state.fixed i) x.toFin).map BitVec.ofFin = some a at stored
  cases hk : lk (state.fixed i) x.toFin with
  | none => rw [hk] at stored; cases stored
  | some y =>
    rw [hk] at stored
    simp only [Option.map_some, Option.some.injEq] at stored
    rw [← stored]

theorem lk_empty_fixed (i : FixedIndex) (z : Fin (2 ^ 128)) :
    lk ((LazyOracle.empty : LState).fixed i) z = none :=
  Kriterion.ArgoMAC.Security.Phase3.PublicFirst.lk_empty z

end Lookups

section SystemA

variable (source : Stage1Source) (input : AffineInput)

theorem curveX_notIntercepted (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveXM source.publicValue (restoredBits source input)
      (restoredMac source input))) :
    interceptAnswer (restoredBits source input) q = none :=
  curve_notIntercepted _ .curveX (Or.inl rfl) q
    (mem_queriesAlong_allQ ans (evalLaneM_allQ _ _ _ _ _ _) q member)

theorem curveY_notIntercepted (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveYM source.publicValue (restoredBits source input)
      (restoredMac source input))) :
    interceptAnswer (restoredBits source input) q = none :=
  curve_notIntercepted _ .curveY (Or.inr rfl) q
    (mem_queriesAlong_allQ ans (evalLaneM_allQ _ _ _ _ _ _) q member)

theorem curveX_mem_opening (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveXM source.publicValue (restoredBits source input)
      (restoredMac source input))) :
    q ∈ queriesAlong ans (openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input)) := by
  rw [openingQueriesM_eq, queriesAlong_bind]
  exact List.mem_append_left _ member

theorem curveY_mem_opening (ans : (request : Request) → request.Answer) (q : Request)
    (member : q ∈ queriesAlong ans (curveYM source.publicValue (restoredBits source input)
      (restoredMac source input))) :
    q ∈ queriesAlong ans (openingQueriesM source.publicValue (restoredBits source input)
      (restoredMac source input)) := by
  rw [openingQueriesM_eq, queriesAlong_bind, queriesAlong_bind]
  exact List.mem_append_right _ (List.mem_append_left _ member)

variable (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)

include member

/-- **After the opening, system A's path is stored**, and the opening's answers there are the
stored ones. -/
theorem curve_stored_answer (q : Request)
    (onPath : q ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)))
    (notIntercepted : interceptAnswer (restoredBits source input) q = none) :
    StoredAs ran.2.1 ⟨q, answerOf ran.2.1 q⟩ ∧
      refillAns (restoredBits source input) ran.2.1 q = answerOf ran.2.1 q :=
  ⟨(opening_described source input tape ran member).stored q onPath notIntercepted,
    refillAns_plain notIntercepted⟩

/-- **Any later state reads system A as the opening did.** -/
theorem curve_agree (later : LState) (grow : Grows ran.2.1 later) :
    FreeQuery.eval (answerOf later) (curveXM source.publicValue (restoredBits source input)
        (restoredMac source input)) =
      FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveXM source.publicValue (restoredBits source input) (restoredMac source input)) ∧
    FreeQuery.eval (answerOf later) (curveYM source.publicValue (restoredBits source input)
        (restoredMac source input)) =
      FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveYM source.publicValue (restoredBits source input) (restoredMac source input)) := by
  refine ⟨(queriesAlong_congr _ _ _ fun q onPath => ?_).2,
    (queriesAlong_congr _ _ _ fun q onPath => ?_).2⟩
  · obtain ⟨stored, same⟩ := curve_stored_answer source input tape ran member q
      (curveX_mem_opening source input _ q onPath) (curveX_notIntercepted source input _ q onPath)
    rw [same]
    exact answerOf_of_stored (storedAs_grows grow stored)
  · obtain ⟨stored, same⟩ := curve_stored_answer source input tape ran member q
      (curveY_mem_opening source input _ q onPath) (curveY_notIntercepted source input _ q onPath)
    rw [same]
    exact answerOf_of_stored (storedAs_grows grow stored)

theorem tOf_agree (later : LState) (grow : Grows ran.2.1 later) :
    tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (answerOf later) =
      tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) := by
  obtain ⟨x, y⟩ := curve_agree source input tape ran member later grow
  unfold tOf
  rw [x, y]

/-- **The opening's only hash key is its bridge input.** -/
theorem opening_hash_key (k : BaseField) (found : ran.2.1.hash.lookup k ≠ none) :
    k = tOf source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) ran.2.1) := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp found
  rcases (opening_described source input tape ran member).hash k v hv with old | onPath
  · cases old
  · rcases mem_opening _ _ _ _ _ onPath with a | b | c | d | e | f
    · exact absurd a (lane_not_hash _ k)
    · exact absurd b (lane_not_hash _ k)
    · exact PublicQuery.hash.inj c
    · exact absurd (mem_queriesAlong_allQ _ (whitePadsM_allQ _) _ d) not_encAt_hash
    · exact absurd e (lane_not_hash _ k)
    · exact absurd f (lane_not_hash _ k)

/-- **A stored mask pair of the opening has the tape's Davies–Meyer value.** -/
theorem site_dm (i : FixedIndex) (x a : Block)
    (stored : StoredAs ran.2.1 ⟨.fixedForward i x, a⟩)
    (answerEq : refillAns (restoredBits source input) ran.2.1 (.fixedForward i x) = a)
    {cell : Kriterion.ArgoMAC.Phase3.Lazy.Cell} (cellEq : cellOf i = some cell) :
    fwdAns (refillAns (restoredBits source input) ran.2.1) i x ^^^ x = tapeH tape i := by
  have found := stored_fixed_lk stored
  rcases (opening_described source input tape ran member).fixed i _ _ found with old | ⟨_, _, tapeOut⟩
  · rw [lk_empty_fixed] at old
    cases old
  · have out := tapeOut _ cellEq
    simp only [BitVec.ofFin_toFin] at out
    unfold fwdAns
    rw [answerEq, out, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, tapeH_of_cell cellEq]

/-- **System A's value on the tape.** -/
theorem curveX_value :
    FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveXM source.publicValue (restoredBits source input) (restoredMac source input)) =
      laneValue curveElementCountX .curveX
        (fun chunk => Pipeline.readCurveX (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .x) (tapeH tape) := by
  refine lane_eval_eq _ _ _ _ _ _ _ _ fun i x onPath ⟨c, switch, el, b, same⟩ => ?_
  obtain ⟨stored, answerEq⟩ := curve_stored_answer source input tape ran member _
    (curveX_mem_opening source input _ _ onPath) (curveX_notIntercepted source input _ _ onPath)
  exact site_dm source input tape ran member i x (a := fwdAns (answerOf ran.2.1) i x) stored
    answerEq (by rw [same]; exact cellOf_maskIndex .curveX c switch el b curveXLe)

theorem curveY_value :
    FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (curveYM source.publicValue (restoredBits source input) (restoredMac source input)) =
      laneValue curveElementCountY .curveY
        (fun chunk => Pipeline.readCurveY (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .y) (tapeH tape) := by
  refine lane_eval_eq _ _ _ _ _ _ _ _ fun i x onPath ⟨c, switch, el, b, same⟩ => ?_
  obtain ⟨stored, answerEq⟩ := curve_stored_answer source input tape ran member _
    (curveY_mem_opening source input _ _ onPath) (curveY_notIntercepted source input _ _ onPath)
  exact site_dm source input tape ran member i x (a := fwdAns (answerOf ran.2.1) i x) stored
    answerEq (by rw [same]; exact cellOf_maskIndex .curveY c switch el b curveYLe)

/-- **The opening's bridge input is a function of the tape's masks.** -/
theorem tOf_opening :
    tOf source.publicValue (restoredBits source input) (restoredMac source input)
        (refillAns (restoredBits source input) ran.2.1) =
      curveMap source.publicValue (restoredBits source input) (masksOf tape) := by
  unfold tOf curveMap
  rw [curveX_value source input tape ran member, curveY_value source input tape ran member,
    laneValue_tapeH tape .curveX _ curveXLe, laneValue_tapeH tape .curveY _ curveYLe]

end SystemA

/-! ### The hash conjunct -/

section Conjunct

/-- **The masks of the uniform mask tape are uniform.** -/
theorem uniformMaskTape_masks (f : (MaskSite → BaseField) → ℝ≥0∞) :
    ∑' tape, uniformMaskTape tape * f (masksOf tape) =
      ∑' m, PMF.uniformOfFintype (MaskSite → BaseField) m * f m := by
  unfold uniformMaskTape
  rw [tsum_bind_mul]
  refine tsum_congr fun m => congrArg _ ?_
  rw [← tsum_map_mul, Kriterion.ArgoMAC.Security.Phase3.fibreLaw_map, tsum_pure_mul]

/-- **On the curve, the hash key hits any point with mass `≤ 1/p`.** -/
theorem hash_onCurve_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (k : BaseField) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).hashIn k) ≤ ((Fintype.card BaseField : ℕ) : ℝ≥0∞)⁻¹ := by
  refine le_trans (onCurve_event_le scalar off source input target (fun p => p.hashIn k)
    (fun state => ind (tOf source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) state) = k)) fun tape ran member blocks => ?_) ?_
  · refine tsum_le_of_support' _ _ _ fun result resultMember => ind_mono fun hit => ?_
    rcases hit with inside | inside
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp inside
      rcases (runLazyQ_provenance _ (shadowOnM_forwardOnly _ _ _) _ result resultMember).2 k v hv
        with old | onPath
      · rw [programAllSkip_hash] at old
        exact (opening_hash_key source input tape ran member k
          (by rw [old]; exact Option.some_ne_none _)).symm
      · rw [mem_shadow_hash _ _ _ _ k onPath]
        exact (tOf_agree source input tape ran member result.2
          ((programAllSkip_grows _ _).trans (runLazyQ_grows _ _ result resultMember))).symm
    · exact inside.elim
  · refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape *
      ind (curveMap source.publicValue (restoredBits source input) (masksOf tape) = k))
      fun tape => mul_le_mul' le_rfl ?_) ?_
    · refine le_trans (tsum_mul_le_of_support _ _ (fun _ => ind (curveMap source.publicValue
        (restoredBits source input) (masksOf tape) = k)) fun ran member => ?_)
        (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))
      rcases ran with _ | ran
      · exact zero_le
      · simp only [optWeight]
        rw [tOf_opening source input tape ran member]
    · rw [uniformMaskTape_masks (fun m => ind (curveMap source.publicValue
        (restoredBits source input) m = k))]
      exact uniform_affine_le _ (maskShift (restoredBits source input))
        (shiftCoeff (restoredBits source input)) (shiftCoeff_ne _)
        (fun δ m => curveMap_shift _ _ δ m) k

theorem encAt_hashFree {r : Request} (inside : EncAt r) : HashFree r := by
  cases r with
  | encForward _ _ => trivial
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem designedOffM_hashFree (table : Public) (bits : BitInput) (mac : InputMac) (first : Block) :
    AllQ HashFree (designedOffM table bits mac first) := by
  unfold designedOffM systemAM
  refine ((padsM_allQ _).mono fun _ inside => encAt_hashFree inside).bind fun _ => ?_
  exact ((evalLaneM_allQ _ _ _ _ _ _).mono fun _ inside => hashFree_of_fixedAt inside).bind
    fun _ => ((evalLaneM_allQ _ _ _ _ _ _).mono fun _ inside => hashFree_of_fixedAt inside).bind
      fun _ => .pure _

/-- **Off the curve the designed shadow stores no hash key.** -/
theorem hash_off_zero (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (k : BaseField) :
    ∑' o, privateStage2U uniformMaskTape (designedShadow scalar) scalar source input none o *
        ind ((outcomePoints o).hashIn k) ≤ 0 := by
  refine le_trans (off_event_le scalar source input (fun p => p.hashIn k) (fun _ _ => 0)
    fun first tape => ?_) (le_of_eq (by simp only [mul_zero, tsum_zero]))
  refine le_trans (tsum_mul_le_of_support _ _ (fun _ => 0) fun o member => ?_)
    (le_of_eq (by simp only [mul_zero, tsum_zero]))
  rcases o with _ | outcome
  · exact le_rfl
  · simp only [fillWeight]
    have empty := runFillFlag_invariant LazyOracle.empty _ HashFree (fun s => s.hash = [])
      (fun request state holds same answer answerMember => by
        cases request with
        | hash _ => exact holds.elim
        | fixedForward _ _ =>
          obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
          exact same
        | fixedInverse _ _ =>
          obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
          exact same
        | encForward _ _ =>
          obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
          exact same
        | encInverse _ _ =>
          obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp answerMember
          exact same)
      (fun request state _ cell limb updated _ same consumed success => by
        obtain ⟨index, input, rfl, _⟩ := Kriterion.ArgoMAC.Phase3.Lazy.consumeCell_spec consumed
        rw [program_hash index input _ state updated success]
        exact same)
      _ (designedOffM_hashFree _ _ _ first) _ _ outcome rfl member
    refine le_of_eq (ind_neg fun hit => hit ?_)
    change outcome.2.hash.lookup k = none
    rw [empty]
    rfl

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **The hash conjunct of `PerPairBound (designedShadow scalar) scalar (4/2^128)`.** -/
theorem designedShadow_hashBound (scalar : NonZeroScalar) (pub : PubPart) (input : AffineInput)
    (k : BaseField) :
    (keyedPoints (designedShadow scalar) scalar pub input).toOuterMeasure {p | p.hashIn k} ≤
      4 / 2 ^ 128 := by
  refine keyedPoints_le_of_source _ _ _ _ _ _ fun source => ?_
  cases output : Scheme.scheme.function scalar input with
  | none => exact le_trans (hash_off_zero scalar source input k) zero_le
  | some target =>
    exact le_trans (hash_onCurve_le scalar designedOff source input target k) inv_modulus_le

end Conjunct

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
