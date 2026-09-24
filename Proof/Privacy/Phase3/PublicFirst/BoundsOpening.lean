/-
**Phase 3, P1m — (B1) tools: `HW`'s opening and `M'`'s on-curve shadow, along an answer function.**

* `mem_opening` — the questions of `openingQueriesM` along `ans`: system A's two lanes (at the
  input's MAC labels), the bridge hash at `tOf ans`, the whitening pads at `kOf ans`, system B's two
  lanes (at the labels whitened by `wPadsOf ans`).
* `mem_shadow` — the fixed-key and hash questions of the shadow `shadowOnM` along `ans`: system A's
  lanes again, the bridge hash at `tOf ans`, system B's lanes (whitened by the evaluator's pads
  `ePadsOf ans`, the same whitening: `whitenMac_ePads`), and the gadget, at the transformed labels.
* `opening_fresh` — along every path of the opening the non-designated indices are distinct.
* `opening_described` — **the opening run, described** (`runRefill_describe`).
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsLanes

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Tape Request AllQ EncAt IndexAt queriesAlong
  queriesAlong_bind queriesAlong_pure queriesAlong_vector consumedIndex indexAt_unique
  whitePadsM_allQ)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The programs, named -/

section Programs

variable [FieldCertificate] (table : Public) (bits : BitInput)

/-- System A's `x` lane. -/
abbrev curveXM (mac : InputMac) : Programs.M (Fin curveElementCountX → BaseField) :=
  Programs.evalLaneM curveElementCountX .curveX table.curveXHot
    (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)

/-- System A's `y` lane. -/
abbrev curveYM (mac : InputMac) : Programs.M (Fin curveElementCountY → BaseField) :=
  Programs.evalLaneM curveElementCountY .curveY table.curveYHot
    (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)

/-- System B's `x` lane, at some labels. -/
abbrev pointXM (mac : InputMac) : Programs.M (Fin pointElementCountX → BaseField) :=
  Programs.evalLaneM pointElementCountX .pointX table.pointXHot
    (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)

/-- System B's `y` lane, at some labels. -/
abbrev pointYM (mac : InputMac) : Programs.M (Fin pointElementCountY → BaseField) :=
  Programs.evalLaneM pointElementCountY .pointY table.pointYHot
    (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
    (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)

/-- The bridge hash input along `ans`. -/
abbrev tOf (mac : InputMac) (ans : (request : Request) → request.Answer) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues (FreeQuery.eval ans (curveXM table bits mac))
      (FreeQuery.eval ans (curveYM table bits mac)))

/-- The whitening keys along `ans`. -/
abbrev kOf (mac : InputMac) (ans : (request : Request) → request.Answer) : Block × Block :=
  ans (.hash (tOf table bits mac ans))

/-- The opening's whitening pads along `ans`. -/
abbrev wPadsOf (mac : InputMac) (ans : (request : Request) → request.Answer) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  FreeQuery.eval ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩)

/-- The evaluator's pads along `ans`. -/
abbrev ePadsOf (mac : InputMac) (ans : (request : Request) → request.Answer) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  FreeQuery.eval ans (Programs.evalPadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩
    bits)

theorem openingQueriesM_eq (mac : InputMac) :
    openingQueriesM table bits mac =
      curveXM table bits mac >>= fun curveX => curveYM table bits mac >>= fun curveY =>
        Programs.askHash (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY)) >>= fun hashed =>
          whitePadsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
            pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
              pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY =>
                pure (pointX, pointY) := rfl

theorem queriesAlong_askHash (ans : (request : Request) → request.Answer) (input : BaseField) :
    queriesAlong ans (Programs.askHash input) = [.hash input] := rfl

theorem eval_askHash (ans : (request : Request) → request.Answer) (input : BaseField) :
    FreeQuery.eval ans (Programs.askHash input) = ans (.hash input) := rfl

/-- **The questions of the opening.** -/
theorem mem_opening (mac : InputMac) (ans : (request : Request) → request.Answer) (r : Request)
    (member : r ∈ queriesAlong ans (openingQueriesM table bits mac)) :
    r ∈ queriesAlong ans (curveXM table bits mac) ∨ r ∈ queriesAlong ans (curveYM table bits mac) ∨
      r = .hash (tOf table bits mac ans) ∨
      r ∈ queriesAlong ans (whitePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ∨
      r ∈ queriesAlong ans (pointXM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      r ∈ queriesAlong ans (pointYM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) := by
  rw [openingQueriesM_eq] at member
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash,
    List.mem_append, List.mem_singleton, eval_askHash] at member
  rcases member with a | b | c | d | e | f
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inl d)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr f))))

/-- The whitening pad of a position, from the opening's pads. -/
theorem whitePads_fst (keys : WhiteningKeys) (ans : (request : Request) → request.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (whitePadsM keys) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
    simp only [whitePadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]

/-- The whitening pad of a position, from the evaluator's pads. -/
theorem evalPads_fst (keys : WhiteningKeys) (ans : (request : Request) → request.Answer)
    (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) :
    (FreeQuery.eval ans (Programs.evalPadsM keys bits) coordinate index).1 =
      FreeQuery.eval ans (Programs.padM keys coordinate index false) := by
  cases coordinate <;>
  · simp only [Programs.evalPadsM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn]
    split <;> simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]

/-- The two paddings whiten alike: both read only the bit-`false` pads. -/
theorem whitenMac_ePads (mac : InputMac) (ans : (request : Request) → request.Answer) :
    Programs.whitenMacOf (ePadsOf table bits mac ans) mac =
      Programs.whitenMacOf (wPadsOf table bits mac ans) mac := by
  unfold Programs.whitenMacOf
  simp only [ePadsOf, wPadsOf, evalPads_fst, whitePads_fst]

end Programs

section Shadow

variable [FieldCertificate] [GroupCertificate] (table : Public) (bits : BitInput)

theorem onCurveM_eq (mac : InputMac) :
    Programs.onCurveM table bits mac =
      curveXM table bits mac >>= fun curveX => curveYM table bits mac >>= fun curveY =>
        Programs.askHash (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY)) >>= fun hashed =>
          Programs.evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
            pointXM table bits (Programs.whitenMacOf pads mac) >>= fun pointX =>
              pointYM table bits (Programs.whitenMacOf pads mac) >>= fun pointY =>
                Programs.unlockM (Pipeline.pointTable table) bits.toAffine
                    (Programs.transformMacOf pads mac) >>= fun digits =>
                  pure (some (Garbling.decodeResult
                    { point := bits.toAffine
                      pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
                        (Pipeline.digitValues pointX pointY) bits.toAffine
                      exceptionDigits := digits })) := rfl

theorem evalPadsM_encAt (keys : WhiteningKeys) : AllQ EncAt (Programs.evalPadsM keys bits) := by
  unfold Programs.evalPadsM
  dsimp only
  exact (AllQ.vector fun _ => (Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ => .pure _)
        (.pure _)).bind fun _ =>
    (AllQ.vector fun _ => (Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ =>
      AllQ.ite ((Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ keys _ _ _).bind fun _ => .pure _)
        (.pure _)).bind fun _ => .pure _

theorem queriesAlong_curvePrefixM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (curvePrefixM table bits mac) =
      queriesAlong ans (curveXM table bits mac) ++ (queriesAlong ans (curveYM table bits mac) ++
        [.hash (tOf table bits mac ans)]) := by
  unfold curvePrefixM
  rw [queriesAlong_bind, queriesAlong_bind, queriesAlong_askHash]

theorem eval_curvePrefixM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    FreeQuery.eval ans (curvePrefixM table bits mac) = kOf table bits mac ans := by
  unfold curvePrefixM
  rw [FreeQuery.eval_bind, FreeQuery.eval_bind, eval_askHash]

theorem queriesAlong_onCurveM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (Programs.onCurveM table bits mac) =
      queriesAlong ans (curveXM table bits mac) ++ (queriesAlong ans (curveYM table bits mac) ++
        ([.hash (tOf table bits mac ans)] ++
          (queriesAlong ans (Programs.evalPadsM ⟨(kOf table bits mac ans).1,
              (kOf table bits mac ans).2⟩ bits) ++
            (queriesAlong ans (pointXM table bits
                (Programs.whitenMacOf (ePadsOf table bits mac ans) mac)) ++
              (queriesAlong ans (pointYM table bits
                  (Programs.whitenMacOf (ePadsOf table bits mac ans) mac)) ++
                queriesAlong ans (Programs.unlockM (Pipeline.pointTable table) bits.toAffine
                  (Programs.transformMacOf (ePadsOf table bits mac ans) mac))))))) := by
  rw [onCurveM_eq]
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, queriesAlong_askHash]
  rfl

theorem queriesAlong_shadowOnM (mac : InputMac) (ans : (request : Request) → request.Answer) :
    queriesAlong ans (shadowOnM table bits mac) =
      queriesAlong ans (curvePrefixM table bits mac) ++
        (queriesAlong ans (truePadsM ⟨(kOf table bits mac ans).1, (kOf table bits mac ans).2⟩) ++
          queriesAlong ans (Programs.onCurveM table bits mac)) := by
  unfold shadowOnM
  simp only [queriesAlong_bind, queriesAlong_pure, List.append_nil, eval_curvePrefixM]

theorem truePadsM_encAt (keys : WhiteningKeys) : AllQ EncAt (truePadsM keys) :=
  (AllQ.vector fun _ => Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ _ _ _ _).bind fun _ =>
    (AllQ.vector fun _ => Kriterion.ArgoMAC.Phase3.Lazy.padM_allQ _ _ _ _).bind fun _ => .pure _

theorem not_encAt_fixed {i : FixedIndex} {x : Block} :
    ¬ EncAt (.fixedForward i x : Request) := fun h => h

theorem not_encAt_hash {k : BaseField} : ¬ EncAt (.hash k : Request) := fun h => h

/-- **The fixed-key questions of the shadow.** -/
theorem mem_shadow_fixed (mac : InputMac) (ans : (request : Request) → request.Answer)
    (i : FixedIndex) (x : Block)
    (member : .fixedForward i x ∈ queriesAlong ans (shadowOnM table bits mac)) :
    .fixedForward i x ∈ queriesAlong ans (curveXM table bits mac) ∨
      .fixedForward i x ∈ queriesAlong ans (curveYM table bits mac) ∨
      .fixedForward i x ∈ queriesAlong ans (pointXM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      .fixedForward i x ∈ queriesAlong ans (pointYM table bits
        (Programs.whitenMacOf (wPadsOf table bits mac ans) mac)) ∨
      .fixedForward i x ∈ queriesAlong ans (Programs.unlockM (Pipeline.pointTable table)
        bits.toAffine (Programs.transformMacOf (ePadsOf table bits mac ans) mac)) := by
  rw [queriesAlong_shadowOnM, queriesAlong_curvePrefixM, queriesAlong_onCurveM,
    whitenMac_ePads] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (a | b | c) | d | a | b | c | d | e | f | g
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · cases c
  · exact absurd (mem_queriesAlong_allQ ans (truePadsM_encAt _) _ d) not_encAt_fixed
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · cases c
  · exact absurd (mem_queriesAlong_allQ ans (evalPadsM_encAt bits _) _ d) not_encAt_fixed
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl f)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr g)))

theorem lane_not_hash {count : ℕ} {lane : Lane} {joins : Vector Block foldStepCount}
    {scale : Fin chunkCount → Fin count → BaseField} {word : BitVec coordinateBitCount}
    {labels : Fin coordinateBitCount → Block} (ans : (request : Request) → request.Answer)
    (k : BaseField) :
    (.hash k : Request) ∉ queriesAlong ans (Programs.evalLaneM count lane joins scale word labels) :=
  fun member => by
    have := mem_queriesAlong_allQ ans (Kriterion.ArgoMAC.Phase3.Lazy.evalLaneM_allQ count lane joins
      scale word labels) _ member
    exact this

/-- A gadget question at the given labels. -/
def GadgetQ (mac : InputMac) (r : Request) : Prop :=
  ∃ (d : Fin digitCount) (κ : EncPRF.Coordinate) (pos : Fin coordinateBitCount),
    r = .fixedForward (.gadget d (Pipeline.gadgetCoord κ) pos)
      (Pipeline.macLabels mac (Pipeline.gadgetCoord κ) pos)

theorem gadgetDigestM_gadgetQ (mac : InputMac) (d : Fin digitCount) (κ : EncPRF.Coordinate)
    (labels : CoordinateMac)
    (same : ∀ pos, labels.get pos = Pipeline.macLabels mac (Pipeline.gadgetCoord κ) pos) :
    AllQ (GadgetQ mac) (Programs.gadgetDigestM d κ labels) :=
  (AllQ.vector fun pos => AllQ.bind (.query _ _ ⟨d, κ, pos, by rw [same]⟩ fun _ => .pure _)
    fun _ => .pure _).bind fun _ => .pure _

theorem unlockM_gadgetQ (table' : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    AllQ (GadgetQ mac) (Programs.unlockM table' input mac) :=
  AllQ.vector fun d =>
    ((gadgetDigestM_gadgetQ mac d .x mac.x fun _ => rfl).bind fun _ =>
      (gadgetDigestM_gadgetQ mac d .y mac.y fun _ => rfl).bind fun _ => .pure _).bind
        fun _ => .pure _

/-- **The hash questions of the shadow** are at the bridge input. -/
theorem mem_shadow_hash (mac : InputMac) (ans : (request : Request) → request.Answer)
    (k : BaseField) (member : .hash k ∈ queriesAlong ans (shadowOnM table bits mac)) :
    k = tOf table bits mac ans := by
  rw [queriesAlong_shadowOnM, queriesAlong_curvePrefixM, queriesAlong_onCurveM] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (a | b | c) | d | a | b | c | d | e | f | g
  · exact absurd a (lane_not_hash ans k)
  · exact absurd b (lane_not_hash ans k)
  · exact PublicQuery.hash.inj c
  · exact absurd (mem_queriesAlong_allQ ans (truePadsM_encAt _) _ d) not_encAt_hash
  · exact absurd a (lane_not_hash ans k)
  · exact absurd b (lane_not_hash ans k)
  · exact PublicQuery.hash.inj c
  · exact absurd (mem_queriesAlong_allQ ans (evalPadsM_encAt bits _) _ d) not_encAt_hash
  · exact absurd e (lane_not_hash ans k)
  · exact absurd f (lane_not_hash ans k)
  · obtain ⟨_, _, _, same⟩ := mem_queriesAlong_allQ ans (unlockM_gadgetQ _ _ _) _ g
    cases same

end Shadow

/-! ### The opening is fresh, and its run described -/

section Fresh

variable [FieldCertificate] in
theorem laneSet_ne {lane lane' : Lane} (different : lane ≠ lane') {i : FixedIndex}
    (inside : i ∈ laneSet lane) : i ∉ laneSet lane' := by
  rintro ⟨c', inside'⟩
  obtain ⟨c, inside⟩ := inside
  exact different (indexAt_unique inside inside').1

theorem consumedIndex_none_of_encAt {bits : BitInput} {r : Request} (inside : EncAt r) :
    consumedIndex bits r = none := by
  cases r with
  | encForward _ _ => rfl
  | fixedForward _ _ => exact inside.elim
  | fixedInverse _ _ => exact inside.elim
  | encInverse _ _ => exact inside.elim
  | hash _ => exact inside.elim

theorem inIdx_of_none {bits : BitInput} {S : Set FixedIndex} {r : Request}
    (none : consumedIndex bits r = none) : InIdx bits S r := fun i hi => by
  rw [none] at hi
  cases hi

variable [FieldCertificate]

theorem lane_fresh_avoid (bits : BitInput) (count : ℕ) (countLe : count ≤ elementCountX)
    (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (word : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (U : Set FixedIndex)
    (avoid : ∀ i ∈ laneSet lane, i ∉ U) :
    Fresh bits U (Programs.evalLaneM count lane joins scale word labels) :=
  ((lane_fresh count lane joins scale word labels bits countLe).union_disjoint
    (allQ_inIdx_lane count lane joins scale word labels bits) avoid).mono
      fun _ member => Or.inr member

/-- **Along every path of the opening, the non-designated indices are distinct.** -/
theorem opening_fresh (table : Public) (bits : BitInput) (mac : InputMac) :
    Fresh bits ∅ (openingQueriesM table bits mac) := by
  have hashNone : ∀ t : BaseField, AllQ (fun r => consumedIndex bits r = none)
      (Programs.askHash t) := fun t => .query _ _ rfl fun _ => .pure _
  have padsNone : ∀ keys : WhiteningKeys, AllQ (fun r => consumedIndex bits r = none)
      (whitePadsM keys) := fun keys =>
    (whitePadsM_allQ keys).mono fun _ inside => consumedIndex_none_of_encAt inside
  rw [openingQueriesM_eq]
  refine Fresh.bind (S := laneSet .curveX)
    (lane_fresh _ _ _ _ _ _ bits (by decide)) (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  refine Fresh.bind (S := laneSet .curveY)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i inside outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  · rcases outside with outside | outside
    · exact outside
    · exact laneSet_ne (by decide) inside outside
  refine Fresh.bind (S := ∅) (Fresh.of_none (hashNone _) _)
    ((hashNone _).mono fun _ none => inIdx_of_none none) fun _ => ?_
  refine Fresh.bind (S := ∅) (Fresh.of_none (padsNone _) _)
    ((padsNone _).mono fun _ none => inIdx_of_none none) fun _ => ?_
  refine Fresh.bind (S := laneSet .pointX)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i inside outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => ?_
  · rcases outside with (((outside | outside) | outside) | outside) | outside
    · exact outside
    · exact laneSet_ne (by decide) inside outside
    · exact laneSet_ne (by decide) inside outside
    · exact outside
    · exact outside
  refine Fresh.bind (S := laneSet .pointY)
    (lane_fresh_avoid bits _ (by decide) _ _ _ _ _ _ fun i inside outside => ?_)
    (allQ_inIdx_lane _ _ _ _ _ _ bits) fun _ => .pure _ _
  rcases outside with ((((outside | outside) | outside) | outside) | outside) | outside
  · exact outside
  · exact laneSet_ne (by decide) inside outside
  · exact laneSet_ne (by decide) inside outside
  · exact outside
  · exact outside
  · exact laneSet_ne (by decide) inside outside

variable [GroupCertificate]

/-- **The opening run, described.** -/
theorem opening_described (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record) (member : some ran ∈ (openingRun source input tape).support) :
    Described (restoredBits source input) tape
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input))
      LazyOracle.empty (fun _ => none) ran :=
  runRefill_describe (restoredBits source input) tape _
    (openingQueriesM_forwardOnly _ _ _) ∅ (opening_fresh _ _ _) LazyOracle.empty (fun _ => none) ∅
    (fun _ _ => ⟨fun h => h, rfl⟩) ran (openingRun_mem member)

end Fresh

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
