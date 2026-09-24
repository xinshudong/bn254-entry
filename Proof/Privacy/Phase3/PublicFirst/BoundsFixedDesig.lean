/-
**Phase 3, P1m — (B1) the fixed-key part on the curve: the designated outputs.**

A designated pair is `(E*, o ⊕ E*)` with `o` a limb of a preimage the installation draws **after**
the opening, from targets that read the opening's value. That value is a function of the tape
alone (`opening_value`: system B's masks are the tape's Davies–Meyer values, `0` at a designated
block, `lane_eval_eq`), so `o` is independent of the fold answers behind `E*`:

* `opening_fold_le` — the opening's `E*`-type input of a system-B mask index hits any point with
  mass `≤ 1/2^128` (the fold potential, split after the pads);
* `designated_out_le` — `Pr[y ∈ fixedOut_i] ≤ 1/2^128` at a designated index.
-/

import Proof.Privacy.Phase3.PublicFirst.BoundsFixedPad

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source openingQueriesM whitePadsM IsDesignated
  interceptAnswer programRequests designatedIndex collectorTargets preimages idealSamplers)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell Tape Request AllQ EncAt FixedAt IndexAt
  runRefill cellOf runRefillT dropTouched uniformMaskTape queriesAlong queriesAlong_bind
  runRefill_eq_runRefillT fq_bind_assoc cellOf_maskIndex maskIndex foldLabels runRefillT_bind)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The opening's value is the tape's -/

section Value

open Classical in
/-- The Davies–Meyer value of the opening at a mask index: `0` if designated, else the tape's. -/
def tapeHD (bits : BitInput) (tape : Tape) (index : FixedIndex) : Block :=
  if IsDesignated bits index then 0 else tapeH tape index

variable [FieldCertificate] [GroupCertificate] (source : Stage1Source) (input : AffineInput)
  (tape : Tape)
  (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
    LState × Record)
  (member : some ran ∈ (openingRun source input tape).support)

include member

/-- **A mask question of the opening has the tape's Davies–Meyer value** (`0` if designated). -/
theorem opening_mask_dm (i : FixedIndex) (x : Block)
    (onPath : .fixedForward i x ∈ queriesAlong (refillAns (restoredBits source input) ran.2.1)
      (openingQueriesM source.publicValue (restoredBits source input) (restoredMac source input)))
    {cell : Cell} (cellEq : cellOf i = some cell) :
    fwdAns (refillAns (restoredBits source input) ran.2.1) i x ^^^ x =
      tapeHD (restoredBits source input) tape i := by
  classical
  by_cases designated : IsDesignated (restoredBits source input) i
  · have intercept := Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_designated
      (restoredBits source input) x designated
    unfold fwdAns tapeHD
    rw [refillAns_intercept intercept, if_pos designated, BitVec.xor_self]
    rfl
  · have intercept := Kriterion.ArgoMAC.Phase3.Lazy.interceptAnswer_plain
      (restoredBits source input) x designated
    obtain ⟨stored, answerEq⟩ := curve_stored_answer source input tape ran member _ onPath intercept
    unfold tapeHD
    rw [if_neg designated]
    exact site_dm source input tape ran member i x (a := fwdAns (answerOf ran.2.1) i x) stored
      answerEq cellEq

theorem pointX_value :
    FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (pointXM source.publicValue (restoredBits source input)
          (Programs.whitenMacOf (wPadsOf source.publicValue (restoredBits source input)
            (restoredMac source input) (refillAns (restoredBits source input) ran.2.1))
            (restoredMac source input))) =
      laneValue pointElementCountX .pointX
        (fun chunk => Pipeline.readPointX (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .x)
        (tapeHD (restoredBits source input) tape) := by
  refine lane_eval_eq _ _ _ _ _ _ _ _ fun i x onPath ⟨c, switch, el, b, same⟩ => ?_
  exact opening_mask_dm source input tape ran member i x
    (pointX_mem_opening _ _ _ _ _ onPath)
    (by rw [same]; exact cellOf_maskIndex .pointX c switch el b le_rfl)

theorem pointY_value :
    FreeQuery.eval (refillAns (restoredBits source input) ran.2.1)
        (pointYM source.publicValue (restoredBits source input)
          (Programs.whitenMacOf (wPadsOf source.publicValue (restoredBits source input)
            (restoredMac source input) (refillAns (restoredBits source input) ran.2.1))
            (restoredMac source input))) =
      laneValue pointElementCountY .pointY
        (fun chunk => Pipeline.readPointY (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .y)
        (tapeHD (restoredBits source input) tape) := by
  refine lane_eval_eq _ _ _ _ _ _ _ _ fun i x onPath ⟨c, switch, el, b, same⟩ => ?_
  exact opening_mask_dm source input tape ran member i x
    (pointY_mem_opening _ _ _ _ _ onPath)
    (by rw [same]; exact cellOf_maskIndex .pointY c switch el b le_rfl)

omit member in
theorem eval_openingQueriesM (table : Public) (bits : BitInput) (mac : InputMac)
    (ans : (request : Request) → request.Answer) :
    FreeQuery.eval ans (openingQueriesM table bits mac) =
      (FreeQuery.eval ans (pointXM table bits (Programs.whitenMacOf (wPadsOf table bits mac ans)
          mac)),
        FreeQuery.eval ans (pointYM table bits (Programs.whitenMacOf (wPadsOf table bits mac ans)
          mac))) := by
  rw [openingQueriesM_eq]
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askHash]

/-- **The opening's value is a function of the tape.** -/
theorem opening_value :
    ran.1 = (laneValue pointElementCountX .pointX
        (fun chunk => Pipeline.readPointX (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .x)
        (tapeHD (restoredBits source input) tape),
      laneValue pointElementCountY .pointY
        (fun chunk => Pipeline.readPointY (unpack (source.publicValue.scale.get chunk)))
        (Pipeline.coordBits (restoredBits source input) .y)
        (tapeHD (restoredBits source input) tape)) := by
  rw [(opening_described source input tape ran member).value, eval_openingQueriesM,
    pointX_value source input tape ran member, pointY_value source input tape ran member]

/-- **Every fold index holds exactly the opening's pair after the opening.** -/
theorem fold_opening (lane : Lane) (c : Fin chunkCount) (half : Bool) :
    let pads := wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) ran.2.1)
    let W := laneW (laneJoins source.publicValue lane) (laneLabels (restoredMac source input) pads
      lane) c
    let index := foldIdx lane c (chunkValue (laneWord (restoredBits source input) lane) c).toNat half
    (ran.2.1.fixed index).used = 1 ∧
      lk (ran.2.1.fixed index) W.toFin =
        some (fwdAns (refillAns (restoredBits source input) ran.2.1) index W).toFin := by
  intro pads W index
  have onA := lane_mem_opening _ _ _ _ lane _ (fold_mem_lane (refillAns (restoredBits source input)
    ran.2.1) _ lane _ (laneScale source.publicValue lane) _
      (laneLabels (restoredMac source input) pads lane) c half)
  obtain ⟨stored, answerEq⟩ := curve_stored_answer source input tape ran member _ onA
    (intercept_none_of_hot lane c _ half _)
  have lk1 := stored_fixed_lk (a := fwdAns (answerOf ran.2.1) index W) stored
  have fwdEq : fwdAns (refillAns (restoredBits source input) ran.2.1) index W =
      fwdAns (answerOf ran.2.1) index W := answerEq
  refine ⟨?_, by rw [fwdEq]; exact lk1⟩
  have small := used_le_one _ (inputOf source.publicValue (restoredBits source input)
      (restoredMac source input) pads (refillAns (restoredBits source input) ran.2.1)
      (restoredMac source input) index).toFin
    fun x y found => by
      rcases (opening_described source input tape ran member).fixed index x y found
        with old | ⟨onPath, _, _⟩
      · rw [lk_empty_fixed] at old
        cases old
      · rw [← opening_fixed_input _ _ _ _ _ index _ onPath, BitVec.toFin_ofFin]
  have positive : (ran.2.1.fixed index).used ≠ 0 := by
    intro zero
    have known : (ran.2.1.fixed index).knownInput W.toFin :=
      (knownInput_iff _ _).mpr (by rw [lk1]; exact Option.some_ne_none _)
    unfold SparsePermutation.knownInput at known
    omega
  omega

end Value

/-! ### The opening's inputs at system B's masks -/

section OpeningFold

variable [FieldCertificate] [GroupCertificate]

/-- **After the opening, the canonical input of a system-B mask index hits any point with mass
`≤ 1/2^128`.** -/
theorem opening_fold_le (source : Stage1Source) (input : AffineInput) (tape : Tape) (lane : Lane)
    (point : lane = .pointX ∨ lane = .pointY) (c : Fin chunkCount) (s : Fin (2 ^ chunkBits))
    (e : Fin elementCountX) (b : Fin 3) (z : Block) :
    ∑' ran, openingRun source input tape ran * optWeight (fun state =>
      ind (inputOf source.publicValue (restoredBits source input) (restoredMac source input)
        (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
          (refillAns (restoredBits source input) state))
        (refillAns (restoredBits source input) state) (restoredMac source input)
        (.scale lane c s e b) = z)) ran ≤ delta := by
  set value := (chunkValue (laneWord (restoredBits source input) lane) c).toNat with valueDef
  let fixedPart : (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) → Block :=
    fun pads => foldLabels value
      (labelAt (chunkLabels (laneLabels (restoredMac source input) pads lane) c))
      (joinAt (hotSlice (laneJoins source.publicValue lane) c)) 0 ⟨s.val, by
        have := s.isLt; unfold chunkBits at this; exact this⟩
  refine opening_split_le source input tape _ _ (openingQueriesM_padsSplit _ _ _)
    (padsRest_forward _ _ _) _ (fun pads => chunkFoldPot lane c value (z ^^^ fixedPart pads))
    (fun pads => chunkFoldPot_step lane c value _) (fun pads => chunkFoldPot_siteSame lane c value _)
    delta (fun mid midMember => ?_) (fun mid midMember ranT ranMember openMember => ?_)
  · -- after the pads, the chunk's fold indices are empty
    have d := runRefill_describe (restoredBits source input) tape _
      (padsFirst_forward source.publicValue (restoredBits source input)
        (restoredMac source input)) ∅ (padsFirst_fresh _ _ _) LazyOracle.empty (fun _ => none) ∅
      (fun _ _ => ⟨fun h => h, rfl⟩) _ (runRefillT_mem_runRefill _ _ _ _ _ _ _ midMember)
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
      (padsFirst_fresh source.publicValue (restoredBits source input)
        (restoredMac source input)) (padsFirst_forward _ _ _) _ mid midMember ranT ranMember
    rw [eval_padsFirst] at value'
    have padsEq : wPadsOf source.publicValue (restoredBits source input)
        (restoredMac source input)
        (refillAns (restoredBits source input) ranT.2.1) = mid.1 := value'
    obtain ⟨used0, lk0⟩ := fold_opening source input tape (dropTouched ranT) openMember lane c
      false
    obtain ⟨used1, lk1⟩ := fold_opening source input tape (dropTouched ranT) openMember lane c
      true
    refine le_trans (ind_mono fun same => ?_) (foldF_bound _ _ _ used0 used1 _ _ _ _ lk0 lk1)
    rw [inputOf_scale] at same
    rw [BitVec.ofFin_toFin, BitVec.ofFin_toFin,
      show (dropTouched ranT).2.1 = ranT.2.1 from rfl]
    rw [padsEq] at same ⊢
    exact (xor_eq_iff _ _ _).mp same

end OpeningFold

/-! ### The designated outputs -/

section Designated

variable [FieldCertificate] [GroupCertificate]

theorem tsum_swap3 {A C B : Type} (P : A → ℝ≥0∞) (u : C → ℝ≥0∞) (Q : C → B → ℝ≥0∞)
    (K : B → A → ℝ≥0∞) :
    ∑' a, P a * ∑' c, u c * ∑' b, Q c b * K b a =
      ∑' c, u c * ∑' b, Q c b * ∑' a, P a * K b a := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun c => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

/-- The preimages the installation draws, from the opening's value. -/
abbrev blocksLaw (scalar : NonZeroScalar) (source : Stage1Source) (input : AffineInput)
    (value : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (coins : Coins) : PMF (Option (Fin digitCount × Fin 3 → Block × Block × Block)) :=
  preimages idealSamplers (collectorTargets (restoredBits source input)
    (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable source.publicValue)
      (Pipeline.digitValues value.1 value.2) (restoredBits source input).toAffine)
    (fun digit => trueRows scalar coins input digit))

/-- **After the opening**: the continuation's event mass, through the preimages. -/
theorem post_blocks_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (event : Points FixedIndex EncPRF.PermutationIndex → Prop)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (K : (Fin digitCount × Fin 3 → Block × Block × Block) → ℝ≥0∞)
    (perRun : ∀ blocks : Fin digitCount × Fin 3 → Block × Block × Block,
        ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
              (restoredMac source input))
            (programAllSkip (programRequests (restoredBits source input) ran.2.2 blocks) ran.2.1)
            result *
          ind (event ((pointsOf result.2).union
            (requestPoints (programRequests (restoredBits source input) ran.2.2 blocks)))) ≤
        K blocks) :
    letI : Fintype Coins := Fintype.ofFinite Coins
    ∑' o, privateContU (planBShadow scalar off) scalar source input ran o *
      ind (event (outcomePoints o)) ≤
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' blocks, blocksLaw scalar source input ran.1 coins blocks * Option.elim blocks 0 K := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  unfold privateContU
  dsimp only
  rw [tsum_bind_mul]
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  rw [tsum_bind_mul]
  refine tsum_mul_le_of_support _ _ _ fun blocks blocksMember => ?_
  rcases blocks with _ | blocks
  · exact absurd blocksMember (preimages_ne_none _)
  · dsimp only
    rw [tsum_bind_mul]
    refine le_trans (tsum_le_of_support' _ _ _ fun coin _ => ?_) le_rfl
    obtain ⟨delta, offCoin⟩ := coin
    rw [tsum_map_mul]
    simp only [planBShadow_onCurve, outcomePoints]
    have bounded := perRun blocks
    rw [show (Lamport.restore input (sourceLabels source input)).input = restoredBits source input
      from rfl]
    exact bounded

/-- The opening-state weight of one designated preimage limb. -/
abbrev limbWeight (source : Stage1Source) (input : AffineInput) (i : FixedIndex) (z : Block)
    (state : LState) : ℝ≥0∞ :=
  ind (inputOf source.publicValue (restoredBits source input) (restoredMac source input)
    (wPadsOf source.publicValue (restoredBits source input) (restoredMac source input)
      (refillAns (restoredBits source input) state))
    (refillAns (restoredBits source input) state) (restoredMac source input) i = z)

/-- **A designated output of the final state is `E* ⊕ o` with `o` the requested limb.** -/
theorem designated_run_le (source : Stage1Source) (input : AffineInput) (tape : Tape)
    (ran : ((Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField)) ×
      LState × Record)
    (member : some ran ∈ (openingRun source input tape).support) (d : Fin digitCount) (col b : Fin 3)
    (y : Block) (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    ∑' result, runLazyQ (shadowOnM source.publicValue (restoredBits source input)
          (restoredMac source input))
        (programAllSkip (programRequests (restoredBits source input) ran.2.2 blocks) ran.2.1)
        result *
      ind (((pointsOf result.2).union
        (requestPoints (programRequests (restoredBits source input) ran.2.2 blocks))).fixedOut
          (designatedIndex (restoredBits source input) d col b) y) ≤
      limbWeight source input (designatedIndex (restoredBits source input) d col b)
        (y ^^^ Kriterion.ArgoMAC.Phase3.Glue.limbAt b (blocks (d, col))) ran.2.1 := by
  refine tsum_le_of_support' _ _ _ fun result resultMember => ind_mono fun hit => ?_
  obtain ⟨inp, out, inReq, yEq⟩ : ∃ inp out, (designatedIndex (restoredBits source input) d col b,
      some inp, out) ∈ programRequests (restoredBits source input) ran.2.2 blocks ∧
        y = out ^^^ inp := by
    rcases hit with ⟨x, found⟩ | ⟨inp, out, inReq, yEq⟩
    · obtain ⟨inp, out, inReq, _, yEq⟩ := final_designated_output source input tape ran member
        blocks result resultMember _ ⟨d, col, b, rfl⟩ x y.toFin found
      exact ⟨inp, out, inReq, by rw [← yEq, BitVec.ofFin_toFin]⟩
    · exact ⟨inp, out, inReq, yEq⟩
  obtain ⟨d', c', b', same, _, outEq⟩ := mem_programRequests inReq
  have slot := Kriterion.ArgoMAC.Phase3.Glue.candidateIndex_injective
    (a₁ := (d, col, b, Kriterion.ArgoMAC.Phase3.Glue.designatedSwitch (restoredBits source input)))
    (a₂ := (d', c', b', Kriterion.ArgoMAC.Phase3.Glue.designatedSwitch (restoredBits source input)))
    same
  simp only [Prod.mk.injEq] at slot
  obtain ⟨rfl, rfl, rfl, -⟩ := slot
  have inpEq := request_input source input tape ran member blocks (restoredMac source input) _ inp
    out inReq
  rw [← inpEq, yEq, outEq, BitVec.xor_comm _ inp, BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero]

/-- A designated index is a system-B `pointX` mask index. -/
theorem designatedIndex_scale (bits : BitInput) (d : Fin digitCount) (col b : Fin 3) :
    ∃ (s : Fin (2 ^ chunkBits)) (e : Fin elementCountX),
      designatedIndex bits d col b = .scale .pointX Kriterion.ArgoMAC.Phase3.Glue.chunkZero s e b := by
  unfold designatedIndex
  refine ⟨_, _, scaleIndexOf_eq _ _ _ _ _ ?_ ?_⟩
  · exact lt_of_lt_of_le (Fin.isLt _) (by unfold pointElementCountX elementCountX; omega)
  · exact lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by norm_num) (chunkWidth_le _))

/-- **Per tape**: the designated output mass, for an opening whose value is `V`. -/
theorem designated_tape_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (tape : Tape)
    (V : (Fin pointElementCountX → BaseField) × (Fin pointElementCountY → BaseField))
    (valueEq : ∀ ran, some ran ∈ (openingRun source input tape).support → ran.1 = V)
    (d : Fin digitCount) (col b : Fin 3) (y : Block) :
    ∑' ranOpt, openingRun source input tape ranOpt *
      ∑' o, abortCont (privateContU (planBShadow scalar off) scalar source input) ranOpt o *
        ind ((outcomePoints o).fixedOut (designatedIndex (restoredBits source input) d col b) y) ≤
      delta := by
  letI : Fintype Coins := Fintype.ofFinite Coins
  refine le_trans (tsum_mul_le_of_support _ _ (fun ranOpt => ∑' coins,
    PMF.uniformOfFintype Coins coins * ∑' blocks, blocksLaw scalar source input V coins blocks *
      Option.elim blocks 0 fun bl => optWeight (limbWeight source input
        (designatedIndex (restoredBits source input) d col b)
        (y ^^^ Kriterion.ArgoMAC.Phase3.Glue.limbAt b (bl (d, col)))) ranOpt)
    fun ranOpt member => ?_) ?_
  · rcases ranOpt with _ | ran
    · exact absurd member (openingRun_ne_none source input tape)
    · simp only [abortCont]
      refine le_trans (post_blocks_le scalar off source input
        (fun p => p.fixedOut (designatedIndex (restoredBits source input) d col b) y) ran
        (fun bl => limbWeight source input (designatedIndex (restoredBits source input) d col b)
          (y ^^^ Kriterion.ArgoMAC.Phase3.Glue.limbAt b (bl (d, col))) ran.2.1)
        fun bl => designated_run_le source input tape ran member d col b y bl) (le_of_eq ?_)
      rw [valueEq ran member]
      rfl
  · rw [tsum_swap3 (openingRun source input tape) (PMF.uniformOfFintype Coins)
      (fun coins blocks => blocksLaw scalar source input V coins blocks)
      (fun (blocks : Option (Fin digitCount × Fin 3 → Block × Block × Block)) ranOpt =>
        Option.elim blocks 0 fun bl =>
        optWeight (limbWeight source input (designatedIndex (restoredBits source input) d col b)
          (y ^^^ Kriterion.ArgoMAC.Phase3.Glue.limbAt b (bl (d, col)))) ranOpt)]
    refine tsum_le_of_support' _ _ _ fun coins _ => tsum_le_of_support' _ _ _ fun blocks _ => ?_
    rcases blocks with _ | bl
    · simp only [Option.elim, mul_zero, tsum_zero, zero_le]
    · obtain ⟨s, e, idxEq⟩ := designatedIndex_scale (restoredBits source input) d col b
      show ∑' ranOpt, openingRun source input tape ranOpt * optWeight (limbWeight source input
        (designatedIndex (restoredBits source input) d col b)
          (y ^^^ Kriterion.ArgoMAC.Phase3.Glue.limbAt b (bl (d, col)))) ranOpt ≤ delta
      rw [idxEq]
      exact opening_fold_le source input tape .pointX (Or.inl rfl) _ s e b _

/-- **The output mass at a designated index**, on the curve: `≤ 1/2^128`. -/
theorem designated_out_le (scalar : NonZeroScalar) (off : OffShadow) (source : Stage1Source)
    (input : AffineInput) (target : Point) (d : Fin digitCount) (col b : Fin 3) (y : Block) :
    ∑' o, privateStage2U uniformMaskTape (planBShadow scalar off) scalar source input (some target)
        o * ind ((outcomePoints o).fixedOut (designatedIndex (restoredBits source input) d col b) y) ≤
      delta := by
  rw [privateStage2U_some_eq, tsum_bind_mul]
  refine le_trans (ENNReal.tsum_le_tsum (g := fun tape => uniformMaskTape tape * delta)
    fun tape => mul_le_mul' le_rfl ?_) (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe,
      one_mul]))
  rw [tsum_bind_mul]
  exact designated_tape_le scalar off source input tape _
    (fun ran member => opening_value source input tape ran member) d col b y

end Designated

end


end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
