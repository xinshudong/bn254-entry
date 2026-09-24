/-
**Phase 3, P1o — the coincidence guess, part 1: what the reach asks.**

`CoincidenceGuess` (`LiftGuess.lean`) bounds, at a fixed input `u`, the mass of `Coincide u`: the
reach (the full evaluator `Programs.onCurveM` on `u`'s labels, run on the tape) asks a garbler
question the designed rule hides. This file pins down **every** question of the reach, as a pure
function of the tape (`AsksOnly`, `laneAsks`, `onCurveM_asks`):

* each lane asks the step-1 fold gates **off** its active parent, at its level-1 labels, and every
  block of every switch **off** its active switch, at its one-hot labels (`LaneAsk`);
* the bridge hash at `t_eval = t + mask·(x³ + 3 − y²)` (`reach_hashArg`: the evaluator's curve
  values are the garbler's, `Pipeline.curveValues_garble`);
* EncPRF questions (the pads);
* every gadget position of every digit, at the transformed label of `u`'s bit.
-/

import Proof.Privacy.Phase3.PublicFirst.LiftHop
import Proof.Privacy.Phase3.Hidden

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (transcriptOf QueryOnly)

noncomputable section

/-! ### 1. Every question of a program, on given answers -/

/-- Every question `P` asks on the answers `ans` satisfies `S`. -/
def AsksOnly {α : Type} (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop) (P : FreeQuery Programs.Spec α) :
    Prop :=
  ∀ entry ∈ transcriptOf ans P, S entry.1

namespace AsksOnly

variable {α β : Type} {ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer}
  {S S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}

theorem pure' (value : α) : AsksOnly ans S (Pure.pure value : FreeQuery Programs.Spec α) := by
  intro entry member
  cases member

theorem bind {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β}
    (first : AsksOnly ans S P) (rest : AsksOnly ans S (f (P.eval ans))) : AsksOnly ans S (P >>= f) := by
  intro entry member
  rw [Hidden.transcriptOf_bind] at member
  rcases List.mem_append.mp member with inFirst | inRest
  · exact first entry inFirst
  · exact rest entry inRest

theorem bind_eq {P : FreeQuery Programs.Spec α} {f : α → FreeQuery Programs.Spec β} (value : α)
    (first : AsksOnly ans S P) (evalEq : P.eval ans = value) (rest : AsksOnly ans S (f value)) :
    AsksOnly ans S (P >>= f) := by
  subst evalEq
  exact bind first rest

theorem mono {P : FreeQuery Programs.Spec α} (only : AsksOnly ans S P) (weaker : ∀ q, S q → S' q) :
    AsksOnly ans S' P :=
  fun entry member => weaker _ (only entry member)

theorem of_queryOnly {P : FreeQuery Programs.Spec α} (only : QueryOnly S P) : AsksOnly ans S P :=
  only.mem ans

theorem vector : ∀ (count : Nat) {P : Fin count → FreeQuery Programs.Spec α},
    (∀ index, AsksOnly ans S (P index)) → AsksOnly ans S (FreeQuery.vector count P)
  | 0, _, _ => pure' _
  | count + 1, P, each => by
      show AsksOnly ans S (FreeQuery.vector count (fun index => P index.castSucc) >>= fun values =>
          P (Fin.last count) >>= fun value => Pure.pure (values.push value))
      exact bind (vector count fun index => each index.castSucc)
        (bind (each (Fin.last count)) (pure' _))

end AsksOnly

/-! ### 2. One lane of the evaluator -/

variable [FieldCertificate] [GroupCertificate]

/-- **A question of one lane of the evaluator**: a step-1 fold gate off the active parent, at the
level-1 label, or a block of a switch off the active one, at its one-hot label. -/
def LaneAsk (O : PermutationOracle FixedIndex Block) (lane : Lane) (count : Nat)
    (joins : Vector Block foldStepCount)
    (bits : BitVec PlanB.coordinateBits) (labels : Fin PlanB.coordinateBits → Block)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  ∃ c : Fin chunkCount,
    (∃ (r : Fin (2 ^ 1)) (half : Bool), r ≠ activeAt (chunkValue bits c).toNat 1 ∧
      q = .fixedForward (hotIndexNat lane c 1 r.val half)
        (evalFold O lane c (chunkValue bits c).toNat (labelAt (chunkLabels labels c))
          (joinAt (hotSlice joins c)) 1 r)) ∨
    (∃ (j : Fin (2 ^ chunkWidth c)) (element : Fin count) (block : Fin 3),
      j ≠ chunkOf bits c ∧
      q = .fixedForward (scaleIndexOf lane c j.val element block)
        (evalFold O lane c (chunkValue bits c).toNat (labelAt (chunkLabels labels c))
          (joinAt (hotSlice joins c)) (chunkWidth c) j))

/-- The fold asks each gate off the active parent of its level, at the level's label. -/
theorem evalFoldM_asks (O : Oracle) (lane : Lane) (c : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ steps,
    AsksOnly (publicAnswer O)
      (fun q => ∃ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < steps ∧ r ≠ activeAt value n ∧
        q = .fixedForward (hotIndexNat lane c n r.val half) (evalFold O.1 lane c value bitLabel join n r))
      (Programs.evalFoldM lane c value bitLabel join steps)
  | 0 => AsksOnly.pure' _
  | steps + 1 => by
      show AsksOnly _ _ (Programs.evalFoldM lane c value bitLabel join steps >>= fun previous =>
        Programs.evalStepM lane c steps (bitLabel steps) (join steps) (activeAt value steps) previous
          >>= fun right => Pure.pure (extendLevel steps previous right))
      refine AsksOnly.bind_eq _ ((evalFoldM_asks O lane c value bitLabel join steps).mono
        fun q ⟨n, r, half, small, off, eq⟩ => ⟨n, r, half, by omega, off, eq⟩)
        (Programs.eval_evalFoldM O lane c value bitLabel join steps) ?_
      refine AsksOnly.bind ?_ (AsksOnly.pure' _)
      unfold Programs.evalStepM
      refine AsksOnly.bind (AsksOnly.vector _ fun entry => ?_) (AsksOnly.pure' _)
      by_cases same : entry = activeAt value steps
      · rw [if_pos same]
        exact AsksOnly.pure' _
      · rw [if_neg same]
        refine AsksOnly.of_queryOnly ?_
        unfold Programs.foldMaskM
        refine QueryOnly.bind (hashM_ask _ _ ⟨steps, entry, false, by omega, same, rfl⟩)
          fun _ => QueryOnly.bind (hashM_ask _ _ ⟨steps, entry, true, by omega, same, rfl⟩)
            fun _ => QueryOnly.pure' _

/-- No gate of step `0` is asked: its only entry is the active one. -/
theorem activeAt_zero (value : Nat) (r : Fin (2 ^ 0)) : r = activeAt value 0 :=
  Fin.ext (by
    have h1 := r.isLt
    have h2 := (activeAt value 0).isLt
    simp only [pow_zero] at h1 h2
    omega)

/-- A switch's mask asks its own blocks at its label. -/
theorem switchMaskM_asks (count : Nat) (lane : Lane) (c : Fin chunkCount) (switch : Nat) (label : Block) :
    QueryOnly (fun q => ∃ (element : Fin count) (block : Fin 3),
        q = .fixedForward (scaleIndexOf lane c switch element block) label)
      (Programs.switchMaskM count lane c switch label) := by
  unfold Programs.switchMaskM
  refine QueryOnly.bind (QueryOnly.vector _ fun element => ?_) fun _ => QueryOnly.pure' _
  exact QueryOnly.bind (hashM_ask _ _ ⟨element, 0, rfl⟩) fun _ =>
    QueryOnly.bind (hashM_ask _ _ ⟨element, 1, rfl⟩) fun _ =>
      QueryOnly.bind (hashM_ask _ _ ⟨element, 2, rfl⟩) fun _ => QueryOnly.pure' _

/-- **Every question of one lane of the evaluator** is a `LaneAsk`. -/
theorem laneAsks (O : Oracle) (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec PlanB.coordinateBits)
    (labels : Fin PlanB.coordinateBits → Block) :
    AsksOnly (publicAnswer O) (LaneAsk O.1 lane count joins bits labels)
      (Programs.evalLaneM count lane joins scale bits labels) := by
  unfold Programs.evalLaneM
  refine AsksOnly.bind (AsksOnly.vector _ fun c => ?_) (AsksOnly.pure' _)
  unfold Programs.evalChunkM
  refine AsksOnly.bind_eq _ ((evalFoldM_asks O lane c (chunkValue bits c).toNat
      (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c)).mono ?_)
    (Programs.eval_evalFoldM O lane c _ _ _ (chunkWidth c)) ?_
  · rintro q ⟨n, r, half, small, off, rfl⟩
    refine ⟨c, Or.inl ?_⟩
    have two : chunkWidth c = 2 := chunkWidth_two c
    have nOne : n = 1 := by
      rcases Nat.lt_or_ge n 1 with zero | one
      · obtain rfl : n = 0 := by omega
        exact absurd (activeAt_zero _ r) off
      · omega
    subst nOne
    exact ⟨r, half, off, rfl⟩
  · refine AsksOnly.bind ?_ (AsksOnly.pure' _)
    unfold Programs.evalMasksM
    refine AsksOnly.bind (AsksOnly.vector _ fun switch => ?_) (AsksOnly.pure' _)
    by_cases same : switch = chunkOf bits c
    · rw [if_pos same]
      exact AsksOnly.pure' _
    · rw [if_neg same]
      refine (AsksOnly.of_queryOnly (switchMaskM_asks count lane c switch.val _)).mono ?_
      rintro q ⟨element, block, rfl⟩
      exact ⟨c, Or.inr ⟨switch, element, block, same, rfl⟩⟩

/-! ### 3. The whole reach -/

/-- The evaluator's pads ask only EncPRF questions, at their first whitening key. -/
theorem evalPadsM_encOnly (keys : WhiteningKeys) (bits : BitInput) :
    QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool),
      q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first)) (Programs.evalPadsM keys bits) := by
  have pad : ∀ coordinate index bit,
      QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool),
        q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
        (Programs.padM keys coordinate index bit) :=
    fun coordinate index bit =>
      QueryOnly.bind (QueryOnly.ask _ ⟨coordinate, index, bit, rfl⟩) fun _ => QueryOnly.pure' _
  have row : ∀ (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount) (index : Fin coordinateBitCount),
      QueryOnly (fun q => ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool),
        q = .encForward (coordinate, index) (encodeBit bit ^^^ keys.first))
        (Programs.padM keys which index false >>= fun zero =>
        if word.getLsb index then Programs.padM keys which index true >>= fun one => Pure.pure (zero, one)
        else Pure.pure (zero, zero)) := by
    intro which word index
    refine QueryOnly.bind (pad _ _ _) fun _ => ?_
    split
    · exact QueryOnly.bind (pad _ _ _) fun _ => QueryOnly.pure' _
    · exact QueryOnly.pure' _
  exact QueryOnly.bind (QueryOnly.vector _ fun index => row .x bits.xBits index) fun _ =>
    QueryOnly.bind (QueryOnly.vector _ fun index => row .y bits.yBits index) fun _ => QueryOnly.pure' _

/-- The gadget asks every position of every digit at the given label. -/
theorem unlockM_asks (table : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    QueryOnly (fun q => ∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
        q = .fixedForward (.gadget o κ position) (macAt mac κ position))
      (Programs.unlockM table input mac) := by
  unfold Programs.unlockM
  refine QueryOnly.vector _ fun o => QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
  unfold Programs.gadgetMaskM Programs.gadgetDigestM
  exact QueryOnly.bind (QueryOnly.bind (QueryOnly.vector _ fun index =>
      hashM_ask _ _ ⟨o, .x, index, rfl⟩) fun _ => QueryOnly.pure' _) fun _ =>
    QueryOnly.bind (QueryOnly.bind (QueryOnly.vector _ fun index =>
      hashM_ask _ _ ⟨o, .y, index, rfl⟩) fun _ => QueryOnly.pure' _) fun _ => QueryOnly.pure' _

/-- The reach's bridge-hash question. -/
def reachHashArg (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) : BaseField :=
  CurveMembership.evaluate table.curve bits.toAffine
    (Pipeline.curveValues (Pipeline.curveXValues O.1 table bits mac)
      (Pipeline.curveYValues O.1 table bits mac))

/-- The reach's pads, keyed by its own bridge hash. -/
def reachPads (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads O.2.1
    ⟨(O.2.2 (reachHashArg O table bits mac)).1, (O.2.2 (reachHashArg O table bits mac)).2⟩ bits

/-- An EncPRF question of the reach: a pad at its own first whitening key. -/
def ReachEnc (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  ∃ (coordinate : EncPRF.Coordinate) (index : Fin coordinateBitCount) (bit : Bool),
    q = .encForward (coordinate, index) (encodeBit bit ^^^ (O.2.2 (reachHashArg O table bits mac)).1)

/-- **A question of the reach.** -/
def ReachAsk (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) : Prop :=
  LaneAsk O.1 .curveX curveElementCountX table.curveXHot (Pipeline.coordBits bits .x)
    (Pipeline.macLabels mac .x) q ∨
  LaneAsk O.1 .curveY curveElementCountY table.curveYHot (Pipeline.coordBits bits .y)
    (Pipeline.macLabels mac .y) q ∨
  q = .hash (reachHashArg O table bits mac) ∨ ReachEnc O table bits mac q ∨
  LaneAsk O.1 .pointX pointElementCountX table.pointXHot (Pipeline.coordBits bits .x)
    (Pipeline.macLabels (Programs.whitenMacOf (reachPads O table bits mac) mac) .x) q ∨
  LaneAsk O.1 .pointY pointElementCountY table.pointYHot (Pipeline.coordBits bits .y)
    (Pipeline.macLabels (Programs.whitenMacOf (reachPads O table bits mac) mac) .y) q ∨
  ∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
    q = .fixedForward (.gadget o κ position)
      (macAt (Programs.transformMacOf (reachPads O table bits mac) mac) κ position)

/-- **Every question of the reach is a `ReachAsk`.** -/
theorem onCurveM_asks (O : Oracle) (table : Public) (bits : BitInput) (mac : InputMac) :
    AsksOnly (publicAnswer O) (ReachAsk O table bits mac) (Programs.onCurveM table bits mac) := by
  unfold Programs.onCurveM
  refine AsksOnly.bind_eq (Pipeline.curveXValues O.1 table bits mac)
    ((laneAsks O _ .curveX _ _ _ _).mono fun q h => Or.inl h) (Programs.eval_evalLaneM _ _ _ _ _ _ _) ?_
  refine AsksOnly.bind_eq (Pipeline.curveYValues O.1 table bits mac)
    ((laneAsks O _ .curveY _ _ _ _).mono fun q h => Or.inr (Or.inl h))
    (Programs.eval_evalLaneM _ _ _ _ _ _ _) ?_
  refine AsksOnly.bind_eq (O.2.2 (reachHashArg O table bits mac))
    (fun entry member => ?_) (Programs.eval_askHash _ _) ?_
  · rcases List.mem_singleton.mp member with rfl
    exact Or.inr (Or.inr (Or.inl rfl))
  refine AsksOnly.bind_eq (reachPads O table bits mac)
    ((AsksOnly.of_queryOnly (evalPadsM_encOnly _ _)).mono fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
    (Programs.eval_evalPadsM _ _ _) ?_
  refine AsksOnly.bind ((laneAsks O _ .pointX _ _ _ _).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) ?_
  refine AsksOnly.bind ((laneAsks O _ .pointY _ _ _ _).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) ?_
  refine AsksOnly.bind ((AsksOnly.of_queryOnly (unlockM_asks _ _ _)).mono
    fun q h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) (AsksOnly.pure' _)

/-! ### 4. The reach on a tape, as a pure function of the tape -/

/-- The bridge value the reach asks at `u`: `t + mask · (x³ + 3 − y²)`. -/
def evalKey (coins : Coins) (input : AffineInput) : BaseField :=
  coins.bridgeKey + coins.curveMask.value * curveGap input

/-- **The reach's bridge question is `t + mask·(x³ + 3 − y²)`**: the evaluator's curve values are
the garbler's (`Pipeline.curveValues_garble`), whatever the input. -/
theorem reach_hashArg (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
      (tape.1.inputMacKey.encode (BitInput.ofAffine input)) = evalKey tape.1 input := by
  unfold reachHashArg
  rw [garble_table, Pipeline.curveValues_garble _ _ _ _ _ _ _ _ _ _ _ _ (coins_correlated tape.1)
    (delivers tape.2.1) input, BitInput.toAffineOfAffine]
  exact CurveMembership.evaluateEncoded _ _ _ _ _ input

/-- Off the curve the reach never asks the bridge key. -/
theorem evalKey_ne (coins : Coins) (input : AffineInput) (invalid : validate input = false) :
    evalKey coins input ≠ coins.bridgeKey := by
  intro same
  have zero : coins.curveMask.value * curveGap input = 0 := by
    unfold evalKey at same
    linear_combination same
  rcases mul_eq_zero.mp zero with maskZero | gapZero
  · exact coins.curveMask.nonzero maskZero
  · exact curveGap_ne_zero input invalid gapZero

/-- On the curve the reach asks the bridge key. -/
theorem evalKey_eq (coins : Coins) (input : AffineInput) (valid : validate input = true) :
    evalKey coins input = coins.bridgeKey := by
  have gap : curveGap input = 0 := by
    have onCurve := (validate_eq_true_iff input).mp valid
    unfold OnCurve at onCurve
    unfold curveGap
    linear_combination -onCurve
  unfold evalKey
  rw [gap, mul_zero, add_zero]

/-- The encoded labels of `u` on a tape. -/
def macOf (tape : Coins × Oracle) (input : AffineInput) : InputMac :=
  tape.1.inputMacKey.encode (BitInput.ofAffine input)

/-- **The reach's pads on a tape**: the EncPRF pads keyed by `hash(t_eval)`. -/
def padsOf (tape : Coins × Oracle) (input : AffineInput) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads tape.2.2.1
    ⟨(tape.2.2.2 (evalKey tape.1 input)).1, (tape.2.2.2 (evalKey tape.1 input)).2⟩
    (BitInput.ofAffine input)

theorem reachPads_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) :
    reachPads tape.2 (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
      (macOf tape input) = padsOf tape input := by
  unfold reachPads padsOf macOf
  rw [reach_hashArg]

/-- A lane's published fold joins. -/
def lanePub (table : Public) : Lane → Vector Block foldStepCount
  | .curveX => table.curveXHot
  | .curveY => table.curveYHot
  | .pointX => table.pointXHot
  | .pointY => table.pointYHot

/-- The labels the reach holds in each lane: raw for system A, whitened by its own pads for
system B. -/
def laneLabels (tape : Coins × Oracle) (input : AffineInput) : Lane → Fin PlanB.coordinateBits → Block
  | .curveX => Pipeline.macLabels (macOf tape input) .x
  | .curveY => Pipeline.macLabels (macOf tape input) .y
  | .pointX => Pipeline.macLabels (Programs.whitenMacOf (padsOf tape input) (macOf tape input)) .x
  | .pointY => Pipeline.macLabels (Programs.whitenMacOf (padsOf tape input) (macOf tape input)) .y

/-- The reach's labels at level `n` of a chunk's fold. -/
def reachFold (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (n : Nat) : Fin (2 ^ n) → Block :=
  evalFold tape.2.1 lane c (chunkValue (inputBits input lane.coord) c).toNat
    (labelAt (chunkLabels (laneLabels tape input lane) c))
    (joinAt (hotSlice (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane) c)) n

/-- The garbler's labels at level `n` of a chunk's fold. -/
def garbFold (tape : Coins × Oracle) (lane : Lane) (c : Fin chunkCount) (n : Nat) : Fin (2 ^ n) → Block :=
  (garbleFold tape.2.1 lane c ((Hidden.laneKeys tape).1 lane)
    (labelAt fun p => (chunkKey ((Hidden.laneKeys tape).2 lane) c p).1) n).1

/-- The garbler's one-hot labels of a chunk. -/
def garbChunk (tape : Coins × Oracle) (lane : Lane) (c : Fin chunkCount) : Fin (2 ^ chunkWidth c) → Block :=
  (garbleChunk tape.2.1 lane ((Hidden.laneKeys tape).1 lane) ((Hidden.laneKeys tape).2 lane) c).1

/-- One label pair of a key. -/
def keyAt (key : InputMacKey) : Coord → Fin PlanB.coordinateBits → BitAdaptor.Key
  | .x, position => key.x.get position
  | .y, position => key.y.get position

/-- The garbler's transformed label of a gadget position, at a bit. -/
def glabel (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool) : Block :=
  BitAdaptor.encode (keyAt (EncPRF.transformKey tape.2.2.1
    (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) tape.1.inputMacKey) κ position) bit

/-- The reach's transformed label of a gadget position. -/
def reachGadget (tape : Coins × Oracle) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) : Block :=
  macAt (Programs.transformMacOf (padsOf tape input) (macOf tape input)) κ position

/-! ### 5. The coincidence events -/

/-- The level-1 coincidence of a chunk: the reach's label at an inactive parent is the garbler's. -/
def Coin1 (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) : Prop :=
  ∃ r : Fin (2 ^ 1), r ≠ activeAt (chunkValue (inputBits input lane.coord) c).toNat 1 ∧
    reachFold parameter scalar tape input lane c 1 r = garbFold tape lane c 1 r

/-- **Event 1** (system B off the curve): a level-1 coincidence. -/
def Hit1 (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) : Prop :=
  Hidden.laneIsPoint lane = true ∧ validate input = false ∧ Coin1 parameter scalar tape input lane c

/-- A switch of a width-2 chunk. -/
def castSwitch (c : Fin chunkCount) (j : Fin 4) : Fin (2 ^ chunkWidth c) :=
  ⟨j.val, by rw [chunkWidth_two]; exact j.isLt⟩

/-- **Event 2**: no level-1 coincidence, and the reach's one-hot label of a switch is the
garbler's. -/
def Hit2 (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (j : Fin 4) : Prop :=
  ¬ Coin1 parameter scalar tape input lane c ∧
    reachFold parameter scalar tape input lane c (chunkWidth c) (castSwitch c j) =
      garbChunk tape lane c (castSwitch c j)

/-- **Event 3** (off the curve): the reach's gadget label of a position is the garbler's at a bit. -/
def GadgetOff (tape : Coins × Oracle) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) : Prop :=
  validate input = false ∧ reachGadget tape input κ position = glabel tape κ position bit

/-- **Event 4** (on the curve): the two transformed labels of a position collide. -/
def GadgetOn (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits) : Prop :=
  glabel tape κ position false = glabel tape κ position true

/-! ### 6. The gadget labels -/

theorem vget_ofFn {α : Type} (f : Fin coordinateBitCount → α) (position : Fin PlanB.coordinateBits) :
    (Vector.ofFn f).get position = f position :=
  Vector.get_ofFn f position

theorem encodeCoordinate_get (key : CoordinateMacKey) (bits : BitVec coordinateBitCount)
    (position : Fin coordinateBitCount) :
    (encodeCoordinate key bits).get position = BitAdaptor.encode (key.get position) (bits.getLsb position) := by
  simp only [encodeCoordinate, Vector.get_ofFn]
  rfl

/-- The garbler's gadget label of a digit with an exceptional input is the transformed label at
its exceptional bit. -/
theorem gadgetLabel_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) (o : Fin digitCount) (κ : Coord)
    (position : Fin PlanB.coordinateBits)
    (some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true) :
    Hidden.gadgetLabel scalar tape o κ position =
      glabel tape κ position (Hidden.exceptionalBit scalar tape.1.offsets o κ position) := by
  obtain ⟨phi, found⟩ := Option.isSome_iff_exists.mp some
  unfold Hidden.gadgetLabel Hidden.exceptionalBit
  rw [found]
  cases κ
  · exact encodeCoordinate_get _ _ _
  · exact encodeCoordinate_get _ _ _

/-- **On the curve the reach's gadget label is the garbler's at `u`'s bit.** -/
theorem reachGadget_onCurve (tape : Coins × Oracle) (input : AffineInput) (valid : validate input = true)
    (κ : Coord) (position : Fin PlanB.coordinateBits) :
    reachGadget tape input κ position = glabel tape κ position ((inputBits input κ).getLsb position) := by
  have key := evalKey_eq tape.1 input valid
  unfold reachGadget padsOf glabel
  rw [key]
  cases κ
  · simp only [macAt, Programs.transformMacOf, Programs.realEvalPads, keyAt, macOf,
      EncPRF.transformKey, EncPRF.transformCoordinateKey, InputMacKey.encode]
    rw [vget_ofFn, vget_ofFn]
    simp only [encodeCoordinate, Vector.getElem_ofFn]
    show encrypt (EncPRF.evenMansourPad _ _
          (EncPRF.Counter.mk .x position ((coordinateBits input.x).getLsb position)))
        (BitAdaptor.encode _ ((coordinateBits input.x).getLsb position)) =
      BitAdaptor.encode _ ((coordinateBits input.x).getLsb position)
    generalize (coordinateBits input.x).getLsb position = b
    cases b <;> rfl
  · simp only [macAt, Programs.transformMacOf, Programs.realEvalPads, keyAt, macOf,
      EncPRF.transformKey, EncPRF.transformCoordinateKey, InputMacKey.encode]
    rw [vget_ofFn, vget_ofFn]
    simp only [encodeCoordinate, Vector.getElem_ofFn]
    show encrypt (EncPRF.evenMansourPad _ _
          (EncPRF.Counter.mk .y position ((coordinateBits input.y).getLsb position)))
        (BitAdaptor.encode _ ((coordinateBits input.y).getLsb position)) =
      BitAdaptor.encode _ ((coordinateBits input.y).getLsb position)
    generalize (coordinateBits input.y).getLsb position = b
    cases b <;> rfl

/-! ### 7. A coincidence is one of the events -/

/-- A coincidence is a non-EncPRF garbler entry the reach asks and the designed rule hides. -/
theorem coincide_entry (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    ∃ e ∈ garblerTranscript scalar tape, e.IsEnc = false ∧
      e.1 ∈ (transcriptOf (publicAnswer tape.2)
        (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
          (macOf tape input))).map Sigma.fst ∧
      designedRule scalar tape input e = false := by
  by_contra none
  apply hit
  unfold visibleInstall designedInstall visibleEntries
  refine List.filter_congr fun e member => ?_
  cases enc : e.IsEnc
  · cases d : designedRule scalar tape input e
    · have notReached : e.1 ∉ (reachTranscript (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) tape).map
            Sigma.fst := by
        intro reached
        rw [reach_eq] at reached
        exact none ⟨e, member, enc, reached, d⟩
      simp [notReached]
    · have asks := designed_asks parameter scalar tape input e member d
      unfold Asks at asks
      have reached : e.1 ∈ (reachTranscript (Scheme.scheme.garble parameter scalar tape).1 input
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) tape).map
            Sigma.fst := by
        rw [reach_eq]
        exact asks
      simp [reached]
  · simp

theorem laneIsPoint_of_curve (lane : Lane) (curve : laneIsCurve lane = false) :
    Hidden.laneIsPoint lane = true := by
  cases lane <;> simp_all [laneIsCurve, Hidden.laneIsPoint]

/-- **A hidden garbler entry a lane of the reach asks is event 1 or event 2.** -/
theorem lane_events (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (count : Nat) (index : FixedIndex) (x : Block)
    (ask : LaneAsk tape.2.1 lane count (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane)
      (inputBits input lane.coord) (laneLabels tape input lane) (.fixedForward index x))
    (good : x = Hidden.garblerPointOf scalar tape index)
    (notDesigned : designedIndex scalar tape input index = false) :
    (∃ c, Hit1 parameter scalar tape input lane c) ∨
      (∃ c j, Hit2 parameter scalar tape input lane c j) := by
  obtain ⟨c, hot | scale⟩ := ask
  · obtain ⟨r, half, off, eq⟩ := hot
    simp only [PublicQuery.fixedForward.injEq] at eq
    obtain ⟨rfl, rfl⟩ := eq
    have rSmall : r.val < 2 := r.isLt
    have point := Hidden.garblerPointOf_hot scalar tape lane c 1 r.val half
      (by rw [chunkWidth_two]; omega) rSmall
    have offNat : r.val ≠ (chunkOf (inputBits input lane.coord) c).val % 2 ^ 1 := by
      intro same
      apply off
      apply Fin.ext
      show r.val = (chunkValue (inputBits input lane.coord) c).toNat % 2 ^ 1
      rw [chunkValue_toNat]
      exact same
    rw [hotIndexNat_eq lane c 1 r.val half (by decide) (by unfold chunkBits; omega)] at notDesigned
    have shown : designedIndex scalar tape input (FixedIndex.hot lane c ⟨1, by decide⟩
        ⟨r.val, by unfold chunkBits; omega⟩ half) =
        (decide (r.val ≠ (chunkOf (inputBits input lane.coord) c).val % 2 ^ 1) &&
          (laneIsCurve lane || validate input)) := rfl
    rw [shown, decide_eq_true offNat, Bool.true_and, Bool.or_eq_false_iff] at notDesigned
    obtain ⟨curve, invalid⟩ := notDesigned
    left
    refine ⟨c, laneIsPoint_of_curve lane curve, invalid, r, off, ?_⟩
    exact good.trans point
  · obtain ⟨j, element, block, off, eq⟩ := scale
    simp only [PublicQuery.fixedForward.injEq] at eq
    obtain ⟨rfl, rfl⟩ := eq
    have point := Hidden.garblerPointOf_scale scalar tape lane c j element block
    have jSmall : j.val < 4 := by
      have four : 2 ^ chunkWidth c = 4 := by rw [chunkWidth_two]; rfl
      calc j.val < 2 ^ chunkWidth c := j.isLt
        _ = 4 := four
    have offNat : j.val ≠ (chunkOf (inputBits input lane.coord) c).val := fun same => off (Fin.ext same)
    have idx : scaleIndexOf lane c j.val element block =
        .scale lane c ⟨j.val, by unfold chunkBits; omega⟩
          ⟨element.val % elementCountX, Nat.mod_lt _ elementCountX_pos⟩ block := by
      unfold scaleIndexOf
      exact scaleIndexNat_eq _ _ _ _ _ (by unfold chunkBits; omega)
    rw [idx] at notDesigned
    have shown : designedIndex scalar tape input (FixedIndex.scale lane c ⟨j.val, by unfold chunkBits; omega⟩
          ⟨element.val % elementCountX, Nat.mod_lt _ elementCountX_pos⟩ block) =
        (decide (j.val ≠ (chunkOf (inputBits input lane.coord) c).val) &&
          (laneIsCurve lane || validate input)) := rfl
    rw [shown, decide_eq_true offNat, Bool.true_and, Bool.or_eq_false_iff] at notDesigned
    obtain ⟨curve, invalid⟩ := notDesigned
    by_cases coin : Coin1 parameter scalar tape input lane c
    · left
      exact ⟨c, laneIsPoint_of_curve lane curve, invalid, coin⟩
    · right
      refine ⟨c, ⟨j.val, jSmall⟩, coin, ?_⟩
      have cast : castSwitch c ⟨j.val, jSmall⟩ = j := Fin.ext rfl
      rw [cast]
      exact good.trans point

/-- **Every coincidence is one of the four events.** -/
theorem coincide_events (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (hit : Coincide parameter scalar tape input) :
    (∃ lane c, Hit1 parameter scalar tape input lane c) ∨
    (∃ lane c j, Hit2 parameter scalar tape input lane c j) ∨
    (∃ κ position bit, GadgetOff tape input κ position bit) ∨
    (∃ κ position, GadgetOn tape κ position) := by
  obtain ⟨e, member, notEnc, reached, notDesigned⟩ := coincide_entry parameter scalar tape input hit
  obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp reached
  have ask := onCurveM_asks tape.2 _ _ _ entry entryMember
  rw [entryEq] at ask
  have good := garblerTranscript_good scalar tape e member
  have shape := garblerTranscript_ask scalar tape e member
  have pads := reachPads_eq parameter scalar tape input
  unfold ReachAsk at ask
  rw [pads] at ask
  obtain ⟨request, answer⟩ := e
  have laneCase : ∀ (lane : Lane) (count : Nat) (index : FixedIndex) (x : Block),
      LaneAsk tape.2.1 lane count (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane)
        (inputBits input lane.coord) (laneLabels tape input lane) (.fixedForward index x) →
      x = Hidden.garblerPointOf scalar tape index → designedIndex scalar tape input index = false →
      (∃ lane c, Hit1 parameter scalar tape input lane c) ∨
      (∃ lane c j, Hit2 parameter scalar tape input lane c j) ∨
      (∃ κ position bit, GadgetOff tape input κ position bit) ∨
      (∃ κ position, GadgetOn tape κ position) := by
    intro lane count index x laneAsk isGood hidden
    rcases lane_events parameter scalar tape input lane count index x laneAsk isGood hidden with
      ⟨c, one⟩ | ⟨c, j, two⟩
    · exact Or.inl ⟨lane, c, one⟩
    · exact Or.inr (Or.inl ⟨lane, c, j, two⟩)
  cases request with
  | fixedForward index x =>
      have isGood : x = Hidden.garblerPointOf scalar tape index := good
      have hidden : designedIndex scalar tape input index = false := notDesigned
      rcases ask with a | a | a | a | a | a | a
      · exact laneCase .curveX _ index x a isGood hidden
      · exact laneCase .curveY _ index x a isGood hidden
      · cases a
      · obtain ⟨_, _, _, eq⟩ := a
        cases eq
      · exact laneCase .pointX _ index x a isGood hidden
      · exact laneCase .pointY _ index x a isGood hidden
      · obtain ⟨o, κ, position, eq⟩ := a
        simp only [PublicQuery.fixedForward.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        have some : (digitEndomorphismBase (Hidden.digitKey scalar tape.1.offsets o).digit).isSome = true :=
          shape
        have label := gadgetLabel_eq scalar tape o κ position some
        have isGood' : reachGadget tape input κ position =
            glabel tape κ position (Hidden.exceptionalBit scalar tape.1.offsets o κ position) :=
          isGood.trans label
        have shown : designedIndex scalar tape input (.gadget o κ position) =
            (validate input && decide ((inputBits input κ).getLsb position =
              Hidden.exceptionalBit scalar tape.1.offsets o κ position)) := rfl
        rw [shown] at hidden
        cases valid : validate input
        · exact Or.inr (Or.inr (Or.inl ⟨κ, position, _, valid, isGood'⟩))
        · rw [valid, Bool.true_and, decide_eq_false_iff_not] at hidden
          have onCurve := reachGadget_onCurve tape input valid κ position
          rw [onCurve] at isGood'
          refine Or.inr (Or.inr (Or.inr ⟨κ, position, ?_⟩))
          unfold GadgetOn
          revert isGood' hidden
          cases (inputBits input κ).getLsb position <;>
            cases Hidden.exceptionalBit scalar tape.1.offsets o κ position <;> simp_all
  | fixedInverse index y => exact good.elim
  | encForward index z => simp [Entry.IsEnc] at notEnc
  | encInverse index z => exact good.elim
  | hash v =>
      have isGood : v = tape.1.bridgeKey := good
      have invalid : validate input = false := notDesigned
      rcases ask with a | a | a | a | a | a | a
      · obtain ⟨c, ⟨r, half, off, eq⟩ | ⟨j, element, block, off, eq⟩⟩ := a <;> cases eq
      · obtain ⟨c, ⟨r, half, off, eq⟩ | ⟨j, element, block, off, eq⟩⟩ := a <;> cases eq
      · simp only [PublicQuery.hash.injEq] at a
        have key := reach_hashArg parameter scalar tape input
        exact absurd (isGood.symm.trans (a.trans key)).symm (evalKey_ne tape.1 input invalid)
      · obtain ⟨_, _, _, eq⟩ := a
        cases eq
      · obtain ⟨c, ⟨r, half, off, eq⟩ | ⟨j, element, block, off, eq⟩⟩ := a <;> cases eq
      · obtain ⟨c, ⟨r, half, off, eq⟩ | ⟨j, element, block, off, eq⟩⟩ := a <;> cases eq
      · obtain ⟨o, κ, position, eq⟩ := a
        cases eq

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess
