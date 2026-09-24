/-
**Phase 3, P1h — the shape of the garbler's questions.**

`GarblerAsk scalar coins`: every question the garbler asks on coins `coins` is the bridge hash, an
EncPRF forward query, or a fixed-key forward query at

* a fold gate of step `1` and entry `0` or `1` (step `0` is free, width-2 chunks have one paid
  step),
* a scale gate whose element slot is one of its lane's (`laneCount`),
* a gadget position of a digit with an exceptional input (`digitEndomorphismBase ≠ none`).

`garblerTranscript_ask`: every garbler transcript entry has this shape.
-/

import Proof.Privacy.Phase3.Hidden.Designed

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden

noncomputable section

namespace Hidden.QueryOnly

variable {S S' : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} {α : Type}

/-- A weaker predicate. -/
theorem imp {P : FreeQuery Programs.Spec α} (only : QueryOnly S P) (weaker : ∀ q, S q → S' q) :
    QueryOnly S' P := by
  induction only with
  | pure value => exact .pure value
  | query request next holds _ ih => exact .query request next (weaker _ holds) ih

end Hidden.QueryOnly

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **The shape of a garbler question.** -/
def GarblerAsk (scalar : NonZeroScalar) (coins : Coins) :
    PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.hot _ _ fold entry _) _ => fold.val = 1 ∧ entry.val < 2
  | .fixedForward (.scale lane _ _ element _) _ => element.val < laneCount lane
  | .fixedForward (.gadget o _ _) _ =>
      (digitEndomorphismBase (digitKey scalar coins.offsets o).digit).isSome = true
  | .encForward _ _ => True
  | .hash _ => True
  | _ => False

theorem garblerAsk_hot (scalar : NonZeroScalar) (coins : Coins) (lane : Lane) (chunk : Fin chunkCount)
    (entry : Nat) (half : Bool) (x : Block) (small : entry < 2) :
    GarblerAsk scalar coins (.fixedForward (hotIndexNat lane chunk 1 entry half) x) := by
  have fold : (1 : Nat) < chunkBits := by unfold chunkBits; omega
  have entryLt : entry < 2 ^ chunkBits := by unfold chunkBits; omega
  rw [hotIndexNat_eq lane chunk 1 entry half fold entryLt]
  exact ⟨rfl, small⟩

theorem garbleFoldM_ask (scalar : NonZeroScalar) (coins : Coins) (lane : Lane) (chunk : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) : ∀ steps, steps ≤ 2 →
    QueryOnly (GarblerAsk scalar coins) (Programs.garbleFoldM lane chunk delta zeroLabel steps)
  | 0, _ => QueryOnly.pure' _
  | steps + 1, small => by
      refine QueryOnly.bind (garbleFoldM_ask scalar coins lane chunk delta zeroLabel steps (by omega))
        fun previous => QueryOnly.bind ?_ fun _ => QueryOnly.pure' _
      unfold Programs.garbleStepM
      split
      · exact QueryOnly.pure' _
      · rename_i nonzero
        obtain rfl : steps = 1 := by omega
        refine QueryOnly.bind (QueryOnly.vector _ fun entry => ?_) fun _ => QueryOnly.pure' _
        have entrySmall : entry.val < 2 := entry.isLt
        exact QueryOnly.bind (QueryOnly.bind (QueryOnly.ask _
            (garblerAsk_hot scalar coins lane chunk entry.val false _ entrySmall)) fun _ => QueryOnly.pure' _)
          fun _ => QueryOnly.bind (QueryOnly.bind (QueryOnly.ask _
            (garblerAsk_hot scalar coins lane chunk entry.val true _ entrySmall)) fun _ => QueryOnly.pure' _)
            fun _ => QueryOnly.pure' _

theorem garblerAsk_scale (scalar : NonZeroScalar) (coins : Coins) {count : Nat} (lane : Lane)
    (bound : count ≤ laneCount lane) (chunk : Fin chunkCount) (switch : Nat) (element : Fin count)
    (block : Fin 3) (x : Block) :
    GarblerAsk scalar coins (.fixedForward (scaleIndexOf lane chunk switch element block) x) := by
  have inRange : element.val < elementCountX := lt_of_lt_of_le element.isLt (bound.trans (laneCount_le lane))
  show (element.val % elementCountX) < laneCount lane
  rw [Nat.mod_eq_of_lt inRange]
  exact lt_of_lt_of_le element.isLt bound

theorem hashM_ask {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop} (index : FixedIndex)
    (label : Block) (holds : S (.fixedForward index label)) : QueryOnly S (Programs.hashM index label) :=
  QueryOnly.bind (QueryOnly.ask _ holds) fun _ => QueryOnly.pure' _

theorem laneM_ask (scalar : NonZeroScalar) (coins : Coins) (count : Nat) (lane : Lane)
    (bound : count ≤ laneCount lane) (delta : Block) (bitKey : Fin PlanB.coordinateBits → Block × Block) :
    QueryOnly (GarblerAsk scalar coins) (Programs.laneM count lane delta bitKey) := by
  refine QueryOnly.bind (QueryOnly.pi _ fun c => ?_) fun _ => QueryOnly.pure' _
  refine QueryOnly.bind (QueryOnly.bind (garbleFoldM_ask scalar coins _ _ _ _ _
    (by rw [chunkWidth_two])) fun _ => QueryOnly.pure' _) fun _ => ?_
  refine QueryOnly.bind (QueryOnly.vector _ fun switch => ?_) fun _ => QueryOnly.pure' _
  refine QueryOnly.bind (QueryOnly.vector _ fun element => ?_) fun _ => QueryOnly.pure' _
  exact QueryOnly.bind (hashM_ask _ _ (garblerAsk_scale scalar coins lane bound _ _ _ _ _)) fun _ =>
    QueryOnly.bind (hashM_ask _ _ (garblerAsk_scale scalar coins lane bound _ _ _ _ _)) fun _ =>
      QueryOnly.bind (hashM_ask _ _ (garblerAsk_scale scalar coins lane bound _ _ _ _ _)) fun _ =>
        QueryOnly.pure' _

theorem gadgetM_ask (scalar : NonZeroScalar) (coins : Coins) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) :
    QueryOnly (GarblerAsk scalar coins)
      (Programs.gadgetM (FieldMacToECMac.outputKeys construction scalar.value coins.offsets) inputKey pads) := by
  refine QueryOnly.vector _ fun output => ?_
  unfold Programs.garbleEntryM
  split
  · exact QueryOnly.pure' _
  · rename_i phi found
    have digit : (digitEndomorphismBase (digitKey scalar coins.offsets output).digit).isSome = true := by
      show (digitEndomorphismBase ((FieldMacToECMac.outputKeys construction scalar.value
        coins.offsets).get output).digit).isSome = true
      rw [found]
      rfl
    have digest : ∀ coordinate mac, QueryOnly (GarblerAsk scalar coins)
        (Programs.gadgetDigestM output coordinate mac) := fun coordinate mac =>
      QueryOnly.bind (QueryOnly.vector _ fun index => hashM_ask _ _ digit) fun _ => QueryOnly.pure' _
    exact QueryOnly.bind (QueryOnly.bind (digest _ _) fun _ => QueryOnly.bind (digest _ _) fun _ =>
      QueryOnly.pure' _) fun _ => QueryOnly.pure' _

/-- **The garbler asks only questions of the garbler's shape.** -/
theorem garbleM_ask (scalar : NonZeroScalar) (coins : Coins) :
    QueryOnly (GarblerAsk scalar coins) (Programs.garbleM scalar coins) := by
  unfold Programs.garbleM
  refine QueryOnly.bind (QueryOnly.ask _ trivial) fun hashed => ?_
  refine QueryOnly.bind ((padsM_encOnly _).imp fun q enc => ?_) fun pads => ?_
  · cases q with
    | encForward _ _ => trivial
    | _ => exact enc.elim
  refine QueryOnly.bind (laneM_ask scalar coins _ .curveX le_rfl _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins _ .curveY le_rfl _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins _ .pointX le_rfl _ _) fun _ => ?_
  refine QueryOnly.bind (laneM_ask scalar coins _ .pointY le_rfl _ _) fun _ => ?_
  exact QueryOnly.bind (gadgetM_ask scalar coins _ _) fun _ => QueryOnly.pure' _

/-- **Every garbler entry has the garbler's shape.** -/
theorem garblerTranscript_ask (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ garblerTranscript scalar tape, GarblerAsk scalar tape.1 entry.1 := by
  rw [garblerTranscript_eq]
  exact (garbleM_ask scalar tape.1).mem _

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
