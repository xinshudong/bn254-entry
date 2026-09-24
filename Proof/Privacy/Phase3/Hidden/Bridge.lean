/-
**Phase 3, P1f — stage 1's bridge key, on the (rest, masks) coordinates.**

The stage-1 view factors through `Φ tape = (restOf tape, maskOf tape)`: the published value is
`publishedOf` of it (`published_eq`: lane tables from the fold gates and the masks, gadget from the
gadget permutations) and the EncPRF entries are the pads' transcript, a function of the rest
(`encEntries_eq`). Under the swapped tape `Φ` is uniform × uniform (`swapped_restMasks`, from
`MaskSwap.swappedTape_garblerMasks`).
-/

import Proof.Privacy.Phase3.Hidden.StageOne
import Proof.Privacy.Phase3.Hidden.QueryOnly

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Hidden
open scoped ENNReal

noncomputable section

/-- The rest of a tape: coins, EncPRF, hash, the non-site permutations. -/
def restOf (tape : Coins × Oracle) : RestTape TapeRest :=
  ((tape.1, tape.2.2.1, tape.2.2.2), fun index => tape.2.1.permutation index.1)

/-- The oracle a rest determines, with trivial site permutations. -/
def restOracle (rest : RestTape TapeRest) : Oracle :=
  (oracleOf rest.2 fun _ => Equiv.refl Block, rest.1.2.1, rest.1.2.2)

section Instances

variable [FieldCertificate] [GroupCertificate]

/-- **Under the swapped tape, the rest and the masks are uniform and independent.** -/
theorem swapped_restMasks :
    swappedChallengeTape.map (fun tape => (restOf tape, maskOf tape)) =
      productPMF (restLaw restUniform) (PMF.uniformOfFintype (MaskSite → BaseField)) := by
  unfold swappedChallengeTape
  rw [PMF.map_comp]
  exact swappedTape_garblerMasks restUniform garblerKeys

/-! ### The EncPRF entries are the pads' transcript -/

theorem isEnc_of_fixedForward (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (fixed : IsFixedForward entry.1) : entry.IsEnc = false := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> first | rfl | exact fixed.elim

theorem isEnc_of_encForward (entry : Entry FixedIndex EncPRF.PermutationIndex)
    (enc : IsEncForward entry.1) : entry.IsEnc = true := by
  obtain ⟨request, answer⟩ := entry
  cases request <;> first | rfl | exact enc.elim

/-- The pads' transcript on the rest's oracle. -/
def encOf (rest : RestTape TapeRest) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  Hidden.transcriptOf (publicAnswer (restOracle rest))
    (Programs.padsM ⟨(rest.1.2.2 rest.1.1.bridgeKey).1, (rest.1.2.2 rest.1.1.bridgeKey).2⟩)

theorem filter_all {α : Type} (P : α → Bool) (l : List α) (all : ∀ a ∈ l, P a = true) :
    l.filter P = l := List.filter_eq_self.mpr all

theorem filter_none {α : Type} (P : α → Bool) (l : List α) (none' : ∀ a ∈ l, P a = false) :
    l.filter P = [] := List.filter_eq_nil_iff.mpr fun a member => by simp [none' a member]

/-- The EncPRF part of a hash-then-pads-then-fixed-key program is the pads' transcript. -/
theorem enc_split {β : Type} (t : BaseField) (O : Oracle)
    (R : Block × Block → Programs.Pads → FreeQuery Programs.Spec β)
    (only : ∀ h p, QueryOnly IsFixedForward (R h p)) :
    (Hidden.transcriptOf (publicAnswer O) (Programs.askHash t >>= fun h =>
        Programs.padsM ⟨h.1, h.2⟩ >>= fun p => R h p)).filter Entry.IsEnc =
      Hidden.transcriptOf (publicAnswer O) (Programs.padsM ⟨(O.2.2 t).1, (O.2.2 t).2⟩) := by
  rw [transcriptOf_bind, transcriptOf_bind]
  have hashHead : Hidden.transcriptOf (publicAnswer O) (Programs.askHash t) =
      [⟨.hash t, publicAnswer O (.hash t)⟩] := rfl
  have keys : FreeQuery.eval (publicAnswer O) (Programs.askHash t) = O.2.2 t := rfl
  rw [hashHead, keys, List.filter_append, List.filter_append,
    filter_none _ [_] (fun a member => by rcases List.mem_singleton.mp member with rfl; rfl),
    filter_all _ _ fun a member => isEnc_of_encForward a ((padsM_encOnly _).mem _ a member),
    filter_none _ _ fun a member => isEnc_of_fixedForward a ((only _ _).mem _ a member),
    List.nil_append, List.append_nil]

/-- **The EncPRF entries are a function of the rest.** -/
theorem encEntries_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    encEntries scalar tape = encOf (restOf tape) := by
  unfold encEntries
  rw [garblerTranscript_eq]
  unfold Programs.garbleM
  refine (enc_split tape.1.bridgeKey tape.2 _ fun _ _ => ?_).trans ?_
  · exact QueryOnly.bind (laneM_fixedOnly _ _ _ _) fun _ => QueryOnly.bind (laneM_fixedOnly _ _ _ _)
      fun _ => QueryOnly.bind (laneM_fixedOnly _ _ _ _) fun _ => QueryOnly.bind (laneM_fixedOnly _ _ _ _)
        fun _ => QueryOnly.bind (gadgetM_fixedOnly _ _ _) fun _ => QueryOnly.pure' _
  · have keys : ((restOf tape).1.2.2 (restOf tape).1.1.bridgeKey) = tape.2.2.2 tape.1.bridgeKey := rfl
    unfold encOf
    rw [keys]
    have same : ∀ request : PublicQuery FixedIndex EncPRF.PermutationIndex, IsEncForward request →
        publicAnswer (restOracle (restOf tape)) request = publicAnswer tape.2 request := by
      intro request enc
      cases request with
      | encForward index input => rfl
      | _ => exact enc.elim
    have agreed := (padsM_encOnly ⟨(tape.2.2.2 tape.1.bridgeKey).1, (tape.2.2.2 tape.1.bridgeKey).2⟩).agree
      tape.2 (restOracle (restOf tape)) same
    exact agreed.1.symm

/-! ### The published value is a function of the rest and the masks -/

/-- One lane's tables from the rest and the masks. -/
def tablesOf (rest : RestTape TapeRest) (masks : MaskSite → BaseField) (ℓ : Lane) :
    Programs.LaneTables (laneCount ℓ) where
  hot c := garbleChunk (restOracle rest).1 ℓ ((garblerKeys rest.1).1 ℓ) ((garblerKeys rest.1).2 ℓ) c
  masks c switch element := masks ⟨ℓ, c, switch, element⟩

/-- **The published value, from the rest and the masks.** -/
def publishedOf (scalar : NonZeroScalar) (z : RestTape TapeRest × (MaskSite → BaseField)) : Public :=
  Programs.assemble (FieldMacToECMac.outputKeys construction scalar.value z.1.1.1.offsets)
    z.1.1.1.pointRandomness z.1.1.1.bridgeKey z.1.1.1.curveMask z.1.1.1.curveR1 z.1.1.1.curveR2
    (tablesOf z.1 z.2 .curveX) (tablesOf z.1 z.2 .curveY) (tablesOf z.1 z.2 .pointX)
    (tablesOf z.1 z.2 .pointY)
    (Vector.ofFn fun output => FieldMacToECMac.garbleEntry
      (Pipeline.gadgetPermutations (restOracle z.1).1) output
      ((FieldMacToECMac.outputKeys construction scalar.value z.1.1.1.offsets).get output)
      (EncPRF.transformKey z.1.1.2.1 (EncPRF.whiteningKeys z.1.1.2.2 z.1.1.1.bridgeKey)
        z.1.1.1.inputMacKey) (z.1.1.1.exceptionPad.get output))

theorem gadget_not_site (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    FixedIndex.gadget o κ position ∉ Set.range siteIndex := by
  rintro ⟨site, same⟩
  simp only [siteIndex, scaleIndexOf, scaleIndexNat] at same
  cases same

theorem restOracle_hot (tape : Coins × Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (fold : Fin chunkBits) (entry : Fin (2 ^ chunkBits)) (half : Bool) :
    tape.2.1.permutation (.hot lane chunk fold entry half) =
      (restOracle (restOf tape)).1.permutation (.hot lane chunk fold entry half) :=
  (oracleOf_other (restOf tape).2 (fun _ => Equiv.refl Block) ⟨_, hot_not_site lane chunk fold entry half⟩).symm

theorem laneTables_eq (tape : Coins × Oracle) (lane : Lane) :
    Programs.laneTables tape.2.1 (laneCount lane) lane ((garblerKeys (restOf tape).1).1 lane)
        ((garblerKeys (restOf tape).1).2 lane) = tablesOf (restOf tape) (maskOf tape) lane := by
  unfold Programs.laneTables tablesOf
  congr 1
  funext c
  exact garbleChunk_congr (fun lane chunk fold entry half => restOracle_hot tape lane chunk fold entry half)
    lane _ _ c

/-- **The published value is `publishedOf` of the rest and the masks.** -/
theorem published_eq (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar tape).1 = publishedOf scalar (restOf tape, maskOf tape) := by
  obtain ⟨coins, oracle⟩ := tape
  rw [← garble_eval parameter scalar coins oracle, Programs.eval_garbleM, ← Programs.assemble_real]
  unfold publishedOf
  have cx := laneTables_eq (coins, oracle) .curveX
  have cy := laneTables_eq (coins, oracle) .curveY
  have px := laneTables_eq (coins, oracle) .pointX
  have py := laneTables_eq (coins, oracle) .pointY
  have gadget : Pipeline.gadgetPermutations oracle.1 =
      Pipeline.gadgetPermutations (restOracle (restOf (coins, oracle))).1 := by
    funext o coordinate position
    show oracle.1.permutation (.gadget o (Pipeline.gadgetCoord coordinate) position) = _
    exact (oracleOf_other (restOf (coins, oracle)).2 (fun _ => Equiv.refl Block)
      ⟨_, gadget_not_site o (Pipeline.gadgetCoord coordinate) position⟩).symm
  simp only [] at cx cy px py
  rw [← cx, ← cy, ← px, ← py, ← gadget]
  rfl

end Instances

end

end Kriterion.ArgoMAC.Security.Phase3
