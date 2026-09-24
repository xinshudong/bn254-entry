/-
**Phase 3, P1d — `G1U`'s stage 1, with the garbler's EncPRF pairs planted after it.**

`G1U` (`hiddenDeletedHybrid`) runs the adversary's first stage on the lazy oracle holding the
garbler's EncPRF entries. `g1uLater` runs it on the empty oracle, stops (`none`) at the first query
that touches one of those entries (`runFlag`, `EncTouch`), and plants them only at the input choice,
before the visible entries.

**`g1u_below_later`**: `Below G1U g1uLater` — for each bit, `g1uLater`'s untouched mass is at most
`G1U`'s (`plant_ge`, `encRel_base`, `encRel_sameLookups`, `plantAll_congr`, `run_map_fst_congr`).
The touch mass, `g1uLater none`, is the stage-1 EncPRF charge of `publicFirst`: at most
`4/2^128` per stage-1 EncPRF query once the planted pairs are independent of the stage-1 view.
-/

import Proof.Privacy.Phase3.PublicFirst.Install

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary)
open scoped ENNReal

noncomputable section

/-- The garbler's EncPRF entries on a tape. -/
def encEntries [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (garblerTranscript scalar tape).filter Entry.IsEnc

theorem encEntries_encOnly [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) : ∀ entry ∈ encEntries scalar tape, (encPair entry).isSome := by
  intro entry member
  have isEnc := (List.mem_filter.mp member).2
  obtain ⟨request, answer⟩ := entry
  cases request <;> simp_all [Entry.IsEnc, encPair]

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`G1U` with the EncPRF entries planted at the input choice**, flagged at a stage-1 touch. -/
def g1uLater (adversary : PlanBAdversary Unit) (parameter : ℕ) (scalar : NonZeroScalar) :
    PMF (Option Bool) :=
  swappedChallengeTape.bind fun tape =>
    let garbled := Scheme.scheme.garble parameter scalar tape
    flagBind (runFlag (plantAll (encEntries scalar tape) LazyOracle.empty)
        (adversary.chooseInput parameter garbled.1 ()) LazyOracle.empty)
      fun selected state =>
        let labels := Scheme.scheme.encode garbled.2 selected.1
        (LazyOracle.run (adversary.decide parameter garbled.1 labels () selected.2)
          (installAll (visibleEntries scalar tape garbled.1 selected.1 labels)
            (plantAll (encEntries scalar tape) state))).map Prod.fst

/-- **Step 2 at `G1U`: planting the EncPRF entries later loses only the touch mass.** -/
theorem g1u_below_later (adversary : PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Below (hiddenDeletedHybrid adversary parameter scalar) (g1uLater adversary parameter scalar) := by
  intro b
  unfold hiddenDeletedHybrid g1uLater
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun tape => mul_le_mul' le_rfl ?_
  let garbled := Scheme.scheme.garble parameter scalar tape
  let KF : AffineInput × adversary.State → LazyOracle.State FixedIndex EncPRF.PermutationIndex →
      PMF Bool := fun selected state =>
    (LazyOracle.run (adversary.decide parameter garbled.1
        (Scheme.scheme.encode garbled.2 selected.1) () selected.2)
      (plantAll (visibleEntries scalar tape garbled.1 selected.1
        (Scheme.scheme.encode garbled.2 selected.1)) state)).map Prod.fst
  have agree : ∀ selected sF sL,
      EncRel (plantAll (encEntries scalar tape) LazyOracle.empty) sF sL →
        KF selected (plantAll (encEntries scalar tape) sL) = KF selected sF := by
    intro selected sF sL related
    have same := encRel_sameLookups (encEntries scalar tape) (encEntries_encOnly scalar tape) related
    exact run_map_fst_congr _ (plantAll_congr _ same.symm)
  have key := plant_ge (plantAll (encEntries scalar tape) LazyOracle.empty) KF
    (fun selected state => KF selected (plantAll (encEntries scalar tape) state)) agree
    (adversary.chooseInput parameter garbled.1 ()) _ _
    (encRel_base (encEntries scalar tape) (encEntries_encOnly scalar tape)) b
  exact key

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
