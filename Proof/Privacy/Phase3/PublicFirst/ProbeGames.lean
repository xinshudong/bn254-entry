/-
**Phase 3, P1g — the probe in `G1U`, as a game: `true` with mass `R/p`.**

`G1U`'s stage-2 state stores every question of the probe with the tape's answer
(`hidden_stored`: each is a visible garbler entry, installed on a state consistent with the tape),
so the probe runs deterministically (`runLazyQ_of_stored`) and returns the low-mask test of the
garbler's own mask at the site `(curveX, 0, 1, 0)` (`probe_value`). Under `G0U`'s swapped tape that
mask is uniform on `F_p` (`MaskSwap.swappedTape_garblerMasks`), so `G1U` outputs `true` with mass
`R/p` (`hiddenDeleted_probe_true`).
-/

import Proof.Privacy.Phase3.PublicFirst.ProbeG1U

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

/-! ### 1. A uniform function, read at one point -/

/-- **One coordinate of a uniform function is uniform.** -/
theorem uniform_eval {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    [inst : Fintype (ι → β)] (i : ι) :
    (@PMF.uniformOfFintype (ι → β) inst _).map (fun f => f i) = PMF.uniformOfFintype β := by
  classical
  have split : (fun f : ι → β => f i) = Prod.fst ∘ (Equiv.funSplitAt i β) := by
    funext f
    rfl
  rw [split, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv,
    Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_fst]

/-- The second factor of a product law, pushed forward. -/
theorem productPMF_map_snd {A C D : Type} (first : PMF A) (second : PMF C) (h : A × C → D)
    (g : C → D) (hg : ∀ x, h x = g x.2) :
    (productPMF first second).map h = second.map g := by
  unfold productPMF
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  have inner : ∀ a : A, h ∘ Prod.mk a = g := fun a => funext fun c => hg (a, c)
  simp only [inner]
  exact PMF.bind_const _ _

/-! ### 2. The probe in `G1U` -/

/-- The swapped site the probe reads: `(curveX, chunk 0, switch 1, element 0)`. -/
def probeSite : MaskSite := ⟨.curveX, chunkZero, probeSwitch, (probeElement : Fin (laneCount .curveX))⟩

section Hidden

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- `G1U`'s stage-1 state: the garbler's EncPRF entries (as `plantAll`). -/
abbrev hiddenStageOne (scalar : NonZeroScalar) (tape : Coins × Oracle) : LState :=
  plantAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty

theorem installAll_eq' (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (state : LState) : installAll entries state = plantAll entries state := rfl

theorem hiddenStageOne_consistent (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    FixedConsistent tape.2.1 (hiddenStageOne scalar tape) :=
  (plantAll_stored tape.2 _ LazyOracle.empty (fixedConsistent_empty _) fun _ member =>
    transcript_answer _ _ (List.mem_filter.mp member).1).1

/-- **Every question of the probe is stored in `G1U`'s stage-2 state, with the tape's answer.** -/
theorem hidden_stored (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ transcript (publicAnswer tape.2)
        (probeM (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput)),
      LazyOracle.query entry.1
          (plantAll (visibleEntries scalar tape (Scheme.scheme.garble parameter scalar tape).1
            offInput (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput))
            (hiddenStageOne scalar tape))
        = PMF.pure (entry.2, plantAll (visibleEntries scalar tape
            (Scheme.scheme.garble parameter scalar tape).1 offInput
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput))
            (hiddenStageOne scalar tape)) := by
  intro entry member
  have stored := (plantAll_stored tape.2 (visibleEntries scalar tape
    (Scheme.scheme.garble parameter scalar tape).1 offInput
    (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput))
    (hiddenStageOne scalar tape) (hiddenStageOne_consistent scalar tape) fun _ member =>
      transcript_answer _ _ (List.mem_filter.mp member).1).2
  unfold probeM at member
  rw [transcript_bind] at member
  rcases List.mem_append.mp member with fold | mask
  · obtain ⟨half, rfl⟩ := probeFold_entries _ _ _ fold
    refine query_fixedForward_stored _ _ _ _ (stored _ _ (Or.inr ?_))
    refine mem_visible ?_ (reach_fold_mem _ _ tape fold) rfl
    refine garbler_of_curveX scalar tape ?_
    have garbler := chunkTables_fold_mem tape.2 curveElementCountX .curveX (tape.1.inputDelta .x)
      (Pipeline.bitKeyOf tape.1.inputMacKey .x)
      ⟨inactiveEntry (probeValue (Scheme.scheme.encode
        (Scheme.scheme.garble parameter scalar tape).2 offInput)), by
        unfold inactiveEntry
        have := Nat.mod_lt (probeValue (Scheme.scheme.encode
          (Scheme.scheme.garble parameter scalar tape).2 offInput)) two_pos
        omega⟩ half
    rw [← probe_level_one parameter scalar tape] at garbler
    exact garbler
  · rw [transcript_probeMaskM] at mask
    obtain ⟨block, rfl⟩ := elementMaskM_entries _ _ mask
    refine query_fixedForward_stored _ _ _ _ (stored _ _ (Or.inr ?_))
    refine mem_visible ?_ (reach_scale_mem _ _ tape mask) rfl
    refine garbler_of_curveX scalar tape (chunkTables_scale_mem tape.2 _ _ ?_)
    rw [← probe_hot parameter scalar tape]
    exact mask

/-- **The probe's answer in `G1U`**: the low-mask test of the garbler's mask at the site. -/
theorem probe_value (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    FreeQuery.eval (publicAnswer tape.2)
        (probeM (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 offInput))
      = lowMask (garblerMask tape.2.1 (garblerKeys (tape.1, tape.2.2)).1
          (garblerKeys (tape.1, tape.2.2)).2 probeSite) := by
  unfold probeM
  rw [FreeQuery.eval_bind, probe_hot]
  unfold probeMaskM
  simp only [FreeQuery.eval_bind, Programs.eval_hashM, FreeQuery.eval_pure]
  rfl

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- `G1U`'s run of the probe on one tape. -/
theorem hidden_tape (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    (LazyOracle.run (probeAdversary.chooseInput parameter
        (Scheme.scheme.garble parameter scalar tape).1 ())
        (installAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty)).bind
      (fun selected => (LazyOracle.run (probeAdversary.decide parameter
          (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 selected.1.1) ()
          selected.1.2)
        (installAll (visibleEntries scalar tape (Scheme.scheme.garble parameter scalar tape).1
          selected.1.1 (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2
            selected.1.1)) selected.2)).map Prod.fst)
      = PMF.pure (lowMask (garblerMask tape.2.1 (garblerKeys (tape.1, tape.2.2)).1
          (garblerKeys (tape.1, tape.2.2)).2 probeSite)) := by
  rw [installAll_eq']
  have first : LazyOracle.run (probeAdversary.chooseInput parameter
      (Scheme.scheme.garble parameter scalar tape).1 ()) (hiddenStageOne scalar tape)
      = PMF.pure ((offInput, ()), hiddenStageOne scalar tape) :=
    PMF.pure_map _ _
  rw [first]
  erw [PMF.pure_bind]
  have second : ∀ (table : Public) (labels : LamportSignature),
      probeAdversary.decide parameter table labels () ()
        = freeOracle (probeM table labels) 5 (probeM_bounded table labels) := fun _ _ => rfl
  simp only [second, installAll_eq']
  erw [run_freeOracle]
  rw [runLazyQ_of_stored _ _ _ (hidden_stored parameter scalar tape), PMF.pure_map, probe_value]

variable [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]

/-- **`G1U` against the probe**: the probe's answer on the swapped tape. -/
theorem hiddenDeleted_probe_eq (parameter : ℕ) (scalar : NonZeroScalar) :
    hiddenDeletedHybrid probeAdversary parameter scalar =
      swappedChallengeTape.map fun tape => lowMask (garblerMask tape.2.1
        (garblerKeys (tape.1, tape.2.2)).1 (garblerKeys (tape.1, tape.2.2)).2 probeSite) := by
  unfold hiddenDeletedHybrid
  rw [← PMF.bind_pure_comp]
  congr 1
  funext tape
  exact hidden_tape parameter scalar tape

/-- **`G1U` outputs `true` with mass `R/p`.** -/
theorem hiddenDeleted_probe_true (parameter : ℕ) (scalar : NonZeroScalar) :
    hiddenDeletedHybrid probeAdversary parameter scalar true
      = (residue : ℝ≥0∞) / baseFieldModulus := by
  rw [hiddenDeleted_probe_eq, swappedChallengeTape, PMF.map_comp]
  have factor : ((fun tape : Coins × Oracle => lowMask (garblerMask tape.2.1
        (garblerKeys (tape.1, tape.2.2)).1 (garblerKeys (tape.1, tape.2.2)).2 probeSite))
        ∘ reassembleEquiv)
      = (fun x : RestTape TapeRest × (MaskSite → BaseField) => lowMask (x.2 probeSite)) ∘
        (fun t => ((t.1, fun index : OtherIndex => t.2.permutation index.1),
          garblerMask t.2 (garblerKeys t.1).1 (garblerKeys t.1).2)) := by
    funext t
    rfl
  rw [factor, ← PMF.map_comp, swappedTape_garblerMasks,
    productPMF_map_snd _ _ _ (fun m : MaskSite → BaseField => lowMask (m probeSite)) fun _ => rfl]
  have marginal := uniform_eval (β := BaseField) (i := probeSite)
  rw [show (fun m : MaskSite → BaseField => lowMask (m probeSite))
      = lowMask ∘ (fun m : MaskSite → BaseField => m probeSite) from rfl, ← PMF.map_comp,
    marginal]
  exact swapped_low

end Hidden

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
