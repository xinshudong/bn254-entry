/-
**Phase 3, P1g — the off-curve probe in `HW`: `true` with mass `R(M+1)/2^384`.**

`HW` at the off-curve input `(0, 0)` makes no oracle call (`openedSimulator`'s stage 2 on
`none`), so the probe runs on the empty lazy oracle: its two fold questions are fresh, and its
three mask blocks are asked at three scale indices no earlier question touched, so they are three
independent uniform blocks whatever the label (`probeMask_lazy`), and the probe's mask is `sampleFp`
of uniform blocks: `HW` outputs `true` with mass `R(M+1)/2^384` (`publicFirst_probe_true`).
-/

import Proof.Privacy.Phase3.PublicFirst.ProbeGames

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (PlanBAdversary chunkZero Stage1Source idealSamplers)
open Kriterion.ArgoMAC.Phase3.Lazy (LState inactiveEntry foldLabels touchedIndex)
open scoped ENNReal

noncomputable section

/-! ### 1. Laws of fresh questions -/

/-- A bind that reads only the first component on the support. -/
theorem bind_fst_of_support {α β γ : Type} (p : PMF (α × β)) (f : α × β → PMF γ)
    (g : α → PMF γ) (agree : ∀ x ∈ p.support, f x = g x.1) :
    p.bind f = (p.map Prod.fst).bind g := by
  rw [PMF.bind_map]
  refine PMF.ext fun c => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases member : x ∈ p.support
  · rw [agree x member]
    rfl
  · rw [(PMF.apply_eq_zero_iff p x).mpr member, zero_mul, zero_mul]

section Fresh

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **A forward question at an index nobody asked is a uniform block.** -/
theorem fresh_answer (state : LState) (index : FixedIndex) (label : Block)
    (fresh : state.fixed index = SparsePermutation.empty _) :
    (LazyOracle.query (.fixedForward index label) state).map Prod.fst
      = PMF.uniformOfFintype Block := by
  rw [Kriterion.ArgoMAC.Phase3.Lazy.query_answer]
  refine PMF.ext fun target => ?_
  have unknownIn : ¬ (state.fixed index).knownInput label.toFin := by
    rw [fresh]
    show ¬ (_ < 0)
    omega
  have unknownOut : ¬ (state.fixed index).knownOutput target.toFin := by
    rw [fresh]
    show ¬ (_ < 0)
    omega
  rw [Kriterion.ArgoMAC.Phase3.Lazy.fresh_answer_apply _ _ unknownIn, if_neg unknownOut, fresh,
    PMF.uniformOfFintype_apply, Kriterion.ArgoMAC.Phase3.Lazy.card_block]
  rfl

/-- A forward question leaves every other index alone. -/
theorem query_fixed_other (state : LState) (index other : FixedIndex) (label : Block)
    (result : Block × LState)
    (member : result ∈ (LazyOracle.query (.fixedForward index label) state).support)
    (different : index ≠ other) : result.2.fixed other = state.fixed other :=
  Kriterion.ArgoMAC.Phase3.Lazy.query_frame (.fixedForward index label) state result member other
    fun same => different (Option.some.inj same)

/-- A fresh question followed by a continuation that reads only its answer. -/
theorem fresh_bind (state : LState) (index : FixedIndex) (label : Block) {γ : Type}
    (fresh : state.fixed index = SparsePermutation.empty _)
    (f : Block × LState → PMF γ) (g : Block → PMF γ)
    (agree : ∀ result ∈ (LazyOracle.query (.fixedForward index label) state).support,
      f result = g result.1) :
    (LazyOracle.query (.fixedForward index label) state).bind f
      = (PMF.uniformOfFintype Block).bind g := by
  exact (bind_fst_of_support _ f g agree).trans
    (congrArg (fun law : PMF Block => law.bind g) (fresh_answer state index label fresh))

/-! ### 2. The probe's three blocks -/

theorem scaleIndex_ne (first second : Fin 3) (different : first ≠ second) :
    scaleIndexOf .curveX chunkZero probeSwitch.val probeElement first ≠
      scaleIndexOf .curveX chunkZero probeSwitch.val probeElement second := by
  intro same
  rw [scaleIndexOf_eq _ _ _ _ _ (by decide) (by decide),
    scaleIndexOf_eq _ _ _ _ _ (by decide) (by decide)] at same
  simp only [FixedIndex.scale.injEq] at same
  exact different same.2.2.2.2

/-- The three limbs of uniform blocks at a label: the lazy mask law. -/
theorem uniform_blocks_low (label : Block) :
    (PMF.uniformOfFintype Block).bind (fun first => (PMF.uniformOfFintype Block).bind
      (fun second => (PMF.uniformOfFintype Block).map (fun third =>
        lowMask (sampleFp (first ^^^ label) (second ^^^ label) (third ^^^ label)))))
      = lazyMaskLaw.map lowMask := by
  have shift : ∀ a : Block, a ^^^ label ^^^ label = a := fun a => by
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  let shiftEquiv : (Block × Block × Block) ≃ (Block × Block × Block) :=
    { toFun := fun t => (t.1 ^^^ label, t.2.1 ^^^ label, t.2.2 ^^^ label)
      invFun := fun t => (t.1 ^^^ label, t.2.1 ^^^ label, t.2.2 ^^^ label)
      left_inv := fun t => by simp only [shift]
      right_inv := fun t => by simp only [shift] }
  have product : (PMF.uniformOfFintype Block).bind (fun first => (PMF.uniformOfFintype Block).bind
      (fun second => (PMF.uniformOfFintype Block).map (fun third =>
        lowMask (sampleFp (first ^^^ label) (second ^^^ label) (third ^^^ label)))))
      = (PMF.uniformOfFintype (Block × Block × Block)).map
          (fun t => lowMask (sampleFp (t.1 ^^^ label) (t.2.1 ^^^ label) (t.2.2 ^^^ label))) := by
    rw [uniformOfFintype_productPMF, uniformOfFintype_productPMF]
    unfold productPMF
    simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map]
    rfl
  rw [product, lazyMaskLaw, PMF.map_comp]
  have factor : (fun t : Block × Block × Block =>
      lowMask (sampleFp (t.1 ^^^ label) (t.2.1 ^^^ label) (t.2.2 ^^^ label)))
      = (lowMask ∘ fun blocks : Block × Block × Block =>
          sampleFp blocks.1 blocks.2.1 blocks.2.2) ∘ shiftEquiv := rfl
  rw [factor, ← PMF.map_comp, Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv]

/-- **The probed blocks, asked fresh, give the lazy mask law.** -/
theorem probeMask_lazy (label : Block) (state : LState)
    (fresh : ∀ block : Fin 3,
      state.fixed (scaleIndexOf .curveX chunkZero probeSwitch.val probeElement block)
        = SparsePermutation.empty _) :
    (runLazyQ (probeMaskM label) state).map Prod.fst = lazyMaskLaw.map lowMask := by
  set index := fun block : Fin 3 => scaleIndexOf .curveX chunkZero probeSwitch.val probeElement block
  have unfolded : runLazyQ (probeMaskM label) state =
      (LazyOracle.query (.fixedForward (index 0) label) state).bind fun first =>
        (LazyOracle.query (.fixedForward (index 1) label) first.2).bind fun second =>
          (LazyOracle.query (.fixedForward (index 2) label) second.2).bind fun third =>
            PMF.pure (lowMask (sampleFp ((show Block from first.1) ^^^ label) ((show Block from second.1) ^^^ label)
              ((show Block from third.1) ^^^ label)), third.2) := rfl
  rw [unfolded, PMF.map_bind, ← uniform_blocks_low label]
  refine fresh_bind _ _ _ (fresh 0) _ _ fun first firstMember => ?_
  rw [PMF.map_bind]
  have firstFresh : ∀ block : Fin 3, block ≠ 0 → first.2.fixed (index block) = SparsePermutation.empty _ :=
    fun block ne => (query_fixed_other _ _ _ _ _ firstMember (scaleIndex_ne 0 block ne.symm)).trans
      (fresh block)
  refine fresh_bind _ _ _ (firstFresh 1 (by decide)) _ _ fun second secondMember => ?_
  rw [PMF.map_bind]
  have secondFresh : second.2.fixed (index 2) = SparsePermutation.empty _ :=
    (query_fixed_other _ _ _ _ _ secondMember (scaleIndex_ne 1 2 (by decide))).trans
      (firstFresh 2 (by decide))
  simp only [PMF.pure_map]
  rw [← fresh_answer _ _ label secondFresh]
  erw [PMF.map_comp]
  rfl

/-- A fold gate's questions leave every other index alone. -/
theorem foldMaskM_frame (lane : Lane) (c : Fin chunkCount) (step gate : ℕ) (label : Block)
    (state : LState) (result : Block × LState)
    (member : result ∈ (runLazyQ (Programs.foldMaskM lane c step gate label) state).support)
    (other : FixedIndex) (notHot : ∀ half, hotIndexNat lane c step gate half ≠ other) :
    result.2.fixed other = state.fixed other := by
  have unfolded : runLazyQ (Programs.foldMaskM lane c step gate label) state =
      (LazyOracle.query (.fixedForward (hotIndexNat lane c step gate false) label) state).bind
        fun first => (LazyOracle.query (.fixedForward (hotIndexNat lane c step gate true) label)
          first.2).bind fun second =>
            PMF.pure (((show Block from first.1) ^^^ label) ^^^ ((show Block from second.1) ^^^ label),
              second.2) := rfl
  rw [unfolded] at member
  obtain ⟨first, firstMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  obtain ⟨second, secondMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  rw [PMF.mem_support_pure_iff] at member
  subst member
  exact (query_fixed_other _ _ _ _ _ secondMember (notHot true)).trans
    (query_fixed_other _ _ _ _ _ firstMember (notHot false))

theorem hot_ne_scale (lane : Lane) (step gate : ℕ) (half : Bool) (block : Fin 3) :
    hotIndexNat lane chunkZero step gate half ≠
      scaleIndexOf .curveX chunkZero probeSwitch.val probeElement block := by
  intro same
  simp only [hotIndexNat, scaleIndexOf, scaleIndexNat] at same
  cases same

/-- **The probe on the empty lazy oracle has the lazy mask law**, whatever the table and labels. -/
theorem probe_lazy (table : Public) (labels : LamportSignature) :
    (runLazyQ (probeM table labels) LazyOracle.empty).map Prod.fst = lazyMaskLaw.map lowMask := by
  unfold probeM
  rw [probeFold_eq, runLazyQ_bind, runLazyQ_bind, PMF.bind_bind, PMF.map_bind]
  have constant : ∀ result ∈ (runLazyQ (Programs.foldMaskM .curveX chunkZero 1
      (inactiveEntry (probeValue labels)) (probeJoin table 0 ^^^ probeBitLabel labels 0))
      LazyOracle.empty).support,
      ((runLazyQ (Pure.pure (foldLabels (probeValue labels) (probeBitLabel labels)
          (probeJoin table) result.1) : Programs.M (Fin (2 ^ chunkWidth chunkZero) → Block))
          result.2).bind fun r => runLazyQ (probeMaskM (r.1 probeSwitch)) r.2).map Prod.fst
        = lazyMaskLaw.map lowMask := by
    intro result member
    show ((PMF.pure (foldLabels (probeValue labels) (probeBitLabel labels) (probeJoin table)
      result.1, result.2)).bind _).map Prod.fst = _
    erw [PMF.pure_bind]
    refine probeMask_lazy _ _ fun block => ?_
    exact (foldMaskM_frame _ _ _ _ _ _ _ member _ fun half => hot_ne_scale _ _ _ half block)
  exact (bind_fst_of_support _ _ (fun _ => lazyMaskLaw.map lowMask) constant).trans
    (PMF.bind_const _ _)

end Fresh

/-! ### 3. The probe in `HW` -/

section PublicFirstGame

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex]
  [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **`HW` against the probe is the lazy mask law.** -/
theorem publicFirst_probe_eq (parameter : ℕ) (scalar : NonZeroScalar) :
    publicFirstHybrid probeAdversary parameter scalar = lazyMaskLaw.map lowMask := by
  unfold publicFirstHybrid
  rw [abstractIdealGame_eq_staged]
  unfold stagedGame
  have stage1 : (openedSimulator (realRows scalar) skipInstallation).stage1 parameter
      LazyOracle.empty = ((PMF.uniformOfFintype Stage1Source).map some).map
        (Option.map fun (source : Stage1Source) => ((source.publicValue, source, LazyOracle.empty) :
          Public × (openedSimulator (realRows scalar) skipInstallation).State × LState)) := rfl
  rw [stage1, PMF.map_comp, PMF.bind_map,
    ← PMF.bind_const (PMF.uniformOfFintype Stage1Source) (lazyMaskLaw.map lowMask)]
  congr 1
  funext source
  show (LazyOracle.run (probeAdversary.chooseInput parameter source.publicValue ())
      LazyOracle.empty).bind _ = _
  have first : LazyOracle.run (probeAdversary.chooseInput parameter source.publicValue ())
      (LazyOracle.empty : LState) = PMF.pure ((offInput, ()), LazyOracle.empty) :=
    PMF.pure_map _ _
  rw [first]
  erw [PMF.pure_bind]
  dsimp only
  rw [function_offInput]
  have second : (openedSimulator (realRows scalar) skipInstallation).stage2 source offInput none
      LazyOracle.empty = PMF.pure (some (Lamport.selectedLabels
        (source.key.encode (BitInput.ofAffine offInput)), LazyOracle.empty)) := rfl
  rw [second]
  erw [PMF.pure_bind]
  show (LazyOracle.run (freeOracle (probeM source.publicValue
    (Lamport.selectedLabels (source.key.encode (BitInput.ofAffine offInput)))) 5
    (probeM_bounded _ _)) LazyOracle.empty).map Prod.fst = _
  rw [run_freeOracle, probe_lazy]

/-- **`HW` outputs `true` with mass `R(M+1)/2^384`.** -/
theorem publicFirst_probe_true (parameter : ℕ) (scalar : NonZeroScalar) :
    publicFirstHybrid probeAdversary parameter scalar true
      = ((quotient + 1) * residue : ℕ) / 2 ^ 384 := by
  rw [publicFirst_probe_eq, lazy_low]

end PublicFirstGame

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
