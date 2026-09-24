/-
**Phase 3, P1s — `LawOn`, step (E), part 15: the private side is at most the core; `OnJoint`.**

* `privSrc`, `privBound`, **`priv_le_bound`**: `onPrivForm` with the reveal weight bounded by the
  `Exact0` indicator (`revealWeight_le`) and `deltaLaw` summed out;
* **`oracle_step`**: at a source of cells, the collector targets are F4's designated solve
  (`targets_link`), the preimages are the per-site laws (`preimages_limbs`), and the uniform oracle
  is the view kernel's EncPRF permutations, hash function and view answers (`inner_O`);
* **`tape_step`**: the mask tape at the view is uniform visible cells and their limb laws
  (`sim_tape`, `visEquiv`);
* **`privSrc_cells`**: the private side at a source of cells, the coins read as offsets and `ρ`s
  (`coins_bd`);
* **`priv_le_core`**: `onPrivForm ≤ onCore` (`tsum_source_cells`, `reorder_core`, `tsum_limbs_sum`);
* **`onJoint_global`**, **`onJoint`**: step (E), `OnLaw.OnJoint scalar input`, at every valid input
  (the garbler's side: `realCore_eq`, `realCore_le`, `onGarbForm_eq`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPriv

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source collectorElement openingQueriesM preimages idealSamplers)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState uniformMaskTape)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The reveal weight bounded by the `Exact0` indicator -/

open Classical in
/-- The private side at a source, the reveal weight bounded by the `Exact0` indicator. -/
def privSrc (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source) : ℝ≥0∞ :=
  ∑' T, uniformMaskTape T *
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' r, preimages idealSamplers (OnLaw.targetsOf scalar source input
            ((openingQueriesM source.publicValue (BitInput.ofAffine input)
              (source.key.encode (BitInput.ofAffine input))).eval
              (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))) coins) r *
          r.elim 0 fun blocks => if Exact0 scalar input coins.offsets then 0 else
            Ψ source.publicValue (sourceLabels source input)
              (OnLaw.onView source.publicValue (BitInput.ofAffine input)
                (source.key.encode (BitInput.ofAffine input))
                (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T blocks) O))

/-- The private side, the reveal weight bounded by the `Exact0` indicator. -/
def privBound (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' source, PMF.uniformOfFintype Stage1Source source * privSrc scalar input Ψ source

/-- **The private side is at most its `Exact0`-indicator bound.** -/
theorem priv_le_bound (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    OnLaw.onPrivForm scalar input Ψ ≤ privBound scalar input Ψ := by
  unfold OnLaw.onPrivForm privBound privSrc OnLaw.mergeK
  refine ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun T =>
    mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun O => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum
      fun coins => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_))))
  rcases r with _ | blocks
  · rw [Option.elim_none, Option.elim_none]
  · rw [Option.elim_some, Option.elim_some]
    exact le_trans (ENNReal.tsum_le_tsum fun delta => mul_le_mul' le_rfl
      (revealWeight_le scalar input Ψ source coins delta _)) (le_of_eq (tsum_pmf_const deltaLaw _))

/-! ### 2. The oracle, the tape, the coins -/

open Classical in
/-- **The oracle at a source of cells**: F4's designated solve, the per-site limb laws, the view
kernel. -/
theorem oracle_step (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells)
    (key : InputMacKey) (T : Tape) :
    ∑' O, PMF.uniformOfFintype (PublicOracle FixedIndex EncPRF.PermutationIndex) O *
      ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' r, preimages idealSamplers (OnLaw.targetsOf scalar (cellsSource cells key) input
            ((openingQueriesM (cellsSource cells key).publicValue (BitInput.ofAffine input)
              ((cellsSource cells key).key.encode (BitInput.ofAffine input))).eval
              (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))) coins) r *
          r.elim 0 (fun blocks => if Exact0 scalar input coins.offsets then 0 else
            Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
              (OnLaw.onView (cellsSource cells key).publicValue (BitInput.ofAffine input)
                ((cellsSource cells key).key.encode (BitInput.ofAffine input))
                (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T blocks) O))) =
    ∑' coins, PMF.uniformOfFintype Coins coins *
      ∑' bd, limbWeight (desT scalar input coins cells (visPart input (masksOf T))) bd *
        (if Exact0 scalar input coins.offsets then 0 else
          ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
            ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H * ∑' x, PMF.uniformOfFintype (VO → Block) x *
              onKW input Ψ (cellsSource cells key).publicValue key E H x
                (Sum.elim (fun i => triplesOf T (visSite input i)) bd)) := by
  have targets : ∀ (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (coins : Coins),
      OnLaw.targetsOf scalar (cellsSource cells key) input
          ((openingQueriesM (cellsSource cells key).publicValue (BitInput.ofAffine input)
            ((cellsSource cells key).key.encode (BitInput.ofAffine input))).eval
            (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))) coins =
        desT scalar input coins cells (visPart input (masksOf T)) := fun O coins =>
    targets_link scalar input cells key T O coins
  simp only [targets, preimages_limbs]
  rw [swapT]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [swapT]
  refine tsum_congr fun bd => congrArg _ ?_
  rw [tsum_mul_ite_zero, inner_O]

open Classical in
/-- **The mask tape at the view**: uniform visible cells and their limb laws. -/
theorem tape_step (cells : PublicCells)
    (Z : (VisIdx input → Block × Block × Block) → (DSite → Block × Block × Block) → ℝ≥0∞) :
    ∑' T, uniformMaskTape T * ∑' coins, PMF.uniformOfFintype Coins coins *
        ∑' bd, limbWeight (desT scalar input coins cells (visPart input (masksOf T))) bd *
          (if Exact0 scalar input coins.offsets then 0 else Z (fun i => triplesOf T (visSite input i)) bd) =
      ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
        ∑' bdv, limbWeight (visEquiv input vis) bdv * ∑' coins, PMF.uniformOfFintype Coins coins *
          ∑' bd, limbWeight (desT scalar input coins cells vis) bd *
            (if Exact0 scalar input coins.offsets then 0 else Z bdv bd) := by
  have visEq : ∀ T : Tape,
      visPart input (masksOf T) = (visEquiv input).symm (masksOf T ∘ visSite input) := by
    intro T
    rw [masks_visSite, Equiv.symm_apply_apply]
  simp only [visEq]
  rw [sim_tape input (fun μ bdv => ∑' coins, PMF.uniformOfFintype Coins coins *
    ∑' bd, limbWeight (desT scalar input coins cells ((visEquiv input).symm μ)) bd *
      (if Exact0 scalar input coins.offsets then 0 else Z bdv bd))]
  rw [tsum_equiv_uniform (visEquiv input).symm]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

open Classical in
/-- **The private side at a source of cells.** -/
theorem privSrc_cells (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells)
    (key : InputMacKey) :
    privSrc scalar input Ψ (cellsSource cells key) =
      ∑' vis, PMF.uniformOfFintype (VisibleCells (offShape input)) vis *
        ∑' bdv, limbWeight (visEquiv input vis) bdv *
          ∑' K, PMF.uniformOfFintype ClampedOffsets K *
            ∑' ρ, PMF.uniformOfFintype (Fin digitCount → NonZeroBase) ρ *
              ∑' bd, limbWeight (desK scalar input K ρ cells vis) bd *
                (if Exact0 scalar input K.1 then 0 else
                  ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
                    ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H *
                      ∑' x, PMF.uniformOfFintype (VO → Block) x *
                        onKW input Ψ (cellsSource cells key).publicValue key E H x (Sum.elim bdv bd)) := by
  unfold privSrc
  rw [tsum_congr fun T => congrArg _ (oracle_step scalar input Ψ cells key T)]
  rw [tape_step scalar input cells (fun bdv bd =>
    ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
      ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H * ∑' x, PMF.uniformOfFintype (VO → Block) x *
        onKW input Ψ (cellsSource cells key).publicValue key E H x (Sum.elim bdv bd))]
  refine tsum_congr fun vis => congrArg _ (tsum_congr fun bdv => congrArg _ ?_)
  exact coins_bd scalar input cells vis _

/-! ### 3. The private side is at most the core; step (E) -/

/-- **The private side is at most the core.** -/
theorem priv_le_core (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    OnLaw.onPrivForm scalar input Ψ ≤ onCore scalar input Ψ := by
  refine le_trans (priv_le_bound scalar input Ψ) (le_of_eq ?_)
  unfold privBound
  rw [tsum_source_cells]
  simp only [privSrc_cells scalar input Ψ]
  unfold onCore coreKEH
  exact reorder_core (fun K : ClampedOffsets => Exact0 scalar input K.1)
    (PMF.uniformOfFintype PublicCells) (PMF.uniformOfFintype InputMacKey)
    (PMF.uniformOfFintype (VisibleCells (offShape input)))
    (fun vis bdv => limbWeight (visEquiv input vis) bdv)
    (PMF.uniformOfFintype ClampedOffsets) (PMF.uniformOfFintype (Fin digitCount → NonZeroBase))
    (fun K ρ cells vis bd => limbWeight (desK scalar input K ρ cells vis) bd)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (PMF.uniformOfFintype EncPRF.HashOracle) (PMF.uniformOfFintype (VO → Block))
    (fun cells key E H x bdv bd =>
      onKW input Ψ (cellsSource cells key).publicValue key E H x (Sum.elim bdv bd))
    (fun K E H cells vis ρ key x =>
      ∑' bd, limbWeight (Sum.elim (visEquiv input vis) (desK scalar input K ρ cells vis)) bd *
        onKW input Ψ (cellsSource cells key).publicValue key E H x bd)
    (fun K E H cells vis ρ key x => tsum_limbs_sum (visEquiv input vis) (desK scalar input K ρ cells vis)
      (fun bd => onKW input Ψ (cellsSource cells key).publicValue key E H x bd))

/-- **Step (E), the joint law on the curve**, at the global instances, at every valid input. -/
theorem onJoint_global (valid : validate input = true) : OnLaw.OnJoint scalar input := by
  intro Ψ _
  calc OnLaw.onPrivForm scalar input Ψ ≤ onCore scalar input Ψ := priv_le_core scalar input Ψ
    _ = realCore scalar input Ψ := (realCore_eq scalar input valid Ψ).symm
    _ ≤ realTarget scalar input Ψ := realCore_le scalar input Ψ
    _ = OnLaw.onGarbForm scalar input Ψ := (onGarbForm_eq scalar input Ψ).symm

/-- **Step (E), the joint law on the curve**, at any instances (they are subsingletons), at every
valid input. -/
theorem onJoint (valid : validate input = true) [first : Fintype FixedIndex]
    [second : Fintype EncPRF.PermutationIndex] [third : DecidableEq FixedIndex]
    [fourth : DecidableEq EncPRF.PermutationIndex] : OnLaw.OnJoint scalar input := by
  have global := onJoint_global scalar input valid
  convert global using 1

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
