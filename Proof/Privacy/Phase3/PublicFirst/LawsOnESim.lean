/-
**Phase 3, P1r — `LawOn`, step (E), part 13: the private side's pieces.**

* `revealWeight_le`: the reveal flag contains `Exact0` (`exact0_reveal`), so the private weight is at
  most the `Exact0`-indicator weight;
* `targets_link`: D's collector targets (at the opening's value) are `simDesignated`;
* `inner_O`: the view of the installed overlay, averaged over the uniform oracle, is the view kernel
  averaged over uniform EncPRF permutations, hash function and view answers, at the triples of the
  mask tape (visible sites) and of the preimages (designated sites);
* `coins_marginal`: a function of the offsets and `ρ` averaged over uniform coins.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEGarb

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (Stage1Source collectorElement designatedIndex)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The reveal flag contains `Exact0` -/

theorem exact0_reveal (source : Stage1Source) (coins : Coins) (Δ : EncPRF.Coordinate → Block) (state : LState)
    (h : Exact0 scalar input coins.offsets) : revealOnPred scalar source input coins Δ state := by
  obtain ⟨o, phi, found, agree⟩ := h
  have restored : (Lamport.restore input (sourceLabels source input)).input = BitInput.ofAffine input := by
    rw [Kriterion.ArgoMAC.Phase3.Lazy.restore_selectedLabels]
  unfold revealOnPred
  refine ⟨o, phi, found, fun c p => ?_⟩
  rw [restored]
  exact Or.inl ((agree c p).resolve_right id)

open Classical in
theorem revealWeight_le (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (source : Stage1Source)
    (coins : Coins) (Δ : EncPRF.Coordinate → Block) (state : LState) :
    OnLaw.revealWeight scalar source input coins Δ Ψ state ≤
      if Exact0 scalar input coins.offsets then 0 else Ψ source.publicValue (sourceLabels source input) state := by
  unfold OnLaw.revealWeight
  by_cases h : Exact0 scalar input coins.offsets
  · have r := exact0_reveal scalar input source coins Δ state h
    simp [r, h]
  · rw [if_neg h]
    split_ifs
    · exact zero_le
    · exact le_rfl

/-! ### 2. The targets -/

theorem targets_link (cells : PublicCells) (key : InputMacKey) (T : Tape) (O : Oracle) (coins : Coins) :
    OnLaw.targetsOf scalar (cellsSource cells key) input
        ((Kriterion.ArgoMAC.Phase3.Glue.openingQueriesM (cellsSource cells key).publicValue
          (BitInput.ofAffine input) ((cellsSource cells key).key.encode (BitInput.ofAffine input))).eval
          (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))) coins =
      fun dc => simDesignated (offShape input) (rowTarget (rowsAt scalar coins dc.1) input)
        (cells.1 dc.1).1 (cells.1 dc.1).2 (digitVisible (offShape input) ((maskSiteEquiv (masksOf T)).1 dc.1))
        (.inl (collectorElement dc.2)) :=
  funext fun dc => targets_eq input scalar cells key _ T O coins dc.1 dc.2

/-! ### 3. The oracle -/

theorem installTape_vis (T : Tape) (blocks : DSite → Block × Block × Block) (i : VisIdx input) (j : Fin 3) :
    OnLaw.installTape (BitInput.ofAffine input) T blocks (visSite input i, j) = T (visSite input i, j) := by
  refine OnLaw.installTape_other _ T blocks _ ?_
  rintro ⟨d, c, b, same⟩
  have sites := siteIndex_injective (a₁ := (desSite (BitInput.ofAffine input) d c, b)) (a₂ := (visSite input i, j)) same
  have eq : wSite input (.inr (d, c)) = wSite input (.inl i) := congrArg Prod.fst sites
  exact Sum.inr_ne_inl (wSite_injective input eq)

theorem installTape_des (T : Tape) (blocks : DSite → Block × Block × Block) (dc : DSite) (j : Fin 3) :
    OnLaw.installTape (BitInput.ofAffine input) T blocks (desSite (BitInput.ofAffine input) dc.1 dc.2, j) =
      Kriterion.ArgoMAC.Phase3.Glue.limbAt j (blocks dc) :=
  OnLaw.installTape_designated _ T blocks _ dc.1 dc.2 j rfl

theorem triples_install (T : Tape) (blocks : DSite → Block × Block × Block) :
    (fun w => triplesOf (OnLaw.installTape (BitInput.ofAffine input) T blocks) (wSite input w)) =
      Sum.elim (fun i => triplesOf T (visSite input i)) blocks := by
  funext w
  rcases w with i | dc
  · rw [show wSite input (.inl i) = visSite input i from rfl]
    unfold triplesOf
    rw [installTape_vis, installTape_vis, installTape_vis]
    rfl
  · rw [desSite_eq]
    unfold triplesOf
    rw [installTape_des, installTape_des, installTape_des]
    rfl

/-- **The installed overlay's view, averaged over the uniform oracle.** -/
theorem inner_O (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (cells : PublicCells) (key : InputMacKey)
    (T : Tape) (blocks : DSite → Block × Block × Block) :
    ∑' O, PMF.uniformOfFintype Oracle O *
        Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
          (OnLaw.onView (cellsSource cells key).publicValue (BitInput.ofAffine input)
            ((cellsSource cells key).key.encode (BitInput.ofAffine input))
            (OnLaw.overlay (OnLaw.installTape (BitInput.ofAffine input) T blocks) O)) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H * ∑' x, PMF.uniformOfFintype (VO → Block) x *
          onKW input Ψ (cellsSource cells key).publicValue key E H x
            (Sum.elim (fun i => triplesOf T (visSite input i)) blocks) := by
  unfold OnLaw.onView
  rw [overlay_uniform input _ _ _ (fun trans => Ψ (cellsSource cells key).publicValue
    (sourceLabels (cellsSource cells key) input) (plantAll trans LazyOracle.empty))]
  refine tsum_congr fun E => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  have view : ∀ v : OtherIndex → Block,
      Ψ (cellsSource cells key).publicValue (sourceLabels (cellsSource cells key) input)
        (plantAll (transcript (tableAnswer (E, H, v, OnLaw.installTape (BitInput.ofAffine input) T blocks))
          (shadowOnM (cellsSource cells key).publicValue (BitInput.ofAffine input)
            ((cellsSource cells key).key.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      onKW input Ψ (cellsSource cells key).publicValue key E H (v ∘ voIdx input)
        (Sum.elim (fun i => triplesOf T (visSite input i)) blocks) := by
    intro v
    show onK input Ψ _ key (E, H, v, _) = _
    rw [onK_view, onKV_tape, triples_install]
  simp only [view]
  exact tsum_restrict (voIdx input) (voIdx_injective input)
    (fun x => onKW input Ψ (cellsSource cells key).publicValue key E H x
      (Sum.elim (fun i => triplesOf T (visSite input i)) blocks))

/-! ### 4. The coins' offsets and `ρ` -/

omit [GroupCertificate] in
theorem rowsGet (keys : OutputKeys) (R : Randomness) (i : Fin digitCount) :
    (FieldMacToECMac.rowsForOutputKeys keys R).get i =
      Coordinates.rows (keys.get i).offset.coordinates (digitEndomorphismBase (keys.get i).digit)
        (R.get i).rho.value := by
  unfold FieldMacToECMac.rowsForOutputKeys
  exact Vector.get_ofFn _ i

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
