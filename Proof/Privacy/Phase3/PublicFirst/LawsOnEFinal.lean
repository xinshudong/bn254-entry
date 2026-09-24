/-
**Phase 3, P1s — `LawOn`, `DesignedLaws` and the Glue's `publicFirst`, real.**

* **`lawOn_all`**: `LawOn` at every on-curve input, at any instances — P1q's `lawOn_all_of_E` from
  step (E) (`OnE.onJoint`);
* **`designedLaws`**: `DesignedLaws` — P1n's `lawOff_all` off the curve (its `Fintype` instances
  are subsingletons), `lawOn_all` on it;
* **`planB_publicFirst`**: the Glue's `publicFirst` field `G1U → HW` at
  `stageOneHitError q₁ + exceptionalError + maskSwapError`, from `designedLaws` and P1k's
  `designedBounds` (`planB_publicFirst_of_laws_bounds`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPrivForm
import Proof.Privacy.Phase3.PublicFirst.LawsOff
import Proof.Privacy.Phase3.PublicFirst.LawsGuess
import Proof.Privacy.Phase3.PublicFirst.BoundsPerPair

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB

/-- **`LawOn` at every on-curve input**, at any instances: step (E) at every valid input. -/
theorem lawOn_all [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
    [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (parameter : ℕ) (scalar : NonZeroScalar) :
    ∀ input target, Scheme.scheme.function scalar input = some target → LawOn parameter scalar input :=
  OnLaw.lawOn_all_of_E parameter scalar fun input valid => OnE.onJoint scalar input valid

/-- **`DesignedLaws`, real**: `LawOff` off the curve, `LawOn` on it, at every input. -/
theorem designedLaws : DesignedLaws := by
  intro field group parameter scalar
  letI := field
  letI := group
  letI : Fintype FixedIndex := Fintype.ofFinite FixedIndex
  letI : Fintype EncPRF.PermutationIndex := Fintype.ofFinite EncPRF.PermutationIndex
  letI : DecidableEq FixedIndex := Classical.decEq FixedIndex
  letI : DecidableEq EncPRF.PermutationIndex := Classical.decEq EncPRF.PermutationIndex
  refine ⟨fun input off => ?_, lawOn_all parameter scalar⟩
  have global := lawOff_all parameter scalar input off
  convert global using 1

/-- **The Glue's `publicFirst` field, real**: `G1U → HW` at
`stageOneHitError q₁ + exceptionalError + maskSwapError`. -/
theorem planB_publicFirst :
    Kriterion.ArgoMAC.Phase3.Glue.GameCoreUntilBad
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.hiddenDeleted
      Kriterion.ArgoMAC.Security.Phase3.planBHybrids.publicFirst fun first _ =>
        Kriterion.ArgoMAC.Phase3.Glue.stageOneHitError first +
          Kriterion.ArgoMAC.Phase3.Glue.exceptionalError +
            Kriterion.ArgoMAC.Phase3.Glue.maskSwapError :=
  planB_publicFirst_of_laws_bounds designedLaws designedBounds

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
