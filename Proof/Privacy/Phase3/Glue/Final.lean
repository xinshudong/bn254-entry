/-
Phase 3 glue: **the final assembly, with everything that is real plugged in.**

`planB_oracleAdaptivePrivacy_of` is `planB_oracleAdaptivePrivacy` at P1's hybrids `planBHybrids`, with
the inputs that are proved today:

* `H_swap`: `planB_maskSwapBound` (P1 `G0 → G0U`, P4 lazy refill `I^U → I`);
* `H_open`: `planB_openingBound` (P1b, `HW → H` at `364/(r−1)`);
* `H_joint.hidden`: `planB_hidden` (P1h, `G0U → G1U` at `L1`);
* `H_abort`: `AbortBound.of_keyAveraged` with P4b's `Lazy.keyAveragedFailBound` (`H → I^U`).

Exactly two named hypotheses remain:
* `publicFirst`: `JointExactnessBound.publicFirst` at `planBHybrids` (P1i, `G1U → HW`);
* `machine`: `MachineBound simulator` (P2; its `cost` field is `MachineBound.of_law`'s).

The conclusion is literally the type of `Submission.solution.adaptivePrivacy`.
-/

import Proof.Privacy.Phase3.Glue.AbortBridge
import Proof.Privacy.Phase3.Hybrids
import Proof.Privacy.Phase3.Hidden.Final
import Proof.Privacy.Phase3.Lazy.FailAssembly

namespace Kriterion.ArgoMAC.Phase3.Glue

open BN254 Cryptography

/-- **The Plan B privacy field from the two remaining hypotheses.** -/
theorem planB_oracleAdaptivePrivacy_of {simulator : BoundedMachine.Simulator}
    (publicFirst : GameCoreUntilBad Security.Phase3.planBHybrids.hiddenDeleted
      Security.Phase3.planBHybrids.publicFirst fun first _ =>
        stageOneHitError first + exceptionalError + maskSwapError)
    (machine : MachineBound simulator) :
    ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
      letI := field
      letI := @Fintype.ofFinite PlanB.FixedIndex inferInstance
      letI := @Fintype.ofFinite EncPRF.PermutationIndex inferInstance
      letI := Classical.decEq PlanB.FixedIndex
      letI := Classical.decEq EncPRF.PermutationIndex
      GarbledCircuit.OracleAdaptivePrivacy (@Scheme.scheme field group) PlanB.Wire.encoding 3363376
        (@uniformRandomTape Scheme.Coins (@Fintype.ofFinite Scheme.Coins inferInstance)
          Scheme.witness)
        (fun parameter scalar coins =>
          (Programs.garbleProgram parameter scalar coins).toOracleProgram) :=
  planB_oracleAdaptivePrivacy simulator Security.Phase3.planBHybrids
    Security.Phase3.planB_maskSwapBound Security.Phase3.planB_openingBound
    ⟨Security.Phase3.planB_hidden, publicFirst⟩ machine
    (AbortBound.of_keyAveraged rfl rfl Lazy.keyAveragedFailBound)

end Kriterion.ArgoMAC.Phase3.Glue
