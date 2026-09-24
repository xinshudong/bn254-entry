/-
**Phase 3, P1b — the `Hybrids` data and `G1U`.**

`Glue.Hybrids` (`Glue/Assembly.lean`) is five `HybridGame`s. This module supplies all five:

| field | game | defined in |
|---|---|---|
| `maskSwapped` (`G0U`) | `maskSwappedHybrid` | `GameSwap.lean` (P1) |
| `hiddenDeleted` (`G1U`) | `hiddenDeletedHybrid` | here |
| `publicFirst` (`HW`) | `publicFirstHybrid` | `Opened.lean` |
| `opened` (`H`) | `openedHybrid` | `Opened.lean` |
| `idealUniform` (`I^U`) | `Lazy.idealUniformHybrid` | `Lazy/Refill.lean` (P4) |

**`G1U`, hidden-entry deletion at the input choice** (design note B §3). The garbling is `G0U`'s:
the tape is `swappedChallengeTape` and the published value and key are `Scheme.scheme.garble` of it.
The adversary's oracle is the shared lazy oracle, populated from the garbler's own transcript on the
tape (`transcript`, the (query, answer) pairs of `Programs.garbleM`):

* **stage 1** sees only the garbler's EncPRF entries (`installAll` of the `enc` part): every
  fixed-key and hash entry of the garbler is absent;
* **at the input choice** the garbler's fixed-key and hash entries that the adversary's own
  evaluation on its input reaches -- the queries of the full evaluator `Programs.onCurveM` on the
  selected labels (system A, `hash(t_eval)`, the pads, system B, the gadget), run on the tape -- are
  installed with the tape's answers (a program that fails is skipped);
* the garbler's other fixed-key and hash entries -- the **hidden** ones: the active switches and
  active fold parents of every lane, the gadget's differing positions, and, off the curve, all of
  system B, the gadget and `hash(t)` -- are never installed.

Why stage 1 already lacks the non-EncPRF entries: the identical-until-bad bounds of `G0U → G1U`
(`L1 = 3q/2^128 + q/(p−1)`) are exact only when the bad event is evaluated in a game where the
garbler's fixed-key points and `t` are independent of the adversary's view, which is `G1U` itself;
a stage-1 touch of such an entry costs at most `2/2^128` (hit plus collision, one garbler point per
fixed-key index) or `1/p` (`t`), inside `L1`'s `3/2^128 + 1/(p−1)` per query. The EncPRF entries stay,
because an EncPRF index carries **two** garbler points (bits `0` and `1` of the Even–Mansour input),
whose stage-1 touches (`4/2^128` per query) are `L2`'s (`G1U → HW`), and because off the curve they
are masked by `hash(t).2` and need not be deleted at all.
-/

import Proof.Privacy.Phase3.OpeningBound
import Proof.Privacy.Phase3.Lazy.IdealPerMask

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Phase3.Glue (HybridGame PlanBAdversary)

noncomputable section

/-! ### Transcripts and installation -/

/-- A query with its answer. -/
abbrev Entry (FixedIndex EncIndex : Type) := Σ query : PublicQuery FixedIndex EncIndex, query.Answer

/-- **The transcript** of a query computation on a complete oracle: every (query, answer) pair, in
order. -/
def transcript {α : Type} (answer : ∀ query : PublicQuery FixedIndex EncPRF.PermutationIndex,
    query.Answer) : FreeQuery Programs.Spec α → List (Entry FixedIndex EncPRF.PermutationIndex)
  | .pure _ => []
  | .query request next => ⟨request, answer request⟩ :: transcript answer (next (answer request))

/-- An EncPRF entry. -/
def Entry.IsEnc {FixedIndex EncIndex : Type} (entry : Entry FixedIndex EncIndex) : Bool :=
  match entry.1 with
  | .encForward _ _ | .encInverse _ _ => true
  | _ => false

/-- Install one entry into the lazy oracle (a failed program is skipped). -/
def installEntry [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex)
    (entry : Entry FixedIndex EncPRF.PermutationIndex) :
    LazyOracle.State FixedIndex EncPRF.PermutationIndex :=
  (LazyOracle.program entry.1 entry.2 oracle).getD oracle

/-- Install a list of entries, in order. -/
def installAll [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (entries : List (Entry FixedIndex EncPRF.PermutationIndex))
    (oracle : LazyOracle.State FixedIndex EncPRF.PermutationIndex) :
    LazyOracle.State FixedIndex EncPRF.PermutationIndex :=
  entries.foldl installEntry oracle

/-! ### `G1U` -/

/-- The garbler's transcript on a tape. -/
def garblerTranscript [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) : List (Entry FixedIndex EncPRF.PermutationIndex) :=
  transcript (publicAnswer tape.2) (Programs.garbleM scalar tape.1)

/-- The adversary's reach at its input: the transcript of the full evaluator (`Programs.onCurveM`:
system A, the bridge hash, the pads, system B, the gadget) on the selected labels, on the tape. -/
def reachTranscript [FieldCertificate] [GroupCertificate] (table : Public) (input : AffineInput)
    (labels : LamportSignature) (tape : Coins × Oracle) :
    List (Entry FixedIndex EncPRF.PermutationIndex) :=
  transcript (publicAnswer tape.2)
    (Programs.onCurveM table (Lamport.restore input labels).input
      (Lamport.restore input labels).inputMac)

open Classical in
/-- The garbler's visible fixed-key and hash entries at an input: those its reach queries. -/
def visibleEntries [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (tape : Coins × Oracle) (table : Public) (input : AffineInput) (labels : LamportSignature) :
    List (Entry FixedIndex EncPRF.PermutationIndex) :=
  (garblerTranscript scalar tape).filter fun entry =>
    !entry.IsEnc && decide (entry.1 ∈ (reachTranscript table input labels tape).map Sigma.fst)

/-- **`G1U`**: `G0U`'s garbling; stage 1 on the garbler's EncPRF entries only; at the input choice
the visible fixed-key and hash entries installed, the hidden ones never. -/
def hiddenDeletedHybrid : HybridGame := fun adversary parameter scalar =>
  swappedChallengeTape.bind fun tape =>
    let garbled := Scheme.scheme.garble parameter scalar tape
    (LazyOracle.run (adversary.chooseInput parameter garbled.1 ())
        (installAll ((garblerTranscript scalar tape).filter Entry.IsEnc) LazyOracle.empty)).bind
      fun selected =>
        let labels := Scheme.scheme.encode garbled.2 selected.1.1
        (LazyOracle.run (adversary.decide parameter garbled.1 labels () selected.1.2)
          (installAll (visibleEntries scalar tape garbled.1 selected.1.1 labels) selected.2)).map
          Prod.fst

/-! ### The record -/

/-- **P1's proof-only hybrids** (`Glue.Hybrids`): `G0U`, `G1U`, `HW`, `H`, `I^U`. -/
def planBHybrids : Kriterion.ArgoMAC.Phase3.Glue.Hybrids where
  maskSwapped := maskSwappedHybrid
  hiddenDeleted := hiddenDeletedHybrid
  publicFirst := publicFirstHybrid
  opened := openedHybrid
  idealUniform := Kriterion.ArgoMAC.Phase3.Lazy.idealUniformHybrid

/-- `H_swap.real` against the record (P1's `maskSwapBound_real`). -/
theorem planB_maskSwap_real :
    Kriterion.ArgoMAC.Phase3.Glue.HopBound Kriterion.ArgoMAC.Phase3.Glue.realHybrid
      planBHybrids.maskSwapped fun _ _ => Kriterion.ArgoMAC.Phase3.Glue.maskSwapError :=
  maskSwapBound_real

/-- **`H_swap`, whole**, against the record: P1's `G0 → G0U` and P4's lazy refill
(`Lazy.maskSwapBound_of`). -/
theorem planB_maskSwapBound : Kriterion.ArgoMAC.Phase3.Glue.MaskSwapBound planBHybrids :=
  Kriterion.ArgoMAC.Phase3.Lazy.maskSwapBound_of planBHybrids rfl rfl

/-- **`H_open`** against the record: `HW → H` at `outputKernelError = 364/(r−1)`. -/
theorem planB_openingBound : Kriterion.ArgoMAC.Phase3.Glue.OpeningBound planBHybrids :=
  ⟨openingBound_kernel⟩

end

end Kriterion.ArgoMAC.Security.Phase3
