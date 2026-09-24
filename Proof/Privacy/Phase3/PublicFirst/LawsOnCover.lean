/-
**Phase 3, P1p — `LawOn`, step (B): the planted entries are among the shadow's questions.**

On the curve, for every completion `O` of the upper state `σ` (the garbler's EncPRF and designed
entries planted on the empty oracle):

* `O` agrees with the tape on the evaluator's questions before the gadget (`agree_preM`: on the
  tape every such question is planted, `OnReach.onCurve_reach_classified`, and `preM` asks no gadget
  question), so the evaluator runs alike on `O` and on the tape up to the gadget, and reads the
  garbler's keys `hash(t)` (`prefix_eval_tape`);
* **every planted entry is an entry of the shadow's transcript on `O`** (`upper_covers`): the
  bit-`true` pads by `truePadsM`, the bit-`false` pads by `evalPadsM`, the designed entries before
  the gadget by the pre-gadget evaluator, the designed gadget entries by `unlockM` at the same labels;
* **`upper_view`**: hence the shadow's transcript planted on `σ` or on the empty oracle has the same
  lookups (`plantAll_sub`), and the upper side of `LawOn` is `E_tape E_{O ~ completion σ} Ψ(P, L,
  onView O)` (`lawOn_upper`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnQuestions
import Proof.Privacy.Phase3.PublicFirst.LawsOffTable

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (publicCompletion public_step)
open Kriterion.ArgoMAC.Phase3.Lazy (LState AllQ)
open scoped ENNReal

noncomputable section

section Cover

variable [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
  [Fintype EncPRF.PermutationIndex] [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
  (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle) (input : AffineInput)

/-- **On the curve a completion of the upper state agrees with the tape before the gadget.** -/
theorem agree_preM (valid : validate input = true) {O : PublicOracle FixedIndex EncPRF.PermutationIndex}
    (consistentO : Hidden.Consistent O (upperEntries parameter scalar tape input)) :
    Hidden.AgreesWith O (Hidden.transcriptOf (publicAnswer tape.2)
      (preM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (tape.1.inputMacKey.encode (BitInput.ofAffine input)))) := by
  intro f fMember
  have consistentT := upper_consistent parameter scalar tape input
  have inOn : f.1 ∈ (Hidden.transcriptOf (publicAnswer tape.2)
      (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (Guess.macOf tape input))).map Sigma.fst := by
    show f.1 ∈ (Hidden.transcriptOf _ (Programs.onCurveM _ _
      (tape.1.inputMacKey.encode (BitInput.ofAffine input)))).map Sigma.fst
    rw [onCurveM_split, Hidden.transcriptOf_bind, List.map_append]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨f, fMember, rfl⟩)
  rcases OnReach.onCurve_reach_classified parameter scalar tape input valid f.1 inOn with
    ⟨u, uUpper, uEq⟩ | ⟨o, κ, p, fEq, _⟩
  · obtain ⟨fq, fa⟩ := f
    obtain ⟨uq, ua⟩ := u
    simp only at uEq
    subst uEq
    have h1 : ua = publicAnswer O uq := consistentO _ uUpper
    have h2 : ua = publicAnswer tape.2 uq := consistentT _ uUpper
    have h3 : publicAnswer tape.2 uq = fa := Hidden.transcriptOf_agrees tape.2 _ _ fMember
    show publicAnswer O uq = fa
    rw [← h1, h2, h3]
  · exact absurd fEq ((notGadget_preM _ _ _).mem _ f fMember o κ p _)

/-- The prefix is the pre-gadget evaluator's first stage. -/
theorem agree_prefix (valid : validate input = true)
    {O : PublicOracle FixedIndex EncPRF.PermutationIndex}
    (consistentO : Hidden.Consistent O (upperEntries parameter scalar tape input)) :
    Hidden.AgreesWith O (Hidden.transcriptOf (publicAnswer tape.2)
      (curvePrefixM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (tape.1.inputMacKey.encode (BitInput.ofAffine input)))) := fun f fMember =>
  agree_preM parameter scalar tape input valid consistentO f (by
    unfold preM
    rw [Hidden.transcriptOf_bind]
    exact List.mem_append_left _ fMember)

/-- **On the curve the prefix reads the garbler's keys `hash(t)`.** -/
theorem prefix_eval_tape (valid : validate input = true) :
    (curvePrefixM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
        (tape.1.inputMacKey.encode (BitInput.ofAffine input))).eval (publicAnswer tape.2) =
      tape.2.2.2 tape.1.bridgeKey := by
  unfold curvePrefixM
  simp only [FreeQuery.eval_bind, Programs.eval_evalLaneM, Programs.eval_askHash]
  show tape.2.2.2 (Guess.reachHashArg tape.2 (Scheme.scheme.garble parameter scalar tape).1
    (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) = _
  rw [Guess.reach_hashArg, Guess.evalKey_eq _ _ valid]

/-- **Every planted entry is an entry of the shadow's transcript on an oracle consistent with the
planted entries** (e.g. a completion of the upper state). -/
theorem upper_covers (valid : validate input = true)
    {O : PublicOracle FixedIndex EncPRF.PermutationIndex}
    (consistentO : Hidden.Consistent O (upperEntries parameter scalar tape input)) :
    ∀ e ∈ upperEntries parameter scalar tape input,
      e ∈ transcript (publicAnswer O) (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
        (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) := by
  intro e inUpper
  have agreeE : publicAnswer O e.1 = e.2 := (consistentO e inUpper).symm
  suffices asks : Asks (publicAnswer O) (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) e.1 by
    have inTranscript := mem_of_asks (publicAnswer O) _ asks
    rw [agreeE] at inTranscript
    exact inTranscript
  obtain ⟨transPre, evalPre⟩ := Hidden.transcriptOf_of_agrees _ tape.2 O
    (agree_preM parameter scalar tape input valid consistentO)
  obtain ⟨_, evalPrefix⟩ := Hidden.transcriptOf_of_agrees _ tape.2 O
    (agree_prefix parameter scalar tape input valid consistentO)
  have keyO := evalPrefix.trans (prefix_eval_tape parameter scalar tape input valid)
  have viaOn : ∀ q, Asks (publicAnswer O) (Programs.onCurveM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q →
      Asks (publicAnswer O) (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
        (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q := by
    intro q h
    unfold shadowOnM
    exact Asks.bind_right (Asks.bind_right (Asks.bind_left h))
  have viaPre : ∀ q, Asks (publicAnswer tape.2) (preM (Scheme.scheme.garble parameter scalar tape).1
      (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q →
      Asks (publicAnswer O) (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
        (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))) q := by
    intro q h
    apply viaOn
    rw [onCurveM_split]
    refine Asks.bind_left ?_
    unfold Asks at h ⊢
    rw [transPre]
    exact h
  rcases List.mem_append.mp inUpper with enc | designed
  · have encEq := garbler_enc (publicAnswer tape.2) scalar tape.1
    unfold encEntries at enc
    change e ∈ (transcript (publicAnswer tape.2) (Programs.garbleM scalar tape.1)).filter
      Entry.IsEnc at enc
    rw [encEq, transcript_eq_transcriptOf] at enc
    obtain ⟨c, i, b, qEq⟩ := (padsM_form _).mem _ e enc
    rw [qEq]
    have firstKey : ((Programs.askHash tape.1.bridgeKey).eval (publicAnswer tape.2)).1 =
        (tape.2.2.2 tape.1.bridgeKey).1 := rfl
    rw [firstKey]
    cases b
    · apply viaPre
      unfold preM
      refine Asks.bind_right ?_
      rw [prefix_eval_tape parameter scalar tape input valid]
      exact Asks.bind_left (asks_evalPadsM_false _ _ _ c i)
    · unfold shadowOnM
      refine Asks.bind_right ?_
      rw [keyO]
      exact Asks.bind_left (asks_truePadsM _ _ c i)
  · obtain ⟨inGarbler, keep⟩ := List.mem_filter.mp designed
    have rule : designedRule scalar tape input e = true := by
      simp only [Bool.and_eq_true] at keep
      exact keep.2
    have asksTape := designed_asks parameter scalar tape input e inGarbler rule
    rw [onCurveM_split] at asksTape
    rcases asks_bind_cases asksTape with pre | gadget
    · exact viaPre _ pre
    · apply viaOn
      rw [onCurveM_split]
      refine Asks.bind_right ?_
      rw [evalPre]
      unfold gadgetPart at gadget ⊢
      rcases asks_bind_cases gadget with unlock | done
      · refine Asks.bind_left ?_
        obtain ⟨f, fMember, fEq⟩ := List.mem_map.mp unlock
        obtain ⟨o, κ, p, qEq⟩ := (Guess.unlockM_asks _ _ _).mem _ f fMember
        rw [← fEq, qEq]
        exact asks_unlock _ _ _ o κ p _ rfl
      · exact absurd done (fun h => List.not_mem_nil h)

/-- **(B) The upper side, on the curve**: the lazy shadow run on the upper state, read through its
final state's lookups, is the view of a completion of the upper state. -/
theorem upper_view (valid : validate input = true) (Φ : LState → ℝ≥0∞)
    (invariant : ∀ s t, SameLookups s t → Φ s = Φ t) :
    ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
          (tape.1.inputMacKey.encode (BitInput.ofAffine input)))
        (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s * Φ s.2 =
      ∑' O, publicCompletion (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) O *
        Φ (onView (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
          (tape.1.inputMacKey.encode (BitInput.ofAffine input)) O) := by
  rw [upper_eager parameter scalar tape input _ _ _ Φ invariant]
  refine tsum_congr fun O => ?_
  by_cases member : O ∈ (publicCompletion (plantAll (upperEntries parameter scalar tape input)
      LazyOracle.empty)).support
  · have same := plantAll_sub O (upperEntries parameter scalar tape input)
      (transcript (publicAnswer O) (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
        (BitInput.ofAffine input) (tape.1.inputMacKey.encode (BitInput.ofAffine input))))
      (completion_upper parameter scalar tape input member)
      (fun e m => (transcript_mem _ _ e m).symm)
      (upper_covers parameter scalar tape input valid (completion_upper parameter scalar tape input member))
    exact congrArg (_ * ·) (invariant _ _ same)
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

omit [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] in
/-- The garbler's input key is the coins'. -/
theorem garble_snd : (Scheme.scheme.garble parameter scalar tape).2 = tape.1.inputMacKey := by
  obtain ⟨coins, oracle⟩ := tape
  rw [← garble_eval parameter scalar coins oracle, Programs.eval_garbleM]

omit [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] in
theorem restore_garble_input :
    (Lamport.restore input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).input =
      BitInput.ofAffine input := by
  rw [restore_encode]

omit [Fintype FixedIndex] [Fintype EncPRF.PermutationIndex] in
theorem restore_garble_mac :
    (Lamport.restore input
      (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).inputMac =
      tape.1.inputMacKey.encode (BitInput.ofAffine input) := by
  rw [restore_encode, garble_snd]

/-- **The upper side of `LawOn`, on the curve**, as the view of a completion. -/
theorem lawOn_upper (valid : validate input = true) (Ψ : Public → LamportSignature → LState → ℝ≥0∞)
    (invariant : ∀ table labels first second, SameLookups first second →
      Ψ table labels first = Ψ table labels second) :
    ∑' s, runLazyQ (shadowOnM (Scheme.scheme.garble parameter scalar tape).1
          (Lamport.restore input
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).input
          (Lamport.restore input
            (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)).inputMac)
        (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) s *
        Ψ (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input) s.2 =
      ∑' O, publicCompletion (plantAll (upperEntries parameter scalar tape input) LazyOracle.empty) O *
        Ψ (Scheme.scheme.garble parameter scalar tape).1
          (Scheme.scheme.encode (Scheme.scheme.garble parameter scalar tape).2 input)
          (onView (Scheme.scheme.garble parameter scalar tape).1 (BitInput.ofAffine input)
            (tape.1.inputMacKey.encode (BitInput.ofAffine input)) O) := by
  rw [restore_garble_input parameter scalar tape input, restore_garble_mac parameter scalar tape input]
  exact upper_view parameter scalar tape input valid _ (invariant _ _)

end Cover

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw
