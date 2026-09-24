/-
**Phase 3, P1r — `LawOn`, step (E), part 3: the shadow on a uniform overlaid oracle is the shadow
on a uniform table.**

`LawOn`'s private side runs the shadow on `overlay T₁ O`, `O` uniform. On such an oracle the shadow
asks every non-site index at **one** point, which reads only the EncPRF permutations, the hash
function and the tape (`pointOf`): the step-1 fold gates at the level-1 labels (they read no oracle,
`evalFold_one`; on the point lanes the labels are whitened by the pads keyed by the hash at the
curve lanes' bridge value, which reads only the tape, `curveKey`), the gadget at the transformed
labels. So its transcript is its transcript on the table whose non-site answers are the uniform
permutations read at those points (`transcript_overlay`), and averaging the permutations gives
uniform non-site answers (`overlay_uniform`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEView

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

/-! ### 1. Agreeing on the asked questions -/

theorem transcript_agree_asked {α : Type} {S : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop}
    (a b : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) :
    ∀ {c : FreeQuery Programs.Spec α}, Guess.AsksOnly a S c → (∀ q, S q → a q = b q) →
      transcript a c = transcript b c
  | .pure _, _, _ => rfl
  | .query request next, only, same => by
      have head : S request := only ⟨request, a request⟩ List.mem_cons_self
      have tail : Guess.AsksOnly a S (next (a request)) := fun entry member =>
        only entry (List.mem_cons_of_mem _ member)
      have rest := transcript_agree_asked a b tail same
      show ⟨request, a request⟩ :: transcript a (next (a request)) =
        ⟨request, b request⟩ :: transcript b (next (b request))
      rw [rest, same request head]

variable [FieldCertificate] [GroupCertificate]

/-- The first fold level reads no oracle. -/
theorem evalFold_one (O O' : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (value : Nat) (bitLabel join : Nat → Block) :
    evalFold O lane c value bitLabel join 1 = evalFold O' lane c value bitLabel join 1 := by
  have step : evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0) (fun _ => 0) =
      evalStep O' lane c 0 (bitLabel 0) (join 0) (activeAt value 0) (fun _ => 0) := by
    funext e
    have same : e = activeAt value 0 := Guess.activeAt_zero value e
    unfold evalStep
    rw [if_pos same, if_pos same]
    congr 1
    exact Programs.xorFoldExcept_congr _ _ _ fun other off =>
      absurd (Guess.activeAt_zero value other) off
  show extendLevel 0 (fun _ => 0) (evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0)
      (fun _ => 0)) = extendLevel 0 (fun _ => 0) (evalStep O' lane c 0 (bitLabel 0) (join 0)
      (activeAt value 0) (fun _ => 0))
  rw [step]

/-! ### 2. The points -/

variable (input : AffineInput)

/-- A published value's fold joins, by lane. -/
def hotOf (P : Public) : Lane → Vector Block foldStepCount
  | .curveX => P.curveXHot
  | .curveY => P.curveYHot
  | .pointX => P.pointXHot
  | .pointY => P.pointYHot

/-- **The pads the evaluator reads**: keyed by the hash at the curve lanes' bridge value. -/
def padsAt (P : Public) (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle)
    (T : Tape) : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  Programs.realEvalPads E
    ⟨(H (curveKey P (BitInput.ofAffine input) T)).1, (H (curveKey P (BitInput.ofAffine input) T)).2⟩
    (BitInput.ofAffine input)

/-- A lane's labels. -/
def labelsAt (P : Public) (mac : InputMac) (E : PermutationOracle EncPRF.PermutationIndex Block)
    (H : EncPRF.HashOracle) (T : Tape) : Lane → Fin coordinateBitCount → Block
  | .curveX => Pipeline.macLabels mac .x
  | .curveY => Pipeline.macLabels mac .y
  | .pointX => Pipeline.macLabels (Programs.whitenMacOf (padsAt input P E H T) mac) .x
  | .pointY => Pipeline.macLabels (Programs.whitenMacOf (padsAt input P E H T) mac) .y

/-- **The point at which the shadow asks a non-site index.** -/
def pointOf (P : Public) (mac : InputMac) (E : PermutationOracle EncPRF.PermutationIndex Block)
    (H : EncPRF.HashOracle) (T : Tape) (i : OtherIndex) : Block :=
  match i.1 with
  | .hot lane c _ entry _ =>
      if small : entry.val < 2 then
        evalFold ⟨fun _ => Equiv.refl Block⟩ lane c
          (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).toNat
          (labelAt (chunkLabels (labelsAt input P mac E H T lane) c)) (joinAt (hotSlice (hotOf P lane) c))
          1 ⟨entry.val, small⟩
      else 0
  | .gadget _ κ p => macAt (Programs.transformMacOf (padsAt input P E H T) mac) κ p
  | .scale _ _ _ _ _ => 0

/-- **The agreement set**: a site (any input), a non-site index at its point, EncPRF, the hash. -/
def AgreeQ (pt : OtherIndex → Block) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index x => index ∈ Set.range siteIndex ∨
      ∃ h : index ∉ Set.range siteIndex, x = pt ⟨index, h⟩
  | .encForward _ _ => True
  | .hash _ => True
  | _ => False

theorem site_mem (lane : Lane) (c : Fin chunkCount) (j : Fin (2 ^ chunkWidth c))
    (element : Fin (laneCount lane)) (block : Fin 3) :
    scaleIndexOf lane c j.val element block ∈ Set.range siteIndex :=
  ⟨(⟨lane, c, j, element⟩, block), rfl⟩

/-- A lane's questions agree, on an overlaid oracle. -/
theorem laneAsk_agree (P : Public) (mac : InputMac) (T : Tape)
    (O : PublicOracle FixedIndex EncPRF.PermutationIndex) (lane : Lane)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex)
    (ask : Guess.LaneAsk (OnLaw.overlay T O).1 lane (laneCount lane) (hotOf P lane)
      (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) (labelsAt input P mac O.2.1 O.2.2 T lane) q) :
    AgreeQ (pointOf input P mac O.2.1 O.2.2 T) q := by
  obtain ⟨c, ⟨r, half, _, rfl⟩ | ⟨j, element, block, _, rfl⟩⟩ := ask
  · refine Or.inr ⟨(hotOther lane c 1 r.val half).2, ?_⟩
    have small : r.val % 2 ^ chunkBits < 2 := by
      have := r.isLt
      simp only [chunkBits] at this ⊢
      omega
    show _ = pointOf input P mac O.2.1 O.2.2 T ⟨.hot lane c _ ⟨r.val % 2 ^ chunkBits, _⟩ half, _⟩
    unfold pointOf
    dsimp only
    rw [dif_pos small, evalFold_one _ ⟨fun _ => Equiv.refl Block⟩]
    congr 1
    apply Fin.ext
    show r.val = r.val % 2 ^ chunkBits
    have := r.isLt
    simp only [chunkBits]
    omega
  · exact Or.inl (site_mem lane c j element block)

/-- The overlay's bridge value is the curve lanes'. -/
theorem reachHashArg_overlay [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (P : Public) (mac : InputMac) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    Guess.reachHashArg (OnLaw.overlay T O) P (BitInput.ofAffine input) mac =
      curveKey P (BitInput.ofAffine input) T := by
  unfold Guess.reachHashArg curveKey
  rw [show Pipeline.curveXValues (OnLaw.overlay T O).1 P (BitInput.ofAffine input) mac =
      laneValue .curveX (fun chunk => Pipeline.readCurveX (unpack (P.scale.get chunk)))
        (Pipeline.coordBits (BitInput.ofAffine input) .x) T from
      (Programs.eval_evalLaneM (OnLaw.overlay T O) curveElementCountX .curveX _ _ _ _).symm.trans
        (evalLaneM_dm (dmOn_overlay T O) .curveX _ _ _ _),
    show Pipeline.curveYValues (OnLaw.overlay T O).1 P (BitInput.ofAffine input) mac =
      laneValue .curveY (fun chunk => Pipeline.readCurveY (unpack (P.scale.get chunk)))
        (Pipeline.coordBits (BitInput.ofAffine input) .y) T from
      (Programs.eval_evalLaneM (OnLaw.overlay T O) curveElementCountY .curveY _ _ _ _).symm.trans
        (evalLaneM_dm (dmOn_overlay T O) .curveY _ _ _ _)]

theorem reachPads_overlay [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (P : Public) (mac : InputMac) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    Guess.reachPads (OnLaw.overlay T O) P (BitInput.ofAffine input) mac = padsAt input P O.2.1 O.2.2 T := by
  unfold Guess.reachPads padsAt
  rw [reachHashArg_overlay]
  rfl

/-- **Every question of the shadow on an overlaid oracle agrees.** -/
theorem shadow_asks_agree [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (P : Public) (mac : InputMac) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    Guess.AsksOnly (publicAnswer (OnLaw.overlay T O)) (AgreeQ (pointOf input P mac O.2.1 O.2.2 T))
      (shadowOnM P (BitInput.ofAffine input) mac) := by
  have lane : ∀ ℓ, ∀ q, Guess.LaneAsk (OnLaw.overlay T O).1 ℓ (laneCount ℓ) (hotOf P ℓ)
      (Pipeline.coordBits (BitInput.ofAffine input) ℓ.coord) (labelsAt input P mac O.2.1 O.2.2 T ℓ) q →
      AgreeQ (pointOf input P mac O.2.1 O.2.2 T) q := fun ℓ q ask => laneAsk_agree input P mac T O ℓ q ask
  have pads := reachPads_overlay input P mac T O
  unfold shadowOnM
  refine Guess.AsksOnly.bind ?_ (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.pure' _)))
  · unfold curvePrefixM
    refine Guess.AsksOnly.bind ((Guess.laneAsks _ _ .curveX _ _ _ _).mono (lane .curveX))
      (Guess.AsksOnly.bind ((Guess.laneAsks _ _ .curveY _ _ _ _).mono (lane .curveY)) ?_)
    intro entry member
    rcases List.mem_singleton.mp member with rfl
    trivial
  · refine Guess.AsksOnly.of_queryOnly ?_
    unfold truePadsM
    have pad : ∀ (keys : WhiteningKeys) c i b, Hidden.QueryOnly (AgreeQ (pointOf input P mac O.2.1 O.2.2 T))
        (Programs.padM keys c i b) := fun _ _ _ _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ => Hidden.QueryOnly.pure' _
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  · refine (Guess.onCurveM_asks _ _ _ _).mono fun q ask => ?_
    rcases ask with h | h | h | h | h | h | ⟨o, κ, p, rfl⟩
    · exact lane .curveX q h
    · exact lane .curveY q h
    · subst h
      trivial
    · obtain ⟨_, _, _, rfl⟩ := h
      trivial
    · rw [pads] at h
      exact lane .pointX q h
    · rw [pads] at h
      exact lane .pointY q h
    · refine Or.inr ⟨(gadgetAt o κ p).2, ?_⟩
      rw [pads]
      rfl

/-! ### 3. The overlaid oracle is a table -/

/-- **On an overlaid oracle the shadow's transcript is its transcript on a table**: the EncPRF
permutations, the hash, the non-site permutations read at the shadow's points, the tape. -/
theorem transcript_overlay [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]
    (P : Public) (mac : InputMac) (T : Tape) (O : PublicOracle FixedIndex EncPRF.PermutationIndex) :
    transcript (publicAnswer (OnLaw.overlay T O)) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (O.2.1, O.2.2,
          fun i => O.1.permutation i.1 (pointOf input P mac O.2.1 O.2.2 T i), T))
        (shadowOnM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_asked _ _ (shadow_asks_agree input P mac T O) fun q agree => ?_
  cases q with
  | fixedForward index x =>
      rcases agree with ⟨cell, rfl⟩ | ⟨h, rfl⟩
      · rw [OnLaw.overlay_site, tableAnswer_site, BitVec.xor_comm]
      · rw [OnLaw.overlay_fixed_other T O index h, tableAnswer_other _ ⟨index, h⟩]
        rfl
  | encForward _ _ => rfl
  | hash _ => rfl
  | fixedInverse _ _ => exact agree.elim
  | encInverse _ _ => exact agree.elim

/-- **The shadow on a uniform overlaid oracle is the shadow on a table with uniform EncPRF
permutations, hash function and non-site answers.** -/
theorem overlay_uniform (P : Public) (mac : InputMac) (T : Tape)
    (G : List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' O, PMF.uniformOfFintype Oracle O *
        G (transcript (publicAnswer (OnLaw.overlay T O)) (shadowOnM P (BitInput.ofAffine input) mac)) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H *
          ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v *
            G (transcript (tableAnswer (E, H, v, T)) (shadowOnM P (BitInput.ofAffine input) mac)) := by
  rw [tsum_congr fun O => congrArg (_ * ·) (congrArg G (transcript_overlay input P mac T O))]
  rw [tsum_uniform_prod (α := PermutationOracle FixedIndex Block)
    (β := PermutationOracle EncPRF.PermutationIndex Block × EncPRF.HashOracle)]
  rw [tsum_swap_mul]
  rw [tsum_uniform_prod (α := PermutationOracle EncPRF.PermutationIndex Block)
    (β := EncPRF.HashOracle)]
  refine tsum_congr fun E => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  dsimp only
  rw [uniform_oracle_eq, tsum_map_mul, tsum_productPMF]
  simp only [oracleOf_other]
  simp only [tsum_const_uniform]
  exact tsum_uniform_perms (pointOf input P mac E H T) (fun v => G (transcript (tableAnswer (E, H, v, T))
    (shadowOnM P (BitInput.ofAffine input) mac)))

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
