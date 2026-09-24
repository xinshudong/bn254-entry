/-
**Phase 3, P1r — `LawOn`, step (E), part 2: the on-curve shadow reads only its view.**

At a fixed input `u` the on-curve shadow (`shadowOnM`: the prefix, the bit-`true` pads, the whole
evaluator) asks, whatever the answers (`shadow_onQ`, index-based):

* at every (lane, chunk) of the **four** lanes, the two halves of the step-1 fold gate of the
  inactive parent (`FoldV`, `foldIdx`) and the three blocks of every switch off the active one
  (`Inact`: the inactive mask sites, `ICell`);
* every gadget position of every digit (`GadV`, `gadIdx`);
* EncPRF and hash questions.

So on answer tables the shadow's transcript reads a table only through its EncPRF permutations, its
hash function, its non-site answers at `VO = FoldV ⊕ GadV` and its limbs at the inactive cells
(`transcript_view`), and the kernel of `LawOn`'s both sides, `onK` (the weight at a published value,
a key's selected labels and the shadow's planted transcript on a table), is a function `onKV` of
exactly these (`onK_view`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEEval
import Proof.Privacy.Phase3.PublicFirst.LawsOff

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

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-! ### 1. The view's indices -/

/-- **An inactive mask site**: its switch is not the active one of its chunk at `u`. -/
def Inact (s : MaskSite) : Prop :=
  s.2.2.1 ≠ chunkOf (Pipeline.coordBits (BitInput.ofAffine input) s.1.coord) s.2.1

instance (s : MaskSite) : Decidable (Inact input s) := by unfold Inact; infer_instance

/-- The inactive cells. -/
abbrev ICell := {c : Cell // Inact input c.1}

/-- The fold view: (lane, chunk, half) of the step-1 gate of the inactive parent. -/
abbrev FoldV := Lane × Fin chunkCount × Bool

/-- The gadget view: every gadget position. -/
abbrev GadV := Fin digitCount × Coord × Fin PlanB.coordinateBits

/-- **The view's non-site indices.** -/
abbrev VO := FoldV ⊕ GadV

/-- The step-1 fold gate of the inactive parent. -/
def foldIdx (f : FoldV) : OtherIndex :=
  hotOther f.1 f.2.1 1 (1 - activeBit input f.1 f.2.1) f.2.2

/-- A gadget position. -/
def gadIdx (g : GadV) : OtherIndex := gadgetAt g.1 g.2.1 g.2.2

/-- The view's non-site indices, as other indices. -/
def voIdx : VO → OtherIndex
  | .inl f => foldIdx input f
  | .inr g => gadIdx g

theorem voIdx_injective : Function.Injective (voIdx input) := by
  rintro (⟨ℓ, c, h⟩ | ⟨o, κ, p⟩) (⟨ℓ', c', h'⟩ | ⟨o', κ', p'⟩) same <;>
    have value := congrArg Subtype.val same <;>
    simp only [voIdx, foldIdx, gadIdx, hotOther, gadgetAt, hotIndexNat, FixedIndex.hot.injEq,
      reduceCtorEq, FixedIndex.gadget.injEq] at value
  · obtain ⟨rfl, rfl, -, entry, rfl⟩ := value
    rfl
  · obtain ⟨rfl, rfl, rfl⟩ := value
    rfl

/-! ### 2. The shadow's questions -/

/-- **A view question**: a view non-site index or an inactive site (any input), EncPRF (forward), the
hash. -/
def OnQ : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward index _ => (∃ v, (voIdx input v).1 = index) ∨
      (∃ (s : MaskSite) (j : Fin 3), Inact input s ∧ siteIndex (s, j) = index)
  | .encForward _ _ => True
  | .hash _ => True
  | _ => False

theorem onQ_hot (lane : Lane) (c : Fin chunkCount) (r : Nat) (half : Bool) (x : Block) (small : r < 2)
    (off : r ≠ (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).val % 2) :
    OnQ input (.fixedForward (hotIndexNat lane c 1 r half) x) := by
  refine Or.inl ⟨.inl (lane, c, half), ?_⟩
  have a : activeBit input lane c =
      (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c).val % 2 := by
    cases lane <;> rfl
  have bound := activeBit_lt input lane c
  show hotIndexNat lane c 1 (1 - activeBit input lane c) half = _
  congr 1
  omega

theorem onQ_site (lane : Lane) (c : Fin chunkCount) (s : Fin (2 ^ chunkWidth c))
    (element : Fin (laneCount lane)) (block : Fin 3) (x : Block)
    (off : s ≠ chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) c) :
    OnQ input (.fixedForward (scaleIndexOf lane c s.val element block) x) :=
  Or.inr ⟨⟨lane, c, s, element⟩, block, off, rfl⟩

theorem onQ_gadget (o : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits) (x : Block) :
    OnQ input (.fixedForward (.gadget o κ p) x) :=
  Or.inl ⟨.inr (o, κ, p), rfl⟩

theorem evalFoldM_onQ (lane : Lane) (chunk : Fin chunkCount) (bitLabel join : Nat → Block) :
    ∀ n, n = 2 → Hidden.QueryOnly (OnQ input) (Programs.evalFoldM lane chunk
      (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk).toNat
      bitLabel join n) := by
  intro n hn
  subst hn
  have value : (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk).toNat =
      (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk).val :=
    chunkValue_toNat _ _
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.bind (Hidden.QueryOnly.pure' _) fun previous =>
    Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _) fun previous =>
      Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  · unfold Programs.evalStepM
    refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ =>
      Hidden.QueryOnly.pure' _
    rw [if_pos (Fin.ext (by
      have := e.isLt
      simp only [pow_zero, Nat.lt_one_iff] at this
      simp [activeAt, this]))]
    exact Hidden.QueryOnly.pure' _
  · unfold Programs.evalStepM
    refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun e => ?_) fun _ =>
      Hidden.QueryOnly.pure' _
    by_cases active : e = activeAt
        (chunkValue (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk).toNat 1
    · rw [if_pos active]
      exact Hidden.QueryOnly.pure' _
    · rw [if_neg active]
      have small : e.val < 2 := e.isLt
      have off : e.val ≠
          (chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk).val % 2 :=
        fun same => active (Fin.ext (by simp only [activeAt]; omega))
      exact Hidden.QueryOnly.bind (hashM_only _ _ (onQ_hot input lane chunk _ false _ small off))
        fun _ => Hidden.QueryOnly.bind (hashM_only _ _ (onQ_hot input lane chunk _ true _ small off))
          fun _ => Hidden.QueryOnly.pure' _

/-- **A lane of the evaluator asks only view questions.** -/
theorem evalLaneM_onQ (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (labels : Fin coordinateBitCount → Block) :
    Hidden.QueryOnly (OnQ input) (Programs.evalLaneM (laneCount lane) lane joins scale
      (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) labels) := by
  refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun chunk => ?_) fun _ =>
    Hidden.QueryOnly.pure' _
  unfold Programs.evalChunkM
  refine Hidden.QueryOnly.bind ?_ fun hotLabels => Hidden.QueryOnly.bind ?_ fun _ =>
    Hidden.QueryOnly.pure' _
  · exact evalFoldM_onQ input lane chunk _ _ _ (Hidden.chunkWidth_eq_two chunk)
  · unfold Programs.evalMasksM
    refine Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun s => ?_) fun _ =>
      Hidden.QueryOnly.pure' _
    by_cases active : s = chunkOf (Pipeline.coordBits (BitInput.ofAffine input) lane.coord) chunk
    · rw [if_pos active]
      exact Hidden.QueryOnly.pure' _
    · rw [if_neg active]
      exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun element =>
        Hidden.QueryOnly.bind (hashM_only _ _ (onQ_site input lane chunk s element 0 _ active)) fun _ =>
          Hidden.QueryOnly.bind (hashM_only _ _ (onQ_site input lane chunk s element 1 _ active))
            fun _ => Hidden.QueryOnly.bind
              (hashM_only _ _ (onQ_site input lane chunk s element 2 _ active)) fun _ =>
                Hidden.QueryOnly.pure' _) fun _ => Hidden.QueryOnly.pure' _

theorem padM_onQ (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    Hidden.QueryOnly (OnQ input) (Programs.padM keys coordinate index bit) :=
  Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ => Hidden.QueryOnly.pure' _

theorem curvePrefixM_onQ (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (OnQ input) (curvePrefixM P (BitInput.ofAffine input) mac) := by
  unfold curvePrefixM
  exact Hidden.QueryOnly.bind (evalLaneM_onQ input .curveX _ _ _) fun _ =>
    Hidden.QueryOnly.bind (evalLaneM_onQ input .curveY _ _ _) fun _ =>
      Hidden.QueryOnly.ask _ trivial

/-- **The on-curve shadow asks only view questions.** -/
theorem shadow_onQ (P : Public) (mac : InputMac) :
    Hidden.QueryOnly (OnQ input) (shadowOnM P (BitInput.ofAffine input) mac) := by
  unfold shadowOnM
  refine Hidden.QueryOnly.bind (curvePrefixM_onQ input P mac) fun hashed =>
    Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
  · unfold truePadsM
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => padM_onQ input _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  · unfold Programs.onCurveM
    refine Hidden.QueryOnly.bind (evalLaneM_onQ input .curveX _ _ _) fun _ =>
      Hidden.QueryOnly.bind (evalLaneM_onQ input .curveY _ _ _) fun _ =>
        Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ =>
          Hidden.QueryOnly.bind ?_ fun _ =>
            Hidden.QueryOnly.bind (evalLaneM_onQ input .pointX _ _ _) fun _ =>
              Hidden.QueryOnly.bind (evalLaneM_onQ input .pointY _ _ _) fun _ =>
                Hidden.QueryOnly.bind ?_ fun _ => Hidden.QueryOnly.pure' _
    · exact OnLaw.queryOnly_mono (Guess.evalPadsM_encOnly _ _) fun q ⟨_, _, _, same⟩ => by
        subst same
        trivial
    · exact OnLaw.queryOnly_mono (Guess.unlockM_asks _ _ _) fun q ⟨o, κ, p, same⟩ => by
        subst same
        exact onQ_gadget input o κ p _

/-! ### 3. The view of a table -/

open Classical in
/-- Non-site answers rebuilt from the view's. -/
def extOther (x : VO → Block) : OtherIndex → Block := fun i =>
  if h : ∃ v, voIdx input v = i then x (Classical.choose h) else 0

theorem extOther_voIdx (x : VO → Block) (v : VO) : extOther input x (voIdx input v) = x v := by
  have h : ∃ v', voIdx input v' = voIdx input v := ⟨v, rfl⟩
  unfold extOther
  rw [dif_pos h, voIdx_injective input (Classical.choose_spec h)]

/-- A tape rebuilt from the inactive cells' limbs. -/
def extTape (t : ICell input → Block) : Tape := fun c =>
  if h : Inact input c.1 then t ⟨c, h⟩ else 0

/-- **The view's table.** -/
def viewTable (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle)
    (x : VO → Block) (t : ICell input → Block) : Table :=
  (E, H, extOther input x, extTape input t)

/-- **The shadow's transcript on a table is its transcript on the table's view.** -/
theorem transcript_view (A : Table) (P : Public) (mac : InputMac) :
    transcript (tableAnswer A) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (viewTable input A.1 A.2.1 (A.2.2.1 ∘ voIdx input)
        (fun c => A.2.2.2 c.1))) (shadowOnM P (BitInput.ofAffine input) mac) := by
  refine transcript_agree_on (shadow_onQ input P mac) _ _ fun q view => ?_
  cases q with
  | fixedForward index x =>
      rcases view with ⟨v, rfl⟩ | ⟨s, j, inact, rfl⟩
      · rw [tableAnswer_other, tableAnswer_other]
        show A.2.2.1 (voIdx input v) = extOther input (A.2.2.1 ∘ voIdx input) (voIdx input v)
        exact (extOther_voIdx input (A.2.2.1 ∘ voIdx input) v).symm
      · rw [tableAnswer_site, tableAnswer_site]
        show A.2.2.2 (s, j) ^^^ x = extTape input (fun c => A.2.2.2 c.1) (s, j) ^^^ x
        unfold extTape
        rw [dif_pos inact]
  | fixedInverse _ _ => exact view.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact view.elim
  | hash _ => rfl

/-! ### 4. The kernel -/

/-- **The kernel of `LawOn`'s both sides**: the weight at a published value, a key's selected
labels, and the shadow's transcript on a table planted on the empty oracle. -/
def onK (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (A : Table) : ℝ≥0∞ :=
  Ψ P (Lamport.selectedLabels (key.encode (BitInput.ofAffine input)))
    (plantAll (transcript (tableAnswer A)
      (shadowOnM P (BitInput.ofAffine input) (key.encode (BitInput.ofAffine input)))) LazyOracle.empty)

/-- The kernel on the view. -/
def onKV (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (E : PermutationOracle EncPRF.PermutationIndex Block) (H : EncPRF.HashOracle) (x : VO → Block)
    (t : ICell input → Block) : ℝ≥0∞ :=
  onK input Ψ P key (viewTable input E H x t)

/-- **The kernel reads a table only through its view.** -/
theorem onK_view (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (P : Public) (key : InputMacKey)
    (A : Table) :
    onK input Ψ P key A = onKV input Ψ P key A.1 A.2.1 (A.2.2.1 ∘ voIdx input) (fun c => A.2.2.2 c.1) := by
  unfold onKV onK
  rw [transcript_view input A]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
