/-
**Phase 3, P1r — `LawOn`, step (E), part 9: the garbler's side (C's output) on the view.**

The garbler's side after (C) (`realTarget`): uniform coins, an answer table `A ~ tableLaw` and fresh
answers `w` at the gadget positions the garbler's designed entries do not plant (`FreshQ`: a digit
without exceptional input, or a position where `u` disagrees with the digit's exceptional input),
the shadow run on the table `freshen A w`. Off `Exact0` (no digit's exceptional input is `u`) it is
bounded below by `realCore`, which drops the `Exact0` outcomes. Here (per coins):

* `real_view`: the table law expanded, the kernel on the view (`xvW`: the fold view from `A`, the
  gadget view from `A` at the planted positions and from `w` at the fresh ones), the published value
  `tablePub` of the coins, the pads at the table's `hash(t)`, the table's non-site answers and limbs;
* `real_tape'`: the tape at the view — uniform masks, the per-site limb laws at the view sites, the
  published value through the masks (`tablePub_cellsW` at any hidden positions).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnERegroup

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The planted gadget positions, `Exact0`, the garbler's side -/

/-- A gadget coordinate as an EncPRF coordinate. -/
def toEnc : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- **A planted gadget position**: its digit has an exceptional input, which agrees with `u` there
(the garbler's designed gadget entries). -/
def Planted (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) (κ : Coord)
    (p : Fin PlanB.coordinateBits) : Prop :=
  ∃ phi, digitEndomorphismBase (outputKeyOf scalar K d).digit = some phi ∧
    inputBit (BitInput.ofAffine (Exception.exceptionalInput phi (outputKeyOf scalar K d).offset.coordinates))
        (toEnc κ) p = inputBit (BitInput.ofAffine input) (toEnc κ) p

/-- **`E₀`: some nonzero digit's exceptional input is `u`.** -/
def Exact0 (K : FieldMacToECMac.SuccessfulOffsets) : Prop :=
  ∃ o, RevealsAt scalar K (BitInput.ofAffine input) (fun _ _ => False) o

/-- A fresh gadget index (the garbler's designed entries leave it empty). -/
def FreshQ (K : FieldMacToECMac.SuccessfulOffsets) (i : OtherIndex) : Prop :=
  match i.1 with
  | .gadget d κ p => ¬ Planted scalar input K d κ p
  | _ => False

open Classical in
/-- **The table with fresh answers at the fresh gadget indices.** -/
def freshen (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : OtherIndex → Block) : Table :=
  (A.1, A.2.1, fun i => if FreshQ scalar input K i then w i else A.2.2.1 i, A.2.2.2)

variable (parameter : ℕ)

/-- **The garbler's side after (C)**: the shadow on the table with fresh answers at the fresh gadget
indices. -/
def realTarget (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
    ∑' w, PMF.uniformOfFintype (OtherIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty)

open Classical in
/-- The garbler's side off `Exact0`. -/
def realCore (Ψ : Public → LamportSignature → LState → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' coins, PMF.uniformOfFintype Coins coins * if Exact0 scalar input coins.offsets then 0 else
    ∑' A, tableLaw A * ∑' w, PMF.uniformOfFintype (OtherIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty)

omit parameter in
theorem realCore_le (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    realCore scalar input Ψ ≤ realTarget scalar input Ψ := by
  unfold realCore realTarget
  refine ENNReal.tsum_le_tsum fun coins => mul_le_mul' le_rfl ?_
  split_ifs
  · exact zero_le
  · exact le_rfl

/-! ### 2. The view of the garbler's side -/

open Classical in
/-- **The view's non-site answers on `freshen`**: the table's at the fold view and the planted
gadget positions, the fresh answers elsewhere. -/
def xvW (K : FieldMacToECMac.SuccessfulOffsets) (v w : OtherIndex → Block) : VO → Block
  | .inl f => v (foldIdx input f)
  | .inr g => if Planted scalar input K g.1 g.2.1 g.2.2 then v (gadIdx g) else w (gadIdx g)

open Classical in
theorem freshen_view (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : OtherIndex → Block) :
    (freshen scalar input K A w).2.2.1 ∘ voIdx input = xvW scalar input K A.2.2.1 w := by
  funext o
  rcases o with f | ⟨d, κ, p⟩
  · show (if FreshQ scalar input K (foldIdx input f) then _ else _) = _
    rw [if_neg (by unfold FreshQ; exact id)]
    rfl
  · show (if FreshQ scalar input K (gadIdx (d, κ, p)) then w (gadIdx (d, κ, p))
        else A.2.2.1 (gadIdx (d, κ, p))) =
      (if Planted scalar input K d κ p then A.2.2.1 (gadIdx (d, κ, p)) else w (gadIdx (d, κ, p)))
    have fresh : FreshQ scalar input K (gadIdx (d, κ, p)) ↔ ¬ Planted scalar input K d κ p := Iff.rfl
    by_cases planted : Planted scalar input K d κ p
    · rw [if_pos planted, if_neg (fun f => fresh.mp f planted)]
    · rw [if_neg planted, if_pos (fresh.mpr planted)]

/-- **The garbler's side, per coins, on the view.** -/
theorem real_view (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (coins : Coins) :
    ∑' A, tableLaw A * ∑' w, PMF.uniformOfFintype (OtherIndex → Block) w *
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      ∑' E, PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block) E *
        ∑' H, PMF.uniformOfFintype EncPRF.HashOracle H *
          ∑' v, PMF.uniformOfFintype (OtherIndex → Block) v * ∑' T, fibreTape T *
            ∑' w, PMF.uniformOfFintype (OtherIndex → Block) w *
              onKW input Ψ (tablePub scalar coins (padsOf E (H coins.bridgeKey)) v T) coins.inputMacKey E H
                (xvW scalar input coins.offsets v w) (fun ws => triplesOf T (wSite input ws)) := by
  have pointwise : ∀ (A : Table) (w : OtherIndex → Block),
      Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
        (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
        (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
          (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
            (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) =
      onKW input Ψ (tablePub scalar coins (padsOf A.1 (A.2.1 coins.bridgeKey)) A.2.2.1 A.2.2.2)
        coins.inputMacKey A.1 A.2.1 (xvW scalar input coins.offsets A.2.2.1 w)
        (fun ws => triplesOf A.2.2.2 (wSite input ws)) := by
    intro A w
    have second : ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 = coins.inputMacKey := by
      rw [garbleM_table]
    rw [garbleM_tablePub, second, tablePads_eq]
    show onK input Ψ _ coins.inputMacKey (freshen scalar input coins.offsets A w) = _
    rw [onK_view, freshen_view, onKV_tape]
    rfl
  simp only [pointwise]
  unfold tableLaw
  rw [tsum_productPMF]
  refine tsum_congr fun E => congrArg _ ?_
  rw [tsum_productPMF]
  refine tsum_congr fun H => congrArg _ ?_
  rw [tsum_productPMF]

/-! ### 3. The hidden gadget positions: fresh ones -/

open Classical in
/-- A fresh position of each digit (`(x, 0)` if there is none). -/
def posOf (K : FieldMacToECMac.SuccessfulOffsets) (d : Fin digitCount) : Coord × Fin PlanB.coordinateBits :=
  if h : ∃ q : Coord × Fin PlanB.coordinateBits, ¬ Planted scalar input K d q.1 q.2 then Classical.choose h
  else (.x, ⟨0, by unfold PlanB.coordinateBits; omega⟩)

theorem inputBit_toEnc (bits : BitInput) (c : EncPRF.Coordinate) (p : Fin coordinateBitCount) :
    inputBit bits (toEnc (Pipeline.gadgetCoord c)) p = inputBit bits c p := by
  cases c <;> rfl

/-- **Off `Exact0` every digit has a fresh position.** -/
theorem posOf_fresh (K : FieldMacToECMac.SuccessfulOffsets) (off : ¬ Exact0 scalar input K)
    (d : Fin digitCount) : ¬ Planted scalar input K d (posOf scalar input K d).1 (posOf scalar input K d).2 := by
  unfold posOf
  split_ifs with h
  · exact Classical.choose_spec h
  · push_neg at h
    intro planted
    obtain ⟨phi, found, _⟩ := planted
    refine off ⟨d, phi, found, fun c p => Or.inl ?_⟩
    obtain ⟨phi', found', agree⟩ := h (Pipeline.gadgetCoord c, p)
    rw [found] at found'
    cases Option.some.inj found'
    rw [← inputBit_toEnc, ← inputBit_toEnc (BitInput.ofAffine input)]
    exact agree

variable (K : FieldMacToECMac.SuccessfulOffsets)

/-- The hidden gadget positions at fixed offsets. -/
abbrev posK : Fin digitCount → Coord × Fin PlanB.coordinateBits := posOf scalar input K

/-- A fold view index is not hidden. -/
theorem foldIdx_not_hidden (f : FoldV) : foldIdx input f ∉ Set.range (hidW input (posK scalar input K)) :=
  hot_not_hiddenW input _ f.1 f.2.1 _ f.2.2
    (fun h => by have b := activeBit_lt input f.1 f.2.1; have h1 := h.1; omega)
    (by have b := activeBit_lt input f.1 f.2.1; omega)

/-- Off `Exact0` a planted gadget index is not hidden. -/
theorem planted_not_hidden (off : ¬ Exact0 scalar input K) (g : GadV)
    (planted : Planted scalar input K g.1 g.2.1 g.2.2) :
    gadIdx g ∉ Set.range (hidW input (posK scalar input K)) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;> have value := congrArg Subtype.val same <;>
    simp only [hidW, gadIdx, hotOther, gadgetAt, hotIndexNat, reduceCtorEq] at value
  injection value with digitEq coordEq position
  obtain ⟨o, κ, p⟩ := g
  simp only at digitEq coordEq position planted
  subst digitEq
  refine posOf_fresh scalar input K off d ?_
  have same : ((posOf scalar input K d).1, (posOf scalar input K d).2) = (κ, p) :=
    Prod.ext coordEq (Fin.ext (congrArg Fin.val position))
  rw [show (posOf scalar input K d).1 = κ from coordEq, show (posOf scalar input K d).2 = p from position]
  exact planted

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
