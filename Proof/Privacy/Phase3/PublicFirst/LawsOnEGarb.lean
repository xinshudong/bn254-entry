/-
**Phase 3, P1r — `LawOn`, step (E), part 12: C's garbler form is `realTarget`.**

P1q's `onGarbForm` answers a fresh gadget question at `x` by the translation `x ⊕ v k`
(`OnLaw.freshAnswer`); `realTarget` by a fresh table value. The shadow asks each gadget position at
one point, the transformed label under the pads keyed by the hash at the curve lanes' bridge value
(`gpt`, `shadow_gadAt`), so the translations are the table values `gpt ⊕ v` (`transcript_fresh`),
uniform with `v` (`garbK_eq`). `freshPos` is `¬ Planted` (`freshPos_iff`).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnECore
import Proof.Privacy.Phase3.PublicFirst.LawsOnCJoint

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnLaw (GPos freshAnswer freshPos garbK onGarbForm)
open scoped ENNReal

noncomputable section

variable [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) (input : AffineInput)

/-! ### 1. The gadget points on a table -/

/-- The shadow's point at a gadget position, on a table. -/
def gpt (P : Public) (mac : InputMac) (A : Table) (k : GPos) : Block :=
  macAt (Programs.transformMacOf (padsAt input P A.1 A.2.1 A.2.2.2) mac) k.2.1 k.2.2

/-- A gadget question at its point, or any other question. -/
def GadAt (P : Public) (mac : InputMac) (A : Table) : PublicQuery FixedIndex EncPRF.PermutationIndex → Prop
  | .fixedForward (.gadget o κ p) x => x = gpt input P mac A (o, κ, p)
  | _ => True

theorem notGadget_gadAt (P : Public) (mac : InputMac) (A : Table)
    (q : PublicQuery FixedIndex EncPRF.PermutationIndex) (h : OnLaw.NotGadget q) :
    GadAt input P mac A q := by
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p => exact absurd rfl (h o κ p x)
      | hot _ _ _ _ _ => trivial
      | scale _ _ _ _ _ => trivial
  | _ => trivial

theorem evalPadsM_enc (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (E : PermutationOracle EncPRF.PermutationIndex Block)
    (hE : ∀ i x, a (.encForward i x) = E.permutation i x) (keys : WhiteningKeys) (bits : BitInput) :
    (Programs.evalPadsM keys bits).eval a = Programs.realEvalPads E keys bits := by
  refine (eval_agree (Guess.evalPadsM_encOnly keys bits) a
    (publicAnswer (⟨fun _ => Equiv.refl Block⟩, E, fun _ => ((0 : Block), (0 : Block)))) ?_).trans
    (Programs.eval_evalPadsM _ _ _)
  rintro q ⟨c, i, b, rfl⟩
  exact hE _ _

theorem preM_pads (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (A : Table)
    (dm : DMOn a A.2.2.2) (hE : ∀ i x, a (.encForward i x) = A.1.permutation i x)
    (hH : ∀ k, a (.hash k) = A.2.1 k) (P : Public) (mac : InputMac) :
    ((OnLaw.preM P (BitInput.ofAffine input) mac).eval a).1 = padsAt input P A.1 A.2.1 A.2.2.2 := by
  unfold OnLaw.preM
  rw [FreeQuery.eval_bind, curvePrefixM_dm dm, hH]
  simp only [FreeQuery.eval_bind, FreeQuery.eval_pure]
  rw [evalPadsM_enc a A.1 hE]
  rfl

/-- **The shadow asks each gadget position at its point.** -/
theorem shadow_gadAt (a : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer) (A : Table)
    (dm : DMOn a A.2.2.2) (hE : ∀ i x, a (.encForward i x) = A.1.permutation i x)
    (hH : ∀ k, a (.hash k) = A.2.1 k) (P : Public) (mac : InputMac) :
    Guess.AsksOnly a (GadAt input P mac A) (shadowOnM P (BitInput.ofAffine input) mac) := by
  unfold shadowOnM
  refine Guess.AsksOnly.bind (Guess.AsksOnly.of_queryOnly (OnLaw.queryOnly_mono (OnLaw.notGadget_prefix _ _ _)
    (notGadget_gadAt input P mac A))) (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.bind ?_ (Guess.AsksOnly.pure' _)))
  · refine Guess.AsksOnly.of_queryOnly ?_
    unfold truePadsM
    have pad : ∀ (keys : WhiteningKeys) c i b, Hidden.QueryOnly (GadAt input P mac A)
        (Programs.padM keys c i b) := fun _ _ _ _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.ask _ trivial) fun _ => Hidden.QueryOnly.pure' _
    exact Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
      Hidden.QueryOnly.bind (Hidden.QueryOnly.vector _ fun _ => pad _ _ _ _) fun _ =>
        Hidden.QueryOnly.pure' _
  · rw [OnLaw.onCurveM_split]
    refine Guess.AsksOnly.bind_eq _ (Guess.AsksOnly.of_queryOnly (OnLaw.queryOnly_mono
      (OnLaw.notGadget_preM _ _ _) (notGadget_gadAt input P mac A))) rfl ?_
    unfold OnLaw.gadgetPart
    refine Guess.AsksOnly.bind ((Guess.AsksOnly.of_queryOnly (Guess.unlockM_asks _ _ _)).mono ?_)
      (Guess.AsksOnly.pure' _)
    rintro q ⟨o, κ, p, rfl⟩
    show _ = gpt input P mac A (o, κ, p)
    unfold gpt
    rw [preM_pads input a A dm hE hH P mac]

/-! ### 2. The translations are table values -/

/-- The fresh table values of the translations. -/
def wOf (P : Public) (mac : InputMac) (A : Table) (v : GPos → Block) : OtherIndex → Block := fun i =>
  match i.1 with
  | .gadget o κ p => gpt input P mac A (o, κ, p) ^^^ v (o, κ, p)
  | _ => 0

theorem freshPos_iff (K : FieldMacToECMac.SuccessfulOffsets) (k : GPos) :
    freshPos scalar K input k = true ↔ ¬ Planted scalar input K k.1 k.2.1 k.2.2 := by
  obtain ⟨o, κ, p⟩ := k
  have hk : Hidden.digitKey scalar K o = outputKeyOf scalar K o := rfl
  have planted : Planted scalar input K o κ p ↔ freshPos scalar K input (o, κ, p) = false := by
    rw [OnLaw.freshPos_false]
    show _ ↔ (digitEndomorphismBase (Hidden.digitKey scalar K o).digit).isSome = true ∧
      (inputBits input κ).getLsb p = Hidden.exceptionalBit scalar K o κ p
    unfold Hidden.exceptionalBit Planted
    rw [hk]
    generalize outputKeyOf scalar K o = key
    cases hphi : digitEndomorphismBase key.digit with
    | none => simp
    | some phi =>
        simp only [Option.isSome_some, true_and, Option.some.injEq, exists_eq_left']
        cases κ <;> exact eq_comm
  rw [planted, Bool.not_eq_false]

open Classical in
theorem freshen_other (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : OtherIndex → Block)
    (index : FixedIndex) (notGadget : ∀ o κ p, index ≠ .gadget o κ p) (x : Block) :
    tableAnswer (freshen scalar input K A w) (.fixedForward index x) = tableAnswer A (.fixedForward index x) := by
  by_cases hit : index ∈ Set.range siteIndex
  · obtain ⟨cell, rfl⟩ := hit
    rw [tableAnswer_site, tableAnswer_site]
    rfl
  · have first := tableAnswer_other (freshen scalar input K A w) ⟨index, hit⟩ x
    have second := tableAnswer_other A ⟨index, hit⟩ x
    refine first.trans (Eq.trans ?_ second.symm)
    show (if FreshQ scalar input K ⟨index, hit⟩ then w ⟨index, hit⟩ else A.2.2.1 ⟨index, hit⟩) =
      A.2.2.1 ⟨index, hit⟩
    rw [if_neg]
    unfold FreshQ
    cases index with
    | gadget o κ p => exact absurd rfl (notGadget o κ p)
    | hot _ _ _ _ _ => exact id
    | scale _ _ _ _ _ => exact id

open Classical in
theorem freshAnswer_table (K : FieldMacToECMac.SuccessfulOffsets) (P : Public) (mac : InputMac) (A : Table)
    (v : GPos → Block) :
    transcript (freshAnswer (freshPos scalar K input) v (tableAnswer A)) (shadowOnM P (BitInput.ofAffine input) mac) =
      transcript (tableAnswer (freshen scalar input K A (wOf input P mac A v)))
        (shadowOnM P (BitInput.ofAffine input) mac) := by
  have dm : DMOn (freshAnswer (freshPos scalar K input) v (tableAnswer A)) A.2.2.2 := fun cell x =>
    dmOn_table A cell x
  refine transcript_agree_asked _ _ (shadow_gadAt input _ A dm (fun _ _ => rfl) (fun _ => rfl) P mac)
    fun q agree => ?_
  cases q with
  | fixedForward index x =>
      cases index with
      | gadget o κ p =>
          have point : x = gpt input P mac A (o, κ, p) := agree
          have lhs : freshAnswer (freshPos scalar K input) v (tableAnswer A) (.fixedForward (.gadget o κ p) x) =
              if freshPos scalar K input (o, κ, p) then x ^^^ v (o, κ, p)
              else tableAnswer A (.fixedForward (.gadget o κ p) x) := rfl
          have rhs : tableAnswer (freshen scalar input K A (wOf input P mac A v)) (.fixedForward (.gadget o κ p) x) =
              if FreshQ scalar input K (gadgetAt o κ p) then gpt input P mac A (o, κ, p) ^^^ v (o, κ, p)
              else A.2.2.1 (gadgetAt o κ p) :=
            tableAnswer_other (freshen scalar input K A (wOf input P mac A v)) (gadgetAt o κ p) x
          have other : tableAnswer A (.fixedForward (.gadget o κ p) x) = A.2.2.1 (gadgetAt o κ p) :=
            tableAnswer_other A (gadgetAt o κ p) x
          have fresh : FreshQ scalar input K (gadgetAt o κ p) ↔ freshPos scalar K input (o, κ, p) = true :=
            (freshPos_iff scalar input K (o, κ, p)).symm
          rw [lhs, rhs]
          by_cases hf : freshPos scalar K input (o, κ, p) = true
          · rw [if_pos (fresh.mpr hf)]
            subst point
            simp [hf]
            rfl
          · rw [if_neg (fun h => hf (fresh.mp h)), ← other]
            simp [hf]
      | hot ℓ c f e h =>
          exact (freshen_other scalar input K A _ (.hot ℓ c f e h) (fun _ _ _ same => by cases same) x).symm
      | scale ℓ c s e b =>
          exact (freshen_other scalar input K A _ (.scale ℓ c s e b) (fun _ _ _ same => by cases same) x).symm
  | _ => rfl

/-! ### 3. C's form is `realTarget` -/

/-- Other answers from gadget values. -/
def extG (u : GPos → Block) : OtherIndex → Block := fun i =>
  match i.1 with
  | .gadget o κ p => u (o, κ, p)
  | _ => 0

open Classical in
theorem freshen_extG (K : FieldMacToECMac.SuccessfulOffsets) (A : Table) (w : OtherIndex → Block) :
    freshen scalar input K A w = freshen scalar input K A (extG (w ∘ gadIdx)) := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl))
  obtain ⟨index, hi⟩ := i
  show (if FreshQ scalar input K ⟨index, hi⟩ then w ⟨index, hi⟩ else A.2.2.1 ⟨index, hi⟩) =
    (if FreshQ scalar input K ⟨index, hi⟩ then extG (w ∘ gadIdx) ⟨index, hi⟩ else A.2.2.1 ⟨index, hi⟩)
  cases index with
  | gadget o κ p => rfl
  | hot _ _ _ _ _ => rw [if_neg (by unfold FreshQ; exact id), if_neg (by unfold FreshQ; exact id)]
  | scale _ _ _ _ _ => rw [if_neg (by unfold FreshQ; exact id), if_neg (by unfold FreshQ; exact id)]

include input in
theorem gadIdx_injective : Function.Injective gadIdx := fun g g' same =>
  Sum.inr_injective (voIdx_injective input (a₁ := .inr g) (a₂ := .inr g') same)

/-- Shifting gadget values by a fixed family. -/
def shiftG (c : GPos → Block) : (GPos → Block) ≃ (GPos → Block) where
  toFun v k := c k ^^^ v k
  invFun v k := c k ^^^ v k
  left_inv v := funext fun k => by simp [← BitVec.xor_assoc]
  right_inv v := funext fun k => by simp [← BitVec.xor_assoc]

theorem wOf_eq (P : Public) (mac : InputMac) (A : Table) (v : GPos → Block) :
    wOf input P mac A v = extG (shiftG (gpt input P mac A) v) := by
  funext i
  obtain ⟨index, hi⟩ := i
  cases index <;> rfl

/-- **C's garbler kernel is `realTarget`'s**, fresh translations as fresh table values. -/
theorem garbK_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞) (coins : Coins) (A : Table) :
    garbK scalar input Ψ coins A =
      ∑' w, PMF.uniformOfFintype (OtherIndex → Block) w *
        Ψ ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
          (Scheme.scheme.encode ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 input)
          (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
            (shadowOnM ((Programs.garbleM scalar coins).eval (tableAnswer A)).1 (BitInput.ofAffine input)
              (coins.inputMacKey.encode (BitInput.ofAffine input)))) LazyOracle.empty) := by
  have second : ((Programs.garbleM scalar coins).eval (tableAnswer A)).2 = coins.inputMacKey := by
    rw [garbleM_table]
  rw [second]
  unfold garbK
  set P := ((Programs.garbleM scalar coins).eval (tableAnswer A)).1
  set mac := coins.inputMacKey.encode (BitInput.ofAffine input)
  let F : (OtherIndex → Block) → ℝ≥0∞ := fun w => Ψ P (Scheme.scheme.encode coins.inputMacKey input)
    (plantAll (transcript (tableAnswer (freshen scalar input coins.offsets A w))
      (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty)
  have lhs : ∀ v, Ψ P (Scheme.scheme.encode coins.inputMacKey input)
      (plantAll (transcript (freshAnswer (freshPos scalar coins.offsets input) v (tableAnswer A))
        (shadowOnM P (BitInput.ofAffine input) mac)) LazyOracle.empty) =
      F (extG (shiftG (gpt input P mac A) v)) := fun v => by
    show _ = Ψ P _ _
    rw [freshAnswer_table, wOf_eq]
  rw [tsum_congr fun v => congrArg _ (lhs v)]
  have shift := tsum_equiv_uniform (shiftG (gpt input P mac A)).symm (fun u => F (extG u))
  rw [Equiv.symm_symm] at shift
  rw [← shift]
  have rhs : ∀ w, F w = F (extG (w ∘ gadIdx)) := fun w => by
    show Ψ P _ _ = Ψ P _ _
    rw [← freshen_extG]
  rw [tsum_congr fun w => congrArg _ (rhs w)]
  exact (tsum_restrict gadIdx (gadIdx_injective input) (fun u => F (extG u))).symm

open Classical in
/-- **C's garbler form is `realTarget`.** -/
theorem onGarbForm_eq (Ψ : Public → LamportSignature → LState → ℝ≥0∞) :
    onGarbForm scalar input Ψ = realTarget scalar input Ψ := by
  unfold onGarbForm realTarget
  simp only [garbK_eq scalar input Ψ]

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
