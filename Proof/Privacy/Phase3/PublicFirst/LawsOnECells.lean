/-
**Phase 3, P1r — `LawOn`, step (E), part 7: the garbler's published value on a table, with the
hidden gadget answer at any position.**

P1n's `tablePub_cells` reads the garbler's published value on a table as F4's published cells, with
each digit's digest hidden at the fixed gadget position `(x, 0)`. On the curve the view contains the
garbler's gadget answers at the **agreeing** positions, so the hidden part must sit at a position
the view does not read; it depends on the output keys. Here the hidden indices take a gadget
position per digit (`hidW pos`), and the whole of P1n's reading is redone at `pos`:

* `regroupW`: the coins without their offsets, the other answers and the masks are the rest
  (`OuterW`: `ρ`, the labels, the other answers off the hidden ones) and F4's coins;
* `foldJoin_splitW`, `digest_splitW`: a fold join is its hidden gate half XOR the rest, a digest its
  hidden answer at `pos d` XOR the rest;
* **`tablePub_cellsW`**: the garbler's published value on a table is the source of F4's published
  cells at the context `ctxW` of the rest.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnETape

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

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)
  (pos : Fin digitCount → Coord × Fin PlanB.coordinateBits)

/-! ### 1. Hidden indices at a gadget position per digit -/

/-- The hidden coins' indices: the active parent's gate half per (lane, chunk), the gadget at
`pos d` per digit. -/
def hidW : HiddenIdx → OtherIndex
  | .inl p => hotOther p.1 p.2 1 (activeBit input p.1 p.2) false
  | .inr d => gadgetAt d (pos d).1 (pos d).2

theorem hidW_injective : Function.Injective (hidW input pos) := by
  rintro (⟨ℓ, c⟩ | d) (⟨ℓ', c'⟩ | d') same <;> have value := congrArg Subtype.val same <;>
    simp only [hidW, hotOther, gadgetAt, hotIndexNat, FixedIndex.hot.injEq, reduceCtorEq,
      FixedIndex.gadget.injEq] at value
  · obtain ⟨rfl, rfl, -⟩ := value
    rfl
  · obtain ⟨rfl, -⟩ := value
    rfl

/-- The other answers with the hidden ones zeroed. -/
def zeroW (rest : {i : OtherIndex // i ∉ Set.range (hidW input pos)} → Block) : OtherIndex → Block :=
  (splitAlong (hidW input pos) (hidW_injective input pos)).symm (fun _ => 0, rest)

theorem zeroW_hidden (rest : {i : OtherIndex // i ∉ Set.range (hidW input pos)} → Block) (h : HiddenIdx) :
    zeroW input pos rest (hidW input pos h) = 0 :=
  splitAlong_symm_image _ _ _ _ h

theorem zeroW_rest (v : OtherIndex → Block) (i : OtherIndex) (notHidden : i ∉ Set.range (hidW input pos)) :
    zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2 i = v i :=
  splitAlong_symm_rest _ _ _ _ ⟨i, notHidden⟩

theorem hot_not_hiddenW (lane : Lane) (chunk : Fin chunkCount) (e : Nat) (half : Bool)
    (off : ¬ (e = activeBit input lane chunk ∧ half = false)) (small : e < 2) :
    hotOther lane chunk 1 e half ∉ Set.range (hidW input pos) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;> have value := congrArg Subtype.val same <;>
    simp only [hidW, hotOther, gadgetAt, hotIndexNat, FixedIndex.hot.injEq, reduceCtorEq] at value
  obtain ⟨rfl, rfl, -, entry, rfl⟩ := value
  have bound := activeBit_lt input ℓ c
  simp only [Fin.mk.injEq, chunkBits] at entry
  exact off ⟨by omega, rfl⟩

theorem gadget_not_hiddenW (output : Fin digitCount) (κ : Coord) (p : Fin PlanB.coordinateBits)
    (off : (κ, p) ≠ pos output) : gadgetAt output κ p ∉ Set.range (hidW input pos) := by
  rintro ⟨(⟨ℓ, c⟩ | d), same⟩ <;> have value := congrArg Subtype.val same <;>
    simp only [hidW, hotOther, gadgetAt, hotIndexNat, reduceCtorEq] at value
  injection value with outputEq coordEq position
  subst outputEq
  exact off (Prod.ext coordEq.symm position.symm)

/-! ### 2. The fold joins and the digests -/

/-- **A fold join is its hidden gate half XOR the rest.** -/
theorem foldJoin_splitW (v : OtherIndex → Block) (lane : Lane) (chunk : Fin chunkCount) (zero : Block) :
    foldJoin v lane chunk zero = v (hidW input pos (.inl (lane, chunk))) ^^^
      foldJoin (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2)
        lane chunk zero := by
  have values : ∀ e (small : e < 2) half, ¬ (e = activeBit input lane chunk ∧ half = false) →
      zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2
        (hotOther lane chunk 1 e half) = v (hotOther lane chunk 1 e half) :=
    fun e small half off => zeroW_rest input pos v _ (hot_not_hiddenW input pos lane chunk e half off small)
  have hidden : zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2
      (hotOther lane chunk 1 (activeBit input lane chunk) false) = 0 :=
    zeroW_hidden input pos _ (.inl (lane, chunk))
  have which := activeBit_lt input lane chunk
  unfold foldJoin
  show _ = v (hotOther lane chunk 1 (activeBit input lane chunk) false) ^^^ _
  rcases (show activeBit input lane chunk = 0 ∨ activeBit input lane chunk = 1 by omega) with a | a
  · rw [a] at hidden ⊢
    rw [hidden, values 0 (by omega) true (by simp), values 1 (by omega) false (by simp [a]),
      values 1 (by omega) true (by simp)]
    refine xor_bits _ _ fun i => ?_
    simp only [BitVec.getLsbD_xor]
    cases (v (hotOther lane chunk 1 0 false)).getLsbD i <;> simp
  · rw [a] at hidden ⊢
    rw [hidden, values 0 (by omega) false (by simp [a]), values 0 (by omega) true (by simp),
      values 1 (by omega) true (by simp)]
    refine xor_bits _ _ fun i => ?_
    simp only [BitVec.getLsbD_xor]
    cases (v (hotOther lane chunk 1 1 false)).getLsbD i <;>
      cases (v (hotOther lane chunk 1 0 false)).getLsbD i <;> simp

theorem xorFold_splitAt {count : Nat} (skip : Fin count) (f g : Fin count → Block)
    (agree : ∀ i, i ≠ skip → f i = g i) :
    xorFold f = g skip ^^^ f skip ^^^ xorFold g := by
  rw [xorFold_split skip f, xorFold_split skip g,
    Programs.xorFoldExcept_congr skip f g agree]
  refine xor_bits _ _ fun i => ?_
  simp only [BitVec.getLsbD_xor]
  cases (xorFoldExcept skip g).getLsbD i <;> cases (f skip).getLsbD i <;>
    cases (g skip).getLsbD i <;> simp

theorem xorFold_hidden {n : Nat} (skip : Fin n) (a mac w : Fin n → Block) (hw : w skip = 0)
    (agree : ∀ i, i ≠ skip → w i = a i) :
    xorFold (fun i => a i ^^^ mac i) = a skip ^^^ xorFold (fun i => w i ^^^ mac i) := by
  rw [xorFold_split skip (fun i => a i ^^^ mac i), xorFold_split skip (fun i => w i ^^^ mac i),
    Programs.xorFoldExcept_congr skip (fun i => w i ^^^ mac i) (fun i => a i ^^^ mac i)
      (fun i off => by rw [agree i off]), hw]
  refine xor_bits _ _ fun j => ?_
  simp only [BitVec.getLsbD_xor]
  cases (a skip).getLsbD j <;> simp

/-- **A digest is its hidden gadget answer XOR the rest.** -/
theorem digest_splitW (v : OtherIndex → Block) (output : Fin digitCount) (mac : InputMac) :
    digest v output mac = v (hidW input pos (.inr output)) ^^^
      digest (zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2)
        output mac := by
  set w := zeroW input pos (splitAlong (hidW input pos) (hidW_injective input pos) v).2
  have atHidden : w (hidW input pos (.inr output)) = 0 := zeroW_hidden input pos _ (.inr output)
  have rest : ∀ (κ : Coord) (i : Fin coordinateBitCount), (κ, i) ≠ pos output →
      w (gadgetAt output κ i) = v (gadgetAt output κ i) := fun κ i off =>
    zeroW_rest input pos v _ (gadget_not_hiddenW input pos output κ i off)
  unfold digest
  rcases hpos : pos output with ⟨κ, p⟩
  have hidEq : hidW input pos (.inr output) = gadgetAt output κ p := by
    show gadgetAt output (pos output).1 (pos output).2 = _
    rw [hpos]
  rw [hidEq] at atHidden ⊢
  let p' : Fin coordinateBitCount := ⟨p.val, p.isLt⟩
  have sameIdx : ∀ κ' : Coord, gadgetAt output κ' p' = gadgetAt output κ' p := fun _ => rfl
  cases κ with
  | x =>
      have hx := xorFold_hidden p' (fun i => v (gadgetAt output .x i)) (fun i => mac.x.get i)
        (fun i => w (gadgetAt output .x i)) (by show w (gadgetAt output .x p') = 0; rw [sameIdx]; exact atHidden)
        (fun i off => rest .x i (by
          rw [hpos]
          intro same
          exact off (Fin.ext (congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same))))
      have ys : (fun index : Fin coordinateBitCount => w (gadgetAt output .y index) ^^^ mac.y.get index) =
          fun index => v (gadgetAt output .y index) ^^^ mac.y.get index :=
        funext fun index => by rw [rest .y index (by rw [hpos]; intro same; cases congrArg Prod.fst same)]
      beta_reduce at hx
      rw [hx, ys]
      show (v (gadgetAt output .x p) ^^^ _) ^^^ _ = _
      rw [BitVec.xor_assoc]
  | y =>
      have hy := xorFold_hidden p' (fun i => v (gadgetAt output .y i)) (fun i => mac.y.get i)
        (fun i => w (gadgetAt output .y i)) (by show w (gadgetAt output .y p') = 0; rw [sameIdx]; exact atHidden)
        (fun i off => rest .y i (by
          rw [hpos]
          intro same
          exact off (Fin.ext (congrArg (fun q : Coord × Fin PlanB.coordinateBits => q.2.val) same))))
      have xs : (fun index : Fin coordinateBitCount => w (gadgetAt output .x index) ^^^ mac.x.get index) =
          fun index => v (gadgetAt output .x index) ^^^ mac.x.get index :=
        funext fun index => by rw [rest .x index (by rw [hpos]; intro same; cases congrArg Prod.fst same)]
      beta_reduce at hy
      rw [hy, xs]
      show _ ^^^ (v (gadgetAt output .y p) ^^^ _) = v (gadgetAt output .y p) ^^^ (_ ^^^ _)
      refine xor_bits _ _ fun j => ?_
      simp only [BitVec.getLsbD_xor]
      cases (v (gadgetAt output .y p)).getLsbD j <;> simp

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
