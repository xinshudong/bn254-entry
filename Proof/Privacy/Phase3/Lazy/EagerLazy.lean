/-
**Phase 3, P4 — the `I^U` tape: from the mask tape to fresh uniform limbs.**

Two exact or data-processing steps on the refill runner, for an arbitrary query computation:

* `uniformMaskTape_etvDist_le` — **the per-mask bias, `N·δ₃`**: the `I^U` tape (masks uniform on
  `F_p`, the tape uniform on the fibre) is within `#MaskSite · δ₃` of a uniform tape. Both are the
  same fibre kernel behind two mask laws (P1's `uniform_eq_bind_fibreLaw`), so the distance is the
  masks' (`masksOf_etvDist_le`).
* `uniform_bind_runRefill` — **eager = lazy, exactly**: running on a uniform tape is running with a
  fresh uniform block drawn at each consumed cell. A cell is consumed only at an index not yet
  touched, and the index is touched from then on (`runRefill_tape_congr`: the run reads the tape
  only at untouched indices), so each cell is read at most once and its block is a fresh uniform
  block independent of everything read before (`uniform_update_eq`).
-/

import Proof.Privacy.Phase3.Lazy.Refill

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex siteIndex_injective masksOf fibreLaw
  uniform_eq_bind_fibreLaw masksOf_etvDist_le)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-! ### The per-mask bias -/

/-- **`I^U`'s tape is `N·δ₃`-close to a uniform tape.** -/
theorem uniformMaskTape_etvDist_le :
    uniformMaskTape.etvDist (PMF.uniformOfFintype Tape) ≤
      (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 := by
  calc uniformMaskTape.etvDist (PMF.uniformOfFintype Tape)
      = ((PMF.uniformOfFintype (MaskSite → BaseField)).bind
            (fibreLaw masksOf masksOf_surjective)).etvDist
          (((PMF.uniformOfFintype Tape).map masksOf).bind
            (fibreLaw masksOf masksOf_surjective)) := by
        rw [uniformMaskTape, ← uniform_eq_bind_fibreLaw]
    _ ≤ (PMF.uniformOfFintype (MaskSite → BaseField)).etvDist
          ((PMF.uniformOfFintype Tape).map masksOf) := PMF.etvDist_bind_right_le _ _ _
    _ = ((PMF.uniformOfFintype Tape).map masksOf).etvDist
          (PMF.uniformOfFintype (MaskSite → BaseField)) := PMF.etvDist_comm _ _
    _ ≤ (Fintype.card MaskSite : ℝ≥0∞) * Kriterion.ArgoMAC.Security.Phase3.delta3 :=
        masksOf_etvDist_le

/-! ### Locality: the run reads the tape only at untouched indices -/

/-- Two tapes that agree at every cell whose index is not yet touched give the same run. -/
theorem runRefill_tape_congr (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex) (first second : Tape),
      (∀ cell, siteIndex cell ∉ touched → first cell = second cell) →
      runRefill bits (fun cell => PMF.pure (first cell)) computation oracle record touched =
        runRefill bits (fun cell => PMF.pure (second cell)) computation oracle record touched := by
  induction computation with
  | pure value => intros; rfl
  | query request next ih =>
      intro oracle record touched first second agree
      have later : ∀ cell, siteIndex cell ∉ touch request touched → first cell = second cell :=
        fun cell notTouched => agree cell fun member => notTouched (subset_touch _ _ member)
      simp only [runRefill]
      split
      · exact ih _ _ _ _ _ _ agree
      · split
        · rename_i cell consumed
          obtain ⟨index, input, rfl, fresh, _, siteEq⟩ := consumeCell_spec consumed
          have same : first cell = second cell := agree cell (siteEq ▸ fresh)
          rw [same]
          congr 1
          funext limb
          split
          · rfl
          · exact ih _ _ _ _ _ _ later
        · congr 1
          funext answer
          exact ih _ _ _ _ _ _ later

/-! ### Eager = lazy -/

/-- Overwrite one cell: `(v, t) ↦ (t[cell := v], t cell)` is a bijection. -/
def updateEquiv (cell : Cell) : (Block × Tape) ≃ (Tape × Block) where
  toFun pair := (Function.update pair.2 cell pair.1, pair.2 cell)
  invFun pair := (pair.1 cell, Function.update pair.1 cell pair.2)
  left_inv pair := by
    obtain ⟨value, tape⟩ := pair
    simp
  right_inv pair := by
    obtain ⟨tape, value⟩ := pair
    simp

/-- **A uniform tape is a uniform block written over a uniform tape at any one cell.** -/
theorem uniform_update_eq (cell : Cell) :
    (PMF.uniformOfFintype (Block × Tape)).map (fun pair => Function.update pair.2 cell pair.1) =
      PMF.uniformOfFintype Tape := by
  have factor : (fun pair : Block × Tape => Function.update pair.2 cell pair.1) =
      Prod.fst ∘ updateEquiv cell := rfl
  rw [factor, ← PMF.map_comp, uniform_equiv (updateEquiv cell), uniform_map_fst]

/-- A uniform pair is two independent uniform draws. -/
theorem uniform_pair_bind {A B C : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (next : A × B → PMF C) :
    (PMF.uniformOfFintype (A × B)).bind next =
      (PMF.uniformOfFintype A).bind fun a => (PMF.uniformOfFintype B).bind fun b => next (a, b) := by
  rw [← uniform_product, PMF.bind_bind]
  congr 1
  funext a
  rw [PMF.bind_map]
  rfl

/-- **Eager = lazy.** A run on a uniform tape is the run that draws a fresh uniform block at each
consumed cell. -/
theorem uniform_bind_runRefill (bits : BitInput) {α : Type}
    (computation : FreeQuery Programs.Spec α) :
    ∀ (oracle : LState) (record : Record) (touched : Set FixedIndex),
      (PMF.uniformOfFintype Tape).bind (fun tape =>
          runRefill bits (fun cell => PMF.pure (tape cell)) computation oracle record touched) =
        runRefill bits (fun _ => PMF.uniformOfFintype Block) computation oracle record touched := by
  induction computation with
  | pure value =>
      intro oracle record touched
      exact PMF.bind_const _ _
  | query request next ih =>
      intro oracle record touched
      simp only [runRefill]
      split
      · exact ih _ _ _ _
      · split
        · rename_i cell consumed
          obtain ⟨index, input, rfl, fresh, _, siteEq⟩ := consumeCell_spec consumed
          simp only [PMF.pure_bind]
          -- write the uniform tape as a uniform block over a uniform tape at `cell`
          conv_lhs => rw [← uniform_update_eq cell, PMF.bind_map]
          have local_read : ∀ (limb : Block) (tape : Tape),
              (match LazyOracle.program (.fixedForward index input)
                  (refillAnswer (.fixedForward index input) limb) oracle with
                | none => PMF.pure none
                | some updated => runRefill bits
                    (fun cell' => PMF.pure (Function.update tape cell limb cell'))
                    (next (refillAnswer (.fixedForward index input) limb)) updated record
                    (touch (.fixedForward index input) touched)) =
              (match LazyOracle.program (.fixedForward index input)
                  (refillAnswer (.fixedForward index input) limb) oracle with
                | none => PMF.pure none
                | some updated => runRefill bits (fun cell' => PMF.pure (tape cell'))
                    (next (refillAnswer (.fixedForward index input) limb)) updated record
                    (touch (.fixedForward index input) touched)) := by
            intro limb tape
            split
            · rfl
            · refine runRefill_tape_congr bits _ _ _ _ _ _ fun cell' notTouched => ?_
              have different : cell' ≠ cell := by
                rintro rfl
                exact notTouched (Or.inr (by rw [siteEq]; rfl))
              exact Function.update_of_ne different _ _
          simp only [Function.comp_def, Function.update_self]
          refine (congrArg (PMF.bind (PMF.uniformOfFintype (Block × Tape)))
            (funext fun pair => local_read pair.1 pair.2)).trans ?_
          rw [uniform_pair_bind]
          congr 1
          funext limb
          split
          · rename_i hprog
            simp only [hprog]
            exact PMF.bind_const _ _
          · rename_i updated hprog
            simp only [hprog]
            exact ih _ _ _ _
        · rw [PMF.bind_comm]
          congr 1
          funext answer
          exact ih _ _ _ _

end

end Kriterion.ArgoMAC.Phase3.Lazy
