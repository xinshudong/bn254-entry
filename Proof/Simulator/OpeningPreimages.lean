/-
**The opening, step 4 (continued): all `273` preimages** (`Opening.preimages`).

The machine's nested `rep 91 (rep 3 preimageOne)` is the flat `rep 273` in `finProdFinEquiv`
(digit-major) order, and the draws are independent: `memSem_preimages` is the product of the `273`
multiplier draws, each `preimageLaw`'s own draw for its target, stored by `preMem`. The limbs of
`y_{d,c} + p · m_{d,c}` sit at `openLimb d c` (`preFold_limb`).
-/

import Proof.Simulator.OpeningPreimage

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Folds of point stores with one scratch write -/

omit [FieldCertificate] in
theorem foldStore_putPointX_off {α : Type} (step : Nat → Memory → α → Memory) (base : Nat → Nat)
    (extra : Word) (extraValue : α → Word) (encode : Nat → α → Word × Word × Word)
    (stores : ∀ index memory value, (step index memory value).ram =
      putPoint (Function.update memory.ram extra (extraValue value)) (base index)
        (encode index value)) :
    ∀ (count : Nat) (memory : Memory) (values : Fin count → α) (target : Word), target ≠ extra →
      (∀ index, index < count → ∀ position, position < 3 → target ≠ word (base index + position)) →
      (foldStore step count memory values).ram target = memory.ram target
  | 0, memory, _, _, _, _ => by rw [foldStore]
  | count + 1, memory, values, target, notExtra, away => by
      rw [foldStore, foldStore_putPointX_off (fun index => step (index + 1))
        (fun index => base (index + 1)) extra extraValue (fun index => encode (index + 1))
        (fun index => stores (index + 1)) count
        _ _ target notExtra (fun index bound => away (index + 1) (by omega)), stores,
        putPoint_off _ _ _ _ (away 0 (by omega)), Function.update_of_ne notExtra]

theorem foldStore_putPointX_at {α : Type} (step : Nat → Memory → α → Memory) (base : Nat → Nat)
    (extra : Word) (extraValue : α → Word) (encode : Nat → α → Word × Word × Word)
    (stores : ∀ index memory value, (step index memory value).ram =
      putPoint (Function.update memory.ram extra (extraValue value)) (base index)
        (encode index value)) :
    ∀ (count : Nat),
      (∀ index, index < count → base index + 2 < 2 ^ 256) →
      (∀ first second, first < count → second < count → first ≠ second →
        ∀ position position', position < 3 → position' < 3 →
          word (base first + position) ≠ word (base second + position')) →
      (∀ index, index < count → ∀ position, position < 3 → word (base index + position) ≠ extra) →
      ∀ (memory : Memory) (values : Fin count → α) (index : Fin count) (position : Nat),
        position < 3 →
        (foldStore step count memory values).ram (word (base index + position)) =
          wordAt (encode index (values index)) position
  | 0, _, _, _, _, _, index, _, _ => index.elim0
  | count + 1, small, distinct, away, memory, values, index, position, inside => by
      rw [foldStore]
      cases index using Fin.cases with
      | zero =>
          show (foldStore (fun index => step (index + 1)) count (step 0 memory (values 0))
            fun index => values index.succ).ram (word (base 0 + position)) = _
          rw [foldStore_putPointX_off (fun index => step (index + 1)) (fun index => base (index + 1))
            extra extraValue (fun index => encode (index + 1)) (fun index => stores (index + 1)) count
            _ _ _
            (away 0 (by omega) position inside)
            (fun later bound position' inside' =>
              distinct 0 (later + 1) (by omega) (by omega) (by omega) position position' inside inside'),
            stores, putPoint_at _ _ _ _ (small 0 (by omega)) inside]
          rfl
      | succ index =>
          have := foldStore_putPointX_at (fun index => step (index + 1)) (fun index => base (index + 1))
            extra extraValue (fun index => encode (index + 1)) (fun index => stores (index + 1)) count
            (fun index bound => small (index + 1) (by omega))
            (fun first second firstBound secondBound different =>
              distinct (first + 1) (second + 1) (by omega) (by omega) (by omega))
            (fun index bound => away (index + 1) (by omega))
            (step 0 memory (values 0)) (fun index => values index.succ) index position inside
          simpa only [Fin.val_succ] using this

/-! ### The 273 preimages -/

/-- The collector target of flat index `i` (digit `i / 3`, collector `i % 3`). -/
def targetAt (targets : Fin digitCount × Fin 3 → BaseField) (index : Nat) : BaseField :=
  if inside : index < digitCount * 3 then targets (finProdFinEquiv.symm ⟨index, inside⟩) else 0

theorem targetAt_val (targets : Fin digitCount × Fin 3 → BaseField) (index : Fin (digitCount * 3)) :
    targetAt targets index.val = targets (finProdFinEquiv.symm index) := by
  unfold targetAt
  rw [dif_pos index.isLt]

theorem targetAt_eq (targets : Fin digitCount × Fin 3 → BaseField) (index : Nat)
    (inside : index < digitCount * 3) :
    targetAt targets index = targets (⟨index / 3, by unfold digitCount at inside ⊢; omega⟩,
      ⟨index % 3, by omega⟩) := by
  unfold targetAt
  rw [dif_pos inside, finProdFinEquiv_symm_apply]
  rfl

/-- The store of flat preimage `i`. -/
def preStep (targets : Fin digitCount × Fin 3 → BaseField) (index : Nat) (memory : Memory)
    (mult : Nat) : Memory :=
  preMem (index / 3) (index % 3) (targetAt targets index) memory mult

omit [FieldCertificate] in
theorem openLimb_flat (index block : Nat) :
    openLimb (index / 3) (index % 3) 0 + block = openBase + 2000 + 3 * index + block := by
  unfold openLimb; omega

/-- **The preimages**: `273` independent multiplier draws, one per target, in digit-major order. -/
theorem memSem_preimages (memory : Memory) (targets : Fin digitCount × Fin 3 → BaseField)
    (cells : ∀ (digit : Fin digitCount) (collector : Fin 3),
      memory.ram (word (openTarget digit collector)) = fieldWord (targets (digit, collector))) :
    Opening.preimages.memSem memory =
      (optionProduct (digitCount * 3) fun index => rejectLaw multiplierWidth
          (fun candidate => decide (candidate < multBound (targets (finProdFinEquiv.symm index))))
          attempts).map
        (Option.map (foldStore (preStep targets) (digitCount * 3) memory)) := by
  have holdsStart : ∀ index, index < digitCount * 3 →
      memory.ram (word (openTarget (index / 3) (index % 3))) = fieldWord (targetAt targets index) := by
    intro index inside
    rw [targetAt_eq targets index inside]
    exact cells ⟨index / 3, by unfold digitCount at inside ⊢; omega⟩ ⟨index % 3, by omega⟩
  unfold Opening.preimages
  rw [memSem_rep_nest 3 (fun digit collector => Opening.preimageOne digit collector) (by norm_num) 91
    memory]
  change (Prog.rep (digitCount * 3) _).memSem memory = _
  have lawIs : (fun index : Fin (digitCount * 3) => rejectLaw multiplierWidth
      (fun candidate => decide (candidate < multBound (targets (finProdFinEquiv.symm index))))
      attempts) = fun index : Fin (digitCount * 3) => rejectLaw multiplierWidth
      (fun candidate => decide (candidate < multBound (targetAt targets index.val))) attempts := by
    funext index
    rw [targetAt_val]
  rw [lawIs]
  exact memSem_rep_law_idx (fun later => ∀ index, index < digitCount * 3 →
      later.ram (word (openTarget (index / 3) (index % 3))) = fieldWord (targetAt targets index))
    (digitCount * 3) (fun index => rejectLaw multiplierWidth
      (fun candidate => decide (candidate < multBound (targetAt targets index))) attempts)
    _ (preStep targets)
    (fun index bound later holds => memSem_preimageOne (index / 3) (index % 3)
      (by unfold digitCount at bound; omega) (by omega)
      later (targetAt targets index) (holds index bound))
    (fun index bound later mult holds other otherBound => by
      unfold digitCount at otherBound bound
      unfold preStep preMem
      rw [(clearRegs_other _ _).1, withRam_ram,
        putPoint_off _ _ _ _ (fun position inside => by addr_ne),
        Function.update_of_ne (by addr_ne), holds other otherBound])
    memory holdsStart

theorem preStep_ram (targets : Fin digitCount × Fin 3 → BaseField) (index : Nat) (memory : Memory)
    (mult : Nat) : (preStep targets index memory mult).ram =
      putPoint (Function.update memory.ram (word tmpM) (word mult))
        (openBase + 2000 + 3 * index) (limbWords ((targetAt targets index).val + pNat * mult)) := by
  unfold preStep preMem
  rw [(clearRegs_other _ _).1, withRam_ram, show openLimb (index / 3) (index % 3) 0 =
    openBase + 2000 + 3 * index by unfold openLimb; omega]

theorem preFold_bits (targets : Fin digitCount × Fin 3 → BaseField) (memory : Memory)
    (mults : Fin (digitCount * 3) → Nat) :
    (foldStore (preStep targets) (digitCount * 3) memory mults).bits = memory.bits :=
  foldStore_bits _ (fun index later mult => by
    unfold preStep preMem; rw [(clearRegs_other _ _).2]; rfl) _ _ _

theorem preFold_sameOff (targets : Fin digitCount × Fin 3 → BaseField) (memory : Memory)
    (mults : Fin (digitCount * 3) → Nat) :
    SameOff memory.ram (foldStore (preStep targets) (digitCount * 3) memory mults).ram :=
  foldStore_invariant (fun later => SameOff memory.ram later.ram) _ (digitCount * 3)
    (fun index bound later mult previous => previous.trans (by
      rw [preStep_ram]
      have bound' : index < 273 := bound
      refine (sameOff_update later.ram (Or.inr rfl) (word mult)).trans ?_
      have step := sameOff_putPoint (Function.update later.ram (word tmpM) (word mult))
        (2000 + 3 * index) (by omega) (limbWords ((targetAt targets index).val + pNat * mult))
      rw [← Nat.add_assoc] at step
      exact step)) memory mults (SameOff.refl _)

/-- **The limbs** of every target's preimage sit at `openLimb d c`. -/
theorem preFold_limb (targets : Fin digitCount × Fin 3 → BaseField) (memory : Memory)
    (mults : Fin (digitCount * 3) → Nat) (index : Fin (digitCount * 3)) (block : Nat)
    (inside : block < 3) :
    (foldStore (preStep targets) (digitCount * 3) memory mults).ram
        (word (openBase + 2000 + 3 * index.val + block)) =
      wordAt (limbWords ((targets (finProdFinEquiv.symm index)).val + pNat * mults index)) block := by
  rw [← targetAt_val targets index]
  exact foldStore_putPointX_at (preStep targets) (fun index => openBase + 2000 + 3 * index)
    (word tmpM) word (fun index mult => limbWords ((targetAt targets index).val + pNat * mult))
    (fun later memory mult => by rw [preStep_ram]) (digitCount * 3)
    (fun index bound => by unfold openBase; unfold digitCount at bound; omega)
    (fun first second firstBound secondBound different position position' inside inside' =>
      word_ne (by unfold openBase; unfold digitCount at firstBound; omega)
        (by unfold openBase; unfold digitCount at secondBound; omega) (by omega))
    (fun index bound position inside' => by
      unfold digitCount at bound
      apply word_ne <;> (try simp only [openBase, tmpM, tmpBase]) <;> omega)
    memory mults index block inside

/-- **The abstract preimage draw, factored through the multiplier draws**: P3's `preimages` of the
machine's samplers is the product of the same `273` rejection draws, mapped to the limbs of
`y + p · m`. -/
theorem preimages_eq [GroupCertificate] (targets : Fin digitCount × Fin 3 → BaseField) :
    preimages boundedSamplers targets =
      (optionProduct (digitCount * 3) fun index => rejectLaw multiplierWidth
          (fun candidate => decide (candidate < multBound (targets (finProdFinEquiv.symm index))))
          attempts).map
        (Option.map fun mults site =>
          limbs ((targets site).val + baseFieldModulus * mults (finProdFinEquiv site))) := by
  unfold preimages
  simp only [boundedSamplers, preimageLaw]
  rw [optionProduct_map_idx (digitCount * 3) _
    (fun index multiplier => limbs ((targets (finProdFinEquiv.symm index)).val +
      baseFieldModulus * multiplier)), PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun drawn => ?_)
  cases drawn with
  | none => rfl
  | some mults =>
      simp only [Function.comp_apply, Option.map_some, Equiv.symm_apply_apply]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
