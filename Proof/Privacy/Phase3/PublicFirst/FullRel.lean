/-
**Phase 3, P1e — the dominance extensions: planting on every component, and through the
simulator's refill runner.**

P1d's `plant_ge` plants EncPRF pairs only and runs an `OracleProgram` by `LazyOracle.run`. The
middle game `M` of `G1U → HW` runs the simulator's whole stage-2 path (P4's refill runner:
interception, first-touch programs, lazy queries of every kind) on a **private** empty oracle and
compares it with `HW`, which runs the same path on the stage-1 state `σ₁`. Seen from the path,
`σ₁` is a *planted* state on top of the private one, on every component:

* `FullRel planted sF sL` — `sF` is `sL` with all of `planted`'s pairs on top: every fixed-key and
  EncPRF permutation is `SparseRel`, and the hash table is `HashRel` (planted keys are fresh in
  `sL`, lookups overlay);
* `FullTouch` — a query touches `planted` (a planted input, a fresh answer on a planted output, a
  planted hash key); a program `x ↦ y` touches it when `x` is planted or `y` a planted output;
* `full_query_step` — one lazy query of any kind, planted first against planted later with touches
  charged `0` later (`sparse_forward_step`, `sparse_inverse_step`, `hash_step`);
* `program_fixed_rel` — off a touch a fixed-key program succeeds on both sides or fails on both,
  and keeps the relation;
* `runRefillFlag` — P4's `runRefill` stopped (`none`) at the first touching query or program;
  **`runRefill_ge`**: it is dominated, outcome by outcome, by `runRefill` on the planted state.
-/

import Proof.Privacy.Phase3.PublicFirst.Plant
import Proof.Privacy.Phase3.Lazy.Refill

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open Cryptography GarbledCircuit
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Sums against binds -/

theorem tsum_bind_mul {α β : Type} (μ : PMF α) (f : α → PMF β) (h : β → ℝ≥0∞) :
    ∑' o, (μ.bind f) o * h o = ∑' a, μ a * ∑' o, f a o * h o := by
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun o => ?_
  ring

theorem tsum_pure_mul {α : Type} (a : α) (h : α → ℝ≥0∞) : ∑' o, PMF.pure a o * h o = h a := by
  classical
  rw [tsum_eq_single a]
  · simp
  · intro o different
    simp [PMF.pure_apply, different]

/-! ### The hash table -/

section Hash

variable {n : ℕ}

/-- The hash table `F` is `L` with `P`'s pairs on top, on keys fresh in `L`. -/
structure HashRel (F L P : HashTable BN254.BaseField n) : Prop where
  lookup : ∀ k, F.lookup k = overlay (P.lookup k) (L.lookup k)
  fresh : ∀ k, P.lookup k ≠ none → L.lookup k = none

theorem HashRel.cons {F L P : HashTable BN254.BaseField n} (rel : HashRel F L P)
    (k : BN254.BaseField) (v : Fin n) (notPlanted : P.lookup k = none) :
    HashRel ((k, v) :: F) ((k, v) :: L) P where
  lookup k' := by
    by_cases same : k' = k
    · subst same
      simp [List.lookup, notPlanted]
    · have different : (k' == k) = false := by simpa [beq_iff_eq] using same
      simp only [List.lookup, different]
      exact rel.lookup k'
  fresh k' planted := by
    have different : k' ≠ k := fun same => planted (same ▸ notPlanted)
    have beqFalse : (k' == k) = false := by simpa [beq_iff_eq] using different
    simp only [List.lookup, beqFalse]
    exact rel.fresh k' planted

/-- **One hash query off the planted keys.** -/
theorem hash_step (positive : 0 < n) {F L P : HashTable BN254.BaseField n} (rel : HashRel F L P)
    (k : BN254.BaseField) (notPlanted : P.lookup k = none)
    (hF hL : Fin n × HashTable BN254.BaseField n → ℝ≥0∞)
    (mono : ∀ v F' L', HashRel F' L' P → hL (v, L') ≤ hF (v, F')) :
    ∑' o, (L.query positive k).distribution o * hL o
      ≤ ∑' o, (F.query positive k).distribution o * hF o := by
  have same : F.lookup k = L.lookup k := by rw [rel.lookup, notPlanted, overlay_none]
  unfold HashTable.query
  rw [same]
  cases found : L.lookup k with
  | some v =>
    simp only [Draw.distribution, tsum_pure_mul]
    exact mono v F L rel
  | none =>
    simp only [Draw.distribution]
    rw [tsum_map_mul, tsum_map_mul]
    exact ENNReal.tsum_le_tsum fun v =>
      mul_le_mul' le_rfl (mono v _ _ (rel.cons k v notPlanted))

end Hash

/-! ### Whole states -/

section Generic

variable {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]

/-- `sF` is `sL` with all of `planted`'s pairs on top, on every component. -/
structure FullRel (planted sF sL : LazyOracle.State FixedIndex EncIndex) : Prop where
  fixed : ∀ index, SparseRel (sF.fixed index) (sL.fixed index) (lk (planted.fixed index))
    (lk (planted.fixed index).reverse)
  enc : ∀ index, SparseRel (sF.enc index) (sL.enc index) (lk (planted.enc index))
    (lk (planted.enc index).reverse)
  hash : HashRel sF.hash sL.hash planted.hash

/-- A query answered `answer` touches the planted pairs. -/
def FullTouch (planted : LazyOracle.State FixedIndex EncIndex) :
    (request : PublicQuery FixedIndex EncIndex) → request.Answer → Prop
  | .fixedForward index input, answer =>
      TouchForward (lk (planted.fixed index)) (lk (planted.fixed index).reverse) input.toFin
        answer.toFin
  | .fixedInverse index output, answer =>
      TouchForward (lk (planted.fixed index).reverse) (lk (planted.fixed index)) output.toFin
        answer.toFin
  | .encForward index input, answer =>
      TouchForward (lk (planted.enc index)) (lk (planted.enc index).reverse) input.toFin
        answer.toFin
  | .encInverse index output, answer =>
      TouchForward (lk (planted.enc index).reverse) (lk (planted.enc index)) output.toFin
        answer.toFin
  | .hash input, _ => planted.hash.lookup input ≠ none

instance (planted : LazyOracle.State FixedIndex EncIndex) (request : PublicQuery FixedIndex EncIndex)
    (answer : request.Answer) : Decidable (FullTouch planted request answer) := by
  cases request <;> unfold FullTouch <;> infer_instance

/-- **One lazy query of any kind**, planted first against planted later. -/
theorem full_query_step {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : FullRel planted sF sL) (request : PublicQuery FixedIndex EncIndex)
    (hF hL : request.Answer × LazyOracle.State FixedIndex EncIndex → ℝ≥0∞)
    (mono : ∀ a sF' sL', FullRel planted sF' sL' → hL (a, sL') ≤ hF (a, sF')) :
    ∑' o, LazyOracle.query request sL o * (if FullTouch planted request o.1 then 0 else hL o)
      ≤ ∑' o, LazyOracle.query request sF o * hF o := by
  classical
  cases request with
  | fixedForward index input =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_forward_step (rel.fixed index) input.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with fixed := Function.update sF.fixed index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with fixed := Function.update sL.fixed index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨fun other => ?_, rel.enc, rel.hash⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.fixed other
  | fixedInverse index output =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_inverse_step (rel.fixed index) output.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with fixed := Function.update sF.fixed index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with fixed := Function.update sL.fixed index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨fun other => ?_, rel.enc, rel.hash⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.fixed other
  | encForward index input =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_forward_step (rel.enc index) input.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with enc := Function.update sF.enc index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with enc := Function.update sL.enc index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨rel.fixed, fun other => ?_, rel.hash⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.enc other
  | encInverse index output =>
    simp only [LazyOracle.query]
    rw [tsum_map_mul, tsum_map_mul]
    refine sparse_inverse_step (rel.enc index) output.toFin
      (fun o => hF (BitVec.ofFin o.1, { sF with enc := Function.update sF.enc index o.2 }))
      (fun o => hL (BitVec.ofFin o.1, { sL with enc := Function.update sL.enc index o.2 }))
      (fun a sF' sL' related => mono _ _ _ ⟨rel.fixed, fun other => ?_, rel.hash⟩)
    by_cases same : other = index
    · subst same
      simpa using related
    · simpa [Function.update_of_ne same] using rel.enc other
  | hash input =>
    by_cases planted' : planted.hash.lookup input ≠ none
    · refine le_trans (le_of_eq ?_) zero_le
      refine ENNReal.tsum_eq_zero.mpr fun o => ?_
      rw [if_pos (show FullTouch planted (.hash input) o.1 from planted'), mul_zero]
    · have notPlanted : planted.hash.lookup input = none := not_not.mp planted'
      simp only [LazyOracle.query]
      rw [tsum_map_mul, tsum_map_mul]
      simp only [FullTouch, planted', if_false]
      exact hash_step Fintype.card_pos rel.hash input notPlanted _ _
        fun v F' L' related => mono _ _ _ ⟨rel.fixed, rel.enc, related⟩

/-- **A fixed-key program off a touch**: it succeeds on both sides, keeping the relation, or fails on
both. -/
theorem program_fixed_rel {planted sF sL : LazyOracle.State FixedIndex EncIndex}
    (rel : FullRel planted sF sL) (index : FixedIndex) (input answer : Block)
    (notTouch : ¬ FullTouch planted (.fixedForward index input) answer) :
    (∃ tF tL, LazyOracle.program (.fixedForward index input) answer sF = some tF ∧
        LazyOracle.program (.fixedForward index input) answer sL = some tL ∧
        FullRel planted tF tL) ∨
      (LazyOracle.program (.fixedForward index input) answer sF = none ∧
        LazyOracle.program (.fixedForward index input) answer sL = none) := by
  classical
  have r := rel.fixed index
  simp only [FullTouch, TouchForward, not_or, not_not] at notTouch
  obtain ⟨freshD, freshDinv⟩ := notTouch
  have inputIff : (sF.fixed index).knownInput input.toFin ↔ (sL.fixed index).knownInput input.toFin := by
    rw [knownInput_iff, knownInput_iff, r.lookup, freshD, overlay_none]
  have outputIff : (sF.fixed index).knownOutput answer.toFin ↔
      (sL.fixed index).knownOutput answer.toFin := by
    constructor
    · intro known
      rcases r.knownOutput_F known with inL | planted'
      · exact inL
      · exact absurd freshDinv planted'
    · exact r.knownOutput_L
  simp only [LazyOracle.program, LazyOracle.permutationProgram]
  by_cases fresh : ¬ (sL.fixed index).knownInput input.toFin ∧
      ¬ (sL.fixed index).knownOutput answer.toFin
  · have freshF : ¬ (sF.fixed index).knownInput input.toFin ∧
        ¬ (sF.fixed index).knownOutput answer.toFin := by
      rw [inputIff, outputIff]; exact fresh
    left
    rw [dif_pos freshF, dif_pos fresh]
    refine ⟨_, _, rfl, rfl, ⟨fun other => ?_, rel.enc, rel.hash⟩⟩
    by_cases same : other = index
    · subst same
      simp only [Function.update_self]
      exact r.extend input.toFin answer.toFin freshD fresh.1 freshF.1 fresh.2 freshF.2 freshDinv _ _
    · simpa [Function.update_of_ne same] using rel.fixed other
  · have staleF : ¬ (¬ (sF.fixed index).knownInput input.toFin ∧
        ¬ (sF.fixed index).knownOutput answer.toFin) := by
      rw [inputIff, outputIff]; exact fresh
    right
    rw [dif_neg staleF, dif_neg fresh]
    exact ⟨rfl, rfl⟩

end Generic

/-! ### The refill runner -/

section Refill

open BN254 Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Phase3.Glue (interceptAnswer recordAfter)
open Kriterion.ArgoMAC.Phase3.Lazy (LState Record Cell consumeCell refillAnswer touch runRefill
  consumeCell_spec)

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- **P4's refill runner, stopped at the first touch** (`none`); `some none` is the runner's own
abort. -/
def runRefillFlag (planted : LState) (bits : BitInput) (draw : Cell → PMF Block) {α : Type} :
    FreeQuery Programs.Spec α → LState → Record → Set FixedIndex →
      PMF (Option (Option (α × LState × Record)))
  | .pure value, oracle, record, _ => PMF.pure (some (some (value, oracle, record)))
  | .query request next, oracle, record, touched =>
      match interceptAnswer bits request with
      | some answer => runRefillFlag planted bits draw (next answer) oracle
          (recordAfter bits request record) touched
      | none => match consumeCell touched oracle request with
        | some cell => (draw cell).bind fun limb =>
            if FullTouch planted request (refillAnswer request limb) then PMF.pure none else
            match LazyOracle.program request (refillAnswer request limb) oracle with
            | none => PMF.pure (some none)
            | some updated => runRefillFlag planted bits draw (next (refillAnswer request limb))
                updated record (touch request touched)
        | none => (LazyOracle.query request oracle).bind fun answer =>
            if FullTouch planted request answer.1 then PMF.pure none else
            runRefillFlag planted bits draw (next answer.1) answer.2 record (touch request touched)

/-- A flagged outcome weighs `0`. -/
def flagged {β : Type} (h : β → ℝ≥0∞) : Option β → ℝ≥0∞
  | none => 0
  | some b => h b

/-- Off a planted input, the consuming rule reads the same on both sides. -/
theorem consumeCell_rel {planted sF sL : LState} (rel : FullRel planted sF sL)
    (touched : Set FixedIndex) (index : FixedIndex) (input : Block)
    (fresh : lk (planted.fixed index) input.toFin = none) :
    consumeCell touched sF (.fixedForward index input)
      = consumeCell touched sL (.fixedForward index input) := by
  have same : (sF.fixed index).knownInput input.toFin ↔ (sL.fixed index).knownInput input.toFin := by
    rw [knownInput_iff, knownInput_iff, (rel.fixed index).lookup, fresh, overlay_none]
  unfold consumeCell
  dsimp only
  congr 1
  exact propext (or_congr Iff.rfl same)

/-- **The refill runner, planted first against planted later.** -/
theorem runRefill_ge (planted : LState) (bits : BitInput) (draw : Cell → PMF Block) {α : Type}
    (hF hL : Option (α × LState × Record) → ℝ≥0∞) (abortLe : hL none ≤ hF none)
    (mono : ∀ a sF sL record, FullRel planted sF sL →
      hL (some (a, sL, record)) ≤ hF (some (a, sF, record)))
    (computation : FreeQuery Programs.Spec α) :
    ∀ (sF sL : LState) (record : Record) (touched : Set FixedIndex), FullRel planted sF sL →
      ∑' o, runRefillFlag planted bits draw computation sL record touched o * flagged hL o
        ≤ ∑' o, runRefill bits draw computation sF record touched o * hF o := by
  induction computation with
  | pure value =>
    intro sF sL record touched rel
    simp only [runRefillFlag, runRefill, tsum_pure_mul, flagged]
    exact mono value sF sL record rel
  | query request next ih =>
    intro sF sL record touched rel
    simp only [runRefillFlag, runRefill]
    cases intercept : interceptAnswer bits request with
    | some answer =>
      exact ih answer sF sL _ touched rel
    | none =>
      simp only
      -- the lazy branch, shared by every request that is not consumed
      have lazyStep : consumeCell touched sF request = none → consumeCell touched sL request = none →
          ∑' o, ((LazyOracle.query request sL).bind fun answer =>
              if FullTouch planted request answer.1 then PMF.pure none else
              runRefillFlag planted bits draw (next answer.1) answer.2 record
                (touch request touched)) o * flagged hL o
            ≤ ∑' o, ((LazyOracle.query request sF).bind fun answer =>
              runRefill bits draw (next answer.1) answer.2 record (touch request touched)) o
                * hF o := by
        intro _ _
        rw [tsum_bind_mul, tsum_bind_mul]
        refine le_trans (le_of_eq (tsum_congr fun o => ?_)) (full_query_step rel request
          (fun o => ∑' r, runRefill bits draw (next o.1) o.2 record (touch request touched) r * hF r)
          (fun o => ∑' r, runRefillFlag planted bits draw (next o.1) o.2 record
            (touch request touched) r * flagged hL r)
          (fun a sF' sL' related => ih a sF' sL' record _ related))
        congr 1
        split_ifs
        · simp [tsum_pure_mul, flagged]
        · rfl
      cases request with
      | fixedForward index input =>
        by_cases plantedInput : lk (planted.fixed index) input.toFin = none
        · rw [← consumeCell_rel rel touched index input plantedInput]
          cases consumed : consumeCell touched sF (.fixedForward index input) with
          | none =>
            have consumedL : consumeCell touched sL (.fixedForward index input) = none := by
              rw [← consumeCell_rel rel touched index input plantedInput]
              exact consumed
            exact lazyStep consumed consumedL
          | some cell =>
            simp only
            rw [tsum_bind_mul, tsum_bind_mul]
            refine ENNReal.tsum_le_tsum fun limb => mul_le_mul' le_rfl ?_
            by_cases touching : FullTouch planted (.fixedForward index input)
                (refillAnswer (.fixedForward index input) limb)
            · rw [if_pos touching, tsum_pure_mul]
              exact zero_le
            · rw [if_neg touching]
              rcases program_fixed_rel rel index input _ touching with
                ⟨tF, tL, successF, successL, related⟩ | ⟨failF, failL⟩
              · rw [successF, successL]
                exact ih _ tF tL record _ related
              · rw [failF, failL, tsum_pure_mul, tsum_pure_mul]
                exact abortLe
        · -- a planted input: every later branch is flagged
          refine le_trans (le_of_eq ?_) zero_le
          have touching : ∀ answer : Block,
              FullTouch planted (.fixedForward index input) answer :=
            fun answer => Or.inl plantedInput
          cases consumeCell touched sL (.fixedForward index input) with
          | none =>
            rw [tsum_bind_mul]
            refine ENNReal.tsum_eq_zero.mpr fun o => ?_
            rw [if_pos (touching o.1), tsum_pure_mul]
            simp [flagged]
          | some cell =>
            simp only
            rw [tsum_bind_mul]
            refine ENNReal.tsum_eq_zero.mpr fun limb => ?_
            rw [if_pos (touching (refillAnswer (.fixedForward index input) limb)), tsum_pure_mul]
            simp [flagged]
      | fixedInverse index output => exact lazyStep rfl rfl
      | encForward index input => exact lazyStep rfl rfl
      | encInverse index output => exact lazyStep rfl rfl
      | hash input => exact lazyStep rfl rfl

end Refill

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
