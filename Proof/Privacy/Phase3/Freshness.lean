/-
**Phase 3, P1, item 4 — the input-freshness bound of note §2.3, with the union over the switch.**

`B-review.md` (2): the note's `Pr[E* ∈ dom_i] ≤ n_i / (2^128 − n)` is false as stated, because the
adversary chooses `j* = α₀ xor 1` through its input `u` *after* stage 1, so "the" designated index
`i` is selected by the view. The fix is a union over the candidate switches.

### What is proved

* `selection_hit_le` — **the union.** For any selection rule (any function of the outcome), the
  selected candidate hits its set with probability at most the sum over all candidates.
* `selection_hit_counterexample` — **the unmultiplied bound is false.** Three candidates, each
  hitting with probability `1/3`, and a selection rule that hits with probability `1`: the union
  factor (the number of candidates) is attained, so no marginal per-candidate bound survives an
  adaptive choice without it.
* `designatedSwitch_bijective` — **the candidate count is `2 ^ chunkBits = 4`, not `3`.** As the
  adversary's `α₀` ranges over the four switches of chunk 0, `j* = α₀ xor 1` ranges over all four.
  The review's `2 ^ chunkBits − 1 = 3` counts the inactive switches of one *fixed* `α₀`.
* `candidateIndex_injective` — the `4 · 819 = 3276` candidate indices
  `scale(pointX, 0, k, 5d + slot(collector), b)` are pairwise distinct.
* `aggregate_hit_le` — **the honest constant.** If each (slot, candidate) hit has mass at most
  `ε · E[n_i]` at its own index `i` (`n_i` = stage-1 entries at `i`, `ε = 1/(2^128 − q₁)` from the
  candidate label's min-entropy), and the entries total at most `q₁`, then the input-freshness
  abort mass over **all** 819 designated programs is at most `ε · q₁`. The per-slot union costs a
  factor `4` only against a per-slot maximum; summed over the distinct candidate indices it costs
  nothing. So:

```
per slot:   Pr[E*_s ∈ dom] ≤ Σ_{k<4} ε · E[n_{i(s,k)}]            (union over 4 switches)
aggregate:  Pr[∃ s, E*_s ∈ dom] ≤ ε · q₁ = q₁ / (2^128 − q₁)       (coefficient 1)
```

**Stated per query** (`perQuery_hit_le`, `planB_perQuery_freshness_le`): each stage-1 query names
one index, and a designated index contains its switch `j*`, so it owns at most one candidate
(`owner_unique`); the collision mass is `≤ ε` per query, `≤ q₁ · ε` in all. The union over the
candidate switches would price a slot at `4`, not `3`; the `3` of P3's `abortError`
(`3 · q₁ / (2^128 − q₁)`) is implied by the per-query coefficient `1`, not by that union.
The output-freshness part (`o_b xor E*` outside the stage-1 range, the note's limb bound
`max_v Pr[o_b = v] ≤ 7 / M`) is **not** proved here.
-/

import Proof.Privacy.Phase3.JointExactness

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open scoped ENNReal

noncomputable section

/-! ### The union over an adaptively selected candidate -/

/-- **The union over the candidates.** Whatever rule selects the candidate — here any function of
the outcome, so in particular the adversary's choice of `u` after its stage-1 queries — the
selected candidate hits its set with probability at most the sum over all candidates. -/
theorem selection_hit_le {Ω A K : Type} [Fintype K] (law : PMF Ω) (select : Ω → K)
    (candidate : K → Ω → A) (hitSet : K → Ω → Set A) :
    law.toOuterMeasure {ω | candidate (select ω) ω ∈ hitSet (select ω) ω}
      ≤ ∑ k, law.toOuterMeasure {ω | candidate k ω ∈ hitSet k ω} := by
  have cover : {ω | candidate (select ω) ω ∈ hitSet (select ω) ω}
      ⊆ ⋃ k, {ω | candidate k ω ∈ hitSet k ω} := fun ω hit =>
    Set.mem_iUnion.mpr ⟨select ω, hit⟩
  exact le_trans (MeasureTheory.measure_mono cover) (MeasureTheory.measure_iUnion_fintype_le _ _)

/-- **The unmultiplied bound is false.** Three candidates hit with probability `1/3` each; the
selection "the one that hits" hits with probability `1`. -/
theorem selection_hit_counterexample :
    ∃ (law : PMF (Fin 3)) (select : Fin 3 → Fin 3) (candidate : Fin 3 → Fin 3 → Bool),
      (∀ k, law.toOuterMeasure {ω | candidate k ω = true} = 3⁻¹) ∧
      law.toOuterMeasure {ω | candidate (select ω) ω = true} = 1 := by
  refine ⟨PMF.uniformOfFintype (Fin 3), id, fun k ω => decide (k = ω), fun k => ?_, ?_⟩
  · have single : {ω : Fin 3 | decide (k = ω) = true} = {k} := by
      ext ω; simp [eq_comm]
    rw [single, PMF.toOuterMeasure_uniformOfFintype_apply]
    simp
  · have everything : {ω : Fin 3 | decide (id ω = ω) = true} = Set.univ := by
      ext ω; simp
    rw [everything, PMF.toOuterMeasure_apply_fintype]
    simp
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-! ### The Plan B candidates -/

/-- `j* = α₀ xor 1` is a bijection of the four switches: every switch is a candidate. -/
theorem designatedSwitch_bijective :
    Function.Bijective fun switch : Fin 4 => (⟨switch.val ^^^ 1, by
      have := switch.isLt
      exact Nat.xor_lt_two_pow (n := 2) this (by norm_num)⟩ : Fin 4) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, rfl⟩
  intro first second same
  have values := congrArg Fin.val same
  simp only at values
  apply Fin.ext
  have := congrArg (· ^^^ 1) values
  simpa [Nat.xor_assoc] using this

/-- There are `2 ^ chunkBits = 4` candidate switches per designated slot. -/
theorem candidateCount : Fintype.card (Fin (2 ^ chunkBits)) = 4 := by
  rw [Fintype.card_fin]; rfl

/-- A designated slot: (digit, collector, block). -/
abbrev DesignatedSlot := Fin digitCount × Fin 3 × Fin 3

/-- The three collectors, as `pointX` element slots of a digit. -/
def collectorOf : Fin 3 → XElement := ![.rowX_x9, .rowY_x9, .rowZ_x9]

theorem collectorOf_injective : Function.Injective collectorOf := by decide

/-- **The candidate index** of a slot at candidate switch `k`:
`scale(pointX, 0, k, 5d + slot(collector), b)`. -/
def candidateIndex (slot : DesignatedSlot) (switch : Fin (2 ^ chunkBits)) : FixedIndex :=
  scaleIndexOf (count := pointElementCountX) .pointX ⟨0, chunkCount_pos⟩ switch.val
    (xElementIndex slot.1 (collectorOf slot.2.1)) slot.2.2

/-- **The `4 · 819` candidate indices are pairwise distinct.** -/
theorem candidateIndex_injective :
    Function.Injective fun pair : DesignatedSlot × Fin (2 ^ chunkBits) =>
      candidateIndex pair.1 pair.2 := by
  rintro ⟨⟨digit, collector, block⟩, switch⟩ ⟨⟨digit', collector', block'⟩, switch'⟩ same
  obtain ⟨-, switchEq, elementEq, blockEq⟩ :=
    Pipeline.scaleIndexOf_injective (count := pointElementCountX) .pointX ⟨0, chunkCount_pos⟩
      ⟨0, chunkCount_pos⟩ switch.val switch'.val _ _ block block'
      Pipeline.pointElementCountX_le_elementCountX switch.isLt switch'.isLt same
  have pairEq := xElementIndex_injective (a₁ := (digit, collectorOf collector))
    (a₂ := (digit', collectorOf collector')) elementEq
  simp only [Prod.mk.injEq] at pairEq
  obtain ⟨digitEq, collectorEq⟩ := pairEq
  rw [digitEq, collectorOf_injective collectorEq, blockEq, Fin.ext switchEq]

/-! ### The aggregate bound -/

/-- The expected number of stage-1 entries at an index. -/
def expectedCount {Ω Index A : Type} (law : PMF Ω) (domain : Index → Ω → Finset A)
    (index : Index) : ℝ≥0∞ :=
  ∑' ω, law ω * ((domain index ω).card : ℝ≥0∞)

/-- **The aggregate input-freshness bound.** Distinct candidate indices; each (slot, candidate)
hit at most `ε` times the expected stage-1 count at its own index; at most `total` entries in all.
Then the selected candidates of all slots hit with total mass at most `ε · total`, for **any**
selection rule. -/
theorem aggregate_hit_le {Ω Slot K Index A : Type} [Fintype Slot] [Fintype K] [Fintype Index]
    (law : PMF Ω) (select : Slot → Ω → K) (index : Slot → K → Index)
    (distinct : Function.Injective fun pair : Slot × K => index pair.1 pair.2)
    (candidate : Slot → K → Ω → A) (domain : Index → Ω → Finset A) (ε : ℝ≥0∞) (total : ℕ)
    (fresh : ∀ slot k, law.toOuterMeasure {ω | candidate slot k ω ∈ domain (index slot k) ω}
      ≤ ε * expectedCount law domain (index slot k))
    (bounded : ∀ ω, ∑ i, (domain i ω).card ≤ total) :
    law.toOuterMeasure
        {ω | ∃ slot, candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω}
      ≤ ε * total := by
  classical
  have union : {ω | ∃ slot, candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω}
      = ⋃ slot, {ω | candidate slot (select slot ω) ω ∈ domain (index slot (select slot ω)) ω} := by
    ext ω; simp
  rw [union]
  refine le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun slot _ => selection_hit_le law (select slot)
    (candidate slot) (fun k ω => (domain (index slot k) ω : Set A))) ?_
  refine le_trans (Finset.sum_le_sum fun slot _ => Finset.sum_le_sum fun k _ => fresh slot k) ?_
  -- regroup: the candidate indices are distinct, so their expected counts sum to at most the
  -- expected total
  have perOutcome : ∀ ω, (∑ slot, ∑ k, ((domain (index slot k) ω).card : ℝ≥0∞)) ≤ total := by
    intro ω
    have regroup : (∑ slot, ∑ k, (domain (index slot k) ω).card)
        = ∑ pair : Slot × K, (domain (index pair.1 pair.2) ω).card := by
      rw [← Finset.sum_product']; rfl
    have image : (∑ pair : Slot × K, (domain (index pair.1 pair.2) ω).card)
        ≤ ∑ i, (domain i ω).card := by
      rw [← Finset.sum_image (f := fun i => (domain i ω).card)
        (fun first _ second _ same => distinct same)]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have natBound := le_trans (le_of_eq regroup) (le_trans image (bounded ω))
    exact_mod_cast natBound
  have swap : (∑ slot, ∑ k, ∑' ω, law ω * ((domain (index slot k) ω).card : ℝ≥0∞))
      = ∑' ω, ∑ slot, ∑ k, law ω * ((domain (index slot k) ω).card : ℝ≥0∞) := by
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc (∑ slot, ∑ k, ε * expectedCount law domain (index slot k))
      = ε * ∑' ω, law ω * (∑ slot, ∑ k, ((domain (index slot k) ω).card : ℝ≥0∞)) := by
        simp only [expectedCount, ← Finset.mul_sum]
        rw [swap]
        simp only [Finset.mul_sum]
    _ ≤ ε * ∑' ω, law ω * (total : ℝ≥0∞) := by
        gcongr with ω
        exact perOutcome ω
    _ = ε * total := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- **§2.3 fixed, at Plan B.** Whatever switch `j*` the adversary's input selects for each of the
`819` designated slots, if every (slot, candidate switch) input hits the stage-1 domain at its own
candidate index with mass at most `ε` times the expected stage-1 count there, and stage 1 makes at
most `q₁` entries, then the input-freshness failures of all `819` programs have total mass at most
`ε · q₁` — with `ε = 1 / (2^128 − q₁)` this is `q₁ / (2^128 − q₁)`. -/
theorem planB_inputFreshness_le {Ω : Type} (law : PMF Ω)
    (select : DesignatedSlot → Ω → Fin (2 ^ chunkBits))
    (candidate : DesignatedSlot → Fin (2 ^ chunkBits) → Ω → Block)
    (domain : FixedIndex → Ω → Finset Block) (ε : ℝ≥0∞) (stageOneQueries : ℕ)
    (fresh : ∀ slot switch, law.toOuterMeasure
        {ω | candidate slot switch ω ∈ domain (candidateIndex slot switch) ω}
      ≤ ε * expectedCount law domain (candidateIndex slot switch))
    (bounded : ∀ ω, ∑ index, (domain index ω).card ≤ stageOneQueries) :
    law.toOuterMeasure {ω | ∃ slot, candidate slot (select slot ω) ω
        ∈ domain (candidateIndex slot (select slot ω)) ω}
      ≤ ε * stageOneQueries :=
  aggregate_hit_le law select candidateIndex candidateIndex_injective candidate domain ε
    stageOneQueries fresh bounded

/-! ### The per-query form

The union over the candidate switches (`selection_hit_le`) is the wrong book-keeping for the
constant: it prices each slot at `4` candidates. The right one is **per stage-1 query**. A query
names one index, and a designated index `scale(pointX, 0, j*, 5d + slot(e), b)` *contains* its switch
`j*`, so every index belongs to at most one (slot, candidate switch) pair (`owner_unique`, from
`candidateIndex_injective`): a query can collide with **one** candidate label only. Hence the
collision mass is at most `ε` per query, and `q₁ · ε` in all, for every selection rule. -/

/-- **One owner per index.** A query index is the candidate index of at most one (slot, switch). -/
theorem owner_unique {Slot K Index : Type} (index : Slot → K → Index)
    (distinct : Function.Injective fun pair : Slot × K => index pair.1 pair.2)
    {slot slot' : Slot} {k k' : K} (same : index slot k = index slot' k') :
    slot = slot' ∧ k = k' := by
  have := @distinct (slot, k) (slot', k') same
  simp only [Prod.mk.injEq] at this
  exact this

/-- **The per-query collision bound.** Stage 1 makes `q` queries `(index, input)`. If each query
collides with the candidate label that owns its index with probability at most `ε`, then — for any
rule selecting each slot's switch after stage 1 — some slot's selected candidate is among the
stage-1 inputs at its own index with probability at most `q · ε`. -/
theorem perQuery_hit_le {Ω Slot K Index A : Type} (law : PMF Ω) (select : Slot → Ω → K)
    (index : Slot → K → Index) (candidate : Slot → K → Ω → A) (q : ℕ)
    (queries : Ω → Fin q → Index × A) (ε : ℝ≥0∞)
    (perQuery : ∀ t : Fin q, law.toOuterMeasure {ω | ∃ slot k,
        index slot k = (queries ω t).1 ∧ candidate slot k ω = (queries ω t).2} ≤ ε) :
    law.toOuterMeasure {ω | ∃ slot t, (queries ω t).1 = index slot (select slot ω)
        ∧ (queries ω t).2 = candidate slot (select slot ω) ω}
      ≤ q * ε := by
  have cover : {ω | ∃ slot t, (queries ω t).1 = index slot (select slot ω)
        ∧ (queries ω t).2 = candidate slot (select slot ω) ω}
      ⊆ ⋃ t, {ω | ∃ slot k, index slot k = (queries ω t).1 ∧ candidate slot k ω = (queries ω t).2} := by
    rintro ω ⟨slot, t, hitIndex, hitInput⟩
    exact Set.mem_iUnion.mpr ⟨t, slot, select slot ω, hitIndex.symm, hitInput.symm⟩
  refine le_trans (MeasureTheory.measure_mono cover)
    (le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_)
  refine le_trans (Finset.sum_le_sum fun t _ => perQuery t) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **§2.3 at Plan B, per query.** The 819 designated programs' input-freshness failures have total
mass at most `q₁ · ε` (`ε = 1/(2^128 − q₁)` from the candidate label's min-entropy before each
query): coefficient `1` per stage-1 query, whatever switch `j*` the adversary's input selects. The
per-query hypothesis concerns a single candidate, because each designated index owns one switch
(`owner_unique`). -/
theorem planB_perQuery_freshness_le {Ω : Type} (law : PMF Ω)
    (select : DesignatedSlot → Ω → Fin (2 ^ chunkBits))
    (candidate : DesignatedSlot → Fin (2 ^ chunkBits) → Ω → Block) (stageOneQueries : ℕ)
    (queries : Ω → Fin stageOneQueries → FixedIndex × Block) (ε : ℝ≥0∞)
    (perQuery : ∀ t, law.toOuterMeasure {ω | ∃ slot switch,
        candidateIndex slot switch = (queries ω t).1 ∧ candidate slot switch ω = (queries ω t).2}
      ≤ ε) :
    law.toOuterMeasure {ω | ∃ slot t, (queries ω t).1 = candidateIndex slot (select slot ω)
        ∧ (queries ω t).2 = candidate slot (select slot ω) ω}
      ≤ stageOneQueries * ε :=
  perQuery_hit_le law select candidateIndex candidate stageOneQueries queries ε perQuery

end

end Kriterion.ArgoMAC.Security.Phase3
