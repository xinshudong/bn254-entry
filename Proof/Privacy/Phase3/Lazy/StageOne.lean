/-
**Phase 3, P4 — the adversary's first stage makes at most `q₁` entries at the mask-site indices.**

`siteUse oracle` counts the entries of the lazy oracle at the `N·3` mask-site indices (distinct
indices, `siteIndex_injective`). A lazy query adds at most one entry, at the one index it touches
(`query_siteUse_le`, from the library's `forward_used_le` / `inverse_used_le`), so a run of a
program with query budget `b` adds at most `b` (`run_siteUse_le`). The adversary's first stage
starts from the empty oracle (Plan B's stage 1 makes no oracle call), so it leaves at most `q₁`
such entries.
-/

import Proof.Privacy.Phase3.Lazy.GameBound

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.Phase3 (MaskSite siteIndex siteIndex_injective)
open scoped ENNReal

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- The entries of the lazy oracle at the mask-site indices. -/
def siteUse (oracle : LState) : ℕ := ∑ cell : Cell, (oracle.fixed (siteIndex cell)).used

/-- With nothing touched, the potential is the site entries. -/
theorem potential_empty (oracle : LState) : potential ∅ oracle = (siteUse oracle : ℝ≥0∞) := by
  classical
  unfold potential siteUse
  push_cast
  refine Finset.sum_congr rfl fun cell _ => ?_
  rw [if_neg (Set.notMem_empty _)]

/-- Replacing one sparse permutation by one at most one entry larger raises the site count by
at most one: at most one cell names that index. -/
theorem siteUse_update_le (fixed : FixedIndex → SparsePermutation (2 ^ 128)) (index : FixedIndex)
    (next : SparsePermutation (2 ^ 128)) (grow : next.used ≤ (fixed index).used + 1) :
    ∑ cell : Cell, (Function.update fixed index next (siteIndex cell)).used ≤
      ∑ cell : Cell, (fixed (siteIndex cell)).used + 1 := by
  have termwise : ∀ cell : Cell, (Function.update fixed index next (siteIndex cell)).used ≤
      (fixed (siteIndex cell)).used + (if siteIndex cell = index then 1 else 0) := by
    intro cell
    by_cases same : siteIndex cell = index
    · rw [same, Function.update_self, if_pos rfl]
      exact grow
    · rw [Function.update_of_ne same, if_neg same, Nat.add_zero]
  have atMostOne : (∑ cell : Cell, (if siteIndex cell = index then 1 else 0 : ℕ)) ≤ 1 := by
    by_cases found : ∃ named : Cell, siteIndex named = index
    · obtain ⟨named, siteNamed⟩ := found
      have reindex : ∀ cell : Cell, (if siteIndex cell = index then 1 else 0 : ℕ) =
          if cell = named then 1 else 0 := by
        intro cell
        by_cases same : cell = named
        · rw [if_pos same, if_pos (same ▸ siteNamed)]
        · rw [if_neg same, if_neg fun equal => same (siteIndex_injective (equal.trans siteNamed.symm))]
      rw [Finset.sum_congr rfl fun cell _ => reindex cell, Finset.sum_ite_eq' Finset.univ named,
        if_pos (Finset.mem_univ _)]
    · rw [Finset.sum_eq_zero fun cell _ => if_neg fun hit => found ⟨cell, hit⟩]
      exact Nat.zero_le _
  calc (∑ cell : Cell, (Function.update fixed index next (siteIndex cell)).used)
      ≤ ∑ cell : Cell, ((fixed (siteIndex cell)).used +
          (if siteIndex cell = index then 1 else 0)) := Finset.sum_le_sum fun cell _ => termwise cell
    _ = ∑ cell : Cell, (fixed (siteIndex cell)).used +
          ∑ cell : Cell, (if siteIndex cell = index then 1 else 0 : ℕ) := Finset.sum_add_distrib
    _ ≤ ∑ cell : Cell, (fixed (siteIndex cell)).used + 1 := Nat.add_le_add_left atMostOne _

/-- **A lazy query adds at most one site entry.** -/
theorem query_siteUse_le (request : Request) (oracle : LState)
    (answer : request.Answer × LState)
    (member : answer ∈ (LazyOracle.query request oracle).support) :
    siteUse answer.2 ≤ siteUse oracle + 1 := by
  cases request with
  | fixedForward index input =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact siteUse_update_le oracle.fixed index drawn.2
        ((oracle.fixed index).forward_used_le input.toFin drawn drawnMember)
  | fixedInverse index output =>
      obtain ⟨drawn, drawnMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact siteUse_update_le oracle.fixed index drawn.2
        ((oracle.fixed index).inverse_used_le output.toFin drawn drawnMember)
  | encForward _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | encInverse _ _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _
  | hash _ =>
      obtain ⟨drawn, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_succ _

/-- **A program with query budget `b` adds at most `b` site entries.** -/
theorem run_siteUse_le {Result : Type} {budget : ℕ}
    (program : OracleProgram (publicOracleSpec FixedIndex EncPRF.PermutationIndex) Result budget) :
    ∀ (oracle : LState) (result : Result × LState),
      result ∈ (LazyOracle.run program oracle).support → siteUse result.2 ≤ siteUse oracle + budget := by
  induction program with
  | pure distribution =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact Nat.le_add_right _ _
  | query request next ih =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨answer, answerMember, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      have step := query_siteUse_le request oracle answer answerMember
      have rest := ih answer.1 answer.2 result resultMember
      omega
  | sample distribution next ih =>
      intro oracle result member
      simp only [LazyOracle.run, runSampled] at member
      obtain ⟨value, _, resultMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih value oracle result resultMember

/-- The empty oracle has no entries. -/
theorem siteUse_empty : siteUse (LazyOracle.empty : LState) = 0 := by
  unfold siteUse
  exact Finset.sum_eq_zero fun _ _ => rfl

end

end Kriterion.ArgoMAC.Phase3.Lazy
