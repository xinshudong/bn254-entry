/-
**Phase 3, P4 — the installation failure, event by event.**

`programAll_fail`: when every request carries an input and the request indices are pairwise
distinct, a failed installation has a request whose input is already known at its index, or whose
programmed output (`limb xor input`) is already used there, **in the oracle the installation
started from**. Earlier programs act at other indices only. With `designated_recorded` (every
input present) and `designated_untouched` (the run leaves designated indices as stage 1 left them),
the failure mass of `I^U` is the mass of events (d), the input part, and (e), the output part,
against the stage-1 entries at the designated indices.
-/

import Proof.Privacy.Phase3.Lazy.Frame

set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [DecidableEq FixedIndex] [DecidableEq EncPRF.PermutationIndex]

/-- A request collides with the oracle: its input is known at its index, or its programmed output
is used there. -/
def Collides (oracle : LState) (request : FixedIndex × Option Block × Block) : Prop :=
  ∃ input, request.2.1 = some input ∧
    ((oracle.fixed request.1).knownInput input.toFin ∨
      (oracle.fixed request.1).knownOutput (request.2.2 ^^^ input).toFin)

/-- A rejected program is a collision. -/
theorem program_none (index : FixedIndex) (input answer : Block) (oracle : LState)
    (rejected : LazyOracle.program (.fixedForward index input) answer oracle = none) :
    (oracle.fixed index).knownInput input.toFin ∨ (oracle.fixed index).knownOutput answer.toFin := by
  simp only [LazyOracle.program, Option.map_eq_none_iff, LazyOracle.permutationProgram] at rejected
  split at rejected
  · cases rejected
  · rename_i fresh
    by_contra both
    exact fresh ⟨fun known => both (Or.inl known), fun known => both (Or.inr known)⟩

/-- **A failed installation is a collision against the starting oracle.** -/
theorem programAll_fail :
    ∀ (requests : List (FixedIndex × Option Block × Block)) (oracle : LState),
      (∀ request ∈ requests, request.2.1 ≠ none) → (requests.map Prod.fst).Nodup →
        programAll requests oracle = none → ∃ request ∈ requests, Collides oracle request
  | [], _, _, _, failed => by simp [programAll] at failed
  | (index, input, output) :: rest, oracle, present, distinct, failed => by
      cases input with
      | none => exact absurd rfl (present _ List.mem_cons_self)
      | some input =>
          simp only [programAll] at failed
          cases programmed : LazyOracle.program (.fixedForward index input) (output ^^^ input)
            oracle with
          | none =>
              exact ⟨_, List.mem_cons_self, input, rfl,
                program_none index input _ oracle programmed⟩
          | some updated =>
              rw [programmed, Option.bind_some] at failed
              simp only [List.map_cons, List.nodup_cons] at distinct
              obtain ⟨request, member, collides⟩ := programAll_fail rest updated
                (fun request member => present request (List.mem_cons_of_mem _ member))
                distinct.2 failed
              refine ⟨request, List.mem_cons_of_mem _ member, ?_⟩
              obtain ⟨input', same, hit⟩ := collides
              have away : request.1 ≠ index := fun equal =>
                distinct.1 (equal ▸ List.mem_map_of_mem member)
              refine ⟨input', same, ?_⟩
              rw [program_frame index input _ oracle updated programmed request.1 away] at hit
              exact hit

end

end Kriterion.ArgoMAC.Phase3.Lazy

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue

/-- The designated indices, as a function of (digit, collector, block), are injective. -/
theorem designatedIndex_injective (bits : BitInput) :
    Function.Injective fun slot : Fin digitCount × Fin 3 × Fin 3 =>
      designatedIndex bits slot.1 slot.2.1 slot.2.2 := by
  rintro ⟨digit, collector, block⟩ ⟨digit', collector', block'⟩ same
  have := candidateIndex_injective (a₁ := (digit, collector, block, designatedSwitch bits))
    (a₂ := (digit', collector', block', designatedSwitch bits)) same
  simp only [Prod.mk.injEq] at this
  obtain ⟨d, c, b, _⟩ := this
  subst d c b
  rfl

/-- **The 819 designated requests are at pairwise distinct indices.** -/
theorem programRequests_nodup (bits : BitInput) (record : Record)
    (blocks : Fin digitCount × Fin 3 → Block × Block × Block) :
    ((programRequests bits record blocks).map Prod.fst).Nodup := by
  have shape : (programRequests bits record blocks).map Prod.fst =
      ((List.finRange digitCount).flatMap fun digit => (List.finRange 3).flatMap fun collector =>
        (List.finRange 3).map fun block => (digit, collector, block)).map
          fun slot : Fin digitCount × Fin 3 × Fin 3 =>
            designatedIndex bits slot.1 slot.2.1 slot.2.2 := by
    simp [programRequests, List.map_flatMap, Function.comp_def]
  rw [shape]
  refine List.Nodup.map (designatedIndex_injective bits) ?_
  refine List.nodup_flatMap.mpr ⟨fun digit _ => List.nodup_flatMap.mpr ⟨fun collector _ =>
    (List.nodup_finRange 3).map fun _ _ same => by simpa using same, ?_⟩, ?_⟩
  · refine (List.nodup_finRange 3).pairwise_of_forall_ne fun first _ second _ different => ?_
    simp only [List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨block, rfl⟩ ⟨block', same⟩
    simp only [Prod.mk.injEq] at same
    exact different same.2.1.symm
  · refine (List.nodup_finRange digitCount).pairwise_of_forall_ne fun first _ second _ different => ?_
    simp only [List.disjoint_left, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨collector, block, rfl⟩ ⟨collector', block', same⟩
    simp only [Prod.mk.injEq] at same
    exact different same.1.symm

end Kriterion.ArgoMAC.Phase3.Lazy

namespace Kriterion.ArgoMAC.Phase3.Lazy

open BN254 Cryptography GarbledCircuit
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Phase3.Glue
open Kriterion.ArgoMAC.Security.Phase3 (simulatedRows)

noncomputable section

variable [FieldCertificate] [GroupCertificate] [DecidableEq FixedIndex]
  [DecidableEq EncPRF.PermutationIndex]

/-- **A failed installation of `I^U` is a collision with a stage-1 entry at a designated index**:
the recorded input `E*` is known there, or the programmed output `o_b xor E*` is used there, in
the oracle stage 1 left (events (d) and (e)). -/
theorem installInputs_fail_collides (table : Public) (input : AffineInput)
    (labels : LamportSignature) (target : Point) (oracle : LState)
    (inputs : Option (List (FixedIndex × Option Block × Block) × LState))
    (member : inputs ∈ (installInputs simulatedRows table input labels target oracle).support)
    (fails : FailsInstall inputs) :
    ∃ (digit : Fin digitCount) (collector block : Fin 3) (recorded output : Block),
      Collides oracle (designatedIndex (Lamport.restore input labels).input digit collector block,
        some recorded, output) := by
  obtain ⟨requests, final, rfl, failed⟩ := fails
  set bits := (Lamport.restore input labels).input
  unfold installInputs at member
  obtain ⟨ran, ranMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  cases ran with
  | none => simp at member
  | some ran =>
      obtain ⟨targets, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      cases targets with
      | none => simp at member
      | some targets =>
          obtain ⟨blocks, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          cases blocks with
          | none => simp at member
          | some blocks =>
              simp only [PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq,
                Prod.mk.injEq] at member
              obtain ⟨requestsEq, finalEq⟩ := member
              subst requestsEq finalEq
              have present : ∀ request ∈ programRequests bits ran.2.2 blocks,
                  request.2.1 ≠ none := by
                intro request requestMember
                simp only [programRequests, List.mem_flatMap, List.mem_map,
                  List.mem_finRange, true_and] at requestMember
                obtain ⟨digit, collector, block, rfl⟩ := requestMember
                exact designated_recorded table bits _ oracle digit collector block _ ranMember
                  ran rfl
              obtain ⟨request, requestMember, collides⟩ := programAll_fail _ _ present
                (programRequests_nodup bits ran.2.2 blocks) failed
              simp only [programRequests, List.mem_flatMap, List.mem_map,
                List.mem_finRange, true_and] at requestMember
              obtain ⟨digit, collector, block, rfl⟩ := requestMember
              obtain ⟨recorded, same, hit⟩ := collides
              refine ⟨digit, collector, block, recorded,
                limbAt block (blocks (digit, collector)), recorded, rfl, ?_⟩
              rw [designated_untouched table bits _ oracle _ ⟨digit, collector, block, rfl⟩ _
                ranMember ran rfl] at hit
              exact hit

end

end Kriterion.ArgoMAC.Phase3.Lazy
