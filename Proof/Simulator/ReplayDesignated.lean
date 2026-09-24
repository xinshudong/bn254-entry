/-
**The replay, the designated chunk (lane `pointX`, chunk `0`)** — first part.

* `rtree_designatedElements`: the machine's `91` designated digits are, as a tree, the `455`
  guarded elements in order (`guardedElement` is `element` off the collectors);
* `isDesignated_iff`: a scale index of lane `pointX`, chunk `0`, is designated exactly at the
  switch `j*` and a collector slot (`e mod 5 ∈ {1, 3, 4}`).
-/

import Proof.Simulator.ReplayLane

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

theorem rtree_seq_fun (first second : Prog) :
    rtree (.seq first second) = fun memory => bindOpt (rtree first memory) (rtree second) := rfl

theorem rtree_rep_five (body : Nat → Prog) (memory : Memory) :
    rtree (Prog.rep 5 body) memory =
      rtree (.seq (body 0) (.seq (body 1) (.seq (body 2) (.seq (body 3) (body 4))))) memory := by
  rw [Prog.rep, Prog.rep, Prog.rep, Prog.rep, Prog.rep, Prog.rep]
  simp only [rtree_seq, rtree_seq_fun, rtree_skip, bindOpt_pure, bindOpt_assoc]

omit [FieldCertificate] in
theorem isCollector_five (digit : Nat) :
    Replay.isCollector (5 * digit) = false ∧ Replay.isCollector (5 * digit + 2) = false := by
  simp only [Replay.isCollector]
  constructor <;> simp [Nat.add_mod]

theorem guarded_plain (spec : Replay.LaneSpec) (chunk switch index : Nat)
    (plain : Replay.isCollector index = false) :
    Replay.guardedElement ordF0 spec chunk switch index = Replay.element ordF0 spec chunk switch index := by
  unfold Replay.guardedElement
  rw [plain]
  rfl

/-- **The designated digits are the guarded elements.** -/
theorem rtree_designatedElements (spec : Replay.LaneSpec) (chunk switch : Nat) :
    ∀ (count : Nat) (memory : Memory),
      rtree (Prog.rep count fun digit => Replay.designatedDigit ordF0 spec chunk switch digit) memory =
        rtree (Prog.rep (5 * count) fun index =>
          Replay.guardedElement ordF0 spec chunk switch index) memory
  | 0, memory => by rw [Nat.mul_zero, Prog.rep, Prog.rep]
  | count + 1, memory => by
      rw [Prog.rep, rtree_seq, show 5 * (count + 1) = 5 * count + 5 by ring, tree_rep_add]
      have previous : rtree (Prog.rep count fun digit => Replay.designatedDigit ordF0 spec chunk switch digit) =
          rtree (Prog.rep (5 * count) fun index => Replay.guardedElement ordF0 spec chunk switch index) :=
        funext (rtree_designatedElements spec chunk switch count)
      have digit : rtree (Replay.designatedDigit ordF0 spec chunk switch count) =
          rtree (Prog.rep 5 fun index =>
            Replay.guardedElement ordF0 spec chunk switch (5 * count + index)) := by
        funext after
        rw [rtree_rep_five]
        obtain ⟨zero, two⟩ := isCollector_five count
        unfold Replay.designatedDigit
        simp only [Nat.add_zero]
        rw [guarded_plain spec chunk switch (5 * count) zero,
          guarded_plain spec chunk switch (5 * count + 2) two]
      rw [digit]
      exact congrArg (fun tree => bindOpt tree _) (congrFun previous memory)

/-! ### Which scale indices are designated -/

omit [FieldCertificate] in
theorem collectorElement_slot (collector : Fin 3) :
    ((collectorElement collector).slot.val = 1 ∧ collector.val = 0) ∨
      ((collectorElement collector).slot.val = 3 ∧ collector.val = 1) ∨
      ((collectorElement collector).slot.val = 4 ∧ collector.val = 2) := by
  fin_cases collector <;> simp [collectorElement, XElement.slot]

omit [FieldCertificate] in
/-- **The designated indices of chunk `0` of lane `pointX`.** -/
theorem isDesignated_iff (bits : BitInput) (switch : Nat) (switchSmall : switch < 4)
    (element : Fin pointElementCountX) (block : Fin 3) :
    IsDesignated bits (scaleIndexOf .pointX chunkZero switch element block) ↔
      switch = (designatedSwitch bits).val ∧ Replay.isCollector element.val = true := by
  have elementSmall : element.val < elementCountX := lt_of_lt_of_le element.isLt (by
    unfold pointElementCountX elementCountX; omega)
  constructor
  · rintro ⟨digit, collector, block', same⟩
    have jSmall : (designatedSwitch bits).val < 2 ^ chunkBits := (designatedSwitch bits).isLt
    have indexSmall : (xElementIndex digit (collectorElement collector)).val < elementCountX :=
      lt_of_lt_of_le (xElementIndex digit (collectorElement collector)).isLt (by
        unfold pointElementCountX elementCountX; omega)
    unfold designatedIndex at same
    rw [scaleIndexOf_eq _ _ _ _ _ indexSmall jSmall,
      scaleIndexOf_eq _ _ _ _ _ elementSmall (by unfold chunkBits; omega)] at same
    simp only [FixedIndex.scale.injEq, Fin.mk.injEq, true_and] at same
    obtain ⟨sameSwitch, sameElement, _⟩ := same
    refine ⟨sameSwitch.symm, ?_⟩
    rw [← sameElement]
    simp only [xElementIndex, xSlotsPerDigit, Replay.isCollector]
    rcases collectorElement_slot collector with ⟨slot, _⟩ | ⟨slot, _⟩ | ⟨slot, _⟩ <;>
      rw [slot] <;> simp [Nat.add_mod]
  · rintro ⟨sameSwitch, collector⟩
    have elementBound := element.isLt
    unfold pointElementCountX at elementBound
    have digitSmall : element.val / 5 < digitCount := by unfold digitCount; omega
    simp only [Replay.isCollector, Bool.or_eq_true, beq_iff_eq] at collector
    obtain ⟨c, slot⟩ : ∃ c : Fin 3, (collectorElement c).slot.val = element.val % 5 := by
      rcases collector with (one | three) | four
      · exact ⟨0, by simp [collectorElement, XElement.slot, one]⟩
      · exact ⟨1, by simp [collectorElement, XElement.slot, three]⟩
      · exact ⟨2, by simp [collectorElement, XElement.slot, four]⟩
    refine ⟨⟨element.val / 5, digitSmall⟩, c, block, ?_⟩
    have jSmall : (designatedSwitch bits).val < 2 ^ chunkBits := (designatedSwitch bits).isLt
    have sameIndex : xElementIndex ⟨element.val / 5, digitSmall⟩ (collectorElement c) = element :=
      Fin.ext (by simp only [xElementIndex, xSlotsPerDigit, slot]; omega)
    unfold designatedIndex
    rw [sameIndex, sameSwitch]

end

end Kriterion.ArgoMAC.PlanB.SimMachine
