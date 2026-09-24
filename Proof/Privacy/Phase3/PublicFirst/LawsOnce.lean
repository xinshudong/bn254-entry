/-
**Phase 3, P1l — the two laws, part 4: system A asks each fixed-key index once.**

`systemAM` (the evaluator's two curve lanes) asks only forward fixed-key questions, at pairwise
distinct indices of the two curve lanes (`systemAM_once`): per (lane, chunk) the fold gates of the
paid step at the non-active parent (two halves) and the three limbs of every element of every
non-active switch. Hence (`LawsFill.runFill_once`) its fill run from a state empty at the curve
lanes is its run on a uniform table.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsFill

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.OperationalOracle
open scoped ENNReal

noncomputable section

/-! ### Index sets -/

/-- The fold gates of `(lane, chunk)` at steps below `n`. -/
def onceFoldSet (lane : Lane) (chunk : Fin chunkCount) (n : Nat) : Set FixedIndex :=
  {i | ∃ k < n, ∃ e < 2 ^ k, ∃ half, i = hotIndexNat lane chunk k e half}

/-- The scale indices of `(lane, chunk)`. -/
def onceMaskSet (lane : Lane) (chunk : Fin chunkCount) : Set FixedIndex :=
  {i | ∃ s e b, i = FixedIndex.scale lane chunk s e b}

/-- The fixed-key indices of `(lane, chunk)`. -/
def chunkSet (lane : Lane) (chunk : Fin chunkCount) : Set FixedIndex :=
  {i | ∃ f e h, i = FixedIndex.hot lane chunk f e h} ∪ onceMaskSet lane chunk

/-- The fixed-key indices of one lane. -/
def onceLaneSet (lane : Lane) : Set FixedIndex := ⋃ chunk, chunkSet lane chunk

theorem hotIndexNat_inj {lane : Lane} {chunk : Fin chunkCount} {k k' e e' : Nat} {h h' : Bool}
    (small : k < 2) (small' : k' < 2) (entry : e < 4) (entry' : e' < 4)
    (same : hotIndexNat lane chunk k e h = hotIndexNat lane chunk k' e' h') :
    k = k' ∧ e = e' ∧ h = h' := by
  simp only [hotIndexNat, FixedIndex.hot.injEq, Fin.mk.injEq] at same
  obtain ⟨_, _, fold, ent, half⟩ := same
  have c2 : chunkBits = 2 := rfl
  simp only [c2] at fold ent
  refine ⟨?_, ?_, half⟩
  · rwa [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt small'] at fold
  · have p : (2 : Nat) ^ 2 = 4 := rfl
    rw [p, Nat.mod_eq_of_lt entry, Nat.mod_eq_of_lt entry'] at ent
    exact ent


/-- A computation followed by a pure step. -/
theorem OnceIn.map {α β : Type} {X : Set FixedIndex} {c : FreeQuery Programs.Spec α}
    (once : OnceIn X c) (g : α → β) : OnceIn X (c >>= fun v => Pure.pure (g v)) :=
  (once.bind (fun v => OnceIn.pure' ∅ (g v)) (Set.disjoint_empty X)).mono (by
    rintro i (member | member)
    · exact member
    · exact member.elim)

/-! ### The fold -/

theorem once_foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (label : Block)
    (small : step < 2) (entrySmall : entry < 4) :
    OnceIn {i | ∃ half, i = hotIndexNat lane chunk step entry half}
      (Programs.foldMaskM lane chunk step entry label) := by
  have apart : Disjoint ({hotIndexNat lane chunk step entry false} : Set FixedIndex)
      {hotIndexNat lane chunk step entry true} := by
    rw [Set.disjoint_singleton]
    intro same
    exact Bool.false_ne_true (hotIndexNat_inj small small entrySmall entrySmall same).2.2
  have whole := (OnceIn.hashM (hotIndexNat lane chunk step entry false) label).bind
    (fun first => (OnceIn.hashM (hotIndexNat lane chunk step entry true) label).map
      (fun second => first ^^^ second)) apart
  refine whole.mono ?_
  rintro i (same | same)
  · exact ⟨false, same⟩
  · exact ⟨true, same⟩

theorem entry_lt_four {step : Nat} (small : step < 2) (e : Fin (2 ^ step)) : e.val < 4 := by
  have : 2 ^ step ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
  have := e.isLt
  omega

theorem once_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) (small : step < 2) :
    OnceIn {i | ∃ e < 2 ^ step, ∃ half, i = hotIndexNat lane chunk step e half}
      (Programs.evalStepM lane chunk step bitLabel join active parent) := by
  have each := OnceIn.vector (2 ^ step)
    (fun e => if e = active then ∅ else {i | ∃ half, i = hotIndexNat lane chunk step e.val half})
    (fun e => if e = active then Pure.pure 0 else Programs.foldMaskM lane chunk step e.val (parent e))
    (fun e => OnceIn.ite _ _ _ _
      (once_foldMaskM lane chunk step e.val (parent e) small (entry_lt_four small e)))
    (by
      intro e e' different
      by_cases he : e = active
      · rw [if_pos he]
        exact Set.empty_disjoint _
      by_cases he' : e' = active
      · rw [if_pos he']
        exact Set.disjoint_empty _
      rw [if_neg he, if_neg he', Set.disjoint_left]
      rintro i ⟨h, rfl⟩ ⟨h', same⟩
      exact different (Fin.ext (hotIndexNat_inj small small (entry_lt_four small e)
        (entry_lt_four small e') same).2.1))
  unfold Programs.evalStepM
  refine (each.map _).mono ?_
  intro i member
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp member
  by_cases active' : e = active
  · rw [if_pos active'] at he
    exact he.elim
  · rw [if_neg active'] at he
    obtain ⟨half, rfl⟩ := he
    exact ⟨e.val, e.isLt, half, rfl⟩

theorem once_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) : ∀ n, n ≤ 2 →
      OnceIn (onceFoldSet lane chunk n) (Programs.evalFoldM lane chunk value bitLabel join n)
  | 0, _ => OnceIn.pure' _ _
  | n + 1, bound => by
      have prefixOnce := once_evalFoldM lane chunk value bitLabel join n (by omega)
      have whole := prefixOnce.bind (fun previous => (once_evalStepM lane chunk n (bitLabel n)
        (join n) (activeAt value n) previous (by omega)).map (extendLevel n previous)) (by
          rw [Set.disjoint_left]
          rintro i ⟨k, hk, e, he, half, rfl⟩ ⟨e', he', half', same⟩
          have ek : e < 4 := lt_of_lt_of_le he (by
            have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
            omega)
          have en : e' < 4 := lt_of_lt_of_le he' (by
            have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
            omega)
          have := (hotIndexNat_inj (by omega) (by omega) ek en same).1
          omega)
      unfold Programs.evalFoldM
      refine whole.mono ?_
      rintro i (⟨k, hk, rest⟩ | ⟨e, he, half, rfl⟩)
      · exact ⟨k, by omega, rest⟩
      · exact ⟨n, by omega, e, he, half, rfl⟩

/-! ### The masks -/

theorem scaleIndexOf_inj {count : Nat} (fits : count ≤ elementCountX) {lane : Lane}
    {chunk : Fin chunkCount} {s s' : Nat} {e e' : Fin count} {b b' : Fin 3} (small : s < 4)
    (small' : s' < 4) (same : scaleIndexOf lane chunk s e b = scaleIndexOf lane chunk s' e' b') :
    s = s' ∧ e = e' ∧ b = b' := by
  rw [scaleIndexOf_eq lane chunk s e b (lt_of_lt_of_le e.isLt fits) small,
    scaleIndexOf_eq lane chunk s' e' b' (lt_of_lt_of_le e'.isLt fits) small'] at same
  obtain ⟨_, _, hs, he, hb⟩ := FixedIndex.scale.inj same
  exact ⟨Fin.mk.inj hs, Fin.ext (Fin.mk.inj he), hb⟩

theorem once_switchMaskM (count : Nat) (fits : count ≤ elementCountX) (lane : Lane)
    (chunk : Fin chunkCount) (s : Nat) (small : s < 4) (label : Block) :
    OnceIn {i | ∃ (e : Fin count) (b : Fin 3), i = scaleIndexOf lane chunk s e b}
      (Programs.switchMaskM count lane chunk s label) := by
  have element : ∀ e : Fin count, OnceIn {i | ∃ b : Fin 3, i = scaleIndexOf lane chunk s e b}
      (Programs.hashM (scaleIndexOf lane chunk s e 0) label >>= fun first =>
        Programs.hashM (scaleIndexOf lane chunk s e 1) label >>= fun second =>
          Programs.hashM (scaleIndexOf lane chunk s e 2) label >>= fun third =>
            Pure.pure (sampleFp first second third)) := by
    intro e
    have limbs : ∀ {b b' : Fin 3}, b ≠ b' →
        Disjoint ({scaleIndexOf lane chunk s e b} : Set FixedIndex) {scaleIndexOf lane chunk s e b'} := by
      intro b b' different
      rw [Set.disjoint_singleton]
      intro same
      exact different (scaleIndexOf_inj fits small small same).2.2
    have whole := (OnceIn.hashM (scaleIndexOf lane chunk s e 0) label).bind (fun first =>
      (OnceIn.hashM (scaleIndexOf lane chunk s e 1) label).bind (fun second =>
        (OnceIn.hashM (scaleIndexOf lane chunk s e 2) label).map
          (fun third => sampleFp first second third)) (limbs (by decide)))
      (Set.disjoint_union_right.mpr ⟨limbs (by decide), limbs (by decide)⟩)
    refine whole.mono ?_
    rintro i (same | same | same)
    · exact ⟨0, same⟩
    · exact ⟨1, same⟩
    · exact ⟨2, same⟩
  have each := OnceIn.vector count (fun e => {i | ∃ b : Fin 3, i = scaleIndexOf lane chunk s e b}) _
    element (by
      intro e e' different
      rw [Set.disjoint_left]
      rintro i ⟨b, rfl⟩ ⟨b', same⟩
      exact different (scaleIndexOf_inj fits small small same).2.1)
  unfold Programs.switchMaskM
  refine (each.map _).mono ?_
  intro i member
  obtain ⟨e, b, rfl⟩ := Set.mem_iUnion.mp member
  exact ⟨e, b, rfl⟩

theorem twoPow_chunkWidth_le (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkWidth chunk)) :
    switch.val < 4 := by
  have bound : 2 ^ chunkWidth chunk ≤ 2 ^ chunkBits :=
    Nat.pow_le_pow_right (by omega) (chunkWidth_le chunk)
  have lt := switch.isLt
  have c2 : chunkBits = 2 := rfl
  rw [c2] at bound
  omega

theorem once_evalMasksM (count : Nat) (fits : count ≤ elementCountX) (lane : Lane)
    (chunk : Fin chunkCount) (hot : HotLabels (chunkWidth chunk))
    (alpha : Fin (2 ^ chunkWidth chunk)) :
    OnceIn (onceMaskSet lane chunk)
      (Programs.evalMasksM count lane chunk (chunkWidth chunk) hot alpha) := by
  have each := OnceIn.vector (2 ^ chunkWidth chunk)
    (fun s => if s = alpha then ∅ else
      {i | ∃ (e : Fin count) (b : Fin 3), i = scaleIndexOf lane chunk s.val e b})
    (fun s => if s = alpha then Pure.pure fun _ => 0 else
      Programs.switchMaskM count lane chunk s.val (hot s))
    (fun s => OnceIn.ite _ _ _ _ (once_switchMaskM count fits lane chunk s.val
      (twoPow_chunkWidth_le chunk s) (hot s)))
    (by
      intro s s' different
      by_cases hs : s = alpha
      · rw [if_pos hs]
        exact Set.empty_disjoint _
      by_cases hs' : s' = alpha
      · rw [if_pos hs']
        exact Set.disjoint_empty _
      rw [if_neg hs, if_neg hs', Set.disjoint_left]
      rintro i ⟨e, b, rfl⟩ ⟨e', b', same⟩
      exact different (Fin.ext (scaleIndexOf_inj fits (twoPow_chunkWidth_le chunk s)
        (twoPow_chunkWidth_le chunk s') same).1))
  unfold Programs.evalMasksM
  refine (each.map _).mono ?_
  intro i member
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp member
  by_cases active : s = alpha
  · rw [if_pos active] at hs
    exact hs.elim
  · rw [if_neg active] at hs
    obtain ⟨e, b, rfl⟩ := hs
    rw [scaleIndexOf_eq lane chunk s.val e b (lt_of_lt_of_le e.isLt fits)
      (by have := twoPow_chunkWidth_le chunk s; unfold chunkBits; omega)]
    exact ⟨_, _, _, rfl⟩

/-! ### One chunk, one lane, system A -/

theorem once_evalChunkM (count : Nat) (fits : count ≤ elementCountX) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block)
    (chunk : Fin chunkCount) :
    OnceIn (chunkSet lane chunk) (Programs.evalChunkM count lane joins scale bits labels chunk) := by
  have fold := once_evalFoldM lane chunk (chunkValue bits chunk).toNat
    (labelAt (chunkLabels labels chunk)) (joinAt (hotSlice joins chunk)) (chunkWidth chunk)
    (by have := chunkWidth_le chunk; unfold chunkBits at this; omega)
  unfold Programs.evalChunkM
  refine (fold.bind (fun hot => (once_evalMasksM count fits lane chunk hot
    (chunkOf bits chunk)).map _) (by
      rw [Set.disjoint_left]
      rintro i ⟨k, _, e, _, half, rfl⟩ ⟨s, e', b, same⟩
      simp only [hotIndexNat] at same
      cases same)).mono ?_
  rintro i (⟨k, _, e, _, half, rfl⟩ | member)
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr member

theorem once_evalLaneM (count : Nat) (fits : count ≤ elementCountX) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block) :
    OnceIn (onceLaneSet lane) (Programs.evalLaneM count lane joins scale bits labels) := by
  unfold Programs.evalLaneM
  refine OnceIn.map (OnceIn.vector chunkCount (chunkSet lane) _
    (once_evalChunkM count fits lane joins scale bits labels) (by
      intro c c' different
      rw [Set.disjoint_left]
      rintro i (⟨f, e, h, rfl⟩ | ⟨s, e, b, rfl⟩) (⟨f', e', h', same⟩ | ⟨s', e', b', same⟩)
      all_goals first
        | (simp only [FixedIndex.hot.injEq] at same; exact different same.2.1)
        | (simp only [FixedIndex.scale.injEq] at same; exact different same.2.1)
        | cases same)) _

/-- **System A asks each fixed-key index at most once, all on the curve lanes.** -/
theorem once_systemAM (table : Public) (bits : BitInput) (mac : InputMac) :
    OnceIn (onceLaneSet .curveX ∪ onceLaneSet .curveY) (systemAM table bits mac) := by
  have lanes : Disjoint (onceLaneSet Lane.curveX) (onceLaneSet Lane.curveY) := by
    rw [Set.disjoint_left]
    intro i left right
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp left
    obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp right
    rcases hc with ⟨f, e, h, rfl⟩ | ⟨s, e, b, rfl⟩ <;>
      rcases hc' with ⟨f', e', h', same⟩ | ⟨s', e', b', same⟩ <;>
      first
        | (simp only [FixedIndex.hot.injEq] at same; cases same.1)
        | (simp only [FixedIndex.scale.injEq] at same; cases same.1)
        | cases same
  have fitsX : curveElementCountX ≤ elementCountX := by decide
  have fitsY : curveElementCountY ≤ elementCountX := by decide
  unfold systemAM
  exact (once_evalLaneM curveElementCountX fitsX .curveX table.curveXHot _
    (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x)).bind
      (fun _ => (once_evalLaneM curveElementCountY fitsY .curveY table.curveYHot _
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y)).map fun _ => ()) lanes

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
