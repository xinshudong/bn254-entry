/-
**Phase 3, P1o — the coincidence guess, part 2: the tape families.**

Each coincidence event (`LawsGuessReach.lean`) is bounded given the stage-1 view `(P, enc)` by a
family of `swappedChallengeTape`-preserving, view-preserving maps under which the event holds for
at most `2` members out of `2^128` (`weighted_guess`):

* **event 1** (a level-1 coincidence of system B off the curve) and **event 3** (a gadget label off
  the curve): the `k₂`-family `familyKey2 0 g` (P1h) moves every garbler label of system B and of the
  gadget by `g`, and keeps the reach's (its pads are keyed by `hash(t_eval)`, `t_eval ≠ t`);
* **event 4** (a gadget collision on the curve): the `Δ`-family moves `pad₀ ⊕ pad₁ ⊕ Δ_κ` by `g`;
* **event 2** (a level-2 coincidence, no level-1 one): the new **transposition family**
  (`transAct`): the fold gate `(ℓ, c, 1, r', 0)` of the inactive parent is precomposed with the
  involution `τ_g` that fixes the garbler's point `G` and `G ⊕ g` and moves every other point by `g`.
  The garbler's transcript, hence the view and the swap kernel's points, are kept; the reach's
  one-hot labels move by `π(X) ⊕ π(τ_g X)` (`X ≠ G` the reach's level-1 label), which hits a given
  value for at most two `g`.
-/

import Proof.Privacy.Phase3.PublicFirst.LawsGuessReach

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (transcriptOf QueryOnly TapeShift shiftTape)
open scoped ENNReal

noncomputable section

/-! ### 1. A view-preserving family bounds a weighted guess -/

open Classical in
/-- **The weighted symmetry bound**: if a finite family of law-preserving, view-preserving maps
moves the event onto at most `k` members from every point, the event has mass at most
`k / #G` against every weight on the view. -/
theorem weighted_guess {Ω V G : Type} [Fintype G] (μ : PMF Ω) (view : Ω → V) (w : V → ℝ≥0∞)
    (event : Ω → Prop) (act : G → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω, (Finset.univ.filter fun g => event (act g ω)).card ≤ k) :
    (Fintype.card G : ℝ≥0∞) * ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) ≤
      k * ∑' ω, μ ω * w (view ω) := by
  have moved : ∀ g, ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) =
      ∑' ω, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) := by
    intro g
    conv_lhs => rw [← preserve g]
    rw [tsum_map_mul]
    simp only [sameView]
  calc (Fintype.card G : ℝ≥0∞) * ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)
      = ∑ g : G, ∑' ω, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) := by
        rw [Finset.sum_congr rfl fun g _ => (moved g).symm, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑' ω, ∑ g : G, μ ω * (w (view ω) * if event (act g ω) then 1 else 0) :=
        (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
    _ = ∑' ω, μ ω * w (view ω) * ((Finset.univ.filter fun g => event (act g ω)).card : ℝ≥0∞) := by
        refine tsum_congr fun ω => ?_
        rw [← Finset.sum_boole, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [mul_assoc]
    _ ≤ ∑' ω, μ ω * w (view ω) * (k : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (by exact_mod_cast few ω)
    _ = k * ∑' ω, μ ω * w (view ω) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ω => ?_
        rw [mul_comm]

open Classical in
/-- The weighted symmetry bound at `#G = 2^128`, divided out. -/
theorem weighted_guess_block {Ω V : Type} (μ : PMF Ω) (view : Ω → V) (w : V → ℝ≥0∞)
    (event : Ω → Prop) (act : Block → Ω → Ω) (preserve : ∀ g, μ.map (act g) = μ)
    (sameView : ∀ g ω, view (act g ω) = view ω) (k : ℕ)
    (few : ∀ ω, (Finset.univ.filter fun g => event (act g ω)).card ≤ k) :
    ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0) ≤
      (k / 2 ^ 128 : ℝ≥0∞) * ∑' ω, μ ω * w (view ω) := by
  have counted := weighted_guess μ view w event act preserve sameView k few
  have card : (Fintype.card Block : ℝ≥0∞) = 2 ^ 128 := by
    rw [Kriterion.ArgoMAC.Security.PGS.card_block]
    norm_num
  rw [card] at counted
  have pos : (2 ^ 128 : ℝ≥0∞) ≠ 0 := by positivity
  have fin : (2 ^ 128 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)
      = (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℝ≥0∞) *
          ∑' ω, μ ω * (w (view ω) * if event ω then 1 else 0)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel pos fin, one_mul]
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * (k * ∑' ω, μ ω * w (view ω)) := mul_le_mul' le_rfl counted
    _ = (k / 2 ^ 128 : ℝ≥0∞) * ∑' ω, μ ω * w (view ω) := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc]

/-! ### 2. The fold at levels 1 and 2 -/

variable [FieldCertificate] [GroupCertificate]

theorem xorFoldExcept_fin1 (skip : Fin 1) (f : Fin 1 → Block) : xorFoldExcept skip f = 0 := by
  unfold xorFoldExcept
  rw [Fin.foldl_succ, Fin.foldl_zero]
  rw [if_pos (Fin.fin_one_eq_zero skip).symm]

theorem xorFoldExcept_fin2 (skip other : Fin 2) (differ : other ≠ skip) (f : Fin 2 → Block) :
    xorFoldExcept skip f = f other := by
  unfold xorFoldExcept
  rw [Fin.foldl_succ_last, Fin.foldl_succ_last, Fin.foldl_zero]
  fin_cases skip <;> fin_cases other <;> simp_all

/-- **The reach's level-1 labels are its held bit label, at both entries.** -/
theorem evalFold_level1 (O : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (value : Nat) (bitLabel join : Nat → Block) (r : Fin (2 ^ 1)) :
    evalFold O lane c value bitLabel join 1 r = join 0 ^^^ bitLabel 0 := by
  have step : ∀ entry : Fin (2 ^ 0), evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0)
      (fun _ => 0) entry = join 0 ^^^ bitLabel 0 := by
    intro entry
    unfold evalStep
    split
    · rw [xorFoldExcept_fin1]
      exact bxor_zero _
    · rename_i off
      exact absurd (activeAt_zero value entry) off
  show extendLevel 0 (fun _ => 0) (evalStep O lane c 0 (bitLabel 0) (join 0) (activeAt value 0)
    (fun _ => 0)) r = _
  unfold extendLevel
  split
  · dsimp only
    rw [step]
    exact bzero_xor _
  · rw [step]

/-- The garbler's level-1 labels: `Δ ⊕ z` and `z`, with `z` the zero label of the chunk's low bit. -/
def levelOne (delta zero : Block) (r : Fin (2 ^ 1)) : Block :=
  if r.val = 0 then delta ^^^ zero else zero

theorem garbleFold_level1 (O : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) (r : Fin (2 ^ 1)) :
    (garbleFold O lane c delta zeroLabel 1).1 r = levelOne delta (zeroLabel 0) r := by
  show extendLevel 0 (fun _ => delta) (garbleStep O lane c 0 (zeroLabel 0) fun _ => delta) r = _
  unfold extendLevel garbleStep levelOne
  have r0 : r.val < 2 ^ 0 ↔ r.val = 0 := by
    rw [pow_zero]
    omega
  by_cases zero : r.val = 0
  · rw [dif_pos (r0.mpr zero), if_pos zero, if_pos rfl]
  · rw [dif_neg (fun h => zero (r0.mp h)), if_neg zero, if_pos rfl]

/-- **The garbler's fold depends on each fold gate only at its own level label.** -/
theorem garbleFold_congr (O O' : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) : ∀ steps,
    (∀ (n : Nat) (r : Fin (2 ^ n)) (half : Bool), n < steps →
      O'.permutation (hotIndexNat lane c n r.val half) ((garbleFold O lane c delta zeroLabel n).1 r) =
        O.permutation (hotIndexNat lane c n r.val half) ((garbleFold O lane c delta zeroLabel n).1 r)) →
    garbleFold O' lane c delta zeroLabel steps = garbleFold O lane c delta zeroLabel steps
  | 0, _ => rfl
  | steps + 1, agree => by
      have previous := garbleFold_congr O O' lane c delta zeroLabel steps
        fun n r half small => agree n r half (by omega)
      have right : garbleStep O' lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1 =
          garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1 := by
        funext r
        unfold garbleStep
        split
        · rfl
        · unfold foldMask PlanB.hash daviesMeyer
          rw [agree steps r false (by omega), agree steps r true (by omega)]
      show (extendLevel steps (garbleFold O' lane c delta zeroLabel steps).1
          (garbleStep O' lane c steps (zeroLabel steps) (garbleFold O' lane c delta zeroLabel steps).1),
        fun step => if step = steps then stepJoin steps (zeroLabel steps)
          (garbleStep O' lane c steps (zeroLabel steps) (garbleFold O' lane c delta zeroLabel steps).1)
          else (garbleFold O' lane c delta zeroLabel steps).2 step) =
        (extendLevel steps (garbleFold O lane c delta zeroLabel steps).1
          (garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1),
        fun step => if step = steps then stepJoin steps (zeroLabel steps)
          (garbleStep O lane c steps (zeroLabel steps) (garbleFold O lane c delta zeroLabel steps).1)
          else (garbleFold O lane c delta zeroLabel steps).2 step)
      rw [previous, right]

/-- The inactive parent at step `1`. -/
def otherParent (value : Nat) : Fin (2 ^ 1) :=
  ⟨1 - value % 2, by have := Nat.mod_lt value (by omega : 2 > 0); show 1 - value % 2 < 2; omega⟩

theorem otherParent_ne (value : Nat) : otherParent value ≠ activeAt value 1 := by
  intro same
  have := congrArg Fin.val same
  simp only [otherParent, activeAt, pow_one] at this
  have := Nat.mod_lt value (by omega : 2 > 0)
  omega

theorem eq_otherParent (value : Nat) (r : Fin (2 ^ 1)) (off : r ≠ activeAt value 1) :
    r = otherParent value := by
  apply Fin.ext
  have small : r.val < 2 := r.isLt
  have mod := Nat.mod_lt value (by omega : 2 > 0)
  have offVal : r.val ≠ value % 2 := fun h => off (Fin.ext (by simp only [activeAt, pow_one]; exact h))
  show r.val = 1 - value % 2
  omega

/-- **The level-2 labels move with the inactive parent's first fold gate.** -/
theorem evalFold_two_diff (O O' : PermutationOracle FixedIndex Block) (lane : Lane) (c : Fin chunkCount)
    (value : Nat) (bitLabel join : Nat → Block)
    (same : ∀ i x, i ≠ hotIndexNat lane c 1 (otherParent value).val false →
      O'.permutation i x = O.permutation i x) :
    ∀ steps, steps = 2 → ∀ j : Fin (2 ^ steps),
      evalFold O' lane c value bitLabel join steps j =
        evalFold O lane c value bitLabel join steps j ^^^
          (O.permutation (hotIndexNat lane c 1 (otherParent value).val false) (join 0 ^^^ bitLabel 0) ^^^
            O'.permutation (hotIndexNat lane c 1 (otherParent value).val false) (join 0 ^^^ bitLabel 0)) := by
  intro steps two j
  subst two
  set X := join 0 ^^^ bitLabel 0
  set I := hotIndexNat lane c 1 (otherParent value).val false
  set d := O.permutation I X ^^^ O'.permutation I X
  have levelOne' : ∀ (P : PermutationOracle FixedIndex Block),
      evalFold P lane c value bitLabel join 1 = fun _ => X :=
    fun P => funext fun r => evalFold_level1 P lane c value bitLabel join r
  have otherHalf : hotIndexNat lane c 1 (otherParent value).val true ≠ I := by
    intro h
    simp only [I, hotIndexNat, FixedIndex.hot.injEq] at h
    exact Bool.noConfusion h.2.2.2.2
  have mask : foldMask O' lane c 1 (otherParent value).val X = foldMask O lane c 1 (otherParent value).val X ^^^ d := by
    unfold foldMask PlanB.hash daviesMeyer
    rw [same _ X otherHalf]
    simp only [d, I, Cryptography.xor]
    generalize O.permutation (hotIndexNat lane c 1 (otherParent value).val false) X = a
    generalize O'.permutation (hotIndexNat lane c 1 (otherParent value).val false) X = b
    generalize O.permutation (hotIndexNat lane c 1 (otherParent value).val true) X = e
    refine BitVec.eq_of_getLsbD_eq fun position _ => ?_
    simp only [BitVec.getLsbD_xor]
    cases a.getLsbD position <;> cases b.getLsbD position <;> cases e.getLsbD position <;>
      cases X.getLsbD position <;> rfl
  have right : ∀ entry : Fin (2 ^ 1),
      evalStep O' lane c 1 (bitLabel 1) (join 1) (activeAt value 1) (fun _ => X) entry =
        evalStep O lane c 1 (bitLabel 1) (join 1) (activeAt value 1) (fun _ => X) entry ^^^ d := by
    intro entry
    unfold evalStep
    split
    · rw [xorFoldExcept_fin2 _ (otherParent value) (otherParent_ne value),
        xorFoldExcept_fin2 _ (otherParent value) (otherParent_ne value)]
      dsimp only
      rw [mask]
      simp only [BitVec.xor_assoc]
    · rename_i off
      rw [eq_otherParent value entry off]
      exact mask
  show extendLevel 1 (evalFold O' lane c value bitLabel join 1)
      (evalStep O' lane c 1 (bitLabel 1) (join 1) (activeAt value 1) (evalFold O' lane c value bitLabel join 1)) j =
    extendLevel 1 (evalFold O lane c value bitLabel join 1)
      (evalStep O lane c 1 (bitLabel 1) (join 1) (activeAt value 1) (evalFold O lane c value bitLabel join 1)) j ^^^ d
  rw [levelOne' O', levelOne' O]
  unfold extendLevel
  split
  · dsimp only
    rw [right]
    exact (BitVec.xor_assoc _ _ _).symm
  · rw [right]

/-! ### 3. The transposition family -/

/-- `τ_g`: fixes `G` and `G ⊕ g`, moves every other point by `g`. -/
def transTauFun (g G x : Block) : Block := if x = G ∨ x = G ^^^ g then x else x ^^^ g

theorem transTauFun_involutive (g G : Block) : Function.Involutive (transTauFun g G) := by
  intro x
  unfold transTauFun
  by_cases h : x = G ∨ x = G ^^^ g
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    have h' : ¬ (x ^^^ g = G ∨ x ^^^ g = G ^^^ g) := by
      rintro (e | e)
      · apply h
        right
        rw [← e, Hidden.xor_cancel_right]
      · apply h
        left
        rw [← Hidden.xor_cancel_right x g, e, Hidden.xor_cancel_right]
    rw [if_neg h', Hidden.xor_cancel_right]

/-- `τ_g` as a permutation. -/
def transTau (g G : Block) : Equiv.Perm Block := (transTauFun_involutive g G).toPerm _

theorem transTau_apply (g G x : Block) : transTau g G x = transTauFun g G x := rfl

theorem transTau_fix (g G : Block) : transTau g G G = G := by
  rw [transTau_apply]
  unfold transTauFun
  rw [if_pos (Or.inl rfl)]

theorem transTau_transTau (g G x : Block) : transTau g G (transTau g G x) = x := transTauFun_involutive g G x

/-- **Few members hit**: off the fixed point, `π ∘ τ_g` sends `X` to a given value for at most two
`g`. -/
theorem transTau_few (G X y : Block) (π : Equiv.Perm Block) (off : X ≠ G) :
    (Finset.univ.filter fun g => π (transTau g G X) = y).card ≤ 2 := by
  classical
  have sub : (Finset.univ.filter fun g => π (transTau g G X) = y) ⊆ {G ^^^ X, X ^^^ π.symm y} := by
    intro g member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
    rw [Finset.mem_insert, Finset.mem_singleton]
    have image : transTau g G X = π.symm y := by rw [← member, Equiv.symm_apply_apply]
    rw [transTau_apply] at image
    unfold transTauFun at image
    by_cases h : X = G ∨ X = G ^^^ g
    · left
      rcases h with h | h
      · exact absurd h off
      · rw [h, Hidden.xor_self_left]
    · right
      rw [if_neg h] at image
      rw [← image, Hidden.xor_self_left]
  calc (Finset.univ.filter fun g => π (transTau g G X) = y).card
      ≤ ({G ^^^ X, X ^^^ π.symm y} : Finset Block).card := Finset.card_le_card sub
    _ ≤ 2 := Finset.card_le_two

open Classical in
/-- Precompose one permutation of a fixed-key oracle with a permutation of `Block`. -/
def transPerm (I : FixedIndex) (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block) :
    PermutationOracle FixedIndex Block :=
  ⟨fun i => if i = I then τ.trans (O.permutation i) else O.permutation i⟩

theorem transPerm_at (I : FixedIndex) (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block)
    (x : Block) : (transPerm I τ O).permutation I x = O.permutation I (τ x) := by
  classical
  show (if I = I then τ.trans (O.permutation I) else O.permutation I) x = _
  rw [if_pos rfl]
  rfl

theorem transPerm_other (I : FixedIndex) (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block)
    (i : FixedIndex) (differ : i ≠ I) : (transPerm I τ O).permutation i = O.permutation i := by
  classical
  show (if i = I then τ.trans (O.permutation i) else O.permutation i) = _
  rw [if_neg differ]

/-- The fold gate the family acts on: the inactive parent's first half. -/
def transIndex (input : AffineInput) (lane : Lane) (c : Fin chunkCount) : FixedIndex :=
  hotIndexNat lane c 1 (otherParent (chunkValue (inputBits input lane.coord) c).toNat).val false

theorem zero_lt_chunkWidth (c : Fin chunkCount) : 0 < chunkWidth c := by rw [chunkWidth_two]; omega

/-- The garbler's point at that gate (coins, EncPRF and hash only). -/
def transPoint (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (rest : TapeRest) : Block :=
  levelOne ((garblerKeys rest).1 lane) ((chunkKey ((garblerKeys rest).2 lane) c ⟨0, zero_lt_chunkWidth c⟩).1)
    (otherParent (chunkValue (inputBits input lane.coord) c).toNat)

/-- The transposition family on a tape. -/
def transAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (tape : Coins × Oracle) : Coins × Oracle :=
  (tape.1, transPerm (transIndex input lane c) (transTau g (transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2)))
    tape.2.1, tape.2.2.1, tape.2.2.2)

theorem labelAt_step0 {width : Nat} (labels : Fin width → Block) (pos : 0 < width) :
    labelAt labels 0 = labels ⟨0, pos⟩ := by
  unfold labelAt
  rw [dif_pos pos]

/-- The garbler's level-1 labels, from the lane keys. -/
theorem garbFold_one (tape : Coins × Oracle) (lane : Lane) (c : Fin chunkCount) (r : Fin (2 ^ 1)) :
    garbFold tape lane c 1 r = levelOne ((Hidden.laneKeys tape).1 lane)
      ((chunkKey ((Hidden.laneKeys tape).2 lane) c ⟨0, zero_lt_chunkWidth c⟩).1) r := by
  unfold garbFold
  rw [garbleFold_level1, labelAt_step0 _ (zero_lt_chunkWidth c)]

/-- **The transposed gate agrees with the original wherever the garbler asks it.** -/
theorem hotIndexNat_eq_transIndex (input : AffineInput) (lane lane' : Lane) (c c' : Fin chunkCount)
    (n r : Nat) (half : Bool) (small : n < 2) (entry : r < 2 ^ n)
    (same : hotIndexNat lane' c' n r half = transIndex input lane c) :
    lane' = lane ∧ c' = c ∧ n = 1 ∧ r = (otherParent (chunkValue (inputBits input lane.coord) c).toNat).val ∧
      half = false := by
  unfold transIndex hotIndexNat at same
  simp only [FixedIndex.hot.injEq, Fin.mk.injEq] at same
  obtain ⟨laneEq, chunkEq, fold, ent, halfEq⟩ := same
  have c2 : chunkBits = 2 := rfl
  have rSmall : r < 4 := by
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have oSmall := (otherParent (chunkValue (inputBits input lane.coord) c).toNat).isLt
  simp only [c2] at fold ent
  refine ⟨laneEq, chunkEq, ?_, ?_, halfEq⟩
  · rwa [Nat.mod_eq_of_lt small] at fold
  · have p : (2 : Nat) ^ 2 = 4 := rfl
    simp only [pow_one] at oSmall
    rwa [p, Nat.mod_eq_of_lt rSmall, Nat.mod_eq_of_lt (by omega)] at ent

/-- **The garbler's chunk is kept** when the transposed gate is precomposed with a permutation
fixing the garbler's point there. -/
theorem garbleChunk_transPerm (input : AffineInput) (lane : Lane) (c : Fin chunkCount)
    (τ : Equiv.Perm Block) (O : PermutationOracle FixedIndex Block) (lane' : Lane) (delta : Block)
    (bitKey : Fin PlanB.coordinateBits → Block × Block) (c' : Fin chunkCount)
    (fixes : lane' = lane → c' = c →
      τ (levelOne delta (bitKey (chunkBitIndex c ⟨0, zero_lt_chunkWidth c⟩)).1
        (otherParent (chunkValue (inputBits input lane.coord) c).toNat)) =
      levelOne delta (bitKey (chunkBitIndex c ⟨0, zero_lt_chunkWidth c⟩)).1
        (otherParent (chunkValue (inputBits input lane.coord) c).toNat)) :
    garbleChunk (transPerm (transIndex input lane c) τ O) lane' delta bitKey c' =
      garbleChunk O lane' delta bitKey c' := by
  have fold := garbleFold_congr O (transPerm (transIndex input lane c) τ O) lane' c' delta
    (labelAt fun p => (chunkKey bitKey c' p).1) (chunkWidth c') (fun n r half small => by
      by_cases hit : hotIndexNat lane' c' n r.val half = transIndex input lane c
      · have small' : n < 2 := by rw [chunkWidth_two] at small; exact small
        obtain ⟨rfl, rfl, rfl, rEq, rfl⟩ :=
          hotIndexNat_eq_transIndex input lane lane' c c' n r.val half small' r.isLt hit
        rw [hit, transPerm_at, garbleFold_level1, labelAt_step0 _ (zero_lt_chunkWidth c')]
        have rIs : r = otherParent (chunkValue (inputBits input lane'.coord) c').toNat := Fin.ext rEq
        rw [rIs]
        exact congrArg _ (fixes rfl rfl)
      · rw [transPerm_other _ _ _ _ hit])
  unfold garbleChunk garbleHot
  rw [fold]

/-! ### 4. The transposition family keeps the swapped tape -/

open Classical in
/-- The transposition family on the split tape's rest. -/
def restAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (rest : RestTape TapeRest) : RestTape TapeRest :=
  (rest.1, fun o => if o.1 = transIndex input lane c then
    (transTau g (transPoint input lane c rest.1)).trans (rest.2 o) else rest.2 o)

theorem restAct_involutive (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block) :
    Function.Involutive (restAct input lane c g) := by
  classical
  rintro ⟨first, other⟩
  refine Prod.ext rfl (funext fun o => ?_)
  show (if o.1 = transIndex input lane c then (transTau g (transPoint input lane c first)).trans
      (if o.1 = transIndex input lane c then (transTau g (transPoint input lane c first)).trans (other o)
        else other o) else
      (if o.1 = transIndex input lane c then (transTau g (transPoint input lane c first)).trans (other o)
        else other o)) = other o
  by_cases hit : o.1 = transIndex input lane c
  · rw [if_pos hit, if_pos hit]
    ext x
    simp only [Equiv.trans_apply, transTau_transTau]
  · rw [if_neg hit, if_neg hit]

/-- The rest action as a permutation. -/
def restActEquiv (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block) :
    RestTape TapeRest ≃ RestTape TapeRest :=
  (restAct_involutive input lane c g).toPerm _

theorem transIndex_not_site (input : AffineInput) (lane : Lane) (c : Fin chunkCount) :
    transIndex input lane c ∉ Set.range siteIndex :=
  Hidden.hotIndexNat_not_site lane c 1 _ false (by rw [chunkWidth_two]; omega)
    (otherParent (chunkValue (inputBits input lane.coord) c).toNat).isLt

theorem restAct_at (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (rest : RestTape TapeRest) (h : transIndex input lane c ∉ Set.range siteIndex) :
    (restAct input lane c g rest).2 ⟨transIndex input lane c, h⟩ =
      (transTau g (transPoint input lane c rest.1)).trans (rest.2 ⟨_, h⟩) := by
  unfold restAct
  exact if_pos rfl

theorem restAct_other (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (rest : RestTape TapeRest) (o : OtherIndex) (differ : o.1 ≠ transIndex input lane c) :
    (restAct input lane c g rest).2 o = rest.2 o := by
  unfold restAct
  exact if_neg differ

theorem oracleOf_restAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (rest : RestTape TapeRest) (scale : SitePerms MaskSite) :
    oracleOf (restAct input lane c g rest).2 scale =
      transPerm (transIndex input lane c) (transTau g (transPoint input lane c rest.1)) (oracleOf rest.2 scale) := by
  classical
  refine oracle_ext fun index => ?_
  by_cases site : index ∈ Set.range siteIndex
  · obtain ⟨s, rfl⟩ := site
    have notI : siteIndex s ≠ transIndex input lane c := fun same =>
      transIndex_not_site input lane c (same ▸ ⟨s, rfl⟩)
    rw [transPerm_other _ _ _ _ notI, oracleOf_site, oracleOf_site]
  · rw [oracleOf_other _ _ ⟨index, site⟩]
    by_cases hit : index = transIndex input lane c
    · subst hit
      ext x
      rw [transPerm_at, oracleOf_other _ _ ⟨_, site⟩, restAct_at]
      rfl
    · rw [transPerm_other _ _ _ _ hit, oracleOf_other _ _ ⟨index, site⟩]
      exact restAct_other input lane c g rest ⟨index, site⟩ hit

theorem transAct_split (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (tape : RestTape TapeRest × SitePerms MaskSite) :
    transAct input lane c g (reassembleEquiv (assemble tape)) =
      reassembleEquiv (assemble (restAct input lane c g tape.1, tape.2)) := by
  obtain ⟨⟨⟨coins, enc, hash⟩, other⟩, scale⟩ := tape
  show (coins, transPerm (transIndex input lane c) (transTau g (transPoint input lane c (coins, enc, hash)))
      (oracleOf other scale), enc, hash) =
    (coins, oracleOf (restAct input lane c g ((coins, enc, hash), other)).2 scale, enc, hash)
  rw [oracleOf_restAct]

/-- **The swap kernel's points are kept.** -/
theorem planBPoint_restAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (rest : RestTape TapeRest) :
    planBPoint garblerKeys (restAct input lane c g rest) = planBPoint garblerKeys rest := by
  funext site
  show (garbleChunk (oracleOf (restAct input lane c g rest).2 fun _ => Equiv.refl Block) site.1.1
      ((garblerKeys rest.1).1 site.1.1) ((garblerKeys rest.1).2 site.1.1) site.1.2.1).1 site.1.2.2.1 =
    (garbleChunk (oracleOf rest.2 fun _ => Equiv.refl Block) site.1.1
      ((garblerKeys rest.1).1 site.1.1) ((garblerKeys rest.1).2 site.1.1) site.1.2.1).1 site.1.2.2.1
  rw [oracleOf_restAct, garbleChunk_transPerm input lane c _ _ _ _ _ _ fun laneEq _ => ?_]
  rw [laneEq]
  exact transTau_fix g _

/-- **The transposition family keeps the swapped tape.** -/
theorem swapped_trans_invariant (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block) :
    swappedChallengeTape.map (transAct input lane c g) = swappedChallengeTape := by
  have law : (swapLaw (restLaw restUniform) (planBPoint garblerKeys)).map
      (fun t => (restAct input lane c g t.1, t.2)) = swapLaw (restLaw restUniform) (planBPoint garblerKeys) := by
    unfold swapLaw
    rw [PMF.map_bind]
    have each : ∀ rest : RestTape TapeRest,
        ((swapKernel (planBPoint garblerKeys rest)).map (Prod.mk rest)).map
            (fun t => (restAct input lane c g t.1, t.2)) =
          (swapKernel (planBPoint garblerKeys (restAct input lane c g rest))).map
            (Prod.mk (restAct input lane c g rest)) := by
      intro rest
      rw [PMF.map_comp, planBPoint_restAct]
      rfl
    simp only [each]
    have restInvariant : (restLaw restUniform).map (restActEquiv input lane c g) = restLaw restUniform := by
      unfold restLaw restUniform
      rw [← uniformOfFintype_productPMF]
      exact Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv _
    conv_rhs => rw [← restInvariant]
    rw [PMF.bind_map]
    rfl
  unfold swappedChallengeTape swappedTape
  rw [PMF.map_comp, PMF.map_comp, PMF.map_comp]
  have factor : ((transAct input lane c g ∘ reassembleEquiv) ∘ assemble) =
      (reassembleEquiv ∘ assemble) ∘ (fun t => (restAct input lane c g t.1, t.2)) := by
    funext tape
    exact transAct_split input lane c g tape
  rw [factor, ← PMF.map_comp, law]

/-! ### 5. The transposition family keeps the view -/

/-- The garbler's point at the transposed gate. -/
theorem garblerPointOf_transIndex (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (tape : Coins × Oracle) :
    Hidden.garblerPointOf scalar tape (transIndex input lane c) =
      transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2) := by
  unfold transIndex
  rw [Hidden.garblerPointOf_hot scalar tape lane c 1 _ false (by rw [chunkWidth_two]; omega)
    (otherParent (chunkValue (inputBits input lane.coord) c).toNat).isLt]
  rw [garbleFold_level1, labelAt_step0 _ (zero_lt_chunkWidth c)]
  rfl

/-- **The garbler runs identically on the transposed tape.** -/
theorem transAct_garbler (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane) (c : Fin chunkCount)
    (g : Block) (tape : Coins × Oracle) :
    transcriptOf (publicAnswer (transAct input lane c g tape).2) (Programs.garbleM scalar tape.1) =
        transcriptOf (publicAnswer tape.2) (Programs.garbleM scalar tape.1) ∧
      (Programs.garbleM scalar tape.1).eval (publicAnswer (transAct input lane c g tape).2) =
        (Programs.garbleM scalar tape.1).eval (publicAnswer tape.2) := by
  refine Hidden.transcriptOf_of_agrees (Programs.garbleM scalar tape.1) tape.2
    (transAct input lane c g tape).2 fun entry member => ?_
  have good := garblerTranscript_good scalar tape entry (by rw [garblerTranscript_eq]; exact member)
  rw [← Hidden.transcriptOf_agrees tape.2 _ entry member]
  obtain ⟨request, answer⟩ := entry
  cases request with
  | fixedForward index x =>
      have isGood : x = Hidden.garblerPointOf scalar tape index := good
      show (transPerm (transIndex input lane c) _ tape.2.1).permutation index x = tape.2.1.permutation index x
      by_cases hit : index = transIndex input lane c
      · subst hit
        rw [transPerm_at, isGood, garblerPointOf_transIndex, transTau_fix]
      · rw [transPerm_other _ _ _ _ hit]
  | fixedInverse _ _ => exact good.elim
  | encForward _ _ => rfl
  | encInverse _ _ => exact good.elim
  | hash _ => rfl

theorem garble_transAct (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (g : Block) (tape : Coins × Oracle) :
    (Scheme.scheme.garble parameter scalar (transAct input lane c g tape)).1 =
      (Scheme.scheme.garble parameter scalar tape).1 := by
  have sameEval := (transAct_garbler scalar input lane c g tape).2
  rw [garble_eval parameter, garble_eval parameter] at sameEval
  exact congrArg Prod.fst sameEval

theorem garblerTranscript_transAct (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (g : Block) (tape : Coins × Oracle) :
    garblerTranscript scalar (transAct input lane c g tape) = garblerTranscript scalar tape := by
  rw [garblerTranscript_eq, garblerTranscript_eq]
  exact (transAct_garbler scalar input lane c g tape).1

/-- **The stage-1 view is kept.** -/
theorem stageOneView_transAct (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (g : Block) (tape : Coins × Oracle) :
    stageOneView parameter scalar (transAct input lane c g tape) = stageOneView parameter scalar tape := by
  show ((Scheme.scheme.garble parameter scalar (transAct input lane c g tape)).1,
      (garblerTranscript scalar (transAct input lane c g tape)).filter Entry.IsEnc) =
    ((Scheme.scheme.garble parameter scalar tape).1, (garblerTranscript scalar tape).filter Entry.IsEnc)
  rw [garble_transAct, garblerTranscript_transAct]

/-! ### 6. Event 2 under the transposition family -/

theorem xor_solve (a b c d : Block) (h : a ^^^ (b ^^^ c) = d) : c = a ^^^ b ^^^ d := by
  subst h
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem xor_shift_solve (a b g : Block) (h : a = b ^^^ g) : g = b ^^^ a := by
  subst h
  exact (Hidden.xor_self_left b g).symm

theorem joinAt_step0 {width : Nat} (joins : Vector Block (width - 1)) : joinAt joins 0 = 0 := if_pos rfl

/-- The reach's level-1 label is its held label of the chunk's low bit. -/
theorem reachFold_one (parameter : ℕ) (scalar : NonZeroScalar) (tape : Coins × Oracle)
    (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (r : Fin (2 ^ 1)) :
    reachFold parameter scalar tape input lane c 1 r = labelAt (chunkLabels (laneLabels tape input lane) c) 0 := by
  unfold reachFold
  rw [evalFold_level1, joinAt_step0]
  exact bzero_xor _

theorem coin1_transAct (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (g : Block) (tape : Coins × Oracle) :
    Coin1 parameter scalar (transAct input lane c g tape) input lane c ↔
      Coin1 parameter scalar tape input lane c := by
  unfold Coin1
  simp only [reachFold_one, garbFold_one]
  exact Iff.rfl

theorem garbChunk_transAct (input : AffineInput) (lane : Lane) (c : Fin chunkCount) (g : Block)
    (tape : Coins × Oracle) : garbChunk (transAct input lane c g tape) lane c = garbChunk tape lane c := by
  unfold garbChunk
  exact congrArg Prod.fst (garbleChunk_transPerm input lane c
    (transTau g (transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2))) tape.2.1 lane
    ((Hidden.laneKeys tape).1 lane) ((Hidden.laneKeys tape).2 lane) c (fun _ _ => transTau_fix g _))

/-- **The reach's one-hot labels move with the transposed gate's answer at its level-1 label.** -/
theorem reachFold_transAct_two (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput)
    (lane : Lane) (c : Fin chunkCount) (g : Block) (tape : Coins × Oracle) (j : Fin (2 ^ chunkWidth c)) :
    reachFold parameter scalar (transAct input lane c g tape) input lane c (chunkWidth c) j =
      reachFold parameter scalar tape input lane c (chunkWidth c) j ^^^
        (tape.2.1.permutation (transIndex input lane c) (labelAt (chunkLabels (laneLabels tape input lane) c) 0) ^^^
          tape.2.1.permutation (transIndex input lane c)
            (transTau g (transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2))
              (labelAt (chunkLabels (laneLabels tape input lane) c) 0))) := by
  unfold reachFold
  rw [garble_transAct]
  have diff := evalFold_two_diff tape.2.1 (transAct input lane c g tape).2.1 lane c
    (chunkValue (inputBits input lane.coord) c).toNat (labelAt (chunkLabels (laneLabels tape input lane) c))
    (joinAt (hotSlice (lanePub (Scheme.scheme.garble parameter scalar tape).1 lane) c))
    (fun i x differ => by
      show (transPerm (transIndex input lane c) _ tape.2.1).permutation i x = _
      rw [transPerm_other (transIndex input lane c) _ tape.2.1 i differ]) (chunkWidth c) (chunkWidth_two c) j
  have at_ : (transAct input lane c g tape).2.1.permutation
      (hotIndexNat lane c 1 (otherParent (chunkValue (inputBits input lane.coord) c).toNat).val false)
      (labelAt (chunkLabels (laneLabels tape input lane) c) 0) =
    tape.2.1.permutation (transIndex input lane c)
      (transTau g (transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2))
        (labelAt (chunkLabels (laneLabels tape input lane) c) 0)) := transPerm_at _ _ _ _
  rw [joinAt_step0, bzero_xor] at diff
  refine diff.trans ?_
  rw [at_]
  rfl

open Classical in
/-- **Event 2 holds for at most two members of the transposition family.** -/
theorem hit2_few (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (j : Fin 4) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g => Hit2 parameter scalar (transAct input lane c g tape) input lane c j).card ≤ 2 := by
  by_cases coin : Coin1 parameter scalar tape input lane c
  · have empty : (Finset.univ.filter fun g =>
        Hit2 parameter scalar (transAct input lane c g tape) input lane c j) = ∅ := by
      refine Finset.filter_false_of_mem fun g _ hit => ?_
      exact hit.1 ((coin1_transAct parameter scalar input lane c g tape).mpr coin)
    rw [empty, Finset.card_empty]
    omega
  · have off : labelAt (chunkLabels (laneLabels tape input lane) c) 0 ≠
        transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2) := by
      intro same
      apply coin
      refine ⟨otherParent (chunkValue (inputBits input lane.coord) c).toNat, otherParent_ne _, ?_⟩
      rw [reachFold_one, garbFold_one]
      exact same
    refine le_trans (Finset.card_le_card ?_) (transTau_few (transPoint input lane c (tape.1, tape.2.2.1, tape.2.2.2))
      (labelAt (chunkLabels (laneLabels tape input lane) c) 0)
      (reachFold parameter scalar tape input lane c (chunkWidth c) (castSwitch c j) ^^^
        tape.2.1.permutation (transIndex input lane c) (labelAt (chunkLabels (laneLabels tape input lane) c) 0) ^^^
          garbChunk tape lane c (castSwitch c j))
      (tape.2.1.permutation (transIndex input lane c)) off)
    intro g member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    have eq := member.2
    rw [reachFold_transAct_two, garbChunk_transAct] at eq
    exact xor_solve _ _ _ _ eq

open Classical in
/-- **Event 2's guess bound.** -/
theorem hit2_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (j : Fin 4)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if Hit2 parameter scalar tape input lane c j then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) * ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => Hit2 parameter scalar tape input lane c j) (transAct input lane c)
    (swapped_trans_invariant input lane c)
    (fun g tape => stageOneView_transAct parameter scalar input lane c g tape) 2
    (hit2_few parameter scalar input lane c j)

/-! ### 7. The `k₂`-family: events 1 and 3 -/

theorem key2Valid (g : Block) : (familyKey2 0 g).Valid := familyKey2_valid 0 (by decide) g

theorem key2_tape_coins (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) :
    (shiftTape (familyKey2 0 g) scalar tape).1 = tape.1 :=
  key2_coins 0 g tape.1

theorem shiftHash_off (T : TapeShift) (key : BaseField) (hash : EncPRF.HashOracle) (value : BaseField)
    (differ : value ≠ key) : Hidden.shiftHash T key hash value = hash value := by
  unfold Hidden.shiftHash
  rw [if_neg differ]

/-- Off the curve the reach's pads are kept: they are keyed by `hash(t_eval)`, `t_eval ≠ t`. -/
theorem padsOf_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (input : AffineInput)
    (invalid : validate input = false) :
    padsOf (shiftTape (familyKey2 0 g) scalar tape) input = padsOf tape input := by
  unfold padsOf
  rw [key2_tape_coins]
  show Programs.realEvalPads tape.2.2.1
      ⟨(Hidden.shiftHash (familyKey2 0 g) tape.1.bridgeKey tape.2.2.2 (evalKey tape.1 input)).1,
        (Hidden.shiftHash (familyKey2 0 g) tape.1.bridgeKey tape.2.2.2 (evalKey tape.1 input)).2⟩
      (BitInput.ofAffine input) = _
  rw [shiftHash_off _ _ _ _ (evalKey_ne tape.1 input invalid)]

theorem macOf_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (input : AffineInput) :
    macOf (shiftTape (familyKey2 0 g) scalar tape) input = macOf tape input := by
  unfold macOf
  rw [key2_tape_coins]

theorem laneLabels_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (input : AffineInput)
    (invalid : validate input = false) (lane : Lane) :
    laneLabels (shiftTape (familyKey2 0 g) scalar tape) input lane = laneLabels tape input lane := by
  have mac := macOf_key2 scalar g tape input
  have pads := padsOf_key2 scalar g tape input invalid
  cases lane
  · exact congrArg (fun m => Pipeline.macLabels m .x) mac
  · exact congrArg (fun m => Pipeline.macLabels m .y) mac
  · exact congrArg₂ (fun p m => Pipeline.macLabels (Programs.whitenMacOf p m) .x) pads mac
  · exact congrArg₂ (fun p m => Pipeline.macLabels (Programs.whitenMacOf p m) .y) pads mac

theorem reachFold_one_key2 (parameter : ℕ) (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle)
    (input : AffineInput) (invalid : validate input = false) (lane : Lane) (c : Fin chunkCount)
    (r : Fin (2 ^ 1)) :
    reachFold parameter scalar (shiftTape (familyKey2 0 g) scalar tape) input lane c 1 r =
      reachFold parameter scalar tape input lane c 1 r := by
  rw [reachFold_one, reachFold_one, laneLabels_key2 scalar g tape input invalid]

theorem levelOne_shift (delta zero g : Block) (r : Fin (2 ^ 1)) :
    levelOne (delta ^^^ 0) (zero ^^^ g) r = levelOne delta zero r ^^^ g := by
  unfold levelOne
  rw [bxor_zero]
  split
  · exact (BitVec.xor_assoc _ _ _).symm
  · rfl

/-- **The `k₂`-family moves the garbler's level-1 labels of system B by `g`.** -/
theorem garbFold_one_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (lane : Lane)
    (point : Hidden.laneIsPoint lane = true) (c : Fin chunkCount) (r : Fin (2 ^ 1)) :
    garbFold (shiftTape (familyKey2 0 g) scalar tape) lane c 1 r = garbFold tape lane c 1 r ^^^ g := by
  rw [garbFold_one, garbFold_one]
  have delta := Hidden.garblerKeys_delta (familyKey2 0 g) scalar
    ((tape.1, tape.2.2.1, tape.2.2.2), fun _ => Equiv.refl Block) lane
  have zero := Hidden.garblerKeys_zero (familyKey2 0 g) scalar
    ((tape.1, tape.2.2.1, tape.2.2.2), fun _ => Equiv.refl Block) lane
    (chunkBitIndex c ⟨0, zero_lt_chunkWidth c⟩)
  have laneZero : ((familyKey2 0 g).lane lane).zero (chunkBitIndex c ⟨0, zero_lt_chunkWidth c⟩) = g := by
    simp [TapeShift.lane, familyKey2, point]
  rw [laneZero] at zero
  show levelOne ((garblerKeys (Hidden.restShift (familyKey2 0 g) scalar
      ((tape.1, tape.2.2.1, tape.2.2.2), fun _ => Equiv.refl Block)).1).1 lane)
    ((garblerKeys (Hidden.restShift (familyKey2 0 g) scalar
      ((tape.1, tape.2.2.1, tape.2.2.2), fun _ => Equiv.refl Block)).1).2 lane
        (chunkBitIndex c ⟨0, zero_lt_chunkWidth c⟩)).1 r = _
  rw [delta, zero]
  exact levelOne_shift _ _ g r

open Classical in
/-- **Event 1 holds for at most two members of the `k₂`-family.** -/
theorem hit1_few (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g =>
      Hit1 parameter scalar (shiftTape (familyKey2 0 g) scalar tape) input lane c).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := Finset.univ.image fun r : Fin (2 ^ 1) =>
    garbFold tape lane c 1 r ^^^ reachFold parameter scalar tape input lane c 1 r) ?_)
    (Finset.card_image_le.trans (by simp))
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  obtain ⟨point, invalid, r, _, eq⟩ := member
  rw [reachFold_one_key2 parameter scalar g tape input invalid, garbFold_one_key2 scalar g tape lane point] at eq
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, (xor_shift_solve _ _ _ eq).symm⟩

open Classical in
/-- **Event 1's guess bound.** -/
theorem hit1_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (lane : Lane)
    (c : Fin chunkCount) (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if Hit1 parameter scalar tape input lane c then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) * ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => Hit1 parameter scalar tape input lane c) (fun g => shiftTape (familyKey2 0 g) scalar)
    (fun g => Hidden.swapped_shift_invariant (familyKey2 0 g) (key2Valid g) scalar)
    (fun g tape => stageOneView_shift (familyKey2 0 g) (key2Valid g) parameter scalar tape) 2
    (hit1_few parameter scalar input lane c)

/-- The EncPRF coordinate of a gadget coordinate. -/
def encCoord : Coord → EncPRF.Coordinate
  | .x => .x
  | .y => .y

/-- **The garbler's gadget label** is the pad of its bit over the Lamport label of its bit. -/
theorem glabel_eq (tape : Coins × Oracle) (κ : Coord) (position : Fin PlanB.coordinateBits) (bit : Bool) :
    glabel tape κ position bit =
      encrypt (Programs.realPads tape.2.2.1 (EncPRF.whiteningKeys tape.2.2.2 tape.1.bridgeKey) (encCoord κ)
        position bit) (BitAdaptor.encode (keyAt tape.1.inputMacKey κ position) bit) := by
  unfold glabel keyAt
  cases κ
  · simp only [EncPRF.transformKey, EncPRF.transformCoordinateKey]
    rw [vget_ofFn]
    cases bit <;> rfl
  · simp only [EncPRF.transformKey, EncPRF.transformCoordinateKey]
    rw [vget_ofFn]
    cases bit <;> rfl

theorem encrypt_shift (p l g : Block) : encrypt (p ^^^ g) l = encrypt p l ^^^ g := by
  simp only [encrypt, Cryptography.xor]
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i <;> cases l.getLsbD i <;> cases g.getLsbD i <;> rfl

/-- **The `k₂`-family moves the garbler's gadget labels by `g`.** -/
theorem glabel_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) :
    glabel (shiftTape (familyKey2 0 g) scalar tape) κ position bit = glabel tape κ position bit ^^^ g := by
  rw [glabel_eq, glabel_eq, key2_tape_coins]
  show encrypt (Programs.realPads tape.2.2.1
      (EncPRF.whiteningKeys (Hidden.shiftHash (familyKey2 0 g) tape.1.bridgeKey tape.2.2.2) tape.1.bridgeKey)
      (encCoord κ) position bit) (BitAdaptor.encode (keyAt tape.1.inputMacKey κ position) bit) = _
  refine (congrArg (fun p => encrypt p (BitAdaptor.encode (keyAt tape.1.inputMacKey κ position) bit))
    (Hidden.realPads_shift (familyKey2 0 g) tape.2.2.1 tape.2.2.2 tape.1.bridgeKey (encCoord κ)
      position bit)).trans ?_
  exact encrypt_shift _ _ g

theorem reachGadget_key2 (scalar : NonZeroScalar) (g : Block) (tape : Coins × Oracle) (input : AffineInput)
    (invalid : validate input = false) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    reachGadget (shiftTape (familyKey2 0 g) scalar tape) input κ position = reachGadget tape input κ position := by
  unfold reachGadget
  rw [padsOf_key2 scalar g tape input invalid, macOf_key2]

open Classical in
/-- **Event 3 holds for at most one member of the `k₂`-family.** -/
theorem gadgetOff_few (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g =>
      GadgetOff (shiftTape (familyKey2 0 g) scalar tape) input κ position bit).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {glabel tape κ position bit ^^^ reachGadget tape input κ position}) ?_)
    (by rw [Finset.card_singleton]; omega)
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  obtain ⟨invalid, eq⟩ := member
  rw [reachGadget_key2 scalar g tape input invalid, glabel_key2] at eq
  rw [Finset.mem_singleton]
  exact xor_shift_solve _ _ _ eq

open Classical in
/-- **Event 3's guess bound.** -/
theorem gadgetOff_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (bit : Bool)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if GadgetOff tape input κ position bit then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) * ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => GadgetOff tape input κ position bit) (fun g => shiftTape (familyKey2 0 g) scalar)
    (fun g => Hidden.swapped_shift_invariant (familyKey2 0 g) (key2Valid g) scalar)
    (fun g tape => stageOneView_shift (familyKey2 0 g) (key2Valid g) parameter scalar tape) 2
    (gadgetOff_few scalar input κ position bit)

/-! ### 8. The `Δ`-family: event 4 -/

theorem keyAt_inputMacKey (coins : Coins) (κ : Coord) (position : Fin PlanB.coordinateBits) :
    keyAt coins.inputMacKey κ position =
      ⟨coins.inputZero κ position, coins.inputZero κ position ^^^ coins.inputDelta κ⟩ := by
  cases κ <;> exact vget_ofFn _ position

theorem collide_xor (p0 p1 z tz d td : Block) :
    encrypt (p0 ^^^ 0) (z ^^^ tz) ^^^ encrypt (p1 ^^^ 0) (z ^^^ tz ^^^ (d ^^^ td)) =
      encrypt p0 z ^^^ encrypt p1 (z ^^^ d) ^^^ td := by
  rw [bxor_zero, bxor_zero]
  simp only [encrypt, Cryptography.xor]
  refine BitVec.eq_of_getLsbD_eq fun i _ => ?_
  simp only [BitVec.getLsbD_xor]
  cases p0.getLsbD i <;> cases p1.getLsbD i <;> cases z.getLsbD i <;> cases tz.getLsbD i <;>
    cases d.getLsbD i <;> cases td.getLsbD i <;> rfl

/-- **The `Δ`-family moves the collision difference `pad₀ ⊕ pad₁ ⊕ Δ_κ` by `g`.** -/
theorem glabel_deltaU (scalar : NonZeroScalar) (κ : Coord) (input : AffineInput) (g : Block)
    (tape : Coins × Oracle) (position : Fin PlanB.coordinateBits) :
    glabel (shiftTape (familyDeltaU κ input g) scalar tape) κ position false ^^^
        glabel (shiftTape (familyDeltaU κ input g) scalar tape) κ position true =
      glabel tape κ position false ^^^ glabel tape κ position true ^^^ g := by
  rw [glabel_eq, glabel_eq, glabel_eq, glabel_eq]
  have e0 := Hidden.realPads_shift (familyDeltaU κ input g) tape.2.2.1 tape.2.2.2 tape.1.bridgeKey
    (encCoord κ) position false
  have e1 := Hidden.realPads_shift (familyDeltaU κ input g) tape.2.2.1 tape.2.2.2 tape.1.bridgeKey
    (encCoord κ) position true
  have key := keyAt_inputMacKey (Hidden.shiftCoins (familyDeltaU κ input g) tape.1) κ position
  have key0 := keyAt_inputMacKey tape.1 κ position
  have tDelta : (familyDeltaU κ input g).delta κ = g := if_pos rfl
  have moved := congrArg₂ (fun a b =>
    encrypt a (BitAdaptor.encode (keyAt (Hidden.shiftCoins (familyDeltaU κ input g) tape.1).inputMacKey κ
      position) false) ^^^
    encrypt b (BitAdaptor.encode (keyAt (Hidden.shiftCoins (familyDeltaU κ input g) tape.1).inputMacKey κ
      position) true)) e0 e1
  refine moved.trans ?_
  rw [key, key0]
  simp only [BitAdaptor.encode, Bool.false_eq_true, if_false, if_true]
  refine (collide_xor _ _ _ _ _ _).trans ?_
  rw [tDelta]

open Classical in
/-- **Event 4 holds for at most one member of the `Δ`-family.** -/
theorem gadgetOn_few (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits) (tape : Coins × Oracle) :
    (Finset.univ.filter fun g =>
      GadgetOn (shiftTape (familyDeltaU κ input g) scalar tape) κ position).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {glabel tape κ position false ^^^ glabel tape κ position true}) ?_)
    (by rw [Finset.card_singleton]; omega)
  intro g member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  have moved := glabel_deltaU scalar κ input g tape position
  rw [member, BitVec.xor_self] at moved
  rw [Finset.mem_singleton]
  have zero : glabel tape κ position false ^^^ glabel tape κ position true ^^^ g = 0 := moved.symm
  calc g = (glabel tape κ position false ^^^ glabel tape κ position true) ^^^
        ((glabel tape κ position false ^^^ glabel tape κ position true) ^^^ g) := (Hidden.xor_self_left _ g).symm
    _ = (glabel tape κ position false ^^^ glabel tape κ position true) ^^^ 0 := by rw [zero]
    _ = _ := bxor_zero _

open Classical in
/-- **Event 4's guess bound.** -/
theorem gadgetOn_bound (parameter : ℕ) (scalar : NonZeroScalar) (input : AffineInput) (κ : Coord)
    (position : Fin PlanB.coordinateBits)
    (weight : Public × List (Entry FixedIndex EncPRF.PermutationIndex) → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * (weight (stageOneView parameter scalar tape) *
        if GadgetOn tape κ position then 1 else 0) ≤
      (2 / 2 ^ 128 : ℝ≥0∞) * ∑' tape, swappedChallengeTape tape * weight (stageOneView parameter scalar tape) :=
  weighted_guess_block swappedChallengeTape (stageOneView parameter scalar) weight
    (fun tape => GadgetOn tape κ position) (fun g => shiftTape (familyDeltaU κ input g) scalar)
    (fun g => Hidden.swapped_shift_invariant (familyDeltaU κ input g) (familyDeltaU_valid κ input g) scalar)
    (fun g tape => stageOneView_shift (familyDeltaU κ input g) (familyDeltaU_valid κ input g) parameter scalar tape) 2
    (gadgetOn_few scalar input κ position)

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.Guess
