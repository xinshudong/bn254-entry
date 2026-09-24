/-
**Phase 3, P1l — the two laws, part 2: the garbler on an answer table.**

On `G1U`'s swapped tape the garbler asks every fixed-key index at one point (`Hidden.Good`), every
EncPRF index at its two pad points and the hash at `t`. Its whole run — transcript and published
value — is therefore its run on the **answer table** of the tape (`tapeTable`): the EncPRF
permutations, `hash(t)`, one answer per non-site index (the permutation at the garbler's point) and
one Davies–Meyer limb per mask cell (`tapeTable_agree`, `transcript_agree`).

**The table is independent of the coins and has an explicit law** (`swapped_tapeTable`):

* the limbs are the fibre-uniform tape (`Laws.swapLaw_dm`: under the swap kernel the Davies–Meyer
  values at the points do not depend on the points);
* the non-site answers are uniform (`Laws.uniform_perms_eval`): the garbler's points at the non-site
  indices it asks — the fold gates of step `1` and the gadget positions — read only the coins,
  EncPRF and the hash (`otherPoint`, `garbleFold_one`);
* `hash(t)` is uniform (`Laws.uniform_fun_eval`).

`swapped_reduce`: every function of the garbler's transcript and result, averaged over the swapped
tape, is its average over uniform coins and an independent `tableLaw` table.
-/

import Proof.Privacy.Phase3.PublicFirst.Laws

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Lazy (Cell)
open Kriterion.ArgoMAC.Security.Phase3.Hidden (garblerPointOf Good laneKeys)
open scoped ENNReal

noncomputable section

/-! ### 1. Answer tables -/

/-- **The garbler's answer table**: the EncPRF permutations, the hash value, one answer per non-site
fixed-key index, one Davies–Meyer limb per mask cell. -/
abbrev Table :=
  PermutationOracle EncPRF.PermutationIndex Block × EncPRF.HashOracle × (OtherIndex → Block) ×
    (Cell → Block)

/-- **Answers from a table.** A site query returns its limb XOR its input (Davies–Meyer output the
limb); any other fixed-key query its index's entry, whatever the input; EncPRF its permutation; the
hash the table's value, at every key. -/
def tableAnswer (A : Table) : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer
  | .fixedForward index input => @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
      (fun hit => A.2.2.2 (Classical.choose hit) ^^^ input) (fun hit => A.2.2.1 ⟨index, hit⟩)
  | .fixedInverse _ _ => (0 : Block)
  | .encForward index input => A.1.permutation index input
  | .encInverse index output => (A.1.permutation index).symm output
  | .hash key => A.2.1 key

theorem tableAnswer_site (A : Table) (cell : Cell) (input : Block) :
    tableAnswer A (.fixedForward (siteIndex cell) input) = A.2.2.2 cell ^^^ input := by
  have hit : siteIndex cell ∈ Set.range siteIndex := ⟨cell, rfl⟩
  show @dite _ (siteIndex cell ∈ Set.range siteIndex) (Classical.propDecidable _)
      (fun hit => A.2.2.2 (Classical.choose hit) ^^^ input) (fun hit => A.2.2.1 ⟨siteIndex cell, hit⟩)
    = _
  rw [dif_pos hit, siteIndex_injective (Classical.choose_spec hit)]

theorem tableAnswer_other (A : Table) (index : OtherIndex) (input : Block) :
    tableAnswer A (.fixedForward index.1 input) = A.2.2.1 index := by
  show @dite _ (index.1 ∈ Set.range siteIndex) (Classical.propDecidable _)
      (fun hit => A.2.2.2 (Classical.choose hit) ^^^ input) (fun hit => A.2.2.1 ⟨index.1, hit⟩)
    = _
  rw [dif_neg index.2]

theorem tableAnswer_enc (A : Table) (index : EncPRF.PermutationIndex) (input : Block) :
    tableAnswer A (.encForward index input) = A.1.permutation index input := rfl

theorem tableAnswer_hash (A : Table) (key : BaseField) : tableAnswer A (.hash key) = A.2.1 key := rfl

/-- **The table law**: uniform EncPRF permutations, hash value and non-site answers, and the
fibre-uniform limb tape, all independent. -/
def tableLaw : PMF Table :=
  productPMF (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (productPMF (PMF.uniformOfFintype EncPRF.HashOracle)
      (productPMF (PMF.uniformOfFintype (OtherIndex → Block)) fibreTape))

/-! ### 2. Transcripts -/

/-- Every transcript entry carries the answer function's answer. -/
theorem transcript_mem {α : Type}
    (ans : ∀ q : PublicQuery FixedIndex EncPRF.PermutationIndex, q.Answer)
    (computation : FreeQuery Programs.Spec α) :
    ∀ entry ∈ transcript ans computation, ans entry.1 = entry.2 := by
  induction computation with
  | pure value => intro entry member; cases member
  | query request next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih _ entry member

/-! ### 3. The garbler's points -/

section Points

variable [FieldCertificate] [GroupCertificate]

/-- The first fold level does not read the oracle. -/
theorem garbleFold_one (first second : PermutationOracle FixedIndex Block) (lane : Lane)
    (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    (garbleFold first lane chunk delta zeroLabel 1).1 = (garbleFold second lane chunk delta zeroLabel 1).1 := by
  have step : garbleStep first lane chunk 0 (zeroLabel 0) (fun _ => delta) =
      garbleStep second lane chunk 0 (zeroLabel 0) (fun _ => delta) := by
    funext e
    simp [garbleStep]
  simp only [garbleFold, step]

/-- The garbler's point at an index, on the tape with the coins, EncPRF and hash of `rest` and the
identity fixed-key oracle (it is the garbler's own point at the fold gates of step `1` and at the
gadget positions, the non-site indices it asks). -/
def otherPoint (scalar : NonZeroScalar) (rest : TapeRest) : FixedIndex → Block :=
  garblerPointOf scalar (rest.1, (⟨fun _ => Equiv.refl Block⟩, rest.2.1, rest.2.2))

/-- At a fold gate of step `1` or a gadget position, `otherPoint` is the garbler's point. -/
theorem otherPoint_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) (index : FixedIndex)
    (kind : (∃ (lane : Lane) (chunk : Fin chunkCount) (fold : Fin chunkBits)
        (entry : Fin (2 ^ chunkBits)) (half : Bool),
        index = .hot lane chunk fold entry half ∧ fold.val = 1) ∨
      ∃ (o : Fin digitCount) (κ : Coord) (position : Fin PlanB.coordinateBits),
        index = .gadget o κ position) :
    otherPoint scalar (tape.1, tape.2.2.1, tape.2.2.2) index = garblerPointOf scalar tape index := by
  rcases kind with ⟨lane, chunk, fold, entry, half, rfl, one⟩ | ⟨o, κ, position, rfl⟩
  · obtain ⟨fold, bound⟩ := fold
    simp only at one
    subst one
    show (garbleFold _ lane chunk _ _ 1).1 _ = (garbleFold _ lane chunk _ _ 1).1 _
    rw [garbleFold_one _ tape.2.1]
    rfl
  · show Hidden.gadgetLabel scalar (tape.1, (⟨fun _ => Equiv.refl Block⟩, tape.2.2.1, tape.2.2.2)) o κ
        position = Hidden.gadgetLabel scalar tape o κ position
    unfold Hidden.gadgetLabel
    dsimp only

/-- The garbler's point at a mask cell is the swap point. -/
theorem planBPoint_eq (scalar : NonZeroScalar) (tape : Coins × Oracle) (cell : Cell) :
    planBPoint garblerKeys (restOf tape) cell = garblerPointOf scalar tape (siteIndex cell) := by
  obtain ⟨⟨lane, chunk, switch, element⟩, block⟩ := cell
  show _ = garblerPointOf scalar tape (scaleIndexOf lane chunk switch.val element block)
  rw [Hidden.garblerPointOf_scale]
  show (garbleChunk (oracleOf (restOf tape).2 fun _ => Equiv.refl Block) lane _ _ chunk).1 switch = _
  rw [garbleChunk_congr (first := oracleOf (restOf tape).2 fun _ => Equiv.refl Block)
    (second := tape.2.1)
    (fun lane chunk fold entry half => (restOracle_hot tape lane chunk fold entry half).symm)]
  rfl

/-- A garbler scale question is at a mask site. -/
theorem scale_site (lane : Lane) (chunk : Fin chunkCount) (switch : Fin (2 ^ chunkBits))
    (element : Fin elementCountX) (block : Fin 3) (small : element.val < laneCount lane) :
    FixedIndex.scale lane chunk switch element block ∈ Set.range siteIndex := by
  have width := Hidden.chunkWidth_eq_two chunk
  have switchSmall : switch.val < 2 ^ chunkWidth chunk := by
    rw [width]
    exact switch.isLt
  refine ⟨(⟨lane, chunk, ⟨switch.val, switchSmall⟩, ⟨element.val, small⟩⟩, block), ?_⟩
  show scaleIndexOf lane chunk switch.val (⟨element.val, small⟩ : Fin (laneCount lane)) block = _
  unfold scaleIndexOf
  rw [scaleIndexNat_eq lane chunk switch.val _ block switch.isLt]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_le small (laneCount_le lane)))

end Points

/-! ### 4. The table of a tape, and why it answers the garbler -/

section Tape

variable [FieldCertificate] [GroupCertificate]

/-- The site permutations of a tape. -/
def sitesOf (tape : Coins × Oracle) : SitePerms MaskSite :=
  fun site => tape.2.1.permutation (siteIndex site)

/-- **The answer table of a tape.** -/
def tapeTable (scalar : NonZeroScalar) (tape : Coins × Oracle) : Table :=
  (tape.2.2.1, tape.2.2.2,
   fun o => tape.2.1.permutation o.1 (otherPoint scalar (tape.1, tape.2.2.1, tape.2.2.2) o.1),
   dmValues (planBPoint garblerKeys (restOf tape)) (sitesOf tape))

/-- **The table of a tape answers every garbler question as the tape does.** -/
theorem tapeTable_agree (scalar : NonZeroScalar) (tape : Coins × Oracle) :
    ∀ entry ∈ garblerTranscript scalar tape, tableAnswer (tapeTable scalar tape) entry.1 = entry.2 := by
  intro entry member
  have good := garblerTranscript_good scalar tape entry member
  have ask := garblerTranscript_ask scalar tape entry member
  have answer := transcript_mem (publicAnswer tape.2) (Programs.garbleM scalar tape.1) entry member
  obtain ⟨request, value⟩ := entry
  simp only at answer
  subst answer
  cases request with
  | fixedForward index input =>
      have point : input = garblerPointOf scalar tape index := good
      by_cases site : index ∈ Set.range siteIndex
      · obtain ⟨cell, rfl⟩ := site
        rw [tableAnswer_site]
        show xor (tape.2.1.permutation (siteIndex cell) (planBPoint garblerKeys (restOf tape) cell))
            (planBPoint garblerKeys (restOf tape) cell) ^^^ input = tape.2.1.permutation (siteIndex cell) input
        rw [planBPoint_eq scalar tape cell, ← point]
        show (tape.2.1.permutation (siteIndex cell) input ^^^ input) ^^^ input = _
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      · rw [tableAnswer_other (tapeTable scalar tape) ⟨index, site⟩]
        show tape.2.1.permutation index (otherPoint scalar (tape.1, tape.2.2.1, tape.2.2.2) index)
          = tape.2.1.permutation index input
        rw [point]
        congr 1
        refine otherPoint_eq scalar tape index ?_
        cases index with
        | hot lane chunk fold entry half => exact Or.inl ⟨lane, chunk, fold, entry, half, rfl, ask.1⟩
        | scale lane chunk switch element block =>
            exact absurd (scale_site lane chunk switch element block ask) site
        | gadget o κ position => exact Or.inr ⟨o, κ, position, rfl⟩
  | fixedInverse index output => exact ask.elim
  | encForward index input => rfl
  | encInverse index output => exact ask.elim
  | hash key => rfl

/-- The table of an assembled tape. -/
def restTable (scalar : NonZeroScalar) (rest : RestTape TapeRest) (dm : Cell → Block) : Table :=
  (rest.1.2.1, rest.1.2.2, fun o => rest.2 o (otherPoint scalar rest.1 o.1), dm)

theorem tapeTable_assemble (scalar : NonZeroScalar) (rest : RestTape TapeRest)
    (scale : SitePerms MaskSite) :
    tapeTable scalar (reassembleEquiv (assemble (rest, scale))) =
      restTable scalar rest (dmValues (planBPoint garblerKeys rest) scale) := by
  have restEq : restOf (reassembleEquiv (assemble (rest, scale))) = rest := by
    obtain ⟨⟨coins, enc, hash⟩, other⟩ := rest
    show ((coins, enc, hash), fun index : OtherIndex => (oracleOf other scale).permutation index.1) = _
    exact Prod.ext rfl (funext fun index => oracleOf_other other scale index)
  have sitesEq : sitesOf (reassembleEquiv (assemble (rest, scale))) = scale :=
    funext fun site => oracleOf_site rest.2 scale site
  unfold tapeTable restTable
  rw [restEq, sitesEq]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun o => ?_) rfl))
  exact congrFun (congrArg Equiv.toFun (oracleOf_other rest.2 scale o)) _

end Tape

/-! ### 5. The law of the table -/

section Law

/-- An average over an independent pair. -/
theorem tsum_productPMF {α β : Type} (μ : PMF α) (ν : PMF β) (f : α × β → ℝ≥0∞) :
    ∑' p, productPMF μ ν p * f p = ∑' a, μ a * ∑' b, ν b * f (a, b) := by
  simp only [productPMF_apply]
  have split : ∑' p : α × β, μ p.1 * ν p.2 * f p = ∑' a, ∑' b, μ a * ν b * f (a, b) :=
    ENNReal.tsum_prod (f := fun a b => μ a * ν b * f (a, b))
  rw [split]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [mul_assoc]

/-- An average over a uniform pair. -/
theorem tsum_uniform_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ≥0∞) :
    ∑' p, PMF.uniformOfFintype (α × β) p * f p =
      ∑' a, PMF.uniformOfFintype α a * ∑' b, PMF.uniformOfFintype β b * f (a, b) := by
  rw [uniformOfFintype_productPMF]
  exact tsum_productPMF _ _ f

/-- An average over a uniform permutation family read at one point per index. -/
theorem tsum_uniform_perms {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Nonempty α] (x : ι → α) (f : (ι → α) → ℝ≥0∞) :
    ∑' π, PMF.uniformOfFintype (ι → Equiv.Perm α) π * f (fun i => π i (x i)) =
      ∑' v, PMF.uniformOfFintype (ι → α) v * f v := by
  rw [← uniform_perms_eval x, tsum_map_mul]

variable [FieldCertificate] [GroupCertificate]

/-- **The garbler's table, averaged over the swapped tape, is an independent `tableLaw` table.** -/
theorem swapped_tapeTable (scalar : NonZeroScalar) (H : Coins × Table → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape * H (tape.1, tapeTable scalar tape) =
      ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A * H (coins, A) := by
  -- the tape is assembled from the rest and the swap kernel
  have assembled : ∑' tape, swappedChallengeTape tape * H (tape.1, tapeTable scalar tape) =
      ∑' x, swapLaw (restLaw restUniform) (planBPoint garblerKeys) x *
        (fun y : RestTape TapeRest × (Cell → Block) => H (y.1.1.1, restTable scalar y.1 y.2))
          (x.1, dmValues (planBPoint garblerKeys x.1) x.2) := by
    unfold swappedChallengeTape swappedTape
    rw [tsum_map_mul, tsum_map_mul]
    refine tsum_congr fun x => ?_
    obtain ⟨rest, scale⟩ := x
    show _ * H ((reassembleEquiv (assemble (rest, scale))).1,
      tapeTable scalar (reassembleEquiv (assemble (rest, scale)))) = _
    rw [tapeTable_assemble]
    rfl
  rw [assembled, ← tsum_map_mul (swapLaw (restLaw restUniform) (planBPoint garblerKeys))
    (fun x => (x.1, dmValues (planBPoint garblerKeys x.1) x.2))
    (fun y : RestTape TapeRest × (Cell → Block) => H (y.1.1.1, restTable scalar y.1 y.2)),
    swapLaw_dm, tsum_productPMF]
  unfold restLaw
  rw [tsum_productPMF]
  unfold restUniform
  rw [tsum_uniform_prod]
  refine tsum_congr fun coins => congrArg _ ?_
  rw [tsum_uniform_prod]
  unfold tableLaw
  rw [tsum_productPMF]
  refine tsum_congr fun enc => congrArg _ ?_
  rw [tsum_productPMF]
  refine tsum_congr fun hash => congrArg _ ?_
  rw [tsum_productPMF]
  simp_rw [← ENNReal.tsum_mul_left]
  have perms := tsum_uniform_perms (ι := OtherIndex) (α := Block)
    (fun o => otherPoint scalar (coins, enc, hash) o.1)
    (fun v => ∑' dm, fibreTape dm * H (coins, (enc, hash, v, dm)))
  simp_rw [ENNReal.tsum_mul_left]
  exact perms

/-- A function of the garbler's transcript and result, on a table. -/
def garblerView (scalar : NonZeroScalar)
    (G : Coins → List (Entry FixedIndex EncPRF.PermutationIndex) → Public × InputMacKey → ℝ≥0∞)
    (x : Coins × Table) : ℝ≥0∞ :=
  G x.1 (transcript (tableAnswer x.2) (Programs.garbleM scalar x.1))
    ((Programs.garbleM scalar x.1).eval (tableAnswer x.2))

/-- **The garbler on the swapped tape is the garbler on an independent `tableLaw` table.** -/
theorem swapped_reduce (scalar : NonZeroScalar)
    (G : Coins → List (Entry FixedIndex EncPRF.PermutationIndex) → Public × InputMacKey → ℝ≥0∞) :
    ∑' tape, swappedChallengeTape tape *
        G tape.1 (garblerTranscript scalar tape) ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2))
      = ∑' coins, PMF.uniformOfFintype Coins coins * ∑' A, tableLaw A *
          G coins (transcript (tableAnswer A) (Programs.garbleM scalar coins))
            ((Programs.garbleM scalar coins).eval (tableAnswer A)) := by
  have pointwise : ∀ tape : Coins × Oracle,
      G tape.1 (garblerTranscript scalar tape) ((Programs.garbleM scalar tape.1).eval (publicAnswer tape.2))
        = garblerView scalar G (tape.1, tapeTable scalar tape) := by
    intro tape
    have same := transcript_agree (Programs.garbleM scalar tape.1) (publicAnswer tape.2)
      (tableAnswer (tapeTable scalar tape)) (tapeTable_agree scalar tape)
    unfold garblerTranscript garblerView
    rw [same.1, same.2]
  have step := swapped_tapeTable scalar (garblerView scalar G)
  simp only [garblerView] at step
  rw [← step]
  exact tsum_congr fun tape => by rw [pointwise tape]; rfl

end Law

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst
