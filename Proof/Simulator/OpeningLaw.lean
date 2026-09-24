/-
**The opening law** (`SimMachine.OpeningLaw`, stated by P2d in `Stage2Spec.lean`).

From every memory satisfying `OpeningPre`, the oracle-free opening `openingFree`
(`tail, horner, lambdas, lifts, solve, preimages`) read through `openView` is P3's
`openingBlocks boundedSamplers …` read through `blocksView`:

1. the tail is `optionProduct 90 curvePointLaw` (`memSem_tail`), and Horner's head clamp aborts
   exactly on `tailLaw`'s check (`memSem_horner`), so tail + head is `boundedSamplers.tail`;
2. the randomisers are `boundedSamplers.lift` (`memSem_lambdas`), and the lifts are `targetRows`
   (`memSem_lifts`);
3. the solve stores P3's `collectorTargets` (`memSem_solve`);
4. the preimages are `preimages boundedSamplers` factored through the same rejection draws
   (`memSem_preimages`, `preimages_eq`); the limb cells hold `blockWord (limbAt b …)` because
   `y + p · m < 2^384` on the draws' support (`preimage_small`);
5. the opening writes only its own cells (`SameOff`), so `tmpJStar`, `E*`, the labels and the
   stacks are unchanged.
-/

import Proof.Simulator.OpeningPreimages
import Proof.Simulator.Stage2Spec

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open BN254 Cryptography Cryptography.BoundedMachine Blocks GarbledCircuit
open Kriterion.ArgoMAC.Phase3.Glue

noncomputable section

variable [FieldCertificate]

/-! ### Small facts -/

omit [FieldCertificate] in
theorem gammaConst_eq_rowField (row : RowGamma) : ∀ slot, gammaConst row slot = rowField row slot
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | _ + 11 => rfl

theorem readWords_outputWords (target : Point) : readWords (outputWords target) = some target := by
  cases target with
  | zero => rfl
  | some x y valid =>
      rw [← readWords_pointWords (.some x y valid)]
      rfl

/-- A cell below the opening's region, other than `tmpM`, is not one of the opening's cells. -/
theorem not_openCell (address : Nat) (below : address < openBase) (notM : address ≠ tmpM) :
    ¬ OpenCell (word address) := by
  unfold OpenCell
  rw [word_small (by unfold openBase at below; omega)]
  intro inside
  rcases inside with inside | same
  · omega
  · exact notM (word_injective (by unfold openBase at below; omega)
      (by unfold tmpM tmpBase; omega) same)

theorem labelVector_sameOff {before after : Word → Word} (same : SameOff before after) :
    labelVector after = labelVector before := by
  unfold labelVector
  congr 1
  funext index
  rw [same _ (not_openCell _ (by unfold labelBase openBase; omega)
    (by unfold labelBase tmpM tmpBase; omega))]

omit [FieldCertificate] in
/-- **The preimage bound**: `y + p · m < 2^384` for every multiplier the draw keeps. -/
theorem preimage_small (value : BaseField) (mult : Nat) (below : mult < multBound value) :
    value.val + pNat * mult < 2 ^ 384 := by
  have split : pNat * preimageQuotient + preimageRemainder = 2 ^ 384 := Nat.div_add_mod _ _
  have valueBelow : value.val < pNat := value.val_lt
  unfold multBound at below
  by_cases small : value.val < preimageRemainder
  · rw [if_pos small] at below
    have : pNat * mult ≤ pNat * preimageQuotient := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [if_neg small] at below
    have : pNat * (mult + 1) ≤ pNat * preimageQuotient := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

omit [FieldCertificate] in
/-- Below `2^384`, the machine's limb words are the zero-extended limbs. -/
theorem limbWords_block (value : Nat) (small : value < 2 ^ 384) (block : Fin 3) :
    wordAt (limbWords value) block.val = blockWord (limbAt block (limbs value)) := by
  fin_cases block
  · show word (value % 2 ^ 128) = BitVec.ofNat 256 (BitVec.ofNat 128 value).toNat
    rw [BitVec.toNat_ofNat]
  · show word (value / 2 ^ 128 % 2 ^ 128) =
      BitVec.ofNat 256 (BitVec.ofNat 128 (value / 2 ^ 128)).toNat
    rw [BitVec.toNat_ofNat]
  · show word (value / 2 ^ 256) = BitVec.ofNat 256 (BitVec.ofNat 128 (value / 2 ^ 256)).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

omit [FieldCertificate] in
/-- A value of an `optionProduct` is a value of every factor. -/
theorem optionProduct_values {α : Type} :
    ∀ (count : Nat) (sample : Fin count → PMF (Option α)) (values : Fin count → α),
      some values ∈ (optionProduct count sample).support →
        ∀ index, some (values index) ∈ (sample index).support
  | 0, _, _, _, index => index.elim0
  | count + 1, sample, values, member, index => by
      simp only [optionProduct, PMF.mem_support_bind_iff] at member
      obtain ⟨head, headMember, rest⟩ := member
      cases head with
      | none => simp at rest
      | some head =>
          simp only [PMF.mem_support_map_iff] at rest
          obtain ⟨tail, tailMember, same⟩ := rest
          cases tail with
          | none => simp at same
          | some tail =>
              simp only [Option.map_some, Option.some.injEq] at same
              subst same
              refine Fin.cases ?_ (fun later => ?_) index
              · simpa using headMember
              · simpa using optionProduct_values count (fun index => sample index.succ) tail
                  tailMember later

theorem solveWords_component (kappaValue : BaseField) (target row : FieldMacToECMac.HomogeneousValue)
    (collector : Fin 3) :
    wordAt (solveWords kappaValue target row) collector.val =
      fieldWord (kappaValue * (collectorComponent collector target - collectorComponent collector row)) := by
  fin_cases collector <;> rfl

/-! ### From the lifts to the view -/

variable [GroupCertificate]

/-- The abstract collector targets of the opening. -/
abbrev absTargets (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (lift : Fin digitCount → NonZeroBase) :
    Fin digitCount × Fin 3 → BaseField :=
  collectorTargets (BitInput.ofAffine input)
    (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable source.publicValue)
      (Pipeline.digitValues pointX pointY) (BitInput.ofAffine input).toAffine)
    (targetRows target tail lift)

omit [GroupCertificate] in
/-- The views agree once the limb cells hold the drawn limbs and the rest is untouched. -/
theorem view_eq (memory0 final : Memory) (blocks : Fin digitCount × Fin 3 → Block × Block × Block)
    (same : SameOff memory0.ram final.ram) (bitsSame : final.bits = memory0.bits)
    (limbCells : ∀ (digit : Fin digitCount) (collector block : Fin 3),
      final.ram (word (openLimb digit collector block)) =
        blockWord (limbAt block (blocks (digit, collector)))) :
    openView final = blocksView memory0 blocks := by
  unfold openView blocksView
  rw [same _ (not_openCell _ (by unfold tmpJStar tmpBase openBase; omega)
      (by unfold tmpJStar tmpM; omega)),
    same _ (not_openCell _ (by unfold hotLabelBase openBase; omega)
      (by unfold hotLabelBase tmpM tmpBase; omega)),
    labelVector_sameOff same, bitsSame]
  congr 1
  funext digit collector block
  exact limbCells digit collector block

/-- **The lifts, the solve and the preimages**, read through the views: P3's `preimages` of the
collector targets of the drawn tail and randomisers. -/
theorem rest_law (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory0 : Memory) (pre : OpeningPre source input target pointX pointY memory0)
    (tail : Vector FieldMacToECMac.AffineOffset 90) (lift : Fin digitCount → NonZeroBase)
    (memory : Memory) (same : SameOff memory0.ram memory.ram) (bitsSame : memory.bits = memory0.bits)
    (lamCells : ∀ digit : Fin digitCount,
      memory.ram (word (openLambda digit)) = fieldWord (lift digit).value)
    (pointCells : ∀ digit : Fin digitCount, (memory.ram (word (openPoint digit)),
      memory.ram (word (openPoint digit + 1)), memory.ram (word (openPoint digit + 2))) =
        pointWords (digitPoints target tail digit)) :
    ((Prog.seq Opening.lifts (Prog.seq Opening.solve (Prog.seq Opening.preimages (.skip 0)))).memSem
        memory).map (Option.map openView) =
      (preimages boundedSamplers (absTargets source input target pointX pointY tail lift)).map
        (Option.map (blocksView memory0)) := by
  set points : Nat → Point := fun digit =>
    if inside : digit < digitCount then digitPoints target tail ⟨digit, inside⟩ else 0 with pointsDef
  set lams : Nat → BaseField := fun digit =>
    if inside : digit < digitCount then (lift ⟨digit, inside⟩).value else 0 with lamsDef
  obtain ⟨lifted, runLifts, bitsLifted, sameLifted, rowsLifted, _⟩ := memSem_lifts memory points lams
    (fun digit inside => by
      simp only [lamsDef, dif_pos (show digit < digitCount from inside)]
      exact lamCells ⟨digit, inside⟩)
    (fun digit inside => by
      simp only [pointsDef, dif_pos (show digit < digitCount from inside)]
      exact pointCells ⟨digit, inside⟩) 91 le_rfl
  have runLifts' : Opening.lifts.memSem memory = PMF.pure (some lifted) := runLifts
  rw [memSem_pure_seq runLifts']
  have sameToLifted : SameOff memory0.ram lifted.ram := same.trans sameLifted
  have inputIs : (BitInput.ofAffine input).toAffine = input := BitInput.toAffineOfAffine input
  obtain ⟨solved, runSolve, bitsSolved, sameSolved, targetsSolved, _⟩ := memSem_solve lifted
    (BitInput.ofAffine input).toAffine (kappa (BitInput.ofAffine input)) (fun digit => source.rows.get digit)
    (fun digit => Pipeline.digitValues pointX pointY digit) (fun digit => targetRows target tail lift digit)
    (by
      rw [sameToLifted _ (not_openCell _ (by unfold reqX requestBase openBase; omega)
        (by unfold reqX requestBase tmpM tmpBase; omega)), pre.reqXCell, wordField_fieldWord, inputIs])
    (by
      rw [sameToLifted _ (not_openCell _ (by unfold reqY requestBase openBase; omega)
        (by unfold reqY requestBase tmpM tmpBase; omega)), pre.reqYCell, wordField_fieldWord, inputIs])
    (by
      rw [sameToLifted _ (not_openCell _ (by unfold tmpKappa tmpBase openBase; omega)
        (by unfold tmpKappa tmpM; omega)), pre.kappaCell, wordField_fieldWord])
    (fun digit slot inside => by
      have digitSmall := digit.isLt
      rw [sameToLifted _ (not_openCell _ (by addr_arith) (by addr_arith)),
        pre.rowCells digit slot inside, wordField_fieldWord, gammaConst_eq_rowField])
    (fun digit element => by
      have digitSmall := digit.isLt
      have slotSmall : element.slot.val < 5 := element.slot.isLt
      rw [sameToLifted _ (not_openCell _ (by addr_arith) (by addr_arith))]
      have := pre.accXCells (xElementIndex digit element)
      rw [show Opening.xCell (5 * digit.val + element.slot.val) =
        accBase + (xElementIndex digit element).val from rfl, this, wordField_fieldWord]
      rfl)
    (fun digit element => by
      have digitSmall := digit.isLt
      have slotSmall : element.slot.val < 4 := element.slot.isLt
      rw [sameToLifted _ (not_openCell _ (by addr_arith) (by addr_arith))]
      have := pre.accYCells (yElementIndex digit element)
      rw [show Opening.yCell (4 * digit.val + element.slot.val) =
        accBase + 458 + (yElementIndex digit element).val from rfl, this, wordField_fieldWord]
      rfl)
    (fun digit position inside => by
      rw [rowsLifted digit.val digit.isLt position inside]
      simp only [pointsDef, lamsDef, dif_pos (show digit.val < digitCount from digit.isLt)]
      rfl) 91 le_rfl
  have runSolve' : Opening.solve.memSem lifted = PMF.pure (some solved) := runSolve
  rw [memSem_pure_seq runSolve']
  set ys := absTargets source input target pointX pointY tail lift with ysDef
  have targetCells : ∀ (digit : Fin digitCount) (collector : Fin 3),
      solved.ram (word (openTarget digit collector)) = fieldWord (ys (digit, collector)) := by
    intro digit collector
    rw [← openTarget_shift, targetsSolved digit digit.isLt collector collector.isLt,
      solveWords_component, ysDef]
    have getIs : (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable source.publicValue)
        (Pipeline.digitValues pointX pointY) (BitInput.ofAffine input).toAffine).get digit =
        FieldMacToECMac.evaluateGamma (source.rows.get digit) (BitInput.ofAffine input).toAffine
          (Pipeline.digitValues pointX pointY digit) := Vector.get_ofFn _ _
    unfold absTargets collectorTargets
    rw [getIs]
  have sameToSolved : SameOff memory0.ram solved.ram := sameToLifted.trans sameSolved
  rw [memSem_seq, memSem_preimages solved ys targetCells, preimages_eq, PMF.bind_map]
  have skipIs : (kleisli (Prog.skip 0).memSem ∘
      Option.map (foldStore (preStep ys) (digitCount * 3) solved)) =
      PMF.pure ∘ Option.map (foldStore (preStep ys) (digitCount * 3) solved) := by
    funext result; cases result <;> rfl
  rw [skipIs, PMF.bind_pure_comp, PMF.map_comp, PMF.map_comp, ← PMF.bind_pure_comp,
    ← PMF.bind_pure_comp]
  apply PMF.bind_congr
  intro drawn positive
  cases drawn with
  | none => rfl
  | some mults =>
      have member := (PMF.mem_support_iff _ _).mpr positive
      have bound : ∀ index, mults index < multBound (ys (finProdFinEquiv.symm index)) := by
        intro index
        have := rejectLaw_support _ _ _ _ (optionProduct_values _ _ mults member index)
        simpa using this.1
      simp only [Function.comp_apply, Option.map_some]
      refine congrArg (fun view => PMF.pure (some view)) ?_
      apply view_eq
      · exact sameToSolved.trans (preFold_sameOff ys solved mults)
      · rw [preFold_bits, bitsSolved, bitsLifted, bitsSame]
      · intro digit collector block
        have limb := preFold_limb ys solved mults (finProdFinEquiv (digit, collector)) block.val
          block.isLt
        rw [Equiv.symm_apply_apply] at limb
        have address : openLimb digit collector block =
            openBase + 2000 + 3 * (finProdFinEquiv (digit, collector)).val + block.val := by
          rw [finProdFinEquiv_apply_val]; dsimp only; unfold openLimb; omega
        rw [address, limb]
        have below := bound (finProdFinEquiv (digit, collector))
        rw [Equiv.symm_apply_apply] at below
        exact limbWords_block _ (preimage_small _ _ below) block

/-! ### The head, the randomisers, and the whole opening -/

/-- The head clamp's point. -/
abbrev headPoint (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) : Point :=
  target - radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints (Vector.ofFn points))

/-- The memory after the tail and the head clamp. -/
abbrev headMem (memory : Memory) (target : Point) (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    Memory :=
  clearRegs (withRam (tailFold memory points) (putPoint (tailFold memory points).ram (openPoint 0)
    (pointWords (headPoint target points)))) headScratch

omit [FieldCertificate] [GroupCertificate] in
theorem wordAt_eq_triple (words : Word × Word × Word) (first second third : Word)
    (h0 : first = wordAt words 0) (h1 : second = wordAt words 1) (h2 : third = wordAt words 2) :
    (first, second, third) = words := by
  rw [h0, h1, h2]; rfl

/-- The digit points sit at `openPoint d` after the tail, the head and the randomisers. -/
theorem pointCells_after (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) (lams : Fin digitCount → NonZeroBase)
    (digit : Fin digitCount) :
    ((foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 1)),
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + 2))) =
        pointWords (digitPoints target (Vector.ofFn points) digit) := by
  have digitSmall : digit.val < 91 := digit.isLt
  have lamOff : ∀ position, position < 3 →
      (foldStore lamMem 91 (headMem memory target points) lams).ram (word (openPoint digit + position)) =
        putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) := by
    intro position inside
    refine (lamFold_off (headMem memory target points) lams (word (openPoint digit + position))
      (fun index bound => word_ne (by unfold openPoint openBase; omega)
        (by unfold openLambda openBase; omega) (by unfold openPoint openLambda; omega))).trans ?_
    unfold headMem
    rw [(clearRegs_other _ _).1, withRam_ram]
  have atCell : ∀ position, position < 3 →
      putPoint (tailFold memory points).ram (openPoint 0) (pointWords (headPoint target points))
          (word (openPoint digit + position)) =
        wordAt (pointWords (digitPoints target (Vector.ofFn points) digit)) position := by
    intro position inside
    by_cases head : digit.val = 0
    · rw [head, putPoint_at _ _ _ _ (by unfold openPoint openBase; omega) inside]
      unfold digitPoints
      rw [dif_pos head]
    · rw [putPoint_off _ _ _ _ (fun position' inside' => word_ne
          (by unfold openPoint openBase; omega) (by unfold openPoint openBase; omega)
          (by unfold openPoint; omega))]
      have tailCell := tailFold_at memory points ⟨digit.val - 1, by omega⟩ position inside
      have digitIs : (⟨digit.val - 1, by omega⟩ : Fin 90).val + 1 = digit.val := by
        show digit.val - 1 + 1 = digit.val; omega
      rw [digitIs, offsetWords_eq] at tailCell
      rw [tailCell]
      unfold digitPoints
      rw [dif_neg head]
      have getIs : (Vector.ofFn points).get ⟨digit.val - 1, by omega⟩ =
          points ⟨digit.val - 1, by omega⟩ := Vector.get_ofFn _ _
      rw [getIs]
  apply wordAt_eq_triple
  · have := lamOff 0 (by omega)
    rw [Nat.add_zero] at this
    rw [this, ← Nat.add_zero (openPoint digit), atCell 0 (by omega)]
  · rw [lamOff 1 (by omega), atCell 1 (by omega)]
  · rw [lamOff 2 (by omega), atCell 2 (by omega)]

theorem headMem_ram (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).ram = putPoint (tailFold memory points).ram (openPoint 0)
      (pointWords (headPoint target points)) := by
  unfold headMem
  rw [(clearRegs_other _ _).1, withRam_ram]

theorem headMem_bits (memory : Memory) (target : Point)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    (headMem memory target points).bits = memory.bits := by
  unfold headMem
  rw [(clearRegs_other _ _).2, withRam_bits, tailFold_bits]

omit [GroupCertificate] in
/-- `memSem_lambdas` with the randomisers indexed by `Fin digitCount` (as `liftLaw` draws them). -/
theorem memSem_lambdas_digit (memory : Memory) :
    Opening.lambdas.memSem memory =
      liftLaw.map (Option.map fun lams : Fin digitCount → NonZeroBase => foldStore lamMem 91 memory lams) :=
  memSem_lambdas memory

/-- **The randomisers onward**: the machine after the head clamp against P3's lift step. -/
theorem lift_law (source : Stage1Source) (input : AffineInput) (target : Point)
    (pointX : Fin pointElementCountX → BaseField) (pointY : Fin pointElementCountY → BaseField)
    (memory : Memory) (pre : OpeningPre source input target pointX pointY memory)
    (points : Fin 90 → FieldMacToECMac.AffineOffset) :
    ((Prog.seq Opening.lambdas (Prog.seq Opening.lifts (Prog.seq Opening.solve
        (Prog.seq Opening.preimages (.skip 0))))).memSem (headMem memory target points)).map
        (Option.map openView) =
      (liftLaw.bind fun lift => match lift with
        | none => PMF.pure none
        | some lift => preimages boundedSamplers
            (absTargets source input target pointX pointY (Vector.ofFn points) lift)).map
        (Option.map (blocksView memory)) := by
  rw [memSem_seq, memSem_lambdas_digit, PMF.bind_map, PMF.map_bind, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none => simp [kleisli, PMF.pure_map]
  | some lams =>
      simp only [Function.comp_apply, Option.map_some, kleisli]
      have sameHead : SameOff (tailFold memory points).ram (headMem memory target points).ram := by
        rw [headMem_ram]
        exact sameOff_putPoint _ 0 (by norm_num) _
      exact rest_law source input target pointX pointY memory pre (Vector.ofFn points) lams
        (foldStore lamMem 91 (headMem memory target points) lams)
        (((tailFold_sameOff memory points).trans sameHead).trans
          (lamFold_sameOff (headMem memory target points) lams))
        ((lamFold_bits (headMem memory target points) lams).trans (headMem_bits memory target points))
        (fun digit => lamFold_at (headMem memory target points) lams digit)
        (fun digit => pointCells_after memory target points lams digit)

omit [FieldCertificate] [GroupCertificate] in
/-- **The opening law** (P2d's `OpeningLaw`, `Stage2Spec.lean`): the machine's oracle-free
opening, read through `openView`, is `openingBlocks boundedSamplers …` read through
`blocksView`. -/
theorem openingLaw : OpeningLaw := by
  intro _ _ source input target pointX pointY memory pre
  have tailIs : (boundedSamplers).tail = tailLaw := rfl
  have liftIs : (boundedSamplers).lift = liftLaw := rfl
  unfold openingFree openingBlocks
  simp only [Prog.seqList]
  rw [memSem_seq, memSem_tail, PMF.bind_map, PMF.map_bind, tailIs, liftIs]
  unfold tailLaw
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun drawn => ?_)
  cases drawn with
  | none => simp [kleisli, PMF.pure_map]
  | some points =>
      simp only [Function.comp_apply, Option.map_some, kleisli, Option.bind_some]
      have request : readWords ((tailFold memory points).ram (word reqTag0),
          (tailFold memory points).ram (word reqQX), (tailFold memory points).ram (word reqQY)) =
            some target := by
        rw [tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)),
          tailFold_sameOff memory points _ (not_openCell _ (by addr_arith) (by addr_arith)),
          pre.outputCells, readWords_outputWords]
      rw [memSem_seq, memSem_horner _ points target (tailFold_at memory points) request]
      by_cases clamp : FieldMacToECMac.clampedFirst (Vector.ofFn points) = 0
      · rw [if_pos clamp, if_pos clamp, PMF.pure_bind]
        simp [kleisli, PMF.pure_map]
      · rw [if_neg clamp, if_neg clamp, PMF.pure_bind]
        simp only [kleisli]
        exact lift_law source input target pointX pointY memory pre points

end

end Kriterion.ArgoMAC.PlanB.SimMachine
