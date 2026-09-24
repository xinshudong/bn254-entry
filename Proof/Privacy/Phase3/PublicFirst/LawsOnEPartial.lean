/-
**Phase 3, P1r — `LawOn`, step (E), part 4: the private side's collector targets are F4's
designated solve.**

On the private side the preimages are drawn at the collector targets
`κ · (W − R)`, `W` the true rows at `u`, `R` the evaluator's rows at the values its
opening delivers with the designated limbs zeroed (`OnE.targetsOf`). Here:

* `laneValue_eq`/`deliveredOf_eq`: a lane's delivered value is F4's `deliveredOf` (`ι(α)·J`
  plus the free fold of the inactive masks);
* `digitValues_zeroDesig`: on the source of F4's cells, with the designated limbs zeroed, the
  opening's digit values are **`digitPartial`** of the cells' joins and the tape's visible masks
  (the designated masks read `sampleFp 0 0 0 = 0`, F4 leaves them out);
* `targets_eq`: the collector target of `(d, c)` is `JointExactness.simDesignated` at the true rows
  (`κ = κ⁻¹`, and the collector has coefficient one in its own row only).
-/

import Proof.Privacy.Phase3.PublicFirst.LawsOnEPoints

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option autoImplicit false

namespace Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB Kriterion.ArgoMAC.FieldMacToECMac
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Phase3.Glue (openingQueriesM collectorTargets IsDesignated designatedIndex
  designatedSwitch chunkZero collectorElement)
open Kriterion.ArgoMAC.Phase3.Lazy (Cell Tape LState)
open scoped ENNReal

noncomputable section

/-! ### 1. A lane's value is F4's `deliveredOf` -/

theorem evalScaleOf_eq {count width : Nat} (masks : Fin (2 ^ width) → Fin count → BaseField)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) (e : Fin count) (zero : masks alpha e = 0) :
    Programs.evalScaleOf width masks alpha join e =
      iota _ alpha * join e + ∑ j, (iota _ j - iota _ alpha) * masks j e := by
  unfold Programs.evalScaleOf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ alpha), ← Finset.add_sum_erase _ _ (Finset.mem_univ alpha),
    if_pos rfl, zero, mul_zero, zero_add]
  have rest : ∀ j ∈ Finset.univ.erase alpha, iota _ j * (if j = alpha then join e -
      ∑ other ∈ Finset.univ.erase alpha, masks other e else masks j e) = iota _ j * masks j e :=
    fun j member => by rw [if_neg (Finset.ne_of_mem_erase member)]
  rw [Finset.sum_congr rfl rest, mul_sub, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem laneValue_eq (lane : Lane) (scale : Fin chunkCount → Fin (laneCount lane) → BaseField)
    (bits : BitVec coordinateBitCount) (T : Tape) (e : Fin (laneCount lane)) :
    laneValue lane scale bits T e = ∑ c, iota _ (chunkOf bits c) * scale c e +
      ∑ c, ∑ j, (iota _ j - iota _ (chunkOf bits c)) * chunkMasks lane c (chunkOf bits c) T j e := by
  unfold laneValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => evalScaleOf_eq _ _ _ e ?_
  unfold chunkMasks
  rw [if_pos rfl]

theorem deliveredOf_eq (α : Alpha) (J : Fin chunkCount → BaseField)
    (Y : ChunkSwitch → BaseField) :
    deliveredOf α J Y = ∑ c, iota _ (α c) * J c +
      ∑ c, ∑ j, (iota _ j - iota _ (α c)) * (if j = α c then 0 else Y ⟨c, j⟩) := by
  unfold deliveredOf
  refine congrArg (_ + ·) ?_
  have split := sum_split_active α (fun cs =>
    (switchIota cs - iota _ (α cs.1)) * (if cs.2 = α cs.1 then 0 else Y cs))
  have active : ∑ c : Fin chunkCount, (switchIota (⟨c, α c⟩ : ChunkSwitch) - iota _ (α c)) *
      (if α c = α c then 0 else Y ⟨c, α c⟩) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [if_pos rfl, mul_zero]
  have inactive : ∀ cs : {cs : ChunkSwitch // ¬ Active α cs},
      (switchIota cs.1 - iota _ (α cs.1.1)) * (if cs.1.2 = α cs.1.1 then 0 else Y cs.1) =
        (switchIota cs.1 - iota _ (α cs.1.1)) * Y cs.1 := fun cs => by
    rw [if_neg (show ¬ (cs.1.2 = α cs.1.1) from cs.2)]
  dsimp only at split
  rw [active, zero_add] at split
  rw [← Fintype.sum_congr _ _ inactive, ← split, Fintype.sum_sigma]
  rfl

/-! ### 2. The designated sites -/

variable [FieldCertificate] [GroupCertificate] (input : AffineInput)

/-- The designated site of a (digit, collector). -/
def desSite (bits : BitInput) (d : Fin digitCount) (c : Fin 3) : MaskSite :=
  ⟨.pointX, chunkZero, designatedSwitch bits, xElementIndex d (collectorElement c)⟩

theorem isDesignated_site (bits : BitInput) (s : MaskSite) (b : Fin 3) :
    IsDesignated bits (siteIndex (s, b)) ↔ ∃ d c, s = desSite bits d c := by
  constructor
  · rintro ⟨d, c, b', same⟩
    have sites := siteIndex_injective (a₁ := (desSite bits d c, b')) (a₂ := (s, b)) same
    exact ⟨d, c, (congrArg Prod.fst sites).symm⟩
  · rintro ⟨d, c, rfl⟩
    exact ⟨d, c, b, rfl⟩

theorem sampleFp_zero : sampleFp 0 0 0 = 0 := by
  simp [sampleFp, blocksToNat]

open Classical in
theorem masksOf_zeroDesig (bits : BitInput) (T : Tape) (s : MaskSite) :
    masksOf (OnLaw.zeroDesig bits T) s = if ∃ d c, s = desSite bits d c then 0 else masksOf T s := by
  have cell : ∀ b, OnLaw.zeroDesig bits T (s, b) =
      if ∃ d c, s = desSite bits d c then 0 else T (s, b) := fun b => by
    unfold OnLaw.zeroDesig
    simp only [isDesignated_site]
  show sampleFp _ _ _ = _
  rw [cell, cell, cell]
  split_ifs
  · exact sampleFp_zero
  · rfl

/-- The designated (chunk, switch) is F4's. -/
theorem designated_eq :
    (offShape input).designated = ⟨chunkZero, designatedSwitch (BitInput.ofAffine input)⟩ := rfl

theorem isCollector_inl (xe : XElement) :
    IsCollector (.inl xe) ↔ ∃ c : Fin 3, collectorElement c = xe := by
  constructor
  · rintro (h | h | h) <;> simp only [Sum.inl.injEq] at h <;> subst h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨c, rfl⟩
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- A point-X digit site is designated exactly when its element is a collector at F4's designated
(chunk, switch). -/
theorem pointX_desSite (d : Fin digitCount) (xe : XElement) (cs : ChunkSwitch) :
    (∃ d' c, (⟨.pointX, cs.1, cs.2, xElementIndex d xe⟩ : MaskSite) = desSite (BitInput.ofAffine input) d' c) ↔
      IsCollector (.inl xe) ∧ cs = (offShape input).designated := by
  rw [designated_eq, isCollector_inl]
  obtain ⟨c, j⟩ := cs
  constructor
  · rintro ⟨d', col, same⟩
    unfold desSite at same
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at same
    obtain ⟨rfl, same⟩ := same
    simp only [heq_eq_eq] at same
    have sw := congrArg Prod.fst same
    have slot := congrArg Prod.snd same
    simp only at sw slot
    subst sw
    have pair := xElementIndex_injective (a₁ := (d, xe)) (a₂ := (d', collectorElement col)) slot
    exact ⟨⟨col, (congrArg Prod.snd pair).symm⟩, rfl⟩
  · rintro ⟨⟨col, rfl⟩, same⟩
    simp only [Sigma.mk.inj_iff] at same
    obtain ⟨rfl, same⟩ := same
    have : j = designatedSwitch (BitInput.ofAffine input) := eq_of_heq same
    subst this
    exact ⟨d, col, rfl⟩

theorem pointY_not_desSite (d : Fin digitCount) (ye : YElement) (cs : ChunkSwitch) :
    ¬ ∃ d' c, (⟨.pointY, cs.1, cs.2, yElementIndex d ye⟩ : MaskSite) = desSite (BitInput.ofAffine input) d' c := by
  rintro ⟨d', c, same⟩
  unfold desSite at same
  simp only [Sigma.mk.inj_iff] at same
  cases same.1

/-! ### 3. The opening's digit values are F4's `digitPartial` -/

theorem readPointX_cells (cells : PublicCells) (key : InputMacKey) (c : Fin chunkCount)
    (d : Fin digitCount) (xe : XElement) :
    Pipeline.readPointX (unpack ((cellsSource cells key).publicValue.scale.get c)) (xElementIndex d xe) =
      (cells.1 d).1 (.inl xe) c := by
  rw [cellsSource_scale, Vector.get_ofFn, unpack_pack_eq]
  show Pipeline.readPointX (Pipeline.assembleWord _ _ _ _) _ = _
  rw [Pipeline.readPointX_assembleWord]
  show (cells.1 (pointXSlots.symm (pointXSlots (d, xe))).1).1
    (.inl (pointXSlots.symm (pointXSlots (d, xe))).2) c = _
  rw [Equiv.symm_apply_apply]

theorem readPointY_cells (cells : PublicCells) (key : InputMacKey) (c : Fin chunkCount)
    (d : Fin digitCount) (ye : YElement) :
    Pipeline.readPointY (unpack ((cellsSource cells key).publicValue.scale.get c)) (yElementIndex d ye) =
      (cells.1 d).1 (.inr ye) c := by
  rw [cellsSource_scale, Vector.get_ofFn, unpack_pack_eq]
  show Pipeline.readPointY (Pipeline.assembleWord _ _ _ _) _ = _
  rw [Pipeline.readPointY_assembleWord]
  show (cells.1 (pointYSlots.symm (pointYSlots (d, ye))).1).1
    (.inr (pointYSlots.symm (pointYSlots (d, ye))).2) c = _
  rw [Equiv.symm_apply_apply]

theorem digitValues_inl (xs : Fin pointElementCountX → BaseField) (ys : Fin pointElementCountY → BaseField)
    (d : Fin digitCount) (xe : XElement) : Pipeline.digitValues xs ys d (.inl xe) = xs (xElementIndex d xe) :=
  rfl

theorem digitValues_inr (xs : Fin pointElementCountX → BaseField) (ys : Fin pointElementCountY → BaseField)
    (d : Fin digitCount) (ye : YElement) : Pipeline.digitValues xs ys d (.inr ye) = ys (yElementIndex d ye) :=
  rfl

theorem pointValues_fst (P : Public) (bits : BitInput) (T : Tape) :
    (pointValues P bits T).1 = laneValue .pointX (fun chunk => Pipeline.readPointX (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .x) T := rfl

theorem pointValues_snd (P : Public) (bits : BitInput) (T : Tape) :
    (pointValues P bits T).2 = laneValue .pointY (fun chunk => Pipeline.readPointY (unpack (P.scale.get chunk)))
      (Pipeline.coordBits bits .y) T := rfl

theorem alphaX_eq (c : Fin chunkCount) :
    chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .x) c = (offShape input).alphaX c := rfl

theorem alphaY_eq (c : Fin chunkCount) :
    chunkOf (Pipeline.coordBits (BitInput.ofAffine input) .y) c = (offShape input).alphaY c := rfl

/-- **The opening's digit values, with the designated limbs zeroed, are F4's `digitPartial`** of
the cells' joins and the tape's visible masks. -/
theorem digitValues_zeroDesig (cells : PublicCells) (key : InputMacKey) (T : Tape) (d : Fin digitCount) :
    Pipeline.digitValues
        (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (OnLaw.zeroDesig (BitInput.ofAffine input) T)).1
        (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (OnLaw.zeroDesig (BitInput.ofAffine input) T)).2 d =
      digitPartial (offShape input) (cells.1 d).1
        (digitVisible (offShape input) ((maskSiteEquiv (masksOf T)).1 d)) := by
  funext e
  unfold digitPartial
  rw [deliveredOf_eq]
  rcases e with xe | ye
  · rw [digitValues_inl, pointValues_fst]
    refine (laneValue_eq .pointX _ _ _ (xElementIndex d xe)).trans ?_
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_)
      (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_)
    · rw [readPointX_cells, alphaX_eq]
      rfl
    · rw [alphaX_eq]
      unfold chunkMasks
      show _ * (if j = (offShape input).alphaX c then 0 else _) =
        _ * (if j = (offShape input).alphaX c then 0 else _)
      by_cases active : j = (offShape input).alphaX c
      · rw [if_pos active, if_pos active, mul_zero, mul_zero]
      · rw [if_neg active, if_neg active, masksOf_zeroDesig]
        congr 1
        unfold extendVisible
        have inactive : ¬ Active ((offShape input).digitAlpha (.inl xe)) ⟨c, j⟩ := active
        by_cases des : IsCollector (.inl xe) ∧ (⟨c, j⟩ : ChunkSwitch) = (offShape input).designated
        · have hit := (pointX_desSite input d xe ⟨c, j⟩).mpr des
          rw [if_pos hit, dif_neg (fun visible => visible.2 des)]
        · have miss : ¬ ∃ d' c', (⟨.pointX, c, j, xElementIndex d xe⟩ : MaskSite) =
              desSite (BitInput.ofAffine input) d' c' := fun hit =>
            des ((pointX_desSite input d xe ⟨c, j⟩).mp hit)
          rw [if_neg miss, dif_pos ⟨inactive, des⟩]
          exact (maskSiteEquiv_pointX (masksOf T) d xe ⟨c, j⟩).symm
  · rw [digitValues_inr, pointValues_snd]
    refine (laneValue_eq .pointY _ _ _ (yElementIndex d ye)).trans ?_
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_)
      (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_)
    · rw [readPointY_cells, alphaY_eq]
      rfl
    · rw [alphaY_eq]
      unfold chunkMasks
      show _ * (if j = (offShape input).alphaY c then 0 else _) =
        _ * (if j = (offShape input).alphaY c then 0 else _)
      by_cases active : j = (offShape input).alphaY c
      · rw [if_pos active, if_pos active, mul_zero, mul_zero]
      · rw [if_neg active, if_neg active, masksOf_zeroDesig,
          if_neg (pointY_not_desSite input d ye ⟨c, j⟩)]
        congr 1
        unfold extendVisible
        have visible : (offShape input).DigitVisibleAt (.inr ye) ⟨c, j⟩ :=
          ⟨active, fun collector => by rcases collector.1 with h | h | h <;> cases h⟩
        rw [dif_pos visible]
        exact (maskSiteEquiv_pointY (masksOf T) d ye ⟨c, j⟩).symm

/-! ### 4. The collector targets are F4's designated solve -/

/-- **The row gap of a collector is its solve gap**: the collector has coefficient one in its own
row and appears in no other. -/
theorem collector_gap (gamma : RowGamma) (u : AffineInput) (values : Biquadratic.Values)
    (target : HomogeneousValue) (c : Fin 3) :
    Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c target -
        Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c (evaluateGamma gamma u values) =
      collectorComponent (.inl (collectorElement c)) (collectorSolve gamma u values target) -
        values (.inl (collectorElement c)) := by
  rw [evaluateGamma_eq_affine]
  fin_cases c <;>
    simp [Kriterion.ArgoMAC.Phase3.Glue.collectorComponent, collectorComponent, collectorElement,
      collectorSolve, rowConstant, rowLinear] <;> ring

theorem evaluateHomogeneous_get (table : FieldMacToECMac.Table) (values : FieldMacToECMac.DigitValues)
    (u : AffineInput) (d : Fin digitCount) :
    (FieldMacToECMac.evaluateHomogeneous table values u).get d = evaluateGamma (table.1.get d) u (values d) :=
  Vector.get_ofFn _ d

theorem rows_cellsSource (cells : PublicCells) (key : InputMacKey) (d : Fin digitCount) :
    (Pipeline.pointTable (cellsSource cells key).publicValue).1.get d = (cells.1 d).2 :=
  get_ofFn_digit (fun d => (cells.1 d).2) d

/-- The true rows of a coin at a digit. -/
def rowsAt (scalar : NonZeroScalar) (coins : Coins) (d : Fin digitCount) : Coordinates.Rows :=
  (FieldMacToECMac.rowsForOutputKeys (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
    coins.pointRandomness).get d

theorem trueRows_eq (scalar : NonZeroScalar) (coins : Coins) (d : Fin digitCount) :
    trueRows scalar coins input d = rowTarget (rowsAt scalar coins d) input :=
  (rowTarget_eq_evaluateRow _ _ (rowsForOutputKeysSparse _ _ d)).symm

/-- **The private side's collector targets**: `κ · (W − R)`, `R` the evaluator's rows at
its opening's values on the overlaid oracle with the designated limbs zeroed. -/
def targetsOf (scalar : NonZeroScalar) (P : Public) (mac : InputMac) (T : Tape) (O : Oracle)
    (coins : Coins) : Fin digitCount × Fin 3 → BaseField :=
  collectorTargets (BitInput.ofAffine input)
    (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable P)
      (Pipeline.digitValues
        ((openingQueriesM P (BitInput.ofAffine input) mac).eval
          (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).1
        ((openingQueriesM P (BitInput.ofAffine input) mac).eval
          (publicAnswer (OnLaw.overlay (OnLaw.zeroDesig (BitInput.ofAffine input) T) O))).2)
      (BitInput.ofAffine input).toAffine)
    (fun digit => trueRows scalar coins input digit)

/-- **The collector target of `(d, c)` is F4's designated solve** at the true rows, from the cells
and the tape's visible masks. -/
theorem targets_eq (scalar : NonZeroScalar) (cells : PublicCells) (key : InputMacKey) (mac : InputMac)
    (T : Tape) (O : Oracle) (coins : Coins) (d : Fin digitCount) (c : Fin 3) :
    targetsOf input scalar (cellsSource cells key).publicValue mac T O coins (d, c) =
      simDesignated (offShape input) (rowTarget (rowsAt scalar coins d) input) (cells.1 d).1 (cells.1 d).2
        (digitVisible (offShape input) ((maskSiteEquiv (masksOf T)).1 d)) (.inl (collectorElement c)) := by
  unfold targetsOf
  rw [openingQueriesM_dm (dmOn_overlay _ O)]
  unfold collectorTargets simDesignated
  rw [kappa_inv_ofInput]
  congr 1
  have evalRow : (FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable (cellsSource cells key).publicValue)
      (Pipeline.digitValues
        (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (OnLaw.zeroDesig (BitInput.ofAffine input) T)).1
        (pointValues (cellsSource cells key).publicValue (BitInput.ofAffine input)
          (OnLaw.zeroDesig (BitInput.ofAffine input) T)).2)
      (BitInput.ofAffine input).toAffine).get d =
      evaluateGamma (cells.1 d).2 input
        (digitPartial (offShape input) (cells.1 d).1
          (digitVisible (offShape input) ((maskSiteEquiv (masksOf T)).1 d))) := by
    refine (evaluateHomogeneous_get _ _ _ d).trans ?_
    rw [rows_cellsSource cells key d, BitInput.toAffineOfAffine, digitValues_zeroDesig input cells key T d]
  show Kriterion.ArgoMAC.Phase3.Glue.collectorComponent c (trueRows scalar coins input d) - _ = _
  rw [evalRow, trueRows_eq, collector_gap]
  rfl

end

end Kriterion.ArgoMAC.Security.Phase3.PublicFirst.OnE
