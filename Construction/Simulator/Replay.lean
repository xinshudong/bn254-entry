/-
Stage 2, part 1: the replay of the honest evaluator's queries.

For every lane the machine rebuilds each chunk's one-hot labels exactly as `evalFoldM` does
(two fold queries at the inactive level-1 entry), then asks every inactive switch's
`3 · count` scale blocks in `evalMasksM` order and accumulates the delivered value
`Σ_c [ι(α_c) · J_c[e] + Σ_{j ≠ α_c} (ι(j) − ι(α_c)) · Y_{c,j}[e]]` (the algebraic form of
`evalScaleOf`) in the `acc` region. System A (the curve lanes) runs on the raw labels, then the
bridge value `t = CurveMembership.evaluate`, one hash query, and the `508` whitening pads
(`encForward` at `k1`); system B (the point lanes) runs on the whitened labels.

**The designated switch.** In lane `pointX`, chunk `0`, the switch `j* = α₀ ⊕ 1` is skipped for
the three collectors of every digit (x-slots `5d + 1`, `5d + 3`, `5d + 4`): those `819` blocks
are the ones stage 2 programs. The accumulators of the collectors therefore hold the
*running* sums. The label `E* = E_{0, j*}`, `j*` and `κ = ι(j*) − ι(α₀) = 1 − 2 · (α₀ mod 2)`
are recorded for the opening.

Every index constant is `ord index`, where `ord` is the caller's ordinal function
(instantiated with `Fintype.equivFin`, which `queryFromRegisters` inverts).
-/

import Construction.Simulator.Blocks
import Construction.PGS.Index

namespace Kriterion.ArgoMAC.PlanB.SimMachine

open Cryptography.BoundedMachine Blocks

namespace Replay

/-- A chunk number as a `Fin chunkCount` (the identity below `127`). -/
def chunkFin (chunk : Nat) : Fin chunkCount := ⟨chunk % chunkCount, Nat.mod_lt _ chunkCount_pos⟩

/-- The fold index of step `1`, entry `entry`, half `half`. -/
def hotIdx (lane : Lane) (chunk entry : Nat) (half : Bool) : FixedIndex :=
  hotIndexNat lane (chunkFin chunk) 1 entry half

/-- The scale index of switch `switch`, element `element`, block `block`. -/
def scaleIdx (lane : Lane) (chunk switch element block : Nat) : FixedIndex :=
  .scale lane (chunkFin chunk) ⟨switch % 2 ^ chunkBits, Nat.mod_lt _ twoPowChunkBits_pos⟩
    ⟨element % elementCountX, Nat.mod_lt _ (by unfold elementCountX; omega)⟩
    ⟨block % 3, Nat.mod_lt _ (by omega)⟩

/-- The EncPRF index of label position `position < 508`. -/
def encIdx (position : Nat) : EncPRF.PermutationIndex :=
  (if position < 254 then .x else .y, ⟨position % 254, Nat.mod_lt _ (by omega)⟩)

/-- The static description of one lane. -/
structure LaneSpec where
  lane : Lane
  /-- The coordinate's request cell. -/
  coordinate : Nat
  /-- The first label of the coordinate (raw or whitened region). -/
  labels : Nat
  /-- The number of elements. -/
  count : Nat
  /-- The slot of element `0` in the chunk word and in `acc`. -/
  slot : Nat
  /-- The lane's position among the four fold-join vectors. -/
  hotRow : Nat

def curveXSpec : LaneSpec := ⟨.curveX, reqX, labelBase, 3, 455, 0⟩
def curveYSpec : LaneSpec := ⟨.curveY, reqY, labelBase + 254, 2, 822, 1⟩
def pointXSpec : LaneSpec := ⟨.pointX, reqX, whiteBase, 455, 0, 2⟩
def pointYSpec : LaneSpec := ⟨.pointY, reqY, whiteBase + 254, 364, 458, 3⟩

/-- Is x-slot `element` of lane `pointX` a collector (`x9` of rows X, Y, Z)? -/
def isCollector (element : Nat) : Bool :=
  element % 5 == 1 || element % 5 == 3 || element % 5 == 4

variable (ordF : FixedIndex → Nat) (ordE : EncPRF.PermutationIndex → Nat)

/-- One fold query pair at entry `entry`, leaving `M_entry` in `rC`; `rInput` holds `L0`. -/
def foldPair (spec : LaneSpec) (chunk entry : Nat) : Prog :=
  .seq (cst rIndex (ordF (hotIdx spec.lane chunk entry false)))
    (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rC rFirst rInput)
    (.seq (cst rIndex (ordF (hotIdx spec.lane chunk entry true)))
    (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rFirst rFirst rInput) (ar .xor rC rC rFirst))))))

/-- The fold arm for bit `0` of the chunk equal to `1 - entry`: query entry `entry`, recover the
other one from the join, and store `E_0 .. E_3`. -/
def foldArm (spec : LaneSpec) (chunk entry : Nat) : Prog :=
  let m0 : Register := if entry = 0 then rC else rD
  let m1 : Register := if entry = 0 then rD else rC
  .seq (foldPair ordF spec chunk entry)
    (.seq (loadAt rD (hotBase + 127 * spec.hotRow + chunk))
    (.seq (loadAt rE (spec.labels + 2 * chunk + 1))
    (.seq (ar .xor rD rD rE)
    (.seq (ar .xor rD rD rC)
    (.seq (storeAt (hotLabelBase + 2) m0)
    (.seq (storeAt (hotLabelBase + 3) m1)
    (.seq (ar .xor rE rInput m0)
    (.seq (storeAt hotLabelBase rE)
    (.seq (ar .xor rE rInput m1) (storeAt (hotLabelBase + 1) rE))))))))))

/-- The chunk prefix: `α`, bit `0`, `L0`, then the fold (arm selected by bit `0`). -/
def chunkPrefix (spec : LaneSpec) (chunk : Nat) : Prog :=
  .seq (loadAt rA spec.coordinate)
    (.seq (cst rB (2 * chunk))
    (.seq (ar .shiftRight rA rA rB)
    (.seq (cst rB 3)
    (.seq (ar .and rA rA rB)
    (.seq (storeAt tmpAlpha rA)
    (.seq (cst rB 1)
    (.seq (ar .and rA rA rB)
    (.seq (storeAt tmpBit0 rA)
    (.seq (loadAt rInput (spec.labels + 2 * chunk))
      (.ite rA (foldArm ordF spec chunk 0) (foldArm ordF spec chunk 1)))))))))))

/-- The designated extras of `pointX` chunk `0`: `j* = α ⊕ 1`, `κ = 1 − 2 · bit₀`, and
`E* = E_{j*}`. -/
def designatedPrefix : Prog :=
  .seq (loadAt rA tmpAlpha)
    (.seq (cst rB 1)
    (.seq (ar .xor rA rA rB)
    (.seq (storeAt tmpJStar rA)
    (.seq (cst rB hotLabelBase)
    (.seq (ar .add rA rA rB)
    (.seq (.op (.load rC rA))
    (.seq (storeAt (hotLabelBase + 4) rC)
    (.seq (cst rA 1)
    (.seq (loadAt rB tmpBit0)
    (.seq (ar .fieldAdd rB rB rB)
    (.seq (ar .fieldSub rA rA rB) (storeAt tmpKappa rA))))))))))))

/-- One element of one switch: three blocks, `sampleFp`, and `acc += coef · Y`. `rInput` holds
the switch's one-hot label and `rF` the coefficient `ι(j) − ι(α)`. -/
def element (spec : LaneSpec) (chunk switch index : Nat) : Prog :=
  .seq (cst rIndex (ordF (scaleIdx spec.lane chunk switch index 0)))
    (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rC rFirst rInput)
    (.seq (cst rIndex (ordF (scaleIdx spec.lane chunk switch index 1)))
    (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rD rFirst rInput)
    (.seq (cst rIndex (ordF (scaleIdx spec.lane chunk switch index 2)))
    (.seq (.op (.query 0 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rE rFirst rInput)
    (.seq (cst rAcc (2 ^ 128))
    (.seq (ar .fieldMul rD rD rAcc)
    (.seq (ar .fieldAdd rC rC rD)
    (.seq (cst rAcc c256)
    (.seq (ar .fieldMul rE rE rAcc)
    (.seq (ar .fieldAdd rC rC rE)
    (.seq (ar .fieldMul rC rC rF)
    (.seq (loadAt rD (accBase + spec.slot + index))
    (.seq (ar .fieldAdd rD rD rC) (storeAt (accBase + spec.slot + index) rD))))))))))))))))))

/-- An element of the designated chunk: a collector is skipped exactly at `j*`. -/
def guardedElement (spec : LaneSpec) (chunk switch index : Nat) : Prog :=
  if isCollector index then
    .seq (loadAt rA tmpJStar)
      (.seq (cst rB switch)
      (.seq (ar .xor rA rA rB)
        (.ite rA (element ordF spec chunk switch index) (.skip 0))))
  else element ordF spec chunk switch index

/-- The five x-slots of one digit in the designated chunk: slots `1`, `3`, `4` are collectors. -/
def designatedDigit (spec : LaneSpec) (chunk switch digit : Nat) : Prog :=
  .seq (element ordF spec chunk switch (5 * digit))
    (.seq (guardedElement ordF spec chunk switch (5 * digit + 1))
    (.seq (element ordF spec chunk switch (5 * digit + 2))
    (.seq (guardedElement ordF spec chunk switch (5 * digit + 3))
      (guardedElement ordF spec chunk switch (5 * digit + 4)))))

/-- The elements of one switch. -/
def switchElements (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) : Prog :=
  if designated then Prog.rep 91 fun digit => designatedDigit ordF spec chunk switch digit
  else Prog.rep spec.count fun index => element ordF spec chunk switch index

/-- One switch: skipped at `α`; otherwise load `E_j` and the coefficient, then every element. -/
def switchBody (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) : Prog :=
  .seq (loadAt rInput (hotLabelBase + switch))
    (.seq (loadAt rA tmpAlpha)
    (.seq (cst rF switch)
    (.seq (ar .fieldSub rF rF rA) (switchElements ordF spec designated chunk switch))))

def switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) : Prog :=
  .seq (loadAt rA tmpAlpha)
    (.seq (cst rB switch)
    (.seq (ar .xor rA rA rB)
      (.ite rA (switchBody ordF spec designated chunk switch) (.skip 0))))

/-- The published-join term `acc[e] += ι(α) · J_c[e]`. -/
def joinTerm (spec : LaneSpec) (chunk index : Nat) : Prog :=
  .seq (loadAt rC (scaleCellBase + 824 * chunk + spec.slot + index))
    (.seq (ar .fieldMul rC rC rF)
    (.seq (loadAt rD (accBase + spec.slot + index))
    (.seq (ar .fieldAdd rD rD rC) (storeAt (accBase + spec.slot + index) rD))))

/-- One chunk of one lane. -/
def chunkBody (spec : LaneSpec) (designated : Bool) (chunk : Nat) : Prog :=
  .seq (chunkPrefix ordF spec chunk)
    (.seq (if designated then designatedPrefix else .skip 0)
    (.seq (Prog.rep 4 fun switch => switchStep ordF spec designated chunk switch)
    (.seq (loadAt rF tmpAlpha) (Prog.rep spec.count fun index => joinTerm spec chunk index))))

/-- One lane: its `127` chunks. -/
def lane (spec : LaneSpec) : Prog := Prog.rep chunkCount fun chunk => chunkBody ordF spec false chunk

/-- Lane `pointX`: chunk `0` is the designated one. -/
def designatedLane (spec : LaneSpec) : Prog :=
  .seq (chunkBody ordF spec true 0) (Prog.rep (chunkCount - 1) fun chunk =>
    chunkBody ordF spec false (chunk + 1))

/-- Zero the `824` accumulators. -/
def initAcc : Prog :=
  .seq (cst rA 0) (Prog.rep 824 fun index => storeAt (accBase + index) rA)

/-- The bridge value `t` of `CurveMembership.evaluate`, then the hash query; `k1`, `k2` are
stored. -/
def bridge : Prog :=
  .seq (loadAt rA reqX)
    (.seq (loadAt rB reqY)
    (.seq (ar .fieldMul rC rA rA)
    (.seq (ar .fieldMul rD rC rA)
    (.seq (ar .fieldMul rE rB rB)
    (.seq (loadAt rInput fieldBase)
    (.seq (loadAt rAcc (fieldBase + 1)) (.seq (ar .fieldMul rAcc rAcc rD)
      (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (fieldBase + 2)) (.seq (ar .fieldMul rAcc rAcc rE)
      (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (accBase + 455)) (.seq (ar .fieldMul rAcc rAcc rC)
      (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (accBase + 822)) (.seq (ar .fieldMul rAcc rAcc rB)
      (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (accBase + 456)) (.seq (ar .fieldMul rAcc rAcc rA)
      (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (accBase + 823)) (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (loadAt rAcc (accBase + 457)) (.seq (ar .fieldAdd rInput rInput rAcc)
    (.seq (.op (.query 4 rIndex rInput rFirst rSecond))
    (.seq (storeAt tmpK1 rFirst) (storeAt tmpK2 rSecond)))))))))))))))))))))))))))

/-- One whitened label: `W_i = (π_{enc i}(k1) ⊕ k2) ⊕ L_i`; `rInput = k1`, `rF = k2`. -/
def whitenOne (position : Nat) : Prog :=
  .seq (cst rIndex (ordE (encIdx position)))
    (.seq (.op (.query 2 rIndex rInput rFirst rSecond))
    (.seq (ar .xor rFirst rFirst rF)
    (.seq (loadAt rA (labelBase + position))
    (.seq (ar .xor rFirst rFirst rA) (storeAt (whiteBase + position) rFirst)))))

/-- The `508` whitened labels. -/
def whiten : Prog :=
  .seq (loadAt rInput tmpK1) (.seq (loadAt rF tmpK2) (Prog.rep labelCount fun position =>
    whitenOne ordE position))

/-- **The replay.** -/
def program : Prog :=
  .seq initAcc
    (.seq (lane ordF curveXSpec)
    (.seq (lane ordF curveYSpec)
    (.seq bridge
    (.seq (whiten ordE)
    (.seq (designatedLane ordF pointXSpec) (lane ordF pointYSpec))))))

/-! ### Sizes and costs -/

section Sizes

theorem size_foldArm (spec : LaneSpec) (chunk entry : Nat) : (foldArm ordF spec chunk entry).size = 23 := by
  simp only [foldArm, foldPair, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]
theorem cost_foldArm (spec : LaneSpec) (chunk entry : Nat) : (foldArm ordF spec chunk entry).cost = 23 := by
  simp only [foldArm, foldPair, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]
theorem size_chunkPrefix (spec : LaneSpec) (chunk : Nat) : (chunkPrefix ordF spec chunk).size = 63 := by
  simp only [chunkPrefix, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size,
    Prog.padSet, Prog.padClear, cost_foldArm, size_foldArm]
  norm_num
theorem cost_chunkPrefix (spec : LaneSpec) (chunk : Nat) : (chunkPrefix ordF spec chunk).cost = 39 := by
  simp only [chunkPrefix, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost,
    cost_foldArm]
  norm_num
theorem size_designatedPrefix : designatedPrefix.size = 18 := by
  simp only [designatedPrefix, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]
theorem cost_designatedPrefix : designatedPrefix.cost = 18 := by
  simp only [designatedPrefix, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]
theorem size_element (spec : LaneSpec) (chunk switch index : Nat) :
    (element ordF spec chunk switch index).size = 21 := by
  simp only [element, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]
theorem cost_element (spec : LaneSpec) (chunk switch index : Nat) :
    (element ordF spec chunk switch index).cost = 21 := by
  simp only [element, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]

theorem size_guarded_collector (spec : LaneSpec) (chunk switch index : Nat)
    (collector : isCollector index = true) :
    (guardedElement ordF spec chunk switch index).size = 49 := by
  simp only [guardedElement, collector, if_true, Prog.size_seq, size_cst, size_loadAt, ar,
    Prog.size, Prog.padSet, Prog.padClear, size_element, cost_element, Prog.cost]
  norm_num

theorem cost_guarded_collector (spec : LaneSpec) (chunk switch index : Nat)
    (collector : isCollector index = true) :
    (guardedElement ordF spec chunk switch index).cost = 27 := by
  simp only [guardedElement, collector, if_true, Prog.cost_seq, cost_cst, cost_loadAt, ar,
    Prog.cost, cost_element]
  norm_num

theorem isCollector_digit (digit : Nat) :
    isCollector (5 * digit + 1) = true ∧ isCollector (5 * digit + 3) = true ∧
      isCollector (5 * digit + 4) = true := by
  simp only [isCollector]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.add_mod] <;> omega

theorem size_designatedDigit (spec : LaneSpec) (chunk switch digit : Nat) :
    (designatedDigit ordF spec chunk switch digit).size = 189 := by
  obtain ⟨one, three, four⟩ := isCollector_digit digit
  simp only [designatedDigit, Prog.size_seq, size_element,
    size_guarded_collector ordF spec chunk switch _ one,
    size_guarded_collector ordF spec chunk switch _ three,
    size_guarded_collector ordF spec chunk switch _ four]

theorem cost_designatedDigit (spec : LaneSpec) (chunk switch digit : Nat) :
    (designatedDigit ordF spec chunk switch digit).cost = 123 := by
  obtain ⟨one, three, four⟩ := isCollector_digit digit
  simp only [designatedDigit, Prog.cost_seq, cost_element,
    cost_guarded_collector ordF spec chunk switch _ one,
    cost_guarded_collector ordF spec chunk switch _ three,
    cost_guarded_collector ordF spec chunk switch _ four]

theorem size_switchElements_plain (spec : LaneSpec) (chunk switch : Nat) :
    (switchElements ordF spec false chunk switch).size = spec.count * 21 := by
  simp only [switchElements, Bool.false_eq_true, if_false]
  exact Prog.size_rep _ _ _ fun _ _ => size_element ordF spec chunk switch _

theorem cost_switchElements_plain (spec : LaneSpec) (chunk switch : Nat) :
    (switchElements ordF spec false chunk switch).cost = spec.count * 21 := by
  simp only [switchElements, Bool.false_eq_true, if_false]
  exact Prog.cost_rep _ _ _ fun _ _ => cost_element ordF spec chunk switch _

theorem size_switchElements_designated (spec : LaneSpec) (chunk switch : Nat) :
    (switchElements ordF spec true chunk switch).size = 91 * 189 := by
  simp only [switchElements, if_true]
  exact Prog.size_rep _ _ _ fun _ _ => size_designatedDigit ordF spec chunk switch _

theorem cost_switchElements_designated (spec : LaneSpec) (chunk switch : Nat) :
    (switchElements ordF spec true chunk switch).cost = 91 * 123 := by
  simp only [switchElements, if_true]
  exact Prog.cost_rep _ _ _ fun _ _ => cost_designatedDigit ordF spec chunk switch _

theorem size_switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (switchStep ordF spec designated chunk switch).size =
      7 + 2 * 6 + (switchElements ordF spec designated chunk switch).size +
        (switchElements ordF spec designated chunk switch).cost := by
  simp only [switchStep, switchBody, Prog.size_seq, Prog.size, Prog.cost_seq, Prog.cost,
    Prog.padSet, Prog.padClear]
  simp only [loadAt, cst, ar, Prog.size_seq, Prog.cost_seq, Prog.size, Prog.cost]
  omega

theorem cost_switchStep (spec : LaneSpec) (designated : Bool) (chunk switch : Nat) :
    (switchStep ordF spec designated chunk switch).cost =
      12 + (switchElements ordF spec designated chunk switch).cost := by
  simp only [switchStep, switchBody, Prog.cost_seq, Prog.cost]
  simp only [loadAt, cst, ar, Prog.cost_seq, Prog.cost]
  omega

theorem size_joinTerm (spec : LaneSpec) (chunk index : Nat) :
    (joinTerm spec chunk index).size = 8 := by
  simp only [joinTerm, Prog.size_seq, size_loadAt, size_storeAt, ar, Prog.size]
theorem cost_joinTerm (spec : LaneSpec) (chunk index : Nat) :
    (joinTerm spec chunk index).cost = 8 := by
  simp only [joinTerm, Prog.cost_seq, cost_loadAt, cost_storeAt, ar, Prog.cost]

theorem size_chunkBody_plain (spec : LaneSpec) (chunk : Nat) :
    (chunkBody ordF spec false chunk).size = 141 + 176 * spec.count := by
  simp only [chunkBody, Bool.false_eq_true, if_false, Prog.size_seq, size_chunkPrefix,
    size_loadAt]
  rw [Prog.size_rep 4 _ (19 + 42 * spec.count) fun _ _ => by
      rw [size_switchStep, size_switchElements_plain, cost_switchElements_plain]; omega,
    Prog.size_rep _ _ _ fun _ _ => size_joinTerm spec chunk _]
  simp only [Prog.size]
  omega

theorem cost_chunkBody_plain (spec : LaneSpec) (chunk : Nat) :
    (chunkBody ordF spec false chunk).cost = 89 + 92 * spec.count := by
  simp only [chunkBody, Bool.false_eq_true, if_false, Prog.cost_seq, cost_chunkPrefix,
    cost_loadAt]
  rw [Prog.cost_rep 4 _ (12 + 21 * spec.count) fun _ _ => by
      rw [cost_switchStep, cost_switchElements_plain]; omega,
    Prog.cost_rep _ _ _ fun _ _ => cost_joinTerm spec chunk _]
  simp only [Prog.cost]
  omega

theorem size_chunkBody_designated (spec : LaneSpec) (chunk : Nat) :
    (chunkBody ordF spec true chunk).size = 83 + 4 * 28411 + 8 * spec.count := by
  simp only [chunkBody, if_true, Prog.size_seq, size_chunkPrefix, size_loadAt,
    size_designatedPrefix]
  rw [Prog.size_rep 4 _ 28411 fun _ _ => by
      rw [size_switchStep, size_switchElements_designated, cost_switchElements_designated],
    Prog.size_rep _ _ _ fun _ _ => size_joinTerm spec chunk _]
  omega

theorem cost_chunkBody_designated (spec : LaneSpec) (chunk : Nat) :
    (chunkBody ordF spec true chunk).cost = 59 + 4 * 11205 + 8 * spec.count := by
  simp only [chunkBody, if_true, Prog.cost_seq, cost_chunkPrefix, cost_loadAt,
    cost_designatedPrefix]
  rw [Prog.cost_rep 4 _ 11205 fun _ _ => by
      rw [cost_switchStep, cost_switchElements_designated],
    Prog.cost_rep _ _ _ fun _ _ => cost_joinTerm spec chunk _]
  omega

theorem size_lane (spec : LaneSpec) : (lane ordF spec).size = 127 * (141 + 176 * spec.count) :=
  Prog.size_rep _ _ _ fun _ _ => size_chunkBody_plain ordF spec _

theorem cost_lane (spec : LaneSpec) : (lane ordF spec).cost = 127 * (89 + 92 * spec.count) :=
  Prog.cost_rep _ _ _ fun _ _ => cost_chunkBody_plain ordF spec _

theorem size_designatedLane (spec : LaneSpec) : (designatedLane ordF spec).size =
    83 + 4 * 28411 + 8 * spec.count + 126 * (141 + 176 * spec.count) := by
  simp only [designatedLane, Prog.size_seq, size_chunkBody_designated]
  rw [Prog.size_rep _ _ _ fun _ _ => size_chunkBody_plain ordF spec _]
  rfl

theorem cost_designatedLane (spec : LaneSpec) : (designatedLane ordF spec).cost =
    59 + 4 * 11205 + 8 * spec.count + 126 * (89 + 92 * spec.count) := by
  simp only [designatedLane, Prog.cost_seq, cost_chunkBody_designated]
  rw [Prog.cost_rep _ _ _ fun _ _ => cost_chunkBody_plain ordF spec _]
  rfl

theorem size_initAcc : initAcc.size = 1 + 824 * 2 := by
  simp only [initAcc, Prog.size_seq, size_cst]
  rw [Prog.size_rep _ _ _ fun _ _ => size_storeAt _ _]

theorem cost_initAcc : initAcc.cost = 1 + 824 * 2 := by
  simp only [initAcc, Prog.cost_seq, cost_cst]
  rw [Prog.cost_rep _ _ _ fun _ _ => cost_storeAt _ _]

theorem size_bridge : bridge.size = 40 := by
  simp only [bridge, Prog.size_seq, size_loadAt, size_storeAt, ar, Prog.size]
theorem cost_bridge : bridge.cost = 40 := by
  simp only [bridge, Prog.cost_seq, cost_loadAt, cost_storeAt, ar, Prog.cost]

theorem size_whiten : (whiten ordE).size = 4 + labelCount * 8 := by
  simp only [whiten, Prog.size_seq, size_loadAt]
  rw [Prog.size_rep _ _ 8 fun _ _ => by
    simp only [whitenOne, Prog.size_seq, size_cst, size_loadAt, size_storeAt, ar, Prog.size]]
  omega

theorem cost_whiten : (whiten ordE).cost = 4 + labelCount * 8 := by
  simp only [whiten, Prog.cost_seq, cost_loadAt]
  rw [Prog.cost_rep _ _ 8 fun _ _ => by
    simp only [whitenOne, Prog.cost_seq, cost_cst, cost_loadAt, cost_storeAt, ar, Prog.cost]]
  omega

/-- The replay's code size. -/
def programSize : Nat :=
  (1 + 824 * 2) + 127 * (141 + 176 * 3) + 127 * (141 + 176 * 2) + 40 + (4 + 508 * 8) +
    (83 + 4 * 28411 + 8 * 455 + 126 * (141 + 176 * 455)) + 127 * (141 + 176 * 364)

/-- The replay's cost. -/
def programCost : Nat :=
  (1 + 824 * 2) + 127 * (89 + 92 * 3) + 127 * (89 + 92 * 2) + 40 + (4 + 508 * 8) +
    (59 + 4 * 11205 + 8 * 455 + 126 * (89 + 92 * 455)) + 127 * (89 + 92 * 364)

theorem size_program : (program ordF ordE).size = programSize := by
  simp only [program, Prog.size_seq, size_initAcc, size_lane, size_bridge, size_whiten,
    size_designatedLane]
  rfl

theorem cost_program : (program ordF ordE).cost = programCost := by
  simp only [program, Prog.cost_seq, cost_initAcc, cost_lane, cost_bridge, cost_whiten,
    cost_designatedLane]
  rfl

theorem programSize_eq : programSize = 18532579 := by norm_num [programSize]
theorem programCost_eq : programCost = 9685155 := by norm_num [programCost]

end Sizes

end Replay

end Kriterion.ArgoMAC.PlanB.SimMachine
