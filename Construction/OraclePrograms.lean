/-
This file writes the Plan B garbler and evaluator as query programs.

The pinned library (`aaf2789`) requires `garbleProgram`/`evaluateProgram`: programs that read the
public oracle only through query instructions, whose type index bounds the number of queries on
every path, and which equal `Scheme.scheme` for every complete oracle.

The pure Plan B definitions recompute oracle values freely -- `offsets`, `scaleJoins` and
`evalCoord` rerun the whole `bin-to-hot` fold for every element -- so they are not programs. The
programs below ask every *distinct* question once and keep the answer in a table:

* the fold of one (lane, chunk) is run level by level; level `j ≥ 1` asks both halves of each of
  its `2 ^ j` gates (the evaluator skips its active entry, whose value it recovers from the join);
* one switch's mask vector is asked once -- `3` blocks per element -- and read by the offsets, the
  aggregate and (on the evaluator side) the recovery of the active switch;
* the whitening pad of a position is the bit-`false` EncPRF pad, asked once;
* the gadget asks its `508` labels per nonzero digit.

Each table has a *real* counterpart built from the oracle (`laneTables`, `realPads`, ...), the
table-driven assembly on the real tables is the pure definition by `rfl`, and each program's
`eval` is its real table. The query bounds are exact: garbling `1,305,053`, evaluation
`990,093` (`garbleBudget_eq`, `evaluateBudget_eq`).
-/

import Construction.QueryMonad
import Construction.Scheme

namespace Kriterion.ArgoMAC.Programs

open BN254 Cryptography
open Kriterion.ArgoMAC.PlanB hiding coordinateBits
open Kriterion.ArgoMAC.Scheme (Oracle Coins)
open FreeQuery (Bounded)

/-- The public query interface. -/
abbrev Spec := publicOracleSpec FixedIndex EncPRF.PermutationIndex

/-- A Plan B query computation. -/
abbrev M := FreeQuery Spec

/-! ## Questions

The three kinds of question the programs ask, each at its answer's plain type. -/

/-- Ask a fixed-key permutation in the forward direction. -/
def askFixed (index : FixedIndex) (input : Block) : M Block :=
  FreeQuery.ask (spec := Spec) (.fixedForward index input)

/-- Ask an EncPRF permutation in the forward direction. -/
def askEnc (index : EncPRF.PermutationIndex) (input : Block) : M Block :=
  FreeQuery.ask (spec := Spec) (.encForward index input)

/-- Ask the field hash. -/
def askHash (input : BaseField) : M (Block × Block) :=
  FreeQuery.ask (spec := Spec) (.hash input)

@[simp] theorem eval_askFixed (oracle : Oracle) (index : FixedIndex) (input : Block) :
    (askFixed index input).eval (publicAnswer oracle) = oracle.1.permutation index input := rfl

@[simp] theorem eval_askEnc (oracle : Oracle) (index : EncPRF.PermutationIndex) (input : Block) :
    (askEnc index input).eval (publicAnswer oracle) = oracle.2.1.permutation index input := rfl

@[simp] theorem eval_askHash (oracle : Oracle) (input : BaseField) :
    (askHash input).eval (publicAnswer oracle) = oracle.2.2 input := rfl

theorem bounded_askFixed (index : FixedIndex) (input : Block) : (askFixed index input).Bounded 1 :=
  Bounded.ask _

theorem bounded_askEnc (index : EncPRF.PermutationIndex) (input : Block) :
    (askEnc index input).Bounded 1 :=
  Bounded.ask _

theorem bounded_askHash (input : BaseField) : (askHash input).Bounded 1 :=
  Bounded.ask _

/-! ## Gates -/

/-- One Davies--Meyer fixed-key hash `pi_index(label) xor label`, asked once. -/
def hashM (index : FixedIndex) (label : Block) : M Block :=
  askFixed index label >>= fun image => pure (image ^^^ label)

theorem eval_hashM (oracle : Oracle) (index : FixedIndex) (label : Block) :
    (hashM index label).eval (publicAnswer oracle) = hash oracle.1 index label := rfl

theorem bounded_hashM (index : FixedIndex) (label : Block) : (hashM index label).Bounded 1 :=
  Bounded.bind (bounded_askFixed _ _) fun _ => Bounded.pure' _ 0

/-- The two-image fold-step material of one `bin-to-hot` gate. -/
def foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat) (label : Block) :
    M Block :=
  hashM (hotIndexNat lane chunk step entry false) label >>= fun first =>
    hashM (hotIndexNat lane chunk step entry true) label >>= fun second =>
      pure (first ^^^ second)

theorem eval_foldMaskM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (step entry : Nat) (label : Block) :
    (foldMaskM lane chunk step entry label).eval (publicAnswer oracle) =
      foldMask oracle.1 lane chunk step entry label := rfl

theorem bounded_foldMaskM (lane : Lane) (chunk : Fin chunkCount) (step entry : Nat)
    (label : Block) : (foldMaskM lane chunk step entry label).Bounded 2 :=
  Bounded.bind (bounded_hashM _ _) fun _ =>
    Bounded.bind (bounded_hashM _ _) fun _ => Bounded.pure' _ 0

/-! ## Garbling: the `bin-to-hot` fold -/

/-- The garbler's step material at one level. -/
def garbleStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (zeroLabel : Block)
    (parent : Fin (2 ^ step) → Block) : M (Fin (2 ^ step) → Block) :=
  if step = 0 then pure fun _ => zeroLabel
  else
    FreeQuery.vector (2 ^ step) (fun entry => foldMaskM lane chunk step entry.val (parent entry))
      >>= fun masks => pure masks.get

theorem eval_garbleStepM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (garbleStepM lane chunk step zeroLabel parent).eval (publicAnswer oracle) =
      garbleStep oracle.1 lane chunk step zeroLabel parent := by
  funext entry
  by_cases zero : step = 0
  · rw [garbleStepM, if_pos zero]
    simp only [garbleStep, if_pos zero, FreeQuery.eval_pure]
  · rw [garbleStepM, if_neg zero]
    simp only [garbleStep, if_neg zero, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn, eval_foldMaskM]

/-- The garbler's queries at level `step`: none at the free level `0`. -/
def stepGarbleBudget (step : Nat) : Nat := if step = 0 then 0 else 2 ^ step * 2

theorem bounded_garbleStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (zeroLabel : Block) (parent : Fin (2 ^ step) → Block) :
    (garbleStepM lane chunk step zeroLabel parent).Bounded (stepGarbleBudget step) := by
  unfold garbleStepM
  refine Bounded.ite (fun _ => Bounded.pure' _ _) fun zero => ?_
  refine (Bounded.bind (Bounded.vector_const fun entry =>
    bounded_foldMaskM lane chunk step entry.val (parent entry)) fun _ =>
      Bounded.pure' _ 0).of_eq ?_
  simp [stepGarbleBudget, zero]

/-- The garbler's fold, level by level. -/
def garbleFoldM (lane : Lane) (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    (steps : Nat) → M ((Fin (2 ^ steps) → Block) × (Nat → Block))
  | 0 => pure (fun _ => delta, fun _ => 0)
  | steps + 1 =>
      garbleFoldM lane chunk delta zeroLabel steps >>= fun previous =>
        garbleStepM lane chunk steps (zeroLabel steps) previous.1 >>= fun right =>
          pure (extendLevel steps previous.1 right,
            fun step => if step = steps then stepJoin steps (zeroLabel steps) right
              else previous.2 step)

theorem eval_garbleFoldM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount)
    (delta : Block) (zeroLabel : Nat → Block) (steps : Nat) :
    (garbleFoldM lane chunk delta zeroLabel steps).eval (publicAnswer oracle) =
      garbleFold oracle.1 lane chunk delta zeroLabel steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [garbleFoldM, garbleFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        eval_garbleStepM]

/-- The garbler's fold queries over `steps` levels. -/
def hotGarbleBudget : Nat → Nat
  | 0 => 0
  | steps + 1 => hotGarbleBudget steps + stepGarbleBudget steps

theorem bounded_garbleFoldM (lane : Lane) (chunk : Fin chunkCount) (delta : Block)
    (zeroLabel : Nat → Block) (steps : Nat) :
    (garbleFoldM lane chunk delta zeroLabel steps).Bounded (hotGarbleBudget steps) := by
  induction steps with
  | zero => exact Bounded.pure' _ _
  | succ steps ih =>
      exact (Bounded.bind ih fun previous =>
        Bounded.bind (bounded_garbleStepM lane chunk steps (zeroLabel steps) previous.1) fun _ =>
          Bounded.pure' _ 0).of_eq (by simp [hotGarbleBudget])

/-- **`bin-to-hot`, garbler side**, for chunk `c` of one lane. -/
def garbleChunkM (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block)
    (c : Fin chunkCount) : M (HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)) :=
  garbleFoldM lane c delta (labelAt fun position => (chunkKey bitKey c position).1) (chunkWidth c)
    >>= fun folded =>
      pure (folded.1, Vector.ofFn fun slot : Fin (chunkWidth c - 1) => folded.2 (slot.val + 1))

theorem eval_garbleChunkM (oracle : Oracle) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (garbleChunkM lane delta bitKey c).eval (publicAnswer oracle) =
      garbleChunk oracle.1 lane delta bitKey c := by
  simp only [garbleChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_garbleFoldM]
  rfl

theorem bounded_garbleChunkM (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (garbleChunkM lane delta bitKey c).Bounded (hotGarbleBudget (chunkWidth c)) :=
  (Bounded.bind (bounded_garbleFoldM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by simp)

/-! ## The `scale-hot` switch masks -/

/-- One switch's mask vector: three blocks per element, hashed at the switch's one-hot label. -/
def switchMaskM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) : M (Fin count → BaseField) :=
  FreeQuery.vector count (fun element =>
    hashM (scaleIndexOf lane chunk switch element 0) label >>= fun first =>
      hashM (scaleIndexOf lane chunk switch element 1) label >>= fun second =>
        hashM (scaleIndexOf lane chunk switch element 2) label >>= fun third =>
          pure (sampleFp first second third)) >>= fun values => pure values.get

theorem eval_switchMaskM (oracle : Oracle) (count : Nat) (lane : Lane) (chunk : Fin chunkCount)
    (switch : Nat) (label : Block) :
    (switchMaskM count lane chunk switch label).eval (publicAnswer oracle) =
      switchMask oracle.1 lane chunk switch label := by
  funext element
  simp only [switchMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, eval_hashM]
  rfl

theorem bounded_switchMaskM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (switch : Nat)
    (label : Block) : (switchMaskM count lane chunk switch label).Bounded (count * 3) :=
  (Bounded.bind (Bounded.vector_const fun _ =>
    Bounded.bind (bounded_hashM _ _) fun _ => Bounded.bind (bounded_hashM _ _) fun _ =>
      Bounded.bind (bounded_hashM _ _) fun _ => Bounded.pure' _ 0) fun _ =>
        Bounded.pure' _ 0).of_eq (by simp)

/-! ## One lane of the garbler -/

/-- Everything one lane's garbling reads from the oracle: each chunk's fold (one-hot labels and
published fold joins) and each chunk's switch-mask vectors. -/
structure LaneTables (count : Nat) where
  hot : (c : Fin chunkCount) → HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)
  masks : (c : Fin chunkCount) → Fin (2 ^ chunkWidth c) → Fin count → BaseField

/-- The lane tables of a real oracle. -/
def laneTables (fixed : PermutationOracle FixedIndex Block) (count : Nat) (lane : Lane)
    (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) : LaneTables count where
  hot c := garbleChunk fixed lane delta bitKey c
  masks c switch := switchMask fixed lane c switch.val ((garbleChunk fixed lane delta bitKey c).1 switch)

namespace LaneTables

variable {count : Nat}

/-- The lane's published fold joins, read from its tables. -/
def hotJoins (tables : LaneTables count) : Vector Block foldStepCount :=
  flattenHot fun c position =>
    if inRange : position < chunkWidth c - 1 then (tables.hot c).2.get ⟨position, inRange⟩ else 0

/-- The lane's element offsets `O[e]`, read from its tables. -/
def offsets (tables : LaneTables count) : Fin count → BaseField :=
  fun element => ∑ c : Fin chunkCount, ∑ switch : Fin (2 ^ chunkWidth c),
    iota _ switch * tables.masks c switch element

/-- The lane's published `scale-hot` joins, read from its tables. -/
def scaleJoins (tables : LaneTables count) (slopes : Fin count → BaseField) :
    Fin chunkCount → Fin count → BaseField :=
  fun c element => (∑ switch : Fin (2 ^ chunkWidth c), tables.masks c switch element)
    + chunkScalar slopes c element

end LaneTables

theorem laneTables_hotJoins (fixed : PermutationOracle FixedIndex Block) (count : Nat)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneTables fixed count lane delta bitKey).hotJoins = hotJoins fixed lane delta bitKey := rfl

theorem laneTables_offsets (fixed : PermutationOracle FixedIndex Block) (count : Nat)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneTables fixed count lane delta bitKey).offsets = offsets fixed lane delta bitKey := rfl

theorem laneTables_scaleJoins (fixed : PermutationOracle FixedIndex Block) (count : Nat)
    (lane : Lane) (delta : Block) (bitKey : Fin coordinateBitCount → Block × Block)
    (slopes : Fin count → BaseField) :
    (laneTables fixed count lane delta bitKey).scaleJoins slopes =
      scaleJoins fixed lane delta bitKey slopes := rfl

/-- One chunk's tables. -/
def chunkTablesM (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    M ((HotLabels (chunkWidth c) × Vector Block (chunkWidth c - 1)) ×
      (Fin (2 ^ chunkWidth c) → Fin count → BaseField)) :=
  garbleChunkM lane delta bitKey c >>= fun chunk =>
    FreeQuery.vector (2 ^ chunkWidth c)
        (fun switch => switchMaskM count lane c switch.val (chunk.1 switch)) >>= fun masks =>
      pure (chunk, masks.get)

/-- One lane's tables. -/
def laneM (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) : M (LaneTables count) :=
  FreeQuery.pi chunkCount (chunkTablesM count lane delta bitKey) >>= fun tables =>
    pure { hot := fun c => (tables c).1, masks := fun c => (tables c).2 }

theorem eval_laneM (oracle : Oracle) (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneM count lane delta bitKey).eval (publicAnswer oracle) =
      laneTables oracle.1 count lane delta bitKey := by
  simp only [laneM, chunkTablesM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_pi,
    FreeQuery.eval_vector, eval_garbleChunkM, eval_switchMaskM]
  unfold laneTables
  congr 1
  funext c switch
  rw [Vector.get_ofFn]

/-- One lane's garbling queries. -/
def laneGarbleBudget (count : Nat) : Nat :=
  ∑ c : Fin chunkCount, (hotGarbleBudget (chunkWidth c) + 2 ^ chunkWidth c * (count * 3))

theorem bounded_chunkTablesM (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) (c : Fin chunkCount) :
    (chunkTablesM count lane delta bitKey c).Bounded
      (hotGarbleBudget (chunkWidth c) + 2 ^ chunkWidth c * (count * 3)) := by
  unfold chunkTablesM
  exact (Bounded.bind (bounded_garbleChunkM lane delta bitKey c) fun chunk =>
    Bounded.bind (Bounded.vector_const fun switch =>
      bounded_switchMaskM count lane c switch.val (chunk.1 switch)) fun _ =>
        Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero])

theorem bounded_laneM (count : Nat) (lane : Lane) (delta : Block)
    (bitKey : Fin coordinateBitCount → Block × Block) :
    (laneM count lane delta bitKey).Bounded (laneGarbleBudget count) := by
  unfold laneM
  exact (Bounded.bind (Bounded.pi fun c => bounded_chunkTablesM count lane delta bitKey c)
    fun _ => Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero]; rfl)

/-! ## The EncPRF pads -/

/-- The Even--Mansour pad of one (coordinate, position, bit), asked once. -/
def padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) : M Block :=
  askEnc (coordinate, index) (encodeBit bit ^^^ keys.first) >>= fun image =>
    pure (image ^^^ keys.second)

theorem eval_padM (oracle : Oracle) (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) :
    (padM keys coordinate index bit).eval (publicAnswer oracle) =
      EncPRF.evenMansourPad oracle.2.1 keys { coordinate, index, bit } := rfl

theorem bounded_padM (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (index : Fin coordinateBitCount) (bit : Bool) : (padM keys coordinate index bit).Bounded 1 :=
  Bounded.bind (bounded_askEnc _ _) fun _ => Bounded.pure' _ 0

/-- A table of EncPRF pads, one per (coordinate, position, bit). -/
abbrev Pads := EncPRF.Coordinate → Fin coordinateBitCount → Bool → Block

/-- The pads of a real oracle. -/
def realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) : Pads :=
  fun coordinate index bit => EncPRF.evenMansourPad encOracle keys { coordinate, index, bit }

/-- The garbler asks both pads of every position. -/
def padsM (keys : WhiteningKeys) : M Pads :=
  let row (coordinate : EncPRF.Coordinate) :=
    FreeQuery.vector coordinateBitCount fun index =>
      padM keys coordinate index false >>= fun zero =>
        padM keys coordinate index true >>= fun one => pure (zero, one)
  row .x >>= fun xs => row .y >>= fun ys =>
    pure fun coordinate index bit =>
      let pair := match coordinate with
        | .x => xs.get index
        | .y => ys.get index
      if bit then pair.2 else pair.1

theorem eval_padsM (oracle : Oracle) (keys : WhiteningKeys) :
    (padsM keys).eval (publicAnswer oracle) = realPads oracle.2.1 keys := by
  funext coordinate index bit
  cases coordinate <;> cases bit <;>
    simp only [padsM, realPads, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
      Vector.get_ofFn, eval_padM, Bool.false_eq_true, if_false, if_true]

theorem bounded_padsM (keys : WhiteningKeys) : (padsM keys).Bounded 1016 :=
  (Bounded.bind (Bounded.vector_const fun _ =>
    Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ =>
      Bounded.pure' _ 0) fun _ =>
    Bounded.bind (Bounded.vector_const fun _ =>
      Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ =>
        Bounded.pure' _ 0) fun _ => Bounded.pure' _ 0).of_eq (by norm_num)

/-- The whitened label pairs, from a pad table. -/
def whitenKeyOf (pads : Pads) (key : InputMacKey) : InputMacKey :=
  let coordinate (which : EncPRF.Coordinate) (source : CoordinateMacKey) : CoordinateMacKey :=
    Vector.ofFn fun index =>
      let label := source[index.val]
      { falseLabel := encrypt (pads which index false) label.falseLabel
        trueLabel := encrypt (pads which index false) label.trueLabel }
  { x := coordinate .x key.x, y := coordinate .y key.y }

/-- The bit-dependent transformed label pairs, from a pad table. -/
def transformKeyOf (pads : Pads) (key : InputMacKey) : InputMacKey :=
  let coordinate (which : EncPRF.Coordinate) (source : CoordinateMacKey) : CoordinateMacKey :=
    Vector.ofFn fun index =>
      let label := source[index.val]
      { falseLabel := encrypt (pads which index false) label.falseLabel
        trueLabel := encrypt (pads which index true) label.trueLabel }
  { x := coordinate .x key.x, y := coordinate .y key.y }

theorem whitenKeyOf_realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) :
    whitenKeyOf (realPads encOracle keys) key = EncPRF.whitenKey encOracle keys key := rfl

theorem transformKeyOf_realPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (key : InputMacKey) :
    transformKeyOf (realPads encOracle keys) key = EncPRF.transformKey encOracle keys key := rfl

/-! ## The exception gadget -/

/-- The digest of one coordinate's labels: one fixed-key hash per label, XOR-folded. -/
def gadgetDigestM (output : Fin FieldMacToECMac.outputMacCount) (coordinate : EncPRF.Coordinate)
    (mac : CoordinateMac) : M Block :=
  FreeQuery.vector coordinateBitCount (fun index =>
    hashM (.gadget output (Pipeline.gadgetCoord coordinate) index) (mac.get index)) >>= fun values =>
      pure (Fin.foldl coordinateBitCount (fun acc index => acc ^^^ values.get index) 0)

theorem eval_gadgetDigestM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    (gadgetDigestM output coordinate mac).eval (publicAnswer oracle) =
      FieldMacToECMac.gadgetDigest (Pipeline.gadgetPermutations oracle.1 output coordinate) mac := by
  simp only [gadgetDigestM, FreeQuery.eval_bind, FreeQuery.eval_pure, FreeQuery.eval_vector,
    Vector.get_ofFn, eval_hashM]
  rfl

theorem bounded_gadgetDigestM (output : Fin FieldMacToECMac.outputMacCount)
    (coordinate : EncPRF.Coordinate) (mac : CoordinateMac) :
    (gadgetDigestM output coordinate mac).Bounded 254 :=
  (Bounded.bind (Bounded.vector_const fun _ => bounded_hashM _ _) fun _ =>
    Bounded.pure' _ 0).of_eq (by norm_num)

/-- The gadget mask byte of one digit, over the 508 selected labels. -/
def gadgetMaskM (output : Fin FieldMacToECMac.outputMacCount) (mac : InputMac) : M (BitVec 8) :=
  gadgetDigestM output .x mac.x >>= fun first =>
    gadgetDigestM output .y mac.y >>= fun second =>
      pure (Exception.lowByte (first ^^^ second))

theorem eval_gadgetMaskM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (mac : InputMac) :
    (gadgetMaskM output mac).eval (publicAnswer oracle) =
      FieldMacToECMac.gadgetMask (Pipeline.gadgetPermutations oracle.1) output mac := by
  simp only [gadgetMaskM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_gadgetDigestM]
  rfl

theorem bounded_gadgetMaskM (output : Fin FieldMacToECMac.outputMacCount) (mac : InputMac) :
    (gadgetMaskM output mac).Bounded 508 :=
  Bounded.bind (bounded_gadgetDigestM _ _ _) fun _ =>
    Bounded.bind (bounded_gadgetDigestM _ _ _) fun _ => Bounded.pure' _ 0

/-- The garbler's gadget entry of one digit: a zero digit publishes its pad and asks nothing. -/
def garbleEntryM (output : Fin FieldMacToECMac.outputMacCount) (key : FieldMacToECMac.OutputKey)
    (inputKey : InputMacKey) (pad : Exception.Entry) : M Exception.Entry :=
  match digitEndomorphismBase key.digit with
  | none => pure pad
  | some phi =>
      gadgetMaskM output
          (inputKey.encodeAffine (Exception.exceptionalInput phi key.offset.coordinates))
        >>= fun mask =>
          pure (Exception.writeEntry pad
            (Exception.exceptionIndex (Exception.exceptionalInput phi key.offset.coordinates))
            (mask ^^^ Exception.digitCode key.digit))

theorem eval_garbleEntryM (oracle : Oracle) (output : Fin FieldMacToECMac.outputMacCount)
    (key : FieldMacToECMac.OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (garbleEntryM output key inputKey pad).eval (publicAnswer oracle) =
      FieldMacToECMac.garbleEntry (Pipeline.gadgetPermutations oracle.1) output key inputKey pad := by
  unfold garbleEntryM FieldMacToECMac.garbleEntry
  cases digitEndomorphismBase key.digit with
  | none => rfl
  | some phi =>
      simp only [FreeQuery.eval_bind, FreeQuery.eval_pure, eval_gadgetMaskM]

theorem bounded_garbleEntryM (output : Fin FieldMacToECMac.outputMacCount)
    (key : FieldMacToECMac.OutputKey) (inputKey : InputMacKey) (pad : Exception.Entry) :
    (garbleEntryM output key inputKey pad).Bounded 508 := by
  unfold garbleEntryM
  cases digitEndomorphismBase key.digit with
  | none => exact Bounded.pure' _ _
  | some phi => exact Bounded.bind (bounded_gadgetMaskM _ _) fun _ => Bounded.pure' _ 0

/-- All 91 gadget entries. -/
def gadgetM (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) : M (Vector Exception.Entry FieldMacToECMac.outputMacCount) :=
  FreeQuery.vector FieldMacToECMac.outputMacCount fun output =>
    garbleEntryM output (keys.get output) inputKey (pads.get output)

theorem eval_gadgetM (oracle : Oracle) (keys : FieldMacToECMac.OutputKeys)
    (inputKey : InputMacKey) (pads : FieldMacToECMac.ExceptionPad) :
    (gadgetM keys inputKey pads).eval (publicAnswer oracle) =
      Vector.ofFn fun output => FieldMacToECMac.garbleEntry (Pipeline.gadgetPermutations oracle.1)
        output (keys.get output) inputKey (pads.get output) := by
  simp only [gadgetM, FreeQuery.eval_vector, eval_garbleEntryM]

theorem bounded_gadgetM (keys : FieldMacToECMac.OutputKeys) (inputKey : InputMacKey)
    (pads : FieldMacToECMac.ExceptionPad) :
    (gadgetM keys inputKey pads).Bounded (FieldMacToECMac.outputMacCount * 508) :=
  Bounded.vector_const fun _ => bounded_garbleEntryM _ _ _ _

/-! ## The garbler -/

/-- The published value, assembled from the four lanes' tables and the gadget entries. On the
real tables this is `Pipeline.garble` (`assemble_laneTables`). -/
def assemble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey : BaseField)
    (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (curveX : LaneTables curveElementCountX) (curveY : LaneTables curveElementCountY)
    (pointX : LaneTables pointElementCountX) (pointY : LaneTables pointElementCountY)
    (gadget : Vector Exception.Entry FieldMacToECMac.outputMacCount) : Public :=
  let curveK := Pipeline.curveValues curveX.offsets curveY.offsets
  let curveSlopes := CurveMembership.slopes curveR1 curveR2 curveK
  let digitK : FieldMacToECMac.DigitValues :=
    fun digit => Pipeline.digitValues pointX.offsets pointY.offsets digit
  let pointSlopes : Fin digitCount → Biquadratic.Values := fun digit =>
    Biquadratic.slopes (pointRandomness.get digit).x (pointRandomness.get digit).y
      (pointRandomness.get digit).z (digitK digit)
  let rows := FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness
  { curve := CurveMembership.garble bridgeKey curveMask.value curveR1 curveR2 curveK
    rows := Vector.ofFn fun index =>
      FieldMacToECMac.garbleRow (rows.get index) (pointRandomness.get index) (digitK index)
    exception := gadget
    curveXHot := curveX.hotJoins
    curveYHot := curveY.hotJoins
    pointXHot := pointX.hotJoins
    pointYHot := pointY.hotJoins
    scale := Vector.ofFn fun chunk => pack (Pipeline.assembleWord
      (pointX.scaleJoins (Pipeline.pointXAssemble pointSlopes) chunk)
      (curveX.scaleJoins (Pipeline.curveXAssemble curveSlopes) chunk)
      (pointY.scaleJoins (Pipeline.pointYAssemble pointSlopes) chunk)
      (curveY.scaleJoins (Pipeline.curveYAssemble curveSlopes) chunk)) }

/-- **On the real tables, the assembly is the Plan B garbler.** -/
theorem assemble_real (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (exceptionPad : FieldMacToECMac.ExceptionPad)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (oracle : Oracle) (delta : PlanB.Coord → Block) (key : InputMacKey) :
    assemble outputKeys pointRandomness bridgeKey curveMask curveR1 curveR2
        (laneTables oracle.1 curveElementCountX .curveX (delta .x) (Pipeline.bitKeyOf key .x))
        (laneTables oracle.1 curveElementCountY .curveY (delta .y) (Pipeline.bitKeyOf key .y))
        (laneTables oracle.1 pointElementCountX .pointX (delta .x)
          (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 bridgeKey key) .x))
        (laneTables oracle.1 pointElementCountY .pointY (delta .y)
          (Pipeline.bitKeyOf (Pipeline.whitenedKey oracle.2.1 oracle.2.2 bridgeKey key) .y))
        (Vector.ofFn fun output => FieldMacToECMac.garbleEntry
          (Pipeline.gadgetPermutations oracle.1) output (outputKeys.get output)
          (EncPRF.transformKey oracle.2.1 (EncPRF.whiteningKeys oracle.2.2 bridgeKey) key)
          (exceptionPad.get output)) =
      Pipeline.garble outputKeys pointRandomness exceptionPad bridgeKey curveMask curveR1 curveR2
        oracle.1 oracle.2.1 oracle.2.2 delta key := rfl

/-- **The garbling program**: the bridge-key hash, the EncPRF pads, the four lanes, the gadget. -/
def garbleM (scalar : NonZeroScalar) (coins : Coins) : M (Public × InputMacKey) :=
  let key := coins.inputMacKey
  let outputKeys := FieldMacToECMac.outputKeys construction scalar.value coins.offsets
  askHash coins.bridgeKey >>= fun hashed =>
    padsM ⟨hashed.1, hashed.2⟩ >>= fun pads =>
      laneM curveElementCountX .curveX (coins.inputDelta .x) (Pipeline.bitKeyOf key .x)
        >>= fun curveX =>
      laneM curveElementCountY .curveY (coins.inputDelta .y) (Pipeline.bitKeyOf key .y)
        >>= fun curveY =>
      laneM pointElementCountX .pointX (coins.inputDelta .x)
          (Pipeline.bitKeyOf (whitenKeyOf pads key) .x) >>= fun pointX =>
      laneM pointElementCountY .pointY (coins.inputDelta .y)
          (Pipeline.bitKeyOf (whitenKeyOf pads key) .y) >>= fun pointY =>
      gadgetM outputKeys (transformKeyOf pads key) coins.exceptionPad >>= fun gadget =>
        pure (assemble outputKeys coins.pointRandomness coins.bridgeKey coins.curveMask
          coins.curveR1 coins.curveR2 curveX curveY pointX pointY gadget, key)

theorem eval_garbleM (scalar : NonZeroScalar) (coins : Coins) (oracle : Oracle) :
    (garbleM scalar coins).eval (publicAnswer oracle) =
      (Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value coins.offsets)
        coins.pointRandomness coins.exceptionPad coins.bridgeKey coins.curveMask coins.curveR1
        coins.curveR2 oracle.1 oracle.2.1 oracle.2.2 coins.inputDelta coins.inputMacKey,
        coins.inputMacKey) := by
  simp only [garbleM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askHash, eval_padsM,
    eval_laneM, eval_gadgetM, whitenKeyOf_realPads, transformKeyOf_realPads]
  rw [← assemble_real]
  rfl

/-- The garbler's exact query budget, term by term. -/
def garbleBudget : Nat :=
  1 + (1016 + (laneGarbleBudget curveElementCountX + (laneGarbleBudget curveElementCountY +
    (laneGarbleBudget pointElementCountX + (laneGarbleBudget pointElementCountY +
      (FieldMacToECMac.outputMacCount * 508 + 0))))))

theorem bounded_garbleM (scalar : NonZeroScalar) (coins : Coins) :
    (garbleM scalar coins).Bounded garbleBudget :=
  Bounded.bind (bounded_askHash _) fun _ =>
    Bounded.bind (bounded_padsM _) fun _ =>
      Bounded.bind (bounded_laneM _ _ _ _) fun _ =>
        Bounded.bind (bounded_laneM _ _ _ _) fun _ =>
          Bounded.bind (bounded_laneM _ _ _ _) fun _ =>
            Bounded.bind (bounded_laneM _ _ _ _) fun _ =>
              Bounded.bind (bounded_gadgetM _ _ _) fun _ => Bounded.pure' _ 0

/-! ## The evaluator -/

/-- The evaluator's step material at one level: every entry but the active one is hashed; the
active one is recovered from the published join. -/
def evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat) (bitLabel join : Block)
    (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) : M (Fin (2 ^ step) → Block) :=
  FreeQuery.vector (2 ^ step) (fun entry =>
    if entry = active then pure 0 else foldMaskM lane chunk step entry.val (parent entry))
    >>= fun masks =>
      pure fun entry =>
        if entry = active then join ^^^ bitLabel ^^^ xorFoldExcept active masks.get
        else masks.get entry

/-- `xorFoldExcept` never reads the skipped entry. -/
theorem xorFoldExcept_congr {count : Nat} (skip : Fin count) (first second : Fin count → Block)
    (agree : ∀ entry, entry ≠ skip → first entry = second entry) :
    xorFoldExcept skip first = xorFoldExcept skip second := by
  unfold xorFoldExcept
  congr 1
  funext acc entry
  by_cases same : entry = skip
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same, agree entry same]

theorem eval_evalStepM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (bitLabel join : Block) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    (evalStepM lane chunk step bitLabel join active parent).eval (publicAnswer oracle) =
      evalStep oracle.1 lane chunk step bitLabel join active parent := by
  funext entry
  simp only [evalStepM, evalStep, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector]
  by_cases same : entry = active
  · rw [if_pos same, if_pos same]
    congr 1
    apply xorFoldExcept_congr
    intro other different
    simp only [Vector.get_ofFn, if_neg different, eval_foldMaskM]
  · simp only [if_neg same, Vector.get_ofFn, eval_foldMaskM]

theorem bounded_evalStepM (lane : Lane) (chunk : Fin chunkCount) (step : Nat)
    (bitLabel join : Block) (active : Fin (2 ^ step)) (parent : Fin (2 ^ step) → Block) :
    (evalStepM lane chunk step bitLabel join active parent).Bounded ((2 ^ step - 1) * 2) :=
  (Bounded.bind (Bounded.vector (budget := fun entry => if entry = active then 0 else 2)
    fun entry => Bounded.ite (fun _ => Bounded.pure' _ _) fun different => by
      rw [if_neg different]
      exact bounded_foldMaskM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by
        rw [FreeQuery.sum_ite_skip, Nat.add_zero])

/-- The evaluator's fold, level by level. -/
def evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat) (bitLabel join : Nat → Block) :
    (steps : Nat) → M (Fin (2 ^ steps) → Block)
  | 0 => pure fun _ => 0
  | steps + 1 =>
      evalFoldM lane chunk value bitLabel join steps >>= fun previous =>
        evalStepM lane chunk steps (bitLabel steps) (join steps) (activeAt value steps) previous
          >>= fun right => pure (extendLevel steps previous right)

theorem eval_evalFoldM (oracle : Oracle) (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (steps : Nat) :
    (evalFoldM lane chunk value bitLabel join steps).eval (publicAnswer oracle) =
      evalFold oracle.1 lane chunk value bitLabel join steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [evalFoldM, evalFold, FreeQuery.eval_bind, FreeQuery.eval_pure, ih,
        eval_evalStepM]

/-- The evaluator's fold queries over `steps` levels. -/
def hotEvalBudget : Nat → Nat
  | 0 => 0
  | steps + 1 => hotEvalBudget steps + (2 ^ steps - 1) * 2

theorem bounded_evalFoldM (lane : Lane) (chunk : Fin chunkCount) (value : Nat)
    (bitLabel join : Nat → Block) (steps : Nat) :
    (evalFoldM lane chunk value bitLabel join steps).Bounded (hotEvalBudget steps) := by
  induction steps with
  | zero => exact Bounded.pure' _ _
  | succ steps ih =>
      exact (Bounded.bind ih fun _ =>
        Bounded.bind (bounded_evalStepM _ _ _ _ _ _ _) fun _ =>
          Bounded.pure' _ 0).of_eq (by simp [hotEvalBudget])

/-- The evaluator's switch masks of one chunk: every switch but the active one. -/
def evalMasksM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha : Fin (2 ^ width)) : M (Fin (2 ^ width) → Fin count → BaseField) :=
  FreeQuery.vector (2 ^ width) (fun switch =>
    if switch = alpha then pure fun _ => 0
    else switchMaskM count lane chunk switch.val (hot switch)) >>= fun masks => pure masks.get

/-- The evaluator's free fold of one chunk, read from its switch masks. -/
def evalScaleOf {count : Nat} (width : Nat) (masks : Fin (2 ^ width) → Fin count → BaseField)
    (alpha : Fin (2 ^ width)) (join : Fin count → BaseField) : Fin count → BaseField :=
  fun element => ∑ switch : Fin (2 ^ width), iota _ switch *
    (if switch = alpha then
        join element - ∑ other ∈ Finset.univ.erase alpha, masks other element
      else masks switch element)

theorem evalScaleOf_evalMasksM (oracle : Oracle) (count : Nat) (lane : Lane)
    (chunk : Fin chunkCount) (width : Nat) (hot : HotLabels width) (alpha : Fin (2 ^ width))
    (join : Fin count → BaseField) :
    evalScaleOf width ((evalMasksM count lane chunk width hot alpha).eval (publicAnswer oracle))
        alpha join =
      evalScale oracle.1 lane chunk width hot alpha join := by
  funext element
  simp only [evalScaleOf, evalScale, evalMasksM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn]
  refine Finset.sum_congr rfl fun switch _ => ?_
  by_cases same : switch = alpha
  · rw [if_pos same, if_pos same]
    congr 2
    refine Finset.sum_congr rfl fun other member => ?_
    rw [if_neg (Finset.ne_of_mem_erase member), eval_switchMaskM]
  · rw [if_neg same, if_neg same, if_neg same, eval_switchMaskM]

theorem bounded_evalMasksM (count : Nat) (lane : Lane) (chunk : Fin chunkCount) (width : Nat)
    (hot : HotLabels width) (alpha : Fin (2 ^ width)) :
    (evalMasksM count lane chunk width hot alpha).Bounded ((2 ^ width - 1) * (count * 3)) :=
  (Bounded.bind (Bounded.vector (budget := fun switch => if switch = alpha then 0 else count * 3)
    fun switch => Bounded.ite (fun _ => Bounded.pure' _ _) fun different => by
      rw [if_neg different]
      exact bounded_switchMaskM _ _ _ _ _) fun _ => Bounded.pure' _ 0).of_eq (by
        rw [FreeQuery.sum_ite_skip, Nat.add_zero])

/-- **`Eval` for one lane**: per chunk, rebuild the one-hot labels, then fold them against the
chunk index; sum over the chunks. -/
def evalChunkM (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) : M (Fin count → BaseField) :=
  evalFoldM lane c (chunkValue bits c).toNat
      (labelAt (chunkLabels labels c)) (joinAt (hotSlice joins c)) (chunkWidth c) >>= fun hot =>
    evalMasksM count lane c (chunkWidth c) hot (chunkOf bits c) >>= fun masks =>
      pure (evalScaleOf (chunkWidth c) masks (chunkOf bits c) (scale c))

def evalLaneM (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) : M (Fin count → BaseField) :=
  FreeQuery.vector chunkCount (evalChunkM count lane joins scale bits labels) >>= fun perChunk =>
    pure fun element => ∑ c : Fin chunkCount, perChunk.get c element

theorem eval_evalLaneM (oracle : Oracle) (count : Nat) (lane : Lane)
    (joins : Vector Block foldStepCount) (scale : Fin chunkCount → Fin count → BaseField)
    (bits : BitVec coordinateBitCount) (labels : Fin coordinateBitCount → Block) :
    (evalLaneM count lane joins scale bits labels).eval (publicAnswer oracle) =
      evalCoord oracle.1 lane joins scale bits labels := by
  funext element
  simp only [evalLaneM, evalChunkM, FreeQuery.eval_bind, FreeQuery.eval_pure,
    FreeQuery.eval_vector, Vector.get_ofFn, eval_evalFoldM, evalScaleOf_evalMasksM]
  rfl

/-- One lane's evaluation queries. -/
def laneEvalBudget (count : Nat) : Nat :=
  ∑ c : Fin chunkCount, (hotEvalBudget (chunkWidth c) + (2 ^ chunkWidth c - 1) * (count * 3))

theorem bounded_evalChunkM (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) (c : Fin chunkCount) :
    (evalChunkM count lane joins scale bits labels c).Bounded
      (hotEvalBudget (chunkWidth c) + (2 ^ chunkWidth c - 1) * (count * 3)) := by
  unfold evalChunkM
  exact (Bounded.bind (bounded_evalFoldM _ _ _ _ _ _) fun _ =>
    Bounded.bind (bounded_evalMasksM count lane c _ _ _) fun _ => Bounded.pure' _ 0).of_eq
      (by rw [Nat.add_zero])

theorem bounded_evalLaneM (count : Nat) (lane : Lane) (joins : Vector Block foldStepCount)
    (scale : Fin chunkCount → Fin count → BaseField) (bits : BitVec coordinateBitCount)
    (labels : Fin coordinateBitCount → Block) :
    (evalLaneM count lane joins scale bits labels).Bounded (laneEvalBudget count) := by
  unfold evalLaneM
  exact (Bounded.bind (Bounded.vector fun c => bounded_evalChunkM count lane joins scale bits labels c)
    fun _ => Bounded.pure' _ 0).of_eq (by rw [Nat.add_zero]; rfl)

/-- The evaluator's pads: per position, the whitening pad (bit `false`) and the pad of the held
bit, which is the same question when the bit is `false`. -/
def evalPadsM (keys : WhiteningKeys) (bits : BitInput) :
    M (EncPRF.Coordinate → Fin coordinateBitCount → Block × Block) :=
  let row (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount) :=
    FreeQuery.vector coordinateBitCount fun index =>
      padM keys which index false >>= fun zero =>
        if word.getLsb index then padM keys which index true >>= fun one => pure (zero, one)
        else pure (zero, zero)
  row .x bits.xBits >>= fun xs => row .y bits.yBits >>= fun ys =>
    pure fun which index => match which with
      | .x => xs.get index
      | .y => ys.get index

/-- The evaluator's pads of a real oracle. -/
def realEvalPads (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) :
    EncPRF.Coordinate → Fin coordinateBitCount → Block × Block :=
  fun which index =>
    (EncPRF.evenMansourPad encOracle keys { coordinate := which, index, bit := false },
      EncPRF.evenMansourPad encOracle keys
        { coordinate := which, index,
          bit := match which with
            | .x => bits.xBits.getLsb index
            | .y => bits.yBits.getLsb index })

theorem eval_evalPadsM (oracle : Oracle) (keys : WhiteningKeys) (bits : BitInput) :
    (evalPadsM keys bits).eval (publicAnswer oracle) = realEvalPads oracle.2.1 keys bits := by
  funext which index
  cases which
  · simp only [evalPadsM, realEvalPads, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn]
    cases bit : bits.xBits.getLsb index
    · simp only [Bool.false_eq_true, if_false, FreeQuery.eval_pure, eval_padM]
    · simp only [if_true, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_padM]
  · simp only [evalPadsM, realEvalPads, FreeQuery.eval_bind, FreeQuery.eval_pure,
      FreeQuery.eval_vector, Vector.get_ofFn]
    cases bit : bits.yBits.getLsb index
    · simp only [Bool.false_eq_true, if_false, FreeQuery.eval_pure, eval_padM]
    · simp only [if_true, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_padM]

theorem bounded_evalPadsM (keys : WhiteningKeys) (bits : BitInput) :
    (evalPadsM keys bits).Bounded 1016 := by
  have row : ∀ (which : EncPRF.Coordinate) (word : BitVec coordinateBitCount)
      (index : Fin coordinateBitCount),
      (padM keys which index false >>= fun zero =>
        if word.getLsb index then padM keys which index true >>= fun one => pure (zero, one)
        else pure (zero, zero)).Bounded 2 := fun which word index =>
    Bounded.bind (bounded_padM _ _ _ _) fun _ =>
      Bounded.ite (fun _ => Bounded.bind (bounded_padM _ _ _ _) fun _ => Bounded.pure' _ 0)
        fun _ => Bounded.pure' _ _
  exact (Bounded.bind (Bounded.vector_const fun index => row .x bits.xBits index) fun _ =>
    Bounded.bind (Bounded.vector_const fun index => row .y bits.yBits index) fun _ =>
      Bounded.pure' _ 0).of_eq (by norm_num)

/-- The whitened selected labels, from the evaluator's pads. -/
def whitenMacOf (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) : InputMac := {
  x := Vector.ofFn fun index => encrypt (pads .x index).1 mac.x[index.val]
  y := Vector.ofFn fun index => encrypt (pads .y index).1 mac.y[index.val] }

/-- The transformed selected labels, from the evaluator's pads. -/
def transformMacOf (pads : EncPRF.Coordinate → Fin coordinateBitCount → Block × Block)
    (mac : InputMac) : InputMac := {
  x := Vector.ofFn fun index => encrypt (pads .x index).2 mac.x[index.val]
  y := Vector.ofFn fun index => encrypt (pads .y index).2 mac.y[index.val] }

theorem whitenMacOf_real (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) (mac : InputMac) :
    whitenMacOf (realEvalPads encOracle keys bits) mac = EncPRF.whitenMac encOracle keys mac := rfl

theorem transformMacOf_real (encOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (bits : BitInput) (mac : InputMac) :
    transformMacOf (realEvalPads encOracle keys bits) mac =
      EncPRF.transformMac encOracle keys bits mac := rfl

/-- The 91 exception digits the gadget unlocks. -/
def unlockM (table : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    M (Vector Digit FieldMacToECMac.outputMacCount) :=
  FreeQuery.vector FieldMacToECMac.outputMacCount fun index =>
    gadgetMaskM index mac >>= fun mask => pure (Exception.unlock mask (table.2.get index) input)

theorem eval_unlockM (oracle : Oracle) (table : FieldMacToECMac.Table) (input : AffineInput)
    (mac : InputMac) :
    (unlockM table input mac).eval (publicAnswer oracle) =
      Vector.ofFn fun index => Exception.unlock
        (FieldMacToECMac.gadgetMask (Pipeline.gadgetPermutations oracle.1) index mac)
        (table.2.get index) input := by
  simp only [unlockM, FreeQuery.eval_vector, FreeQuery.eval_bind, FreeQuery.eval_pure,
    eval_gadgetMaskM]

theorem bounded_unlockM (table : FieldMacToECMac.Table) (input : AffineInput) (mac : InputMac) :
    (unlockM table input mac).Bounded (FieldMacToECMac.outputMacCount * (508 + 0)) :=
  Bounded.vector_const fun _ => Bounded.bind (bounded_gadgetMaskM _ _) fun _ => Bounded.pure' _ 0

section Evaluator

variable [FieldCertificate] [GroupCertificate]

/-- The on-curve branch of the evaluator: curve lanes, bridge key, EncPRF, point lanes, gadget. -/
def onCurveM (table : Public) (bits : BitInput) (mac : InputMac) : M (Option (Option Point)) :=
  evalLaneM curveElementCountX .curveX table.curveXHot
      (fun chunk => Pipeline.readCurveX (unpack (table.scale.get chunk)))
      (Pipeline.coordBits bits .x) (Pipeline.macLabels mac .x) >>= fun curveX =>
    evalLaneM curveElementCountY .curveY table.curveYHot
        (fun chunk => Pipeline.readCurveY (unpack (table.scale.get chunk)))
        (Pipeline.coordBits bits .y) (Pipeline.macLabels mac .y) >>= fun curveY =>
      askHash (CurveMembership.evaluate table.curve bits.toAffine
          (Pipeline.curveValues curveX curveY)) >>= fun hashed =>
        evalPadsM ⟨hashed.1, hashed.2⟩ bits >>= fun pads =>
          evalLaneM pointElementCountX .pointX table.pointXHot
              (fun chunk => Pipeline.readPointX (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .x) (Pipeline.macLabels (whitenMacOf pads mac) .x)
            >>= fun pointX =>
          evalLaneM pointElementCountY .pointY table.pointYHot
              (fun chunk => Pipeline.readPointY (unpack (table.scale.get chunk)))
              (Pipeline.coordBits bits .y) (Pipeline.macLabels (whitenMacOf pads mac) .y)
            >>= fun pointY =>
          unlockM (Pipeline.pointTable table) bits.toAffine (transformMacOf pads mac)
            >>= fun digits =>
          pure (some (Garbling.decodeResult
            { point := bits.toAffine
              pointMacs := FieldMacToECMac.evaluateHomogeneous (Pipeline.pointTable table)
                (Pipeline.digitValues pointX pointY) bits.toAffine
              exceptionDigits := digits }))

/-- **The evaluation program.** An off-curve input is refused before any query. -/
def evaluateM (table : Public) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    M (Option (Option Point)) :=
  match decodePoint (Lamport.restore input labels).input.toAffine with
  | none => pure (some none)
  | some _ => onCurveM table (Lamport.restore input labels).input
      (Lamport.restore input labels).inputMac

theorem eval_onCurveM (oracle : Oracle) (table : Public) (bits : BitInput) (mac : InputMac)
    (point : Point) (decoded : decodePoint bits.toAffine = some point) :
    (onCurveM table bits mac).eval (publicAnswer oracle) =
      some ((Pipeline.evaluate oracle.1 oracle.2.1 oracle.2.2 table bits mac).bind
        Garbling.decodeResult) := by
  simp only [onCurveM, FreeQuery.eval_bind, FreeQuery.eval_pure, eval_askHash, eval_evalLaneM,
    eval_evalPadsM, eval_unlockM, whitenMacOf_real, transformMacOf_real]
  simp only [Pipeline.evaluate, decoded, Option.bind_some]
  rfl

theorem eval_evaluateM (oracle : Oracle) (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    (evaluateM table input labels).eval (publicAnswer oracle) =
      Scheme.scheme.evaluate oracle table input labels := by
  unfold evaluateM
  split
  · rename_i decoded
    simp only [Scheme.scheme, Garbling.evaluate, Pipeline.evaluate, decoded, Option.bind_none,
      FreeQuery.eval_pure]
  · rename_i point decoded
    rw [eval_onCurveM oracle table _ _ point decoded]
    rfl

/-- The evaluator's exact query budget, term by term. -/
def evaluateBudget : Nat :=
  laneEvalBudget curveElementCountX + (laneEvalBudget curveElementCountY + (1 + (1016 +
    (laneEvalBudget pointElementCountX + (laneEvalBudget pointElementCountY +
      (FieldMacToECMac.outputMacCount * (508 + 0) + 0))))))

theorem bounded_evaluateM (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) : (evaluateM table input labels).Bounded evaluateBudget := by
  unfold evaluateM
  split
  · exact Bounded.pure' _ _
  · exact Bounded.bind (bounded_evalLaneM _ _ _ _ _ _) fun _ =>
      Bounded.bind (bounded_evalLaneM _ _ _ _ _ _) fun _ =>
        Bounded.bind (bounded_askHash _) fun _ =>
          Bounded.bind (bounded_evalPadsM _ _) fun _ =>
            Bounded.bind (bounded_evalLaneM _ _ _ _ _ _) fun _ =>
              Bounded.bind (bounded_evalLaneM _ _ _ _ _ _) fun _ =>
                Bounded.bind (bounded_unlockM _ _ _) fun _ => Bounded.pure' _ 0

end Evaluator

/-! ## The budgets, evaluated -/

theorem hotGarbleBudget_two : hotGarbleBudget 2 = 4 := rfl

theorem hotEvalBudget_two : hotEvalBudget 2 = 2 := rfl

theorem laneGarbleBudget_eq (count : Nat) :
    laneGarbleBudget count = (chunkCount - 1) * (hotGarbleBudget chunkBits + 2 ^ chunkBits *
      (count * 3)) + (hotGarbleBudget lastChunkBits + 2 ^ lastChunkBits * (count * 3)) := by
  rw [laneGarbleBudget,
    sum_chunkWidth (fun width => hotGarbleBudget width + 2 ^ width * (count * 3))]

theorem laneEvalBudget_eq (count : Nat) :
    laneEvalBudget count = (chunkCount - 1) * (hotEvalBudget chunkBits + (2 ^ chunkBits - 1) *
      (count * 3)) + (hotEvalBudget lastChunkBits + (2 ^ lastChunkBits - 1) * (count * 3)) := by
  rw [laneEvalBudget,
    sum_chunkWidth (fun width => hotEvalBudget width + (2 ^ width - 1) * (count * 3))]

/-- **Garbling asks `1,305,053` questions**: `1` hash, `1,016` EncPRF pads, `2,032` fold hashes,
`1,255,776` switch-mask blocks and `46,228` gadget hashes. -/
theorem garbleBudget_eq : garbleBudget = 1305053 := by
  unfold garbleBudget
  rw [laneGarbleBudget_eq, laneGarbleBudget_eq, laneGarbleBudget_eq, laneGarbleBudget_eq]
  simp only [chunkCount, chunkBits, lastChunkBits, hotGarbleBudget_two, curveElementCountX,
    curveElementCountY, pointElementCountX, pointElementCountY]
  norm_num

/-- **Evaluation asks `990,093` questions**: `1,016` fold hashes, `941,832` switch-mask blocks,
`1` hash, `≤ 1,016` EncPRF pads and `46,228` gadget hashes. -/
theorem evaluateBudget_eq : evaluateBudget = 990093 := by
  unfold evaluateBudget
  rw [laneEvalBudget_eq, laneEvalBudget_eq, laneEvalBudget_eq, laneEvalBudget_eq]
  simp only [chunkCount, chunkBits, lastChunkBits, hotEvalBudget_two, curveElementCountX,
    curveElementCountY, pointElementCountX, pointElementCountY]
  norm_num

/-! ## The indexed programs -/

variable [FieldCertificate] [GroupCertificate]

/-- The garbling query bound, which the program's type carries. -/
def garbleQueries : Nat := 1305053

/-- The evaluation query bound, which the program's type carries. -/
def evaluateQueries : Nat := 990093

/-- **The garbling program**, at its exact budget. -/
def garbleProgram (_parameter : Nat) (scalar : NonZeroScalar) (coins : Coins) :
    QueryProgram Spec (Public × InputMacKey) garbleQueries :=
  FreeQuery.toProgram (garbleM scalar coins) garbleQueries
    ((bounded_garbleM scalar coins).of_eq garbleBudget_eq)

/-- **The evaluation program**, at its exact budget. -/
def evaluateProgram (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    QueryProgram Spec (Option (Option Point)) evaluateQueries :=
  FreeQuery.toProgram (evaluateM table input labels) evaluateQueries
    ((bounded_evaluateM table input labels).of_eq evaluateBudget_eq)

/-- **The garbling program is the scheme's garbler**, for every complete oracle. -/
theorem garbleProgram_correct (parameter : Nat) (scalar : NonZeroScalar) (coins : Coins)
    (oracle : Oracle) :
    (garbleProgram parameter scalar coins).eval (publicAnswer oracle) =
      Scheme.scheme.garble parameter scalar (coins, oracle) := by
  rw [garbleProgram, FreeQuery.eval_toProgram, eval_garbleM]
  rfl

/-- **The evaluation program is the scheme's evaluator**, for every complete oracle. -/
theorem evaluateProgram_correct (table : Public) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) (oracle : Oracle) :
    (evaluateProgram table input labels).eval (publicAnswer oracle) =
      Scheme.scheme.evaluate oracle table input labels := by
  rw [evaluateProgram, FreeQuery.eval_toProgram, eval_evaluateM]

end Kriterion.ArgoMAC.Programs
