/-
**Phase 3, P1 → P3: `MaskSwapBound.real`, against the Glue's own games.**

`Glue/Assembly.lean` asks for `HopBound realHybrid hybrids.maskSwapped (fun _ _ => maskSwapError)`.
This module supplies

* `maskSwappedHybrid : Glue.HybridGame` — **`G0U`**: the Glue's `G0` (`tapeRealGame`, i.e.
  `realGame Scheme.scheme` on the uniform `Coins × Oracle` tape) with the tape drawn from
  `MaskSwap.swappedTape` at the **garbler's own one-hot labels** (`garblerKeys`): every scale mask of
  every lane swapped to uniform `F_p`, the coins, the EncPRF and hash oracles and every non-scale
  fixed-key permutation unchanged;
* `maskSwapBound_real : Glue.HopBound Glue.realHybrid maskSwappedHybrid (fun _ _ => Glue.maskSwapError)`
  — P3's field `MaskSwapBound.real`, verbatim, with P3's constant `maskSwapError = 824 · 508 ·
  (2^384 mod p) / 2^384` matched **exactly** (`maskSwapError_eq`).

The proof: `G0` is `realGame` on `(realTape uniform).map reassemble` (`uniform_eq_realTape`, a
bijection of the tape; the instance mismatch of `Fintype.ofFinite` against the derived instances is
closed by `Subsingleton`), both games are `realGame` of a tape law followed by the same continuation,
so their distance is at most the tape laws' (`PMF.etvDist_bind_right_le`), which is
`MaskSwap.maskSwap_etvDist_le` at the observation `reassemble`; the challenge's `advantage` of two
`PMF Bool` is their total-variation distance (`advantage_le_etvDist`).
-/

import Proof.Privacy.Phase3.MaskSwap
import Proof.Privacy.Phase3.Glue.Assembly

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography GarbledCircuit Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Scheme (Coins Oracle)
open scoped ENNReal

noncomputable section

/-! ### The challenge's advantage is at most the total-variation distance -/

theorem pmf_bool_false (law : PMF Bool) : law false = 1 - law true := by
  have total := law.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at total
  have swapped : (1 : ℝ≥0∞) = law false + law true := by
    rw [← total]; ring
  exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top law _) swapped).symm

theorem etvDist_bool (first second : PMF Bool) :
    first.etvDist second = ENNReal.absDiff (first true) (second true) := by
  simp only [PMF.etvDist]
  rw [tsum_fintype, Fintype.sum_bool, pmf_bool_false first, pmf_bool_false second,
    ENNReal.absDiff_tsub_tsub (PMF.coe_le_one first _) (PMF.coe_le_one second _)
      ENNReal.one_ne_top,
    show ENNReal.absDiff (first true) (second true) + ENNReal.absDiff (first true) (second true)
      = 2 * ENNReal.absDiff (first true) (second true) from by ring,
    mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **The challenge's `advantage` is the total-variation distance** of the two `PMF Bool`s. -/
theorem advantage_eq_etvDist (first second : PMF Bool) :
    Assumptions.advantage first second = (first.etvDist second).toReal := by
  rw [Assumptions.advantage, etvDist_bool]
  exact (ENNReal.absDiff_toReal (PMF.apply_ne_top first _) (PMF.apply_ne_top second _)).symm

/-! ### The tape, reorganised for `MaskSwap` -/

/-- The part of the challenge's tape `MaskSwap` treats as fixed: the private coins, the EncPRF
permutations and the hash. -/
abbrev TapeRest := Coins × PermutationOracle EncPRF.PermutationIndex Block × EncPRF.HashOracle

/-- Put the fixed-key oracle back in its place. -/
def reassembleEquiv : (TapeRest × PermutationOracle FixedIndex Block) ≃ (Coins × Oracle) where
  toFun tape := (tape.1.1, tape.2, tape.1.2.1, tape.1.2.2)
  invFun tape := ((tape.1, tape.2.2.1, tape.2.2.2), tape.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite instances `MaskSwap` needs on the rest (no cardinality is computed). -/
noncomputable instance coinsFintype' : Fintype Coins := Fintype.ofFinite Coins

instance tapeRestNonempty : Nonempty TapeRest :=
  ⟨(Scheme.witness, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

/-- The uniform law of the rest. -/
def restUniform : PMF TapeRest := PMF.uniformOfFintype TapeRest

/-- **The uniform challenge tape is `MaskSwap.realTape`, reassembled** (at the instances `MaskSwap`
uses; `uniformTape_eq` restates it at any instances). -/
theorem uniform_eq_realTape :
    PMF.uniformOfFintype (Coins × Oracle) = (realTape restUniform).map reassembleEquiv := by
  rw [realTape, restUniform, ← uniformOfFintype_productPMF]
  exact (Kriterion.ArgoMAC.Security.PGS.uniformOfFintype_map_equiv reassembleEquiv).symm

/-- The same at any `Fintype` instances: the uniform law does not depend on them. -/
theorem uniformTape_eq (tapeFintype : Fintype (Coins × Oracle)) :
    @PMF.uniformOfFintype (Coins × Oracle) tapeFintype _
      = (realTape restUniform).map reassembleEquiv := by
  rw [← uniform_eq_realTape]
  congr 1
  exact Subsingleton.elim _ _

/-! ### The garbler's one-hot labels -/

/-- **The garbler's lane keys**, read off the rest of the tape exactly as `Pipeline.garble` reads
them: each lane's global offset `Δ_{coord}` and bit keys — the raw Lamport keys for system A, the
EncPRF-whitened keys (`Pipeline.whitenedKey`, keyed by `hash(t)`) for system B. -/
def garblerKeys (rest : TapeRest) :
    (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block) :=
  (fun lane => rest.1.inputDelta lane.coord,
   fun lane => match lane with
    | .curveX => Pipeline.bitKeyOf rest.1.inputMacKey .x
    | .curveY => Pipeline.bitKeyOf rest.1.inputMacKey .y
    | .pointX => Pipeline.bitKeyOf
        (Pipeline.whitenedKey rest.2.1 rest.2.2 rest.1.bridgeKey rest.1.inputMacKey) .x
    | .pointY => Pipeline.bitKeyOf
        (Pipeline.whitenedKey rest.2.1 rest.2.2 rest.1.bridgeKey rest.1.inputMacKey) .y)

/-- The swapped tape at the garbler's own points, reassembled into the challenge's tape. -/
def swappedChallengeTape : PMF (Coins × Oracle) :=
  (swappedTape restUniform (planBPoint garblerKeys)).map reassembleEquiv

/-! ### `G0U` and the hop -/

/-- **`G0U`** as a Glue chain game: the Glue's `G0` with the swapped tape. -/
def maskSwappedHybrid : Kriterion.ArgoMAC.Phase3.Glue.HybridGame := fun adversary parameter scalar =>
  realGame Scheme.scheme (fun _ => swappedChallengeTape) (publicHandler Prod.snd) adversary
    parameter scalar ()

/-- `G0` is `realGame` on the reorganised real tape, at any instances. -/
theorem tapeRealGame_eq_realTape [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
    [Fintype EncPRF.PermutationIndex] [coins : Fintype Coins]
    (adversary : Kriterion.ArgoMAC.Phase3.Glue.PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Kriterion.ArgoMAC.Phase3.Glue.tapeRealGame adversary parameter scalar ()
      = realGame Scheme.scheme (fun _ => (realTape restUniform).map reassembleEquiv)
          (publicHandler Prod.snd) adversary parameter scalar () := by
  unfold Kriterion.ArgoMAC.Phase3.Glue.tapeRealGame
  rw [uniformTape_eq]

/-- Two `realGame`s that differ only in their tape laws are as close as the tape laws. -/
theorem realGame_etvDist_le [FieldCertificate] [GroupCertificate]
    (adversary : Kriterion.ArgoMAC.Phase3.Glue.PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) (first second : PMF (Coins × Oracle)) :
    (realGame Scheme.scheme (fun _ => first) (publicHandler Prod.snd) adversary parameter scalar
        ()).etvDist
      (realGame Scheme.scheme (fun _ => second) (publicHandler Prod.snd) adversary parameter scalar
        ())
      ≤ first.etvDist second := by
  unfold realGame
  exact PMF.etvDist_bind_right_le _ first second

/-- P3's constant is exactly `N · δ₃`. -/
theorem maskSwapError_eq :
    Kriterion.ArgoMAC.Phase3.Glue.maskSwapError
      = ((Fintype.card MaskSite : ℝ≥0∞) * delta3).toReal := by
  rw [Kriterion.ArgoMAC.Phase3.Glue.maskSwapError, Kriterion.ArgoMAC.Phase3.Glue.scaleMaskCount,
    card_maskSite, delta3, reductionResidue, ENNReal.toReal_mul, ENNReal.toReal_div]
  norm_num
  ring

/-- **`G0 → G0U` in the challenge's currency, at any instances.** -/
theorem advantage_real_swapped_le [FieldCertificate] [GroupCertificate] [Fintype FixedIndex]
    [Fintype EncPRF.PermutationIndex] [Fintype Coins]
    (adversary : Kriterion.ArgoMAC.Phase3.Glue.PlanBAdversary Unit) (parameter : ℕ)
    (scalar : NonZeroScalar) :
    Assumptions.advantage (Kriterion.ArgoMAC.Phase3.Glue.tapeRealGame adversary parameter scalar ())
        (realGame Scheme.scheme (fun _ => swappedChallengeTape) (publicHandler Prod.snd) adversary
          parameter scalar ())
      ≤ Kriterion.ArgoMAC.Phase3.Glue.maskSwapError := by
  rw [tapeRealGame_eq_realTape, advantage_eq_etvDist, maskSwapError_eq]
  have finite : (Fintype.card MaskSite : ℝ≥0∞) * delta3 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp))
  refine ENNReal.toReal_mono finite (le_trans (realGame_etvDist_le adversary parameter scalar _ _) ?_)
  exact maskSwap_etvDist_le restUniform (planBPoint garblerKeys) reassembleEquiv

/-- **`MaskSwapBound.real`** (P3's field, verbatim): `G0 → G0U` costs `maskSwapError = N · δ₃`, at the
`Solution` instances, for every adversary (the `2^100` budget hypothesis is not needed). -/
theorem maskSwapBound_real :
    Kriterion.ArgoMAC.Phase3.Glue.HopBound Kriterion.ArgoMAC.Phase3.Glue.realHybrid
      maskSwappedHybrid fun _ _ => Kriterion.ArgoMAC.Phase3.Glue.maskSwapError := by
  intro field group adversary parameter scalar _
  exact @advantage_real_swapped_le field group (Fintype.ofFinite FixedIndex)
    (Fintype.ofFinite EncPRF.PermutationIndex) (Fintype.ofFinite Coins) adversary parameter scalar

end

end Kriterion.ArgoMAC.Security.Phase3
