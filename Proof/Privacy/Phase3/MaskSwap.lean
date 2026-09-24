/-
**Phase 3, P1, theorem 1 — the `G0 → G0U` swap of every garbler scale mask.**

`B-output-aware-simulator.md` §1.5 and `B-review.md` (3): before anything else, the
proof replaces **every** garbler `scale-hot` mask — all four lanes, all `127` chunks, all
`2 ^ b_c = 4` switches, all element slots of the lane — by an independent uniform `F_p` element.
The swap is **non-adaptive**: it is a statement about the whole tape, made before stage 1, and it
never mentions the adversary's input or which masks it will later be unable to compute.

### The tape, and the two laws

The fixed-key oracle is split into the family the garbler reads at the `scale` sites
(`SitePerms MaskSite`: one permutation per (mask site, limb)) and everything else (`OtherIndex`).
The garbler queries every scale site at exactly one point, the one-hot label of its switch, and
that point is a function of the *rest* of the tape only (`garblerPoint_oracleOf`: the one-hot
labels read the `hot` permutations, never a `scale` one).

* `realTape coinsLaw` — the coins, independent of a uniform fixed-key oracle. This is the eager
  tape of the real game.
* `swappedTape coinsLaw point` — the same, except that at every scale site the permutation family
  is drawn by `swapKernel`: first the `N` masks, iid uniform on `F_p`; then the whole family
  uniformly among those that produce these masks at the given points.

### The theorem

`maskSwap_etvDist_le`: for **every** coin law, **every** point function and **every**
observation of the tape (the garbled output together with the entire oracle, or the whole real
game run on it),

```
d( realTape.map observe , swappedTape.map observe )  ≤  N · δ₃ ,   N = 418,592
```

with `δ₃ = (2 ^ 384 mod p) / 2 ^ 384` the bias of one three-block Rule S draw
(`Basic.sampleFp_etvDist_le`) and `N = #MaskSite` (`card_maskSite`), which evaluates to
`824 · 508 = 418,592` from `Params` (`card_maskSite_eq_design`) and `N · δ₃ ≤ 2 ^ -111`
(`maskCount_mul_delta3_le`).

**The proof is data processing over the whole tape.** For a fixed point set the uniform
permutation family disintegrates as "masks from their (biased) pushforward, then the family
uniformly on the fibre" (`uniform_eq_bind_fibreLaw`), and `swapKernel` is the same fibre kernel
behind the uniform mask law. The kernel given the masks is literally the same function in both
laws, so the distance is at most the distance of the two mask laws
(`PMF.etvDist_bind_right_le`), which is `N · δ₃` (`masksOf_etvDist_le`). The points then enter only
through a shared first draw (`etvDist_bind_left_le_const`). No mask is ever singled out.

`swappedTape_garblerMasks`: under the swapped tape the construction's own masks —
`PlanB.switchMask` at the garbler's one-hot label, for every lane, chunk, switch and element — are
iid uniform on `F_p` and independent of the coins and of every non-scale permutation. This is the
exact sense in which "every garbler scale mask is replaced by an independent uniform element".
-/

import Proof.Privacy.Phase3.Basic
import Construction.ArgoMAC.Pipeline

set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 400

namespace Kriterion.ArgoMAC.Security.Phase3

open BN254 Cryptography Kriterion.ArgoMAC.PlanB
open Kriterion.ArgoMAC.Security.PGS (uniformOfFintype_map_equiv div_mul_self_cancel)
open scoped ENNReal

noncomputable section

/-! ## Part 1 — one permutation per site, queried at one point -/

section Generic

variable {M : Type} [Fintype M] [DecidableEq M]

/-- One permutation per (mask site, limb). -/
abbrev SitePerms (M : Type) := M × Fin 3 → Equiv.Perm Block

/-- The permutation family, evaluated at one point per site. -/
def evalAt (point : M × Fin 3 → Block) (perms : SitePerms M) : M × Fin 3 → Block :=
  fun site => perms site (point site)

/-- The Davies–Meyer value at every site. -/
def dmValues (point : M × Fin 3 → Block) (perms : SitePerms M) : M × Fin 3 → Block :=
  fun site => daviesMeyer (perms site) (point site)

/-- Rule S at every mask: three Davies–Meyer limbs, reduced. -/
def masksOf (values : M × Fin 3 → Block) : M → BaseField :=
  fun mask => sampleFp (values (mask, 0)) (values (mask, 1)) (values (mask, 2))

/-- The masks a permutation family produces at the given points. -/
def maskMap (point : M × Fin 3 → Block) (perms : SitePerms M) : M → BaseField :=
  masksOf (dmValues point perms)

/-- Moving one fibre of `evalAt` onto another: post-compose each permutation with the swap of the
two target values. -/
def evalFibreShift (point first second : M × Fin 3 → Block) :
    {perms : SitePerms M // evalAt point perms = first}
      ≃ {perms : SitePerms M // evalAt point perms = second} where
  toFun perms := ⟨fun site => (perms.1 site).trans (Equiv.swap (first site) (second site)),
    funext fun site => by
      show Equiv.swap (first site) (second site) (perms.1 site (point site)) = second site
      rw [show perms.1 site (point site) = first site from congrFun perms.2 site,
        Equiv.swap_apply_left]⟩
  invFun perms := ⟨fun site => (perms.1 site).trans (Equiv.swap (second site) (first site)),
    funext fun site => by
      show Equiv.swap (second site) (first site) (perms.1 site (point site)) = first site
      rw [show perms.1 site (point site) = second site from congrFun perms.2 site,
        Equiv.swap_apply_left]⟩
  left_inv perms := by
    apply Subtype.ext
    funext site
    apply Equiv.ext
    intro value
    show Equiv.swap (second site) (first site)
      (Equiv.swap (first site) (second site) (perms.1 site value)) = perms.1 site value
    rw [Equiv.swap_comm (second site) (first site), Equiv.swap_apply_self]
  right_inv perms := by
    apply Subtype.ext
    funext site
    apply Equiv.ext
    intro value
    show Equiv.swap (first site) (second site)
      (Equiv.swap (second site) (first site) (perms.1 site value)) = perms.1 site value
    rw [Equiv.swap_comm (first site) (second site), Equiv.swap_apply_self]

/-- **A uniform permutation family, evaluated at one point per site, is a uniform block family.**
Every fibre of `evalAt` is moved onto every other by `evalFibreShift`. -/
theorem evalAt_uniform (point : M × Fin 3 → Block) :
    (PMF.uniformOfFintype (SitePerms M)).map (evalAt point)
      = PMF.uniformOfFintype (M × Fin 3 → Block) :=
  uniform_map_of_fibre_equiv (evalAt point) (evalFibreShift point)

/-- XOR by the points, as a bijection of block families. -/
def xorPoints (point : M × Fin 3 → Block) : (M × Fin 3 → Block) ≃ (M × Fin 3 → Block) where
  toFun values site := values site ^^^ point site
  invFun values site := values site ^^^ point site
  left_inv values := funext fun site => by simp [BitVec.xor_assoc]
  right_inv values := funext fun site => by simp [BitVec.xor_assoc]

/-- **Davies–Meyer at one fresh point per site is exactly uniform**, jointly over all sites. -/
theorem dmValues_uniform (point : M × Fin 3 → Block) :
    (PMF.uniformOfFintype (SitePerms M)).map (dmValues point)
      = PMF.uniformOfFintype (M × Fin 3 → Block) := by
  have factor : dmValues point = xorPoints point ∘ evalAt point := rfl
  rw [factor, ← PMF.map_comp, evalAt_uniform, uniformOfFintype_map_equiv]

/-- `Fin 3 → A` as a triple, which is how Rule S's three limbs are indexed. -/
def tripleEquiv (A : Type) : (Fin 3 → A) ≃ (A × A × A) where
  toFun family := (family 0, family 1, family 2)
  invFun triple := ![triple.1, triple.2.1, triple.2.2]
  left_inv family := by
    funext index
    fin_cases index <;> rfl
  right_inv triple := rfl

/-- Regroup a site-indexed block family into one triple per mask. -/
def regroup : (M × Fin 3 → Block) ≃ (M → Block × Block × Block) :=
  (Equiv.curry M (Fin 3) Block).trans (Equiv.piCongrRight fun _ => tripleEquiv Block)

/-- **Rule S, `#M` times.** The masks of a uniform block family are within `#M · δ₃` of a
uniform mask family. -/
theorem masksOf_etvDist_le :
    ((PMF.uniformOfFintype (M × Fin 3 → Block)).map masksOf).etvDist
        (PMF.uniformOfFintype (M → BaseField))
      ≤ (Fintype.card M : ℝ≥0∞) * delta3 := by
  have factor : (masksOf : (M × Fin 3 → Block) → M → BaseField)
      = (fun family mask => sampleFp (family mask).1 (family mask).2.1 (family mask).2.2)
        ∘ regroup := rfl
  rw [factor, ← PMF.map_comp, uniformOfFintype_map_equiv regroup]
  exact etvDist_pi_map_uniform_le (A := Block × Block × Block) (B := BaseField)
    (fun triple => sampleFp triple.1 triple.2.1 triple.2.2) delta3 sampleFp_etvDist_le

/-- The permutation family that makes one prescribed block triple per mask. -/
def realise (point : M × Fin 3 → Block) (values : M × Fin 3 → Block) : SitePerms M :=
  fun site => Equiv.swap (point site) (values site ^^^ point site)

theorem dmValues_realise (point values : M × Fin 3 → Block) :
    dmValues point (realise point values) = values := by
  funext site
  show (Equiv.swap (point site) (values site ^^^ point site)) (point site) ^^^ point site
    = values site
  rw [Equiv.swap_apply_left, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Every mask family is produced by some permutation family, at any points. -/
theorem maskMap_surjective (point : M × Fin 3 → Block) : Function.Surjective (maskMap point) := by
  intro masks
  have each : ∀ mask, ∃ triple : Block × Block × Block,
      sampleFp triple.1 triple.2.1 triple.2.2 = masks mask :=
    fun mask => sampleFp_surjective (masks mask)
  choose triple hTriple using each
  refine ⟨realise point (regroup.symm triple), ?_⟩
  funext mask
  show masksOf (dmValues point (realise point (regroup.symm triple))) mask = masks mask
  rw [dmValues_realise]
  exact hTriple mask

/-- **The swap kernel at a point set.** The `#M` masks are drawn iid uniform on `F_p`; then the
whole permutation family is drawn uniformly among those that produce them. -/
def swapKernel (point : M × Fin 3 → Block) : PMF (SitePerms M) :=
  (PMF.uniformOfFintype (M → BaseField)).bind (fibreLaw (maskMap point) (maskMap_surjective point))

/-- The real mask law at a point set: Rule S of uniform blocks, whatever the points. -/
theorem maskMap_law (point : M × Fin 3 → Block) :
    (PMF.uniformOfFintype (SitePerms M)).map (maskMap point)
      = (PMF.uniformOfFintype (M × Fin 3 → Block)).map masksOf := by
  have factor : maskMap point = masksOf ∘ dmValues point := rfl
  rw [factor, ← PMF.map_comp, dmValues_uniform]

/-- **The per-point-set swap.** The uniform family and the swap kernel share the fibre kernel given
the masks; only the mask law differs. -/
theorem swapKernel_etvDist_le (point : M × Fin 3 → Block) :
    (PMF.uniformOfFintype (SitePerms M)).etvDist (swapKernel point)
      ≤ (Fintype.card M : ℝ≥0∞) * delta3 := by
  rw [uniform_eq_bind_fibreLaw (maskMap point) (maskMap_surjective point), swapKernel,
    ← uniform_eq_bind_fibreLaw (maskMap point) (maskMap_surjective point)]
  conv_lhs => rw [uniform_eq_bind_fibreLaw (maskMap point) (maskMap_surjective point)]
  refine le_trans (PMF.etvDist_bind_right_le _ _ _) ?_
  rw [maskMap_law]
  exact masksOf_etvDist_le

/-- Under the swap kernel the masks are exactly iid uniform. -/
theorem swapKernel_masks (point : M × Fin 3 → Block) :
    (swapKernel point).map (maskMap point) = PMF.uniformOfFintype (M → BaseField) := by
  rw [swapKernel, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (PMF.uniformOfFintype (M → BaseField))]
  exact congrArg _ (funext fun masks => fibreLaw_map (maskMap point) (maskMap_surjective point) masks)

/-! ### The whole tape -/

variable {Rest : Type}

/-- **`G0`.** The rest of the tape under any law; the site permutations uniform and independent. -/
def realLaw (restLaw : PMF Rest) : PMF (Rest × SitePerms M) :=
  restLaw.bind fun rest => (PMF.uniformOfFintype (SitePerms M)).map (Prod.mk rest)

/-- **`G0U`.** The same rest; the site permutations from the swap kernel at the points the rest
determines. -/
def swapLaw (restLaw : PMF Rest) (point : Rest → M × Fin 3 → Block) : PMF (Rest × SitePerms M) :=
  restLaw.bind fun rest => (swapKernel (point rest)).map (Prod.mk rest)

/-- **The swap over the whole tape.** For every law of the rest, every point function and every
observation, the two tapes are `#M · δ₃`-close. -/
theorem swap_etvDist_le {X : Type} (restLaw : PMF Rest) (point : Rest → M × Fin 3 → Block)
    (observe : Rest × SitePerms M → X) :
    ((realLaw restLaw).map observe).etvDist ((swapLaw restLaw point).map observe)
      ≤ (Fintype.card M : ℝ≥0∞) * delta3 := by
  rw [realLaw, swapLaw, PMF.map_bind, PMF.map_bind]
  refine etvDist_bind_left_le_const restLaw _ _ _ fun rest => ?_
  rw [PMF.map_comp, PMF.map_comp]
  exact le_trans (etvDist_map_le' _ _ _) (swapKernel_etvDist_le (point rest))

/-- **Under `G0U` the masks are iid uniform and independent of the rest.** -/
theorem swapLaw_masks (restLaw : PMF Rest) (point : Rest → M × Fin 3 → Block) :
    (swapLaw restLaw point).map (fun tape => (tape.1, maskMap (point tape.1) tape.2))
      = productPMF restLaw (PMF.uniformOfFintype (M → BaseField)) := by
  rw [swapLaw, PMF.map_bind, productPMF]
  refine congrArg _ (funext fun rest => ?_)
  rw [PMF.map_comp]
  have factor : ((fun tape : Rest × SitePerms M => (tape.1, maskMap (point tape.1) tape.2))
      ∘ Prod.mk rest) = Prod.mk rest ∘ maskMap (point rest) := rfl
  rw [factor, ← PMF.map_comp, swapKernel_masks]

end Generic

/-! ## Part 2 — the Plan B scale sites -/

/-- The number of element slots each lane's switch system delivers. -/
def laneCount : Lane → Nat
  | .curveX => curveElementCountX
  | .curveY => curveElementCountY
  | .pointX => pointElementCountX
  | .pointY => pointElementCountY

theorem laneCount_le (lane : Lane) : laneCount lane ≤ elementCountX := by
  cases lane <;> simp only [laneCount, curveElementCountX, curveElementCountY,
    pointElementCountX, pointElementCountY, elementCountX] <;> omega

/-- The four lanes together deliver all `824` elements. -/
theorem sum_laneCount : ∑ lane : Lane, laneCount lane = elementCount := by
  decide

/-- **A garbler scale mask**: (lane, chunk, switch of that chunk, element slot of that lane). One
`F_p` element `Y_{ℓ,c,j}[e]` per site; `PlanB.switchMask` computes it from three limbs. -/
abbrev MaskSite :=
  Σ lane : Lane, Σ chunk : Fin chunkCount, Fin (2 ^ chunkWidth chunk) × Fin (laneCount lane)

/-- The mask count, in the design's terms: `S · Σ_c 2 ^ b_c`. -/
theorem card_maskSite_eq_design :
    Fintype.card MaskSite = elementCount * ∑ chunk : Fin chunkCount, 2 ^ chunkWidth chunk := by
  simp only [MaskSite, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← sum_laneCount, Finset.sum_mul]
  refine Finset.sum_congr rfl fun lane _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun chunk _ => Nat.mul_comm _ _

/-- `Σ_c 2 ^ b_c = 126 · 4 + 4 = 508` at the `b = 2` profile, from the generic chunk sum. -/
theorem sum_twoPow_chunkWidth : ∑ chunk : Fin chunkCount, 2 ^ chunkWidth chunk = 508 := by
  rw [sum_chunkWidth (fun width => 2 ^ width)]
  rfl

/-- **`N = 418,592`**: every garbler scale mask of every lane. -/
theorem card_maskSite : Fintype.card MaskSite = 418592 := by
  rw [card_maskSite_eq_design, sum_twoPow_chunkWidth]
  rfl

/-- **`N · δ₃ ≤ 2 ^ -111`** (the value is `2 ^ -111.86`). -/
theorem maskCount_mul_delta3_le :
    (Fintype.card MaskSite : ℝ≥0∞) * delta3 ≤ (2 ^ 111 : ℝ≥0∞)⁻¹ := by
  have numerals : Fintype.card MaskSite * reductionResidue ≤ 2 ^ 273 := by
    rw [card_maskSite, reductionResidue_eq]
    norm_num
  calc (Fintype.card MaskSite : ℝ≥0∞) * delta3
      = ((Fintype.card MaskSite * reductionResidue : Nat) : ℝ≥0∞) / 2 ^ 384 := by
        rw [delta3, Nat.cast_mul, mul_div_assoc]
    _ ≤ ((2 ^ 273 : Nat) : ℝ≥0∞) / 2 ^ 384 :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr numerals) _
    _ = (2 ^ 111 : ℝ≥0∞)⁻¹ := by
        rw [Nat.cast_pow, Nat.cast_ofNat,
          show (2 : ℝ≥0∞) ^ 384 = 2 ^ 111 * 2 ^ 273 by rw [← pow_add]]
        exact div_mul_self_cancel (by positivity) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

/-- The fixed-key index of a scale site: `PlanB.scaleIndexOf`, exactly as `switchMask` names it. -/
def siteIndex (site : MaskSite × Fin 3) : FixedIndex :=
  scaleIndexOf site.1.1 site.1.2.1 site.1.2.2.1.val site.1.2.2.2 site.2

/-- **One index per site**: the `N · 3` site indices are pairwise distinct. -/
theorem siteIndex_injective : Function.Injective siteIndex := by
  rintro ⟨⟨lane, chunk, switch, element⟩, block⟩ ⟨⟨lane', chunk', switch', element'⟩, block'⟩ same
  have laneEq : lane = lane' :=
    Pipeline.scaleIndexOf_lane lane lane' chunk chunk' switch.val switch'.val element element'
      block block' (laneCount_le lane) (laneCount_le lane')
      (Pipeline.switch_lt_twoPowChunkBits chunk switch)
      (Pipeline.switch_lt_twoPowChunkBits chunk' switch') same
  subst laneEq
  obtain ⟨chunkEq, switchEq, elementEq, blockEq⟩ :=
    Pipeline.scaleIndexOf_injective lane chunk chunk' switch.val switch'.val element element'
      block block' (laneCount_le lane) (Pipeline.switch_lt_twoPowChunkBits chunk switch)
      (Pipeline.switch_lt_twoPowChunkBits chunk' switch') same
  subst chunkEq
  subst elementEq
  subst blockEq
  have : switch = switch' := Fin.ext switchEq
  subst this
  rfl

/-- The indices no garbler scale mask reads: the `hot` and `gadget` families and the unused
element slots of the `scale` family. -/
abbrev OtherIndex := {index : FixedIndex // index ∉ Set.range siteIndex}

/-- Reassemble the oracle from its scale-site part and the rest. The membership test is decided
classically (`Classical.propDecidable`) so that no definitional unfolding can ever enumerate the
`1,255,776` sites; the definition is sealed after its two characterising lemmas. -/
def oracleOf (other : OtherIndex → Equiv.Perm Block) (scale : SitePerms MaskSite) :
    PermutationOracle FixedIndex Block :=
  ⟨fun index => @dite _ (index ∈ Set.range siteIndex) (Classical.propDecidable _)
    (fun hit => scale (Classical.choose hit)) (fun hit => other ⟨index, hit⟩)⟩

theorem oracleOf_site (other : OtherIndex → Equiv.Perm Block) (scale : SitePerms MaskSite)
    (site : MaskSite × Fin 3) : (oracleOf other scale).permutation (siteIndex site) = scale site := by
  have hit : siteIndex site ∈ Set.range siteIndex := ⟨site, rfl⟩
  simp only [oracleOf, dif_pos hit]
  exact congrArg scale (siteIndex_injective (Classical.choose_spec hit))

theorem oracleOf_other (other : OtherIndex → Equiv.Perm Block) (scale : SitePerms MaskSite)
    (index : OtherIndex) : (oracleOf other scale).permutation index.1 = other index := by
  simp only [oracleOf, dif_neg index.2]

attribute [irreducible] oracleOf

/-- The two parts of an oracle. -/
def splitParts (oracle : PermutationOracle FixedIndex Block) :
    (OtherIndex → Equiv.Perm Block) × SitePerms MaskSite :=
  (fun index => oracle.permutation index.1, fun site => oracle.permutation (siteIndex site))

theorem oracle_ext {first second : PermutationOracle FixedIndex Block}
    (same : ∀ index, first.permutation index = second.permutation index) : first = second := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  have : first = second := funext same
  rw [this]

theorem oracleOf_splitParts (oracle : PermutationOracle FixedIndex Block) :
    oracleOf (splitParts oracle).1 (splitParts oracle).2 = oracle := by
  refine oracle_ext fun index => ?_
  by_cases hit : index ∈ Set.range siteIndex
  · obtain ⟨site, rfl⟩ := hit
    exact oracleOf_site _ _ site
  · exact oracleOf_other _ _ ⟨index, hit⟩

theorem splitParts_oracleOf (parts : (OtherIndex → Equiv.Perm Block) × SitePerms MaskSite) :
    splitParts (oracleOf parts.1 parts.2) = parts := by
  obtain ⟨other, scale⟩ := parts
  have first : (splitParts (oracleOf other scale)).1 = other :=
    funext fun index => oracleOf_other other scale index
  have second : (splitParts (oracleOf other scale)).2 = scale :=
    funext fun site => oracleOf_site other scale site
  exact Prod.ext first second

/-- The oracle, split into its non-site and site parts. -/
def oracleSplit :
    PermutationOracle FixedIndex Block ≃ (OtherIndex → Equiv.Perm Block) × SitePerms MaskSite where
  toFun := splitParts
  invFun parts := oracleOf parts.1 parts.2
  left_inv := oracleOf_splitParts
  right_inv := splitParts_oracleOf

/-- A uniform oracle is a uniform non-site part and an independent uniform site family. -/
theorem uniform_oracle_eq :
    PMF.uniformOfFintype (PermutationOracle FixedIndex Block)
      = (productPMF (PMF.uniformOfFintype (OtherIndex → Equiv.Perm Block))
          (PMF.uniformOfFintype (SitePerms MaskSite))).map
        (fun parts => oracleOf parts.1 parts.2) := by
  rw [← uniformOfFintype_productPMF]
  exact (uniformOfFintype_map_equiv oracleSplit.symm).symm

/-! ### The real tape and the swapped tape -/

section Tape

variable {Coins : Type}

/-- The non-site part of the tape: the coins and every permutation no scale mask reads. -/
abbrev RestTape (Coins : Type) := Coins × (OtherIndex → Equiv.Perm Block)

/-- The site permutations and the rest, put back together. -/
def assemble (tape : RestTape Coins × SitePerms MaskSite) : Coins × PermutationOracle FixedIndex Block :=
  (tape.1.1, oracleOf tape.1.2 tape.2)

/-- The law of the rest when the oracle is uniform and independent of the coins. -/
def restLaw (coinsLaw : PMF Coins) : PMF (RestTape Coins) :=
  productPMF coinsLaw (PMF.uniformOfFintype (OtherIndex → Equiv.Perm Block))

/-- **The real (eager) tape**: the coins, independent of a uniform fixed-key oracle. -/
def realTape (coinsLaw : PMF Coins) : PMF (Coins × PermutationOracle FixedIndex Block) :=
  productPMF coinsLaw (PMF.uniformOfFintype (PermutationOracle FixedIndex Block))

/-- **The swapped tape (`G0U`)**: every scale site drawn by the swap kernel at the points the rest
of the tape determines. -/
def swappedTape (coinsLaw : PMF Coins) (point : RestTape Coins → MaskSite × Fin 3 → Block) :
    PMF (Coins × PermutationOracle FixedIndex Block) :=
  (swapLaw (restLaw coinsLaw) point).map assemble

/-- The real tape is `G0` on the split oracle. -/
theorem realTape_eq (coinsLaw : PMF Coins) :
    realTape coinsLaw = (realLaw (restLaw coinsLaw)).map assemble := by
  have left : realTape coinsLaw = coinsLaw.bind fun coins =>
      (PMF.uniformOfFintype (OtherIndex → Equiv.Perm Block)).bind fun other =>
        (PMF.uniformOfFintype (SitePerms MaskSite)).map fun scale => (coins, oracleOf other scale) := by
    rw [realTape, uniform_oracle_eq, productPMF, productPMF]
    refine congrArg _ (funext fun coins => ?_)
    rw [PMF.map_comp, PMF.map_bind]
    refine congrArg _ (funext fun other => ?_)
    rw [PMF.map_comp]
    rfl
  have right : (realLaw (restLaw coinsLaw)).map assemble = coinsLaw.bind fun coins =>
      (PMF.uniformOfFintype (OtherIndex → Equiv.Perm Block)).bind fun other =>
        (PMF.uniformOfFintype (SitePerms MaskSite)).map fun scale => (coins, oracleOf other scale) := by
    rw [realLaw, restLaw, productPMF, PMF.bind_bind, PMF.map_bind]
    refine congrArg _ (funext fun coins => ?_)
    rw [PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun other => ?_)
    rw [Function.comp_apply, PMF.map_comp]
    rfl
  rw [left, right]

/-- **Theorem 1 (`G0 → G0U`), for every observation of the tape.** -/
theorem maskSwap_etvDist_le {X : Type} (coinsLaw : PMF Coins)
    (point : RestTape Coins → MaskSite × Fin 3 → Block)
    (observe : Coins × PermutationOracle FixedIndex Block → X) :
    ((realTape coinsLaw).map observe).etvDist ((swappedTape coinsLaw point).map observe)
      ≤ (Fintype.card MaskSite : ℝ≥0∞) * delta3 := by
  rw [realTape_eq, swappedTape, PMF.map_comp, PMF.map_comp]
  exact swap_etvDist_le (restLaw coinsLaw) point (observe ∘ assemble)

/-- **Theorem 1, as a game hop.** Any randomized continuation run on the tape — the garbler, the
adversary's two stages against the same oracle, the final bit — gains at most `N · δ₃`. -/
theorem maskSwap_bind_etvDist_le {X : Type} (coinsLaw : PMF Coins)
    (point : RestTape Coins → MaskSite × Fin 3 → Block)
    (game : Coins × PermutationOracle FixedIndex Block → PMF X) :
    ((realTape coinsLaw).bind game).etvDist ((swappedTape coinsLaw point).bind game)
      ≤ (Fintype.card MaskSite : ℝ≥0∞) * delta3 := by
  refine le_trans (PMF.etvDist_bind_right_le game _ _) ?_
  have identity := maskSwap_etvDist_le coinsLaw point id
  rwa [PMF.map_id, PMF.map_id] at identity

/-- **Theorem 1 with the numbers in**: `≤ 418,592 · δ₃ ≤ 2 ^ -111`. -/
theorem maskSwap_etvDist_le_numeral {X : Type} (coinsLaw : PMF Coins)
    (point : RestTape Coins → MaskSite × Fin 3 → Block)
    (observe : Coins × PermutationOracle FixedIndex Block → X) :
    ((realTape coinsLaw).map observe).etvDist ((swappedTape coinsLaw point).map observe)
      ≤ (418592 : ℝ≥0∞) * delta3 ∧
    ((realTape coinsLaw).map observe).etvDist ((swappedTape coinsLaw point).map observe)
      ≤ (2 ^ 111 : ℝ≥0∞)⁻¹ := by
  have bound := maskSwap_etvDist_le coinsLaw point observe
  refine ⟨?_, le_trans bound maskCount_mul_delta3_le⟩
  rwa [card_maskSite, Nat.cast_ofNat] at bound

end Tape

/-! ### The garbler's points, and the garbler's masks -/

/-- Two oracles that agree on every `hot` permutation run the same `bin-to-hot` fold. -/
theorem garbleFold_congr {first second : PermutationOracle FixedIndex Block}
    (agree : ∀ lane chunk fold entry half,
      first.permutation (.hot lane chunk fold entry half)
        = second.permutation (.hot lane chunk fold entry half))
    (lane : Lane) (chunk : Fin chunkCount) (delta : Block) (zeroLabel : Nat → Block) :
    ∀ steps, garbleFold first lane chunk delta zeroLabel steps
      = garbleFold second lane chunk delta zeroLabel steps
  | 0 => rfl
  | steps + 1 => by
      have previous := garbleFold_congr agree lane chunk delta zeroLabel steps
      have step : garbleStep first lane chunk steps (zeroLabel steps)
            (garbleFold first lane chunk delta zeroLabel steps).1
          = garbleStep second lane chunk steps (zeroLabel steps)
            (garbleFold second lane chunk delta zeroLabel steps).1 := by
        rw [previous]
        funext entry
        simp only [garbleStep, foldMask, PlanB.hash, hotIndexNat, agree]
      simp only [garbleFold]
      rw [step, previous]

theorem garbleChunk_congr {first second : PermutationOracle FixedIndex Block}
    (agree : ∀ lane chunk fold entry half,
      first.permutation (.hot lane chunk fold entry half)
        = second.permutation (.hot lane chunk fold entry half))
    (lane : Lane) (delta : Block) (bitKey : Fin PlanB.coordinateBits → Block × Block)
    (chunk : Fin chunkCount) :
    garbleChunk first lane delta bitKey chunk = garbleChunk second lane delta bitKey chunk := by
  simp only [garbleChunk, garbleHot, garbleFold_congr agree]

/-- The `hot` indices are never scale sites. -/
theorem hot_not_site (lane : Lane) (chunk : Fin chunkCount) (fold : Fin chunkBits)
    (entry : Fin (2 ^ chunkBits)) (half : Bool) :
    FixedIndex.hot lane chunk fold entry half ∉ Set.range siteIndex := by
  rintro ⟨site, same⟩
  simp only [siteIndex, scaleIndexOf, scaleIndexNat] at same
  cases same

/-- **The garbler's query point at a scale site**: the one-hot label of its switch, from the lane's
`bin-to-hot` fold on the lane's bit keys. -/
def garblerPoint (oracle : PermutationOracle FixedIndex Block) (delta : Lane → Block)
    (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) (site : MaskSite × Fin 3) : Block :=
  (garbleChunk oracle site.1.1 (delta site.1.1) (bitKey site.1.1) site.1.2.1).1 site.1.2.2.1

/-- **The garbler's points do not read the scale family.** -/
theorem garblerPoint_oracleOf (other : OtherIndex → Equiv.Perm Block)
    (scale scale' : SitePerms MaskSite) (delta : Lane → Block)
    (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) :
    garblerPoint (oracleOf other scale) delta bitKey
      = garblerPoint (oracleOf other scale') delta bitKey := by
  funext site
  simp only [garblerPoint]
  rw [garbleChunk_congr (first := oracleOf other scale) (second := oracleOf other scale')
    (fun lane chunk fold entry half => by
      rw [oracleOf_other other scale ⟨_, hot_not_site lane chunk fold entry half⟩,
        oracleOf_other other scale' ⟨_, hot_not_site lane chunk fold entry half⟩])]

/-- The Plan B point function: the garbler's one-hot labels, computed from the rest of the tape.
`keys` reads each lane's global offset and bit keys off the coins (the raw Lamport keys for system
A, the EncPRF-whitened keys for system B). -/
def planBPoint {Coins : Type} (keys : Coins → (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block))
    (rest : RestTape Coins) : MaskSite × Fin 3 → Block :=
  garblerPoint (oracleOf rest.2 fun _ => Equiv.refl Block) (keys rest.1).1 (keys rest.1).2

/-- **The construction's garbler mask at a site** — `PlanB.switchMask` at the garbler's own one-hot
label, exactly as `PlanB.garbleScale` and `PlanB.outputMask` read it. -/
def garblerMask (oracle : PermutationOracle FixedIndex Block) (delta : Lane → Block)
    (bitKey : Lane → Fin PlanB.coordinateBits → Block × Block) (mask : MaskSite) : BaseField :=
  switchMask (count := laneCount mask.1) oracle mask.1 mask.2.1 mask.2.2.1.val
    ((garbleChunk oracle mask.1 (delta mask.1) (bitKey mask.1) mask.2.1).1 mask.2.2.1) mask.2.2.2

/-- The construction's masks are `maskMap` of the site family at the garbler's points. -/
theorem garblerMask_oracleOf {Coins : Type}
    (keys : Coins → (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block))
    (rest : RestTape Coins) (scale : SitePerms MaskSite) :
    garblerMask (oracleOf rest.2 scale) (keys rest.1).1 (keys rest.1).2
      = maskMap (planBPoint keys rest) scale := by
  have points : planBPoint keys rest
      = garblerPoint (oracleOf rest.2 scale) (keys rest.1).1 (keys rest.1).2 :=
    garblerPoint_oracleOf rest.2 (fun _ => Equiv.refl Block) scale _ _
  rw [points]
  funext mask
  have limb : ∀ block : Fin 3, (oracleOf rest.2 scale).permutation
      (scaleIndexOf mask.1 mask.2.1 mask.2.2.1.val mask.2.2.2 block) = scale (mask, block) :=
    fun block => oracleOf_site rest.2 scale (mask, block)
  simp only [garblerMask, switchMask, sampleVector, PlanB.hash, maskMap, masksOf, dmValues,
    garblerPoint, limb]

/-- **Every garbler scale mask, swapped.** Under `G0U` with the garbler's own points, the
construction's `N = 418,592` masks — every lane, chunk, switch and element — are iid uniform on
`F_p` and independent of the coins and of every non-scale permutation. -/
theorem swappedTape_garblerMasks {Coins : Type} (coinsLaw : PMF Coins)
    (keys : Coins → (Lane → Block) × (Lane → Fin PlanB.coordinateBits → Block × Block)) :
    (swappedTape coinsLaw (planBPoint keys)).map
        (fun tape => ((tape.1, fun index : OtherIndex => tape.2.permutation index.1),
          garblerMask tape.2 (keys tape.1).1 (keys tape.1).2))
      = productPMF (restLaw coinsLaw) (PMF.uniformOfFintype (MaskSite → BaseField)) := by
  rw [swappedTape, PMF.map_comp, ← swapLaw_masks (restLaw coinsLaw) (planBPoint keys)]
  refine congrArg (fun observe => PMF.map observe (swapLaw (restLaw coinsLaw) (planBPoint keys)))
    (funext fun tape => ?_)
  obtain ⟨⟨coins, other⟩, scale⟩ := tape
  have others : (fun index : OtherIndex => (oracleOf other scale).permutation index.1) = other :=
    funext fun index => oracleOf_other other scale index
  show (((coins, fun index : OtherIndex => (oracleOf other scale).permutation index.1),
      garblerMask (oracleOf other scale) (keys coins).1 (keys coins).2))
    = ((coins, other), maskMap (planBPoint keys (coins, other)) scale)
  rw [others, garblerMask_oracleOf keys (coins, other) scale]

end

end Kriterion.ArgoMAC.Security.Phase3
