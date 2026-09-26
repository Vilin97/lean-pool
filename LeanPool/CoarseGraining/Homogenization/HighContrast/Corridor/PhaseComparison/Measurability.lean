/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.Geometry
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.LawObservable
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity
public import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability

/-!
# Per-phase measurability of the corridor observable

The coarse observable is only
a.e.-measurable under a `RestrictionLawCarrier` (the C3 wrap
`aestronglyMeasurable_coarseBlockQuadratic_cubeSet`), so `comp_measurable`
cannot be applied against `L` directly.  Instead:

1. The corridor modification is packaged as the carrier endomorphism
   `corridorReg ℓ σ : RegCoeffField d → RegCoeffField d` — the corridor
   indicator is a fixed spatial set, so each entry of the modified field is a
   Borel case-split between a constant and the original entry, preserving both
   carrier regularity conjuncts.  The endomorphism is *genuinely* `Measurable`
   at the join (`measurable_corridorReg`): the pointwise lane is a case-split
   between a constant and an evaluation, and the entry-test lane is **affine**
   in the generators — `entryTestR i j φ (corridorReg ℓ σ a)` is a constant
   plus the entry test of `a` against the complementary-masked probe
   `Set.indicator (corridorSet ℓ σ)ᶜ φ` (the spatial case-split is
   `a`-independent, unlike the elliptic truncation, so both lanes are honest).
2. The pushforward `L.map (corridorReg ℓ σ)` is again a `RestrictionLawCarrier`
   (`lawCarrier_map_corridorReg`): probability is preserved by measurability,
   and a.e. local uniform ellipticity is preserved by the pointwise corridor
   modification (`aeLocallyUniformlyEllipticField_corridorReg`); the a.e.
   pushforward uses `MeasureTheory.ae_map_iff`, whose measurable-set side
   condition is `measurableSet_aeLocallyUniformlyEllipticField` (the countable
   `⋂_Q ⋃_k` of the AEE quantitative-slice sets, each genuinely
   `LocalSigmaR`-measurable on the carrier).
3. The C3 wrap on the pushforward pulls back along the measurable corridor
   endomorphism via `AEStronglyMeasurable.comp_measurable`
   (`aestronglyMeasurable_phaseObservable`).
-/

@[expose] public section

open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier AELocallyUniformlyEllipticField
  AELocallyUniformlyEllipticLaw lawCarrier_of_aeLocallyUniformlyElliptic)
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The corridor set is open, hence measurable -/

/-- The corridor set is open: it is a countable union over `(i, n)` of the open
slabs `{x | |x i − σ i − n·ℓ| < 1}`. -/
theorem isOpen_corridorSet (ℓ : ℝ) (σ : Vec d) : IsOpen (corridorSet ℓ σ) := by
  have hset : corridorSet ℓ σ
      = ⋃ i : Fin d, ⋃ n : ℤ, {x : Vec d | |x i - σ i - n * ℓ| < 1} := by
    ext x
    simp only [mem_corridorSet, Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [hset]
  refine isOpen_iUnion fun i => isOpen_iUnion fun n => ?_
  have hcont : Continuous (fun x : Vec d => |x i - σ i - n * ℓ|) :=
    (((continuous_apply i).sub continuous_const).sub continuous_const).abs
  exact isOpen_lt hcont continuous_const

/-- The corridor set is measurable. -/
theorem measurableSet_corridorSet (ℓ : ℝ) (σ : Vec d) :
    MeasurableSet (corridorSet ℓ σ) :=
  (isOpen_corridorSet ℓ σ).measurableSet

/-! ## M1.1 — the corridor carrier endomorphism and its genuine measurability -/

/-- The corridor modification as a carrier endomorphism (identity matrix on the
corridor set, the original field off it).  Both regularity conjuncts are
preserved: each entry is a Borel case-split between a constant and the original
entry over the measurable corridor set. -/
noncomputable def corridorReg (ℓ : ℝ) (σ : Vec d) (a : RegCoeffField d) :
    RegCoeffField d where
  toFun := corridorField ℓ σ a.toFun
  entry_measurable := fun i j => by
    classical
    have hEq : (fun x => corridorField ℓ σ a.toFun x i j)
        = fun x => if x ∈ corridorSet ℓ σ then (1 : Mat d) i j else a x i j := by
      funext x
      by_cases hx : x ∈ corridorSet ℓ σ
      · rw [corridorField_apply_of_mem hx, if_pos hx]
      · rw [corridorField_apply_of_not_mem hx, if_neg hx]
    rw [hEq]
    exact Measurable.ite (measurableSet_corridorSet ℓ σ) measurable_const
      (a.entry_measurable i j)
  entry_locInt := fun i j => by
    classical
    have hEq : (fun x => corridorField ℓ σ a.toFun x i j)
        = fun x => (corridorSet ℓ σ).indicator (fun _ => (1 : Mat d) i j) x
            + ((corridorSet ℓ σ)ᶜ).indicator (fun x => a x i j) x := by
      funext x
      by_cases hx : x ∈ corridorSet ℓ σ
      · simp [corridorField_apply_of_mem hx, Set.indicator_of_mem hx,
          Set.indicator_of_notMem (by simpa using hx : x ∉ (corridorSet ℓ σ)ᶜ)]
      · simp [corridorField_apply_of_not_mem hx, Set.indicator_of_notMem hx,
          Set.indicator_of_mem (by simpa using hx : x ∈ (corridorSet ℓ σ)ᶜ)]
    rw [hEq]
    refine LocallyIntegrable.add ?_ ?_
    · exact (locallyIntegrable_const ((1 : Mat d) i j)).indicator
        (measurableSet_corridorSet ℓ σ)
    · rw [locallyIntegrable_iff]
      intro K hK
      exact ((a.entry_locInt i j).integrableOn_isCompact hK).indicator
        (measurableSet_corridorSet ℓ σ).compl

@[simp] theorem corridorReg_toFun (ℓ : ℝ) (σ : Vec d) (a : RegCoeffField d) :
    (corridorReg ℓ σ a).toFun = corridorField ℓ σ a.toFun := rfl

@[simp] theorem corridorReg_apply (ℓ : ℝ) (σ : Vec d) (a : RegCoeffField d)
    (x : Vec d) :
    corridorReg ℓ σ a x = corridorField ℓ σ a.toFun x := rfl

/-- Affine generator transport for the corridor endomorphism: the entry test of
the modified field is a constant plus the entry test of the original field
against the complementary-masked probe. -/
theorem entryTestR_corridorReg (i j : Fin d) {φ : Vec d → ℝ} (hφ : IsProbeR φ)
    (ℓ : ℝ) (σ : Vec d) (a : RegCoeffField d) :
    entryTestR i j φ (corridorReg ℓ σ a)
      = (∫ x, (corridorSet ℓ σ).indicator (fun x => (1 : Mat d) i j * φ x) x)
          + entryTestR i j (Set.indicator (corridorSet ℓ σ)ᶜ φ) a := by
  classical
  have hint1 :
      Integrable ((corridorSet ℓ σ).indicator (fun x => (1 : Mat d) i j * φ x)) volume := by
    have h1 : Integrable (fun x => (1 : RegCoeffField d) x i j * φ x) volume :=
      integrable_entry_mul_probe i j hφ (1 : RegCoeffField d)
    exact h1.indicator (measurableSet_corridorSet ℓ σ)
  have hint2 :
      Integrable (fun x => a x i j * Set.indicator (corridorSet ℓ σ)ᶜ φ x) volume :=
    integrable_entry_mul_probe i j (hφ.indicator (measurableSet_corridorSet ℓ σ).compl) a
  have hEq : (fun x => corridorReg ℓ σ a x i j * φ x)
      = fun x => (corridorSet ℓ σ).indicator (fun x => (1 : Mat d) i j * φ x) x
          + a x i j * Set.indicator (corridorSet ℓ σ)ᶜ φ x := by
    funext x
    by_cases hx : x ∈ corridorSet ℓ σ
    · simp [corridorField_apply_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (by simpa using hx : x ∉ (corridorSet ℓ σ)ᶜ)]
    · simp [corridorField_apply_of_not_mem hx, Set.indicator_of_notMem hx,
        Set.indicator_of_mem (by simpa using hx : x ∈ (corridorSet ℓ σ)ᶜ)]
  unfold entryTestR
  rw [hEq, integral_add hint1 hint2]

/-- **The corridor endomorphism is genuinely measurable at the join.**  The
pointwise lane is a case-split between a constant and an evaluation; the
entry-test lane is affine in the carrier generators (the spatial case-split is
independent of the field, unlike the elliptic truncation). -/
theorem measurable_corridorReg (ℓ : ℝ) (σ : Vec d) :
    Measurable (corridorReg (d := d) ℓ σ) := by
  classical
  refine measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    by_cases hy : y ∈ corridorSet ℓ σ
    · have hfun : (fun a : RegCoeffField d => corridorReg ℓ σ a y i j)
          = fun _ => (1 : Mat d) i j := by
        funext a; simp [corridorField_apply_of_mem hy]
      rw [hfun]; exact measurable_const
    · have hfun : (fun a : RegCoeffField d => corridorReg ℓ σ a y i j)
          = fun a => a y i j := by
        funext a; simp [corridorField_apply_of_not_mem hy]
      rw [hfun]; exact measurable_apply_entry y i j
  · intro i j φ hφ
    have hfun : (fun a => entryTestR i j φ (corridorReg ℓ σ a))
        = fun a =>
            (∫ x, (corridorSet ℓ σ).indicator (fun x => (1 : Mat d) i j * φ x) x)
              + entryTestR i j (Set.indicator (corridorSet ℓ σ)ᶜ φ) a := by
      funext a; exact entryTestR_corridorReg i j hφ ℓ σ a
    rw [hfun]
    exact measurable_const.add
      (measurable_entryTestR i j (hφ.indicator (measurableSet_corridorSet ℓ σ).compl))

/-! ## M1.2 — ellipticity transport through the corridor -/

/-- The corridor modification preserves a.e. local uniform ellipticity.  On the
corridor set the field is the identity, elliptic with any constants
`lam'' ≤ 1 ≤ Lam''`; off it the field is unchanged.  On each triadic cube, with
original constants `(lam, Lam)`, the modified field is a.e.
`(min lam 1, max Lam 1)`-elliptic; its spatial a.e.-strong measurability is the
piecewise combination of the original coordinate map and a constant, gated by
the measurable `corridorSet`. -/
theorem aeLocallyUniformlyEllipticField_corridorReg {ℓ : ℝ} {σ : Vec d}
    {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a) :
    AELocallyUniformlyEllipticField (corridorReg ℓ σ a) := by
  classical
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hAOn⟩ := ha Q
  have hAOn' : IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun := hAOn
  set U : Set (Vec d) := openCubeSet Q with hUdef
  refine ⟨min lam 1, max Lam 1, lt_min hlam one_pos, ?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left lam 1) (le_trans hle (le_max_left Lam 1))
  · exact hAOn'.measurableSet
  · -- spatial a.e.-strong measurability (piecewise)
    intro i j
    have hEq :
        (fun x => restrictCoeffField U (corridorField ℓ σ a.toFun) x i j)
          = (corridorSet ℓ σ).piecewise
              (fun x => restrictCoeffField U (fun _ => (1 : Mat d)) x i j)
              (fun x => restrictCoeffField U a.toFun x i j) := by
      funext x
      by_cases hxU : x ∈ U <;> by_cases hxS : x ∈ corridorSet ℓ σ <;>
        simp [Set.piecewise, restrictCoeffField, corridorField, hxU, hxS]
    rw [corridorReg_toFun, hEq]
    refine AEStronglyMeasurable.piecewise (measurableSet_corridorSet ℓ σ) ?_ ?_
    · have hb1 :
          (fun x : Vec d => restrictCoeffField U (fun _ => (1 : Mat d)) x i j)
            = U.indicator (fun _ => (1 : Mat d) i j) := by
        funext x; by_cases hxU : x ∈ U <;> simp [restrictCoeffField, hxU]
      rw [hb1]
      exact (measurable_const.indicator hAOn'.measurableSet).aestronglyMeasurable.restrict
    · exact (hAOn'.aestronglyMeasurable_restrictCoeffField_apply i j).restrict
  · -- pointwise ellipticity a.e.
    have hminpos : (0 : ℝ) < min lam 1 := lt_min hlam one_pos
    filter_upwards [hAOn'.ae_isEllipticMatrix] with x hx
    by_cases hxS : x ∈ corridorSet ℓ σ
    · rw [corridorReg_toFun, corridorField_apply_of_mem hxS]
      exact (isEllipticMatrix_one (le_max_right Lam 1)).mono hminpos
        (min_le_right lam 1) le_rfl
    · rw [corridorReg_toFun, corridorField_apply_of_not_mem hxS]
      exact hx.mono hminpos (min_le_left lam 1) (le_max_left Lam 1)

/-! ## M1.3 — measurability of the local-uniform-ellipticity support -/

/-- The set of locally a.e.-uniformly elliptic carrier fields is genuinely
measurable: it equals the countable `⋂_Q ⋃_k` of the AEE quantitative-slice
sets (`AELocallyUniformlyEllipticField.exists_aeeQuantitativeEllipticSlice_cubeSet`
forward; the definition `AEEQuantitativeEllipticSlice = IsAEEllipticFieldOn (k+1)⁻¹ (k+1)`
plus `IsAEEllipticFieldOn.mono` to the open core backward), each slice set being
genuinely `LocalSigmaR`-measurable on the carrier
(`measurableSet_localSigmaR_aeeQuantitativeEllipticSlice`, Packet P4b) and
`LocalSigmaR ≤` the canonical carrier σ-algebra. -/
theorem measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet {b : RegCoeffField d | AELocallyUniformlyEllipticField b} := by
  classical
  have hEq : {b : RegCoeffField d | AELocallyUniformlyEllipticField b}
      = ⋂ Q : TriadicCube d, ⋃ k : ℕ,
          {b : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k b.toFun} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hb Q
      exact hb.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro hb Q
      obtain ⟨k, hk⟩ := hb Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) (cubeSet Q) b.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (Book.Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

/-! ## M1.4 — pushforward `RestrictionLawCarrier` transport -/

/-- The pushforward of a `RestrictionLawCarrier` law along the corridor endomorphism is
again a `RestrictionLawCarrier` law. -/
theorem lawCarrier_map_corridorReg {L : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier L)
    (ℓ : ℝ) (σ : Vec d) :
    RestrictionLawCarrier (L.map (corridorReg ℓ σ)) := by
  have hT : Measurable (corridorReg (d := d) ℓ σ) := measurable_corridorReg ℓ σ
  have : IsProbabilityMeasure L := hP.isProbability
  have : IsProbabilityMeasure (L.map (corridorReg ℓ σ)) :=
    L.isProbabilityMeasure_map hT.aemeasurable
  refine lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [AELocallyUniformlyEllipticLaw,
    ae_map_iff hT.aemeasurable measurableSet_aeLocallyUniformlyEllipticField]
  filter_upwards [hP.ae_locally_uniformly_elliptic] with a ha
  exact aeLocallyUniformlyEllipticField_corridorReg ha

/-! ## M1 — the per-phase measurability theorem -/

/-- **M1 (per-phase measurability).**  For a fixed grid phase `σ`, the coarse
observable at the corridor-modified coefficient is a.e.-strongly-measurable under
any `RestrictionLawCarrier` law. -/
theorem aestronglyMeasurable_phaseObservable [NeZero d] {L : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier L) (m : ℤ) (ℓ : ℝ) (σ : Vec d) (P : BlockVec d) :
    AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a.toFun)) P)) L := by
  have hT : Measurable (corridorReg (d := d) ℓ σ) := measurable_corridorReg ℓ σ
  have hPush : RestrictionLawCarrier (L.map (corridorReg ℓ σ)) := lawCarrier_map_corridorReg hP ℓ σ
  have hG :
      AEStronglyMeasurable
        (fun b : RegCoeffField d =>
          blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) b.toFun) P))
        (L.map (corridorReg ℓ σ)) :=
    aestronglyMeasurable_coarseBlockQuadratic_cubeSet hPush m P
  exact hG.comp_measurable hT

end Homogenization
