/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.EuclideanHsMeasurability
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Exact Euclidean fractional `H^s` on centered triadic cubes

This module defines the literal physical-cube Gagliardo energy with normalized
volume in its first variable and unnormalized restricted volume in its second.
It then transports that energy to the centered unit cube under
`x ↦ (3 ^ m) • x`.

## Main definitions

- `centeredCubeEuclideanHsProductMeasure`: the physical product measure.
- `centeredCubeEuclideanHsEnergy`: the literal physical Euclidean energy.
- `centeredCubeEuclideanHsESeminorm`: its extended square root.
- `MemCenteredCubeEuclideanHs`: measurable finite-energy membership.

## Main results

- `centeredCubeEuclideanHsEnergy_eq_scale_mul_pullbackToUnit`: exact
  `(3 ^ m) ^ (-2s)` energy scaling.
- `centeredCubeEuclideanHsESeminorm_eq_scale_mul_pullbackToUnit`: exact
  `(3 ^ m) ^ (-s)` seminorm scaling.
- `memCenteredCubeEuclideanHs_iff_pullbackToUnit`: exact membership transport.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The source measure `fint_{□_m} dx ∫_{□_m} dy`: normalized volume in
the first variable and unnormalized restricted volume in the second. -/
noncomputable def centeredCubeEuclideanHsProductMeasure (d : ℕ) (m : ℤ) :
    Measure (Vec d × Vec d) :=
  (centeredCubeDomain d m).normalizedVolume.prod
    (centeredCubeDomain d m).restrictedVolume

/-- The physical product measure is exactly the established Gagliardo cube
measure, with no additional normalization convention. -/
theorem centeredCubeEuclideanHsProductMeasure_eq_gagliardoCubeMeasure
    (d : ℕ) (m : ℤ) :
    centeredCubeEuclideanHsProductMeasure d m =
      Gagliardo.gagliardoCubeMeasure (originCube d m) := by
  unfold centeredCubeEuclideanHsProductMeasure Gagliardo.gagliardoCubeMeasure
  rw [show centeredCubeDomain d m =
      cubeBoundedMeasurableDomain (originCube d m) by rfl]
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]

/-- The literal physical integrand
`|F(x)-F(y)|² / |x-y|^(d + 2s)` on the centered cube at scale `m`. -/
noncomputable def centeredCubeEuclideanHsIntegrand {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    Vec d × Vec d → ℝ≥0∞ :=
  fun z => ENNReal.ofReal
    (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
      Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))

/-- The squared physical Euclidean fractional quantity. -/
noncomputable def centeredCubeEuclideanHsEnergy {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  ∫⁻ z, centeredCubeEuclideanHsIntegrand s F z
    ∂centeredCubeEuclideanHsProductMeasure d m

/-- The exact extended Euclidean fractional seminorm on the centered cube. -/
noncomputable def centeredCubeEuclideanHsESeminorm {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  centeredCubeEuclideanHsEnergy s F ^ ((2 : ℝ)⁻¹)

/-- Membership in the literal physical centered-cube Euclidean `H^s` carrier. -/
structure MemCenteredCubeEuclideanHs {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : Prop where
  integrand_aemeasurable :
    AEMeasurable (centeredCubeEuclideanHsIntegrand s F)
      (centeredCubeEuclideanHsProductMeasure d m)
  energy_lt_top : centeredCubeEuclideanHsEnergy s F < ∞

/-- Formula accessor for the physical squared energy. -/
theorem centeredCubeEuclideanHsEnergy_eq_lintegral {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsEnergy s F =
      ∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂centeredCubeEuclideanHsProductMeasure d m :=
  rfl

/-- Formula accessor for the physical extended seminorm. -/
theorem centeredCubeEuclideanHsESeminorm_eq_lintegral {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsESeminorm s F =
      (∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂centeredCubeEuclideanHsProductMeasure d m) ^ ((2 : ℝ)⁻¹) :=
  rfl

private theorem ae_restrictedVolume_of_ae_normalizedVolume {d : ℕ} {m : ℤ}
    {F G : CenteredCubeEuclideanL2Field d m}
    (hFG : F =ᵐ[(centeredCubeDomain d m).normalizedVolume] G) :
    F =ᵐ[(centeredCubeDomain d m).restrictedVolume] G := by
  rw [BoundedMeasurableDomain.normalizedVolume] at hFG
  unfold Filter.EventuallyEq at hFG ⊢
  rw [ae_iff] at hFG ⊢
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    or_iff_right (ENNReal.inv_ne_zero.mpr (centeredCubeDomain d m).volume_ne_top)] at hFG
  exact hFG

/-- The physical integrand is invariant under normalized-volume a.e.
replacement of the field. -/
theorem centeredCubeEuclideanHsIntegrand_congr_ae {d : ℕ} {m : ℤ}
    {s : FractionalOrder} {F G : CenteredCubeEuclideanL2Field d m}
    (hFG : F =ᵐ[(centeredCubeDomain d m).normalizedVolume] G) :
    centeredCubeEuclideanHsIntegrand s F =ᵐ[
      centeredCubeEuclideanHsProductMeasure d m]
        centeredCubeEuclideanHsIntegrand s G := by
  have hFG_restricted :
      F =ᵐ[(centeredCubeDomain d m).restrictedVolume] G :=
    ae_restrictedVolume_of_ae_normalizedVolume hFG
  have hfst :
      (fun z : Vec d × Vec d => F z.1) =ᵐ[
        centeredCubeEuclideanHsProductMeasure d m] fun z => G z.1 := by
    rw [centeredCubeEuclideanHsProductMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae_eq hFG
  have hsnd :
      (fun z : Vec d × Vec d => F z.2) =ᵐ[
        centeredCubeEuclideanHsProductMeasure d m] fun z => G z.2 := by
    rw [centeredCubeEuclideanHsProductMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae_eq hFG_restricted
  filter_upwards [hfst, hsnd] with z hz1 hz2
  simp only [centeredCubeEuclideanHsIntegrand, hz1, hz2]

/-- The physical squared energy is invariant under normalized-volume a.e.
replacement of the field. -/
theorem centeredCubeEuclideanHsEnergy_congr_ae {d : ℕ} {m : ℤ}
    {s : FractionalOrder} {F G : CenteredCubeEuclideanL2Field d m}
    (hFG : F =ᵐ[(centeredCubeDomain d m).normalizedVolume] G) :
    centeredCubeEuclideanHsEnergy s F = centeredCubeEuclideanHsEnergy s G := by
  unfold centeredCubeEuclideanHsEnergy
  exact lintegral_congr_ae (centeredCubeEuclideanHsIntegrand_congr_ae hFG)

/-- The physical extended seminorm is invariant under normalized-volume a.e.
replacement of the field. -/
theorem centeredCubeEuclideanHsESeminorm_congr_ae {d : ℕ} {m : ℤ}
    {s : FractionalOrder} {F G : CenteredCubeEuclideanL2Field d m}
    (hFG : F =ᵐ[(centeredCubeDomain d m).normalizedVolume] G) :
    centeredCubeEuclideanHsESeminorm s F =
      centeredCubeEuclideanHsESeminorm s G := by
  unfold centeredCubeEuclideanHsESeminorm
  rw [centeredCubeEuclideanHsEnergy_congr_ae hFG]

private theorem measurable_euclideanDist_pair (d : ℕ) :
    Measurable (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
  have hsub : Measurable (fun z : Vec d × Vec d => z.1 - z.2) :=
    measurable_fst.sub measurable_snd
  have hh : Measurable (fun z : Vec d × Vec d => HilbertVec.ofVec (z.1 - z.2)) :=
    (HilbertVec.ofVecL d).continuous.measurable.comp hsub
  simpa only [euclideanDist, euclideanNorm_eq_norm_ofVec] using hh.norm

private theorem measurable_centeredCubeEuclideanHsIntegrand_of_measurable {d : ℕ}
    {m : ℤ} (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m)
    (hF : Measurable F) : Measurable (centeredCubeEuclideanHsIntegrand s F) := by
  unfold centeredCubeEuclideanHsIntegrand
  apply Measurable.ennreal_ofReal
  apply Measurable.div
  · exact ((HilbertVec.ofVecL d).continuous.measurable.comp
      ((hF.comp measurable_fst).sub (hF.comp measurable_snd))).norm.pow measurable_const
  · change Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1))
    exact (measurable_euclideanDist_pair d).pow measurable_const

/-- The physical Euclidean integrand is a.e.-measurable for every stored
centered-cube `L²` field. -/
theorem aemeasurable_centeredCubeEuclideanHsIntegrand {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    AEMeasurable (centeredCubeEuclideanHsIntegrand s F)
      (centeredCubeEuclideanHsProductMeasure d m) := by
  exact (measurable_centeredCubeEuclideanHsIntegrand_of_measurable s
    F.measurableRepresentative F.measurable_measurableRepresentative).aemeasurable.congr
      (centeredCubeEuclideanHsIntegrand_congr_ae
        F.ae_eq_measurableRepresentative).symm

/-- Physical centered-cube membership is exactly finite physical energy. -/
theorem memCenteredCubeEuclideanHs_iff_energy_lt_top {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    MemCenteredCubeEuclideanHs s F ↔ centeredCubeEuclideanHsEnergy s F < ∞ := by
  constructor
  · exact fun h => h.energy_lt_top
  · exact fun h => ⟨aemeasurable_centeredCubeEuclideanHsIntegrand s F, h⟩

/-- The measurable equivalence implementing centered-cube dilation. -/
noncomputable def centeredCubeDilationMeasurableEquiv {d : ℕ} (m : ℤ) :
    Vec d ≃ᵐ Vec d :=
  (Homeomorph.smulOfNeZero (centeredCubeScale m)
    (centeredCubeScale_ne_zero m)).toMeasurableEquiv

@[simp] theorem centeredCubeDilationMeasurableEquiv_apply {d : ℕ} (m : ℤ)
    (x : Vec d) :
    centeredCubeDilationMeasurableEquiv (d := d) m x = centeredCubeDilation m x :=
  rfl

/-- Dilation applied in both variables of the physical product measure. -/
noncomputable def centeredCubePairDilation {d : ℕ} (m : ℤ) :
    Vec d × Vec d → Vec d × Vec d :=
  Prod.map (centeredCubeDilation m) (centeredCubeDilation m)

/-- The product measure gains exactly the inverse Jacobian from its
unnormalized second variable under dilation. -/
theorem map_centeredCubePairDilation_productMeasure {d : ℕ} (m : ℤ) :
    Measure.map (centeredCubePairDilation (d := d) m)
        (centeredCubeEuclideanHsProductMeasure d 0) =
      ENNReal.ofReal (((centeredCubeScale m) ^ d)⁻¹) •
        centeredCubeEuclideanHsProductMeasure d m := by
  let : IsFiniteMeasure (cubeMeasure (originCube d 0)) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top (originCube d 0))⟩
  let : IsFiniteMeasure (cubeMeasure (originCube d m)) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top (originCube d m))⟩
  let : SFinite (centeredCubeDomain d 0).normalizedVolume := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    infer_instance
  let : SFinite (centeredCubeDomain d 0).restrictedVolume := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
    infer_instance
  let : SFinite (centeredCubeDomain d m).restrictedVolume := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
    infer_instance
  unfold centeredCubePairDilation centeredCubeEuclideanHsProductMeasure
  rw [← Measure.map_prod_map _ _ (measurable_centeredCubeDilation m)
    (measurable_centeredCubeDilation m)]
  rw [map_centeredCubeDilation_normalizedVolume,
    map_centeredCubeDilation_restrictedVolume, Measure.prod_smul_right]

private theorem centeredCubeMeasureScale_mul_inverseScale (d : ℕ) (m : ℤ) :
    ENNReal.ofReal ((centeredCubeScale m) ^ d) *
        ENNReal.ofReal (((centeredCubeScale m) ^ d)⁻¹) = 1 := by
  rw [← ENNReal.ofReal_mul (pow_nonneg (centeredCubeScale_pos m).le d)]
  rw [mul_inv_cancel₀ (pow_ne_zero d (centeredCubeScale_ne_zero m))]
  exact ENNReal.ofReal_one

/-- The physical product measure is the Jacobian multiple of the pushforward
of the unit product measure. -/
theorem centeredCubeEuclideanHsProductMeasure_eq_smul_map {d : ℕ} (m : ℤ) :
    centeredCubeEuclideanHsProductMeasure d m =
      ENNReal.ofReal ((centeredCubeScale m) ^ d) •
        Measure.map (centeredCubePairDilation (d := d) m)
          (centeredCubeEuclideanHsProductMeasure d 0) := by
  rw [map_centeredCubePairDilation_productMeasure]
  rw [smul_smul, centeredCubeMeasureScale_mul_inverseScale, one_smul]

private theorem centeredCubeEuclideanHsIntegrand_dilation {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m)
    (z : Vec d × Vec d) :
    centeredCubeEuclideanHsIntegrand s F (centeredCubePairDilation m z) =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-((d : ℝ) + 2 * s.1)) *
        euclideanHsIntegrand s F.pullbackToUnit z := by
  let r : ℝ := centeredCubeScale m
  let N : ℝ := ‖HilbertVec.ofVec (F (r • z.1) - F (r • z.2))‖ ^ 2
  let D : ℝ := euclideanDist z.1 z.2
  let a : ℝ := (d : ℝ) + 2 * s.1
  have hr : 0 < r := centeredCubeScale_pos m
  have hD : 0 ≤ D := euclideanDist_nonneg _ _
  have hquot :
      N / Real.rpow (r * D) a =
        Real.rpow r (-a) * (N / Real.rpow D a) := by
    change N / ((r * D) ^ a) = r ^ (-a) * (N / D ^ a)
    rw [Real.mul_rpow hr.le hD, Real.rpow_neg hr.le]
    have hA : r ^ a ≠ 0 := (Real.rpow_pos_of_pos hr a).ne'
    field_simp
  unfold centeredCubeEuclideanHsIntegrand euclideanHsIntegrand
  change ENNReal.ofReal
      (N / Real.rpow (euclideanDist (r • z.1) (r • z.2)) a) =
    (ENNReal.ofReal r) ^ (-a) * ENNReal.ofReal (N / Real.rpow D a)
  rw [euclideanDist_smul, abs_of_pos hr]
  change ENNReal.ofReal (N / Real.rpow (r * D) a) = _
  rw [hquot]
  change ENNReal.ofReal (r ^ (-a) * (N / Real.rpow D a)) = _
  have hrpow_nonneg : 0 ≤ r ^ (-a) := Real.rpow_nonneg hr.le (-a)
  rw [ENNReal.ofReal_mul hrpow_nonneg]
  change ENNReal.ofReal (r ^ (-a)) * ENNReal.ofReal (N / Real.rpow D a) = _
  rw [← ENNReal.ofReal_rpow_of_pos hr]

private theorem centeredCubeHsScaleFactors_mul {d : ℕ} (m : ℤ)
    (s : FractionalOrder) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ d *
        (ENNReal.ofReal (centeredCubeScale m)) ^ (-((d : ℝ) + 2 * s.1)) =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-2 * s.1) := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_add _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) ENNReal.ofReal_ne_top]
  congr 1
  ring

private theorem centeredCubeScale_rpow_ne_top (m : ℤ) (a : ℝ) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ a ≠ ∞ := by
  intro htop
  rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
  · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
  · exact ENNReal.ofReal_ne_top htop'.1

/-- Exact physical energy scaling under pullback to the centered unit cube. -/
theorem centeredCubeEuclideanHsEnergy_eq_scale_mul_pullbackToUnit {d : ℕ}
    {m : ℤ} (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsEnergy s F =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-2 * s.1) *
        euclideanHsEnergy s F.pullbackToUnit := by
  unfold centeredCubeEuclideanHsEnergy euclideanHsEnergy
  rw [centeredCubeEuclideanHsProductMeasure_eq_smul_map]
  rw [lintegral_smul_measure]
  let T : (Vec d × Vec d) ≃ᵐ (Vec d × Vec d) :=
    (centeredCubeDilationMeasurableEquiv (d := d) m).prodCongr
      (centeredCubeDilationMeasurableEquiv (d := d) m)
  have hT : (⇑T : Vec d × Vec d → Vec d × Vec d) =
      centeredCubePairDilation m := by
    rfl
  rw [← hT]
  rw [lintegral_map_equiv]
  have hT_apply (z : Vec d × Vec d) : T z = centeredCubePairDilation m z :=
    congrFun hT z
  simp_rw [hT_apply, centeredCubeEuclideanHsIntegrand_dilation]
  have hk_top :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-((d : ℝ) + 2 * s.1)) ≠ ∞ :=
    centeredCubeScale_rpow_ne_top m _
  rw [lintegral_const_mul'
    ((ENNReal.ofReal (centeredCubeScale m)) ^ (-((d : ℝ) + 2 * s.1))) _
    hk_top]
  change ENNReal.ofReal ((centeredCubeScale m) ^ d) *
      ((ENNReal.ofReal (centeredCubeScale m)) ^ (-((d : ℝ) + 2 * s.1)) *
        ∫⁻ z, euclideanHsIntegrand s F.pullbackToUnit z
          ∂euclideanHsProductMeasure d) = _
  rw [← mul_assoc, ENNReal.ofReal_pow (centeredCubeScale_pos m).le,
    centeredCubeHsScaleFactors_mul]

/-- Exact physical seminorm scaling under pullback to the centered unit cube. -/
theorem centeredCubeEuclideanHsESeminorm_eq_scale_mul_pullbackToUnit {d : ℕ}
    {m : ℤ} (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsESeminorm s F =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        euclideanHsESeminorm s F.pullbackToUnit := by
  unfold centeredCubeEuclideanHsESeminorm euclideanHsESeminorm
  rw [centeredCubeEuclideanHsEnergy_eq_scale_mul_pullbackToUnit]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Physical centered-cube fractional membership is exactly membership of the
unit pullback. -/
theorem memCenteredCubeEuclideanHs_iff_pullbackToUnit {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    MemCenteredCubeEuclideanHs s F ↔ MemEuclideanHs s F.pullbackToUnit := by
  rw [memCenteredCubeEuclideanHs_iff_energy_lt_top,
    memEuclideanHs_iff_energy_lt_top,
    centeredCubeEuclideanHsEnergy_eq_scale_mul_pullbackToUnit]
  let c : ℝ≥0∞ := (ENNReal.ofReal (centeredCubeScale m)) ^ (-2 * s.1)
  have hc_pos : 0 < c := ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (centeredCubeScale_pos m)) ENNReal.ofReal_ne_top
  have hc_top : c < ∞ := by
    rw [lt_top_iff_ne_top]
    exact centeredCubeScale_rpow_ne_top m _
  constructor
  · intro h
    rcases ENNReal.mul_lt_top_iff.mp h with hfinite | hzero
    · exact hfinite.2
    · rcases hzero with hc_zero | henergy_zero
      · exact False.elim (hc_pos.ne' hc_zero)
      · simpa only [henergy_zero] using ENNReal.zero_lt_top
  · exact fun h => ENNReal.mul_lt_top hc_top h

end

end Homogenization
