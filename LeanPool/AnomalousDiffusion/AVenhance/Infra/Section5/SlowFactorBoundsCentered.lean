/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TestDensity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.CenteredSpectralMean

/-! Centered Appendix C estimates in the smooth-test norm. Only the fast
factor is required to have zero mean; the actual product is centered explicitly. -/

@[expose] public section

noncomputable section
open scoped ENNReal
open MeasureTheory Homogenization AVenhance
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5

theorem SlowFactorBoundsCentered.centered_avg_cube (f : Vec 2 → ℝ) : cellAverage f = ∫ x in
    unitCube, f x := by
  rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
  exact Infra.Torus.integral_unitCell_eq_unitCube f

theorem SlowFactorBoundsCentered.centered_continuous_L2 {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemL2On unitCube f := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

theorem SlowFactorBoundsCentered.centered_product_L2 {f g : Vec 2 → ℝ} (hf : Continuous f)
    (hg : LocallyIntegrable g (volume : Measure (Vec 2)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec 2))) :
    MemL2On unitCube (fun x => f x * g x) := by
  have hs : LocallyIntegrable (fun x => |f x * g x| ^ 2) (volume : Measure (Vec 2)) := by
    simpa only [abs_mul, mul_pow, Pi.pow_apply] using hg2.continuous_mul (hf.abs.pow 2)
  have hm := hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have h := (cellMemLp_two_of_localSquare hm hs).1
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  exact h

/-- Homeomorphism underlying a periodic volume-preserving flow in the centered estimates. -/
def SlowFactorBoundsCentered.centeredFlowHomeomorph (X : PeriodicVolumePreservingDiffeomorphism 2) :
    Vec 2 ≃ₜ Vec 2 where
  toEquiv := ⟨X.toFun, X.invFun, X.left_inv, X.right_inv⟩
  continuous_toFun := X.contDiff_toFun.continuous
  continuous_invFun := X.contDiff_invFun.continuous

theorem SlowFactorBoundsCentered.centered_flow_local_integrable (X :
    PeriodicVolumePreservingDiffeomorphism 2)
    {g : Vec 2 → ℝ} (hg : LocallyIntegrable g (volume : Measure (Vec 2))) :
    LocallyIntegrable (fun x => g (X.invFun x)) (volume : Measure (Vec 2)) := by
  let e := SlowFactorBoundsCentered.centeredFlowHomeomorph X
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e.toMeasurableEquiv X.measurePreserving
  have h := (locallyIntegrable_map_homeomorph e.symm).1
    (by rw [hmp.map_eq]; exact hg)
  exact h

theorem centered_hMinusOneNorm_eq_ergodic {h : Vec 2 → ℝ}
    (hL2 : MemL2On unitCube h)
    (hh : LocallyIntegrable h (volume : Measure (Vec 2))) :
    hMinusOneNorm (centerCell h) = homogeneousHMinusOneNorm h := by
  have hcenter : MemL2On unitCube (centerCell h) :=
    hL2.sub (SlowFactorBoundsCentered.centered_continuous_L2 continuous_const)
  have hm : MeanZeroOn unitCube (centerCell h) := by
    change (∫ x in unitCube, centerCell h x) = 0
    rw [← SlowFactorBoundsCentered.centered_avg_cube]
    exact cellAverage_centerCell hh
  rw [hMinusOneNorm_eq_ergodic hcenter hm,
    homogeneousHMinusOneNorm_centerCell_eq hh]

theorem centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow
    {N : ℕ} (hN : 0 < N)
    (X : PeriodicVolumePreservingDiffeomorphism 2)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderivComp : HasCoordinateAnalyticL2Bounds
      (fun x => (f (X.toFun x) : ℂ)) Cf r)
    {g : Vec 2 → ℝ}
    (hg : LocallyIntegrable g (volume : Measure (Vec 2)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2)
      (volume : Measure (Vec 2)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ))
    (hnear : FlowDerivativeNearIdentity X)
    (hgMean : cellAverage g = 0) :
    hMinusOneNorm (centerCell (fun x => f x * g (X.invFun x))) ≤
      ENNReal.ofReal (
        (3 * (2 : ℝ) ^ 2) *
          (((1 + 64 * (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) +
            1024 * ((2 : ℝ) + 1)) / (N : ℝ)) *
              (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) *
              (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) +
            (1 + 64 * (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) +
              1024 * ((2 : ℝ) + 1)) * Cf *
              (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) *
              Real.exp (-r * (N : ℝ) / 4096))) := by
  have hcomp := SlowFactorBoundsCentered.centered_flow_local_integrable X hg
  have hs := SlowFactorBoundsCentered.centered_flow_local_integrable X hg2
  have hL2 := SlowFactorBoundsCentered.centered_product_L2 hf.continuous hcomp hs
  rw [centered_hMinusOneNorm_eq_ergodic hL2 (hcomp.continuous_mul hf.continuous)]
  exact homogeneousHMinusOneNorm_le_of_fastPeriodicProduct_flow_without_product_mean
    (by norm_num) hN X hf hper Cf r hCf hr hderivComp hg hg2 hfast hNr hnear hgMean

/-- Consumer repair: retain a separate proof of the actual total's zero mean.
Component estimates are made on centered data, with no component-mean premise. -/
theorem frozen_hMinusOneNorm_sum_le_of_centered_bounds {ι : Type*}
    (s : Finset ι) (h : ι → Vec 2 → ℝ) (B : ι → ℝ≥0∞)
    (hL2 : ∀ i ∈ s, MemL2On unitCube (h i))
    (hh : ∀ i ∈ s, LocallyIntegrable (h i) (volume : Measure (Vec 2)))
    (hm : cellAverage (fun x => ∑ i ∈ s, h i x) = 0)
    (hb : ∀ i ∈ s, hMinusOneNorm (centerCell (h i)) ≤ B i) :
    hMinusOneNorm (fun x => ∑ i ∈ s, h i x) ≤ ∑ i ∈ s, B i := by
  have hsumL2 : MemL2On unitCube (fun x => ∑ i ∈ s, h i x) := by
    exact memLp_finsetSum s hL2
  have hsumMean : MeanZeroOn unitCube (fun x => ∑ i ∈ s, h i x) := by
    change (∫ x in unitCube, ∑ i ∈ s, h i x) = 0
    rw [← SlowFactorBoundsCentered.centered_avg_cube]; exact hm
  rw [hMinusOneNorm_eq_ergodic hsumL2 hsumMean]
  apply (homogeneousHMinusOneNorm_finset_sum_le s h hh).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← centered_hMinusOneNorm_eq_ergodic (hL2 i hi) (hh i hi)]
  exact hb i hi

end AVenhance.Infra.Section5
