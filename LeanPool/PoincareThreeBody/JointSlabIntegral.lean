/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.JointBallFiberSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrating a joint analytic power series over a time slab

This file turns the uniform fiber series supplied by a joint analytic ball into a power series
for its parameter integral over any closed time interval contained in a smaller slab.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Set Topology

/-- For a fixed degree, the restricted parameter coefficient varies continuously with time as
long as the time displacement remains inside the joint convergence ball. -/
theorem continuousOn_jointBallFiberSeries_degree
    (jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (centerTime : ℝ) (degree : ℕ) {timeBound : NNReal}
    (hradius : (timeBound : ENNReal) < jointSeries.radius) :
    ContinuousOn (fun time ↦ jointBallFiberSeries jointSeries centerTime time degree)
      {time | |time - centerTime| ≤ (timeBound : ℝ)} := by
  let shift : ℝ → ℝ × ℝ := fun time ↦ (0, time - centerTime)
  let restrictCoefficient :
      ((ℝ × ℝ) [×degree]→L[ℝ] ℝ) →L[ℝ] (ℝ [×degree]→L[ℝ] ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin degree ↦ parameterInclusion)
  have hchange :=
    (jointSeries.hasFPowerSeriesOnBall_changeOrigin degree
      (lt_of_le_of_lt (by positivity : (0 : ENNReal) ≤ timeBound) hradius)).continuousOn
  have hshift : Continuous shift := by
    fun_prop
  have hmaps : MapsTo shift
      {time | |time - centerTime| ≤ (timeBound : ℝ)}
      (Metric.eball (0 : ℝ × ℝ) jointSeries.radius) := by
    intro time htime
    rw [Metric.mem_eball, edist_zero_right]
    change (‖shift time‖₊ : ENNReal) < jointSeries.radius
    apply lt_of_le_of_lt _ hradius
    have hnorm : ‖time - centerTime‖ ≤ (timeBound : ℝ) := by
      simpa [Real.norm_eq_abs] using htime
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    simpa [shift, Prod.norm_def] using hnorm
  have hcontinuous := restrictCoefficient.continuous.comp_continuousOn
    (hchange.comp hshift.continuousOn hmaps)
  apply hcontinuous.congr
  intro time _
  rfl

/-- A time-independent majorant for one coefficient of the parameter fiber series. -/
noncomputable def jointBallFiberCoefficientBound
    (jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (timeBound : NNReal) (degree : ℕ) : NNReal :=
  ∑' index : Σ order : ℕ,
      {subset : Finset (Fin (degree + order)) // subset.card = order},
    ‖jointSeries (degree + index.1)‖₊ * timeBound ^ index.1

/-- Every fiber coefficient on the slab is bounded by the coefficient majorant above. -/
theorem nnnorm_jointBallFiberSeries_le_coefficientBound
    (jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (centerTime time : ℝ) (degree : ℕ) {timeBound : NNReal}
    (hradius : (timeBound : ENNReal) < jointSeries.radius)
    (htime : |time - centerTime| ≤ (timeBound : ℝ)) :
    ‖jointBallFiberSeries jointSeries centerTime time degree‖₊ ≤
      jointBallFiberCoefficientBound jointSeries timeBound degree := by
  let shift : ℝ × ℝ := (0, time - centerTime)
  have hshiftNorm : ‖shift‖₊ ≤ timeBound := by
    apply NNReal.coe_le_coe.mp
    simpa [shift, Prod.norm_def, Real.norm_eq_abs] using htime
  have hshiftRadius : (‖shift‖₊ : ENNReal) < jointSeries.radius :=
    (ENNReal.coe_le_coe.mpr hshiftNorm).trans_lt hradius
  calc
    ‖jointBallFiberSeries jointSeries centerTime time degree‖₊ ≤
        ‖jointSeries.changeOrigin shift degree‖₊ * ‖parameterInclusion‖₊ ^ degree := by
      exact FormalMultilinearSeries.nnnorm_compContinuousLinearMap_le
        (jointSeries.changeOrigin shift) parameterInclusion degree
    _ = ‖jointSeries.changeOrigin shift degree‖₊ := by
      rw [show ‖parameterInclusion‖₊ = 1 by
        ext
        exact norm_parameterInclusion]
      simp
    _ ≤ ∑' index : Σ order : ℕ,
          {subset : Finset (Fin (degree + order)) // subset.card = order},
        ‖jointSeries (degree + index.1)‖₊ * ‖shift‖₊ ^ index.1 :=
      jointSeries.nnnorm_changeOrigin_le degree hshiftRadius
    _ ≤ jointBallFiberCoefficientBound jointSeries timeBound degree := by
      unfold jointBallFiberCoefficientBound
      apply Summable.tsum_le_tsum (fun index ↦ by gcongr)
        (jointSeries.changeOriginSeries_summable_aux₂ hshiftRadius degree)
        (jointSeries.changeOriginSeries_summable_aux₂ hradius degree)

/-- The coefficient majorants are summable at every parameter radius whose sum with the slab
half-width remains inside the original joint convergence radius. -/
theorem summable_coefficientBound_mul_pow
    (jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    {timeBound fiberRadius : NNReal}
    (hradii : ((timeBound + fiberRadius : NNReal) : ENNReal) < jointSeries.radius) :
    Summable (fun degree ↦
      (jointBallFiberCoefficientBound jointSeries timeBound degree : ℝ) *
        (fiberRadius : ℝ) ^ degree) := by
  have hall := jointSeries.changeOriginSeries_summable_aux₁ hradii
  have hdegrees := (NNReal.summable_sigma.1 hall).2
  have hnnreal : Summable (fun degree ↦
      jointBallFiberCoefficientBound jointSeries timeBound degree *
        fiberRadius ^ degree) := by
    simpa only [jointBallFiberCoefficientBound, NNReal.tsum_mul_right] using hdegrees
  simpa only [NNReal.coe_mul, NNReal.coe_pow] using NNReal.summable_coe.mpr hnnreal

/-- Integrating over a finite measurable time set contained in a joint analytic slab preserves a
uniform parameter power series. -/
theorem hasFPowerSeriesOnBall_setIntegral_of_joint_ball_of_measurableSet
    {function : ℝ × ℝ → ℝ}
    {jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ}
    {centerParameter centerTime : ℝ} {timeSet : Set ℝ}
    {jointRadius timeBound fiberRadius : NNReal}
    (hjoint : HasFPowerSeriesOnBall function jointSeries
      (centerParameter, centerTime) jointRadius)
    (hfiberRadius : 0 < fiberRadius)
    (hradii : timeBound + fiberRadius < jointRadius)
    (htimeSet : MeasurableSet timeSet) (htimeFinite : volume timeSet < ⊤)
    (hinterval : ∀ time ∈ timeSet,
      |time - centerTime| ≤ (timeBound : ℝ)) :
    HasFPowerSeriesOnBall
      (fun parameter ↦ ∫ time in timeSet, function (parameter, time))
      (integralFormalMultilinearSeries (volume.restrict timeSet)
        (jointBallFiberSeries jointSeries centerTime))
      centerParameter fiberRadius := by
  have htimeRadius : (timeBound : ENNReal) < jointSeries.radius := by
    exact (ENNReal.coe_lt_coe.mpr
      ((lt_of_le_of_lt (le_add_right (le_refl timeBound)) hradii))).trans_le hjoint.r_le
  have hsumRadius : ((timeBound + fiberRadius : NNReal) : ENNReal) <
      jointSeries.radius := (ENNReal.coe_lt_coe.mpr hradii).trans_le hjoint.r_le
  have hseries : ∀ᵐ time ∂(volume.restrict timeSet),
      HasFPowerSeriesOnBall (fun parameter ↦ function (parameter, time))
        (jointBallFiberSeries jointSeries centerTime time)
        centerParameter fiberRadius := by
    filter_upwards [ae_restrict_mem htimeSet] with time htime
    exact hasFPowerSeriesOnBall_fiber_of_joint_ball hjoint
      (hinterval time htime) hfiberRadius hradii
  have hcoeffIntegrable : ∀ degree,
      Integrable (fun time ↦ jointBallFiberSeries jointSeries centerTime time degree)
        (volume.restrict timeSet) := by
    intro degree
    apply IntegrableOn.of_bound htimeFinite
      (((continuousOn_jointBallFiberSeries_degree jointSeries centerTime degree htimeRadius).mono
        (fun time htime ↦ hinterval time htime)).aestronglyMeasurable htimeSet)
      (jointBallFiberCoefficientBound jointSeries timeBound degree : ℝ)
    filter_upwards [ae_restrict_mem htimeSet] with time htime
    exact_mod_cast nnnorm_jointBallFiberSeries_le_coefficientBound
      jointSeries centerTime time degree htimeRadius (hinterval time htime)
  have hcoeffSummable : Summable (fun degree ↦
      (∫ time in timeSet,
        ‖jointBallFiberSeries jointSeries centerTime time degree‖) *
          (fiberRadius : ℝ) ^ degree) := by
    have hmajorant := summable_coefficientBound_mul_pow jointSeries hsumRadius
    have hmajorantScaled := hmajorant.mul_left
      (volume timeSet).toReal
    apply hmajorantScaled.of_nonneg_of_le
    · intro degree
      positivity
    · intro degree
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg fiberRadius.2 degree)
      have hconstant : Integrable
          (fun _ : ℝ ↦ (jointBallFiberCoefficientBound
            jointSeries timeBound degree : ℝ))
          (volume.restrict timeSet) := integrableOn_const htimeFinite.ne
      calc
        (∫ time in timeSet,
            ‖jointBallFiberSeries jointSeries centerTime time degree‖) ≤
            ∫ _time : ℝ in timeSet,
              (jointBallFiberCoefficientBound jointSeries timeBound degree : ℝ) := by
          apply integral_mono_ae (hcoeffIntegrable degree).norm hconstant
          filter_upwards [ae_restrict_mem htimeSet] with time htime
          exact_mod_cast nnnorm_jointBallFiberSeries_le_coefficientBound
            jointSeries centerTime time degree htimeRadius (hinterval time htime)
        _ = (volume timeSet).toReal *
              (jointBallFiberCoefficientBound jointSeries timeBound degree : ℝ) := by
          simp [Measure.real]
  exact hasFPowerSeriesOnBall_integral_of_uniform
    (volume.restrict timeSet) hfiberRadius hseries
      hcoeffIntegrable hcoeffSummable

/-- Closed intervals are the principal special case of measurable time sets. -/
theorem hasFPowerSeriesOnBall_setIntegral_of_joint_ball
    {function : ℝ × ℝ → ℝ}
    {jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ}
    {centerParameter centerTime start finish : ℝ}
    {jointRadius timeBound fiberRadius : NNReal}
    (hjoint : HasFPowerSeriesOnBall function jointSeries
      (centerParameter, centerTime) jointRadius)
    (hfiberRadius : 0 < fiberRadius)
    (hradii : timeBound + fiberRadius < jointRadius)
    (hinterval : ∀ time ∈ Icc start finish,
      |time - centerTime| ≤ (timeBound : ℝ)) :
    HasFPowerSeriesOnBall
      (fun parameter ↦ ∫ time in Icc start finish, function (parameter, time))
      (integralFormalMultilinearSeries (volume.restrict (Icc start finish))
        (jointBallFiberSeries jointSeries centerTime))
      centerParameter fiberRadius := by
  apply hasFPowerSeriesOnBall_setIntegral_of_joint_ball_of_measurableSet
    hjoint hfiberRadius hradii measurableSet_Icc
  · rw [Real.volume_Icc]
    finiteness
  · exact hinterval

end LeanPool.PoincareThreeBody
