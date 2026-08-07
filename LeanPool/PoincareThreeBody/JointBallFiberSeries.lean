/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AnalyticParameterIntegral
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Constructions

/-!
# Uniform fiber series from one joint analytic ball

A joint power series on a ball in `(parameter, time)` yields parameter power series with a common
radius on any smaller time slab.  These are the local pieces used in the compact-interval
parameter-integral theorem.
-/

namespace LeanPool.PoincareThreeBody

open Filter Set Topology

/-- The isometric inclusion of the analytic parameter as the first product coordinate. -/
def parameterInclusion : ℝ →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.inl ℝ ℝ ℝ

@[simp]
theorem parameterInclusion_apply (value : ℝ) :
    parameterInclusion value = (value, 0) := rfl

@[simp]
theorem norm_parameterInclusion : ‖parameterInclusion‖ = 1 := by
  exact ContinuousLinearMap.norm_inl ℝ ℝ ℝ

/-- Restrict a changed-origin joint series to displacement in the first coordinate. -/
noncomputable def jointBallFiberSeries
    (jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (centerTime time : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (jointSeries.changeOrigin (0, time - centerTime)).compContinuousLinearMap
    parameterInclusion

/-- A joint analytic ball gives all nearby time fibers a common parameter radius. -/
theorem hasFPowerSeriesOnBall_fiber_of_joint_ball
    {function : ℝ × ℝ → ℝ} {jointSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ}
    {centerParameter centerTime time : ℝ}
    {jointRadius timeBound fiberRadius : NNReal}
    (hjoint : HasFPowerSeriesOnBall function jointSeries
      (centerParameter, centerTime) jointRadius)
    (htime : |time - centerTime| ≤ (timeBound : ℝ))
    (hfiberRadius : 0 < fiberRadius)
    (hradii : timeBound + fiberRadius < jointRadius) :
    HasFPowerSeriesOnBall (fun parameter ↦ function (parameter, time))
      (jointBallFiberSeries jointSeries centerTime time)
      centerParameter fiberRadius := by
  let shift : ℝ × ℝ := (0, time - centerTime)
  have hshiftNorm : ‖shift‖ = |time - centerTime| := by
    simp [shift, Prod.norm_def]
  have hshift : (‖shift‖₊ : ENNReal) < jointRadius := by
    have hreal : ‖shift‖ < (jointRadius : ℝ) := by
      rw [hshiftNorm]
      have htimeBound : (timeBound : ℝ) < (jointRadius : ℝ) := by
        exact_mod_cast (lt_of_le_of_lt (le_add_right (le_refl timeBound)) hradii)
      exact htime.trans_lt htimeBound
    exact_mod_cast hreal
  have hcenter :
      (centerParameter, centerTime) + shift + (0, -time) =
        parameterInclusion centerParameter := by
    ext <;> simp [shift]
  have hchanged := hjoint.changeOrigin hshift
  have htranslated := hchanged.comp_sub (0, -time)
  rw [hcenter] at htranslated
  have hrestricted := htranslated.compContinuousLinearMap
    (u := parameterInclusion) (x := centerParameter)
  have hradius : (fiberRadius : ENNReal) ≤
      ((jointRadius : ENNReal) - ‖shift‖₊) / ‖parameterInclusion‖ₑ := by
    rw [enorm_eq_nnnorm, show ‖parameterInclusion‖₊ = 1 by
      ext
      exact norm_parameterInclusion]
    simp only [ENNReal.coe_one, div_one]
    rw [ENNReal.le_sub_iff_add_le_right (by simp) hshift.le]
    rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
    change (fiberRadius : ℝ) + ‖shift‖ ≤ (jointRadius : ℝ)
    rw [hshiftNorm]
    simpa [add_comm] using (add_le_add_left htime (fiberRadius : ℝ)).trans
      (by exact_mod_cast hradii.le)
  have hpositive : 0 < (fiberRadius : ENNReal) := by
    exact_mod_cast hfiberRadius
  have hmono := hrestricted.mono hpositive hradius
  apply hmono.congr
  intro parameter _
  simp [parameterInclusion]

end LeanPool.PoincareThreeBody
