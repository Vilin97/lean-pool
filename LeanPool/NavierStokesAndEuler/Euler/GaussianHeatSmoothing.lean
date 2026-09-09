/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatDerivative

@[expose] public section

/-! Gaussian averaging genuinely gains one strong derivative for every cylinder L² datum. -/

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerLiftedWeakDerivative EulerCylinderMollifier EulerClosedTranslationGraph
    EulerSpatialSobolevInverse
  EulerCylinderCoordinates
open scoped ENNReal NNReal Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

theorem lineHeatDerivative_add (a : LiftTangent) (v : ℝ≥0) (f g : LiftL2 period) :
    lineHeatDerivative period a v (f+g) = lineHeatDerivative period a v f + lineHeatDerivative
      period a v g := by
  have h : (∫ x : ℝ, x • lineOrbit period a (f+g) x ∂gaussianReal 0 v) =
      (∫ x : ℝ, x • lineOrbit period a f x ∂gaussianReal 0 v) +
      (∫ x : ℝ, x • lineOrbit period a g x ∂gaussianReal 0 v) := by
    simp only [lineOrbit, map_add, smul_add]
    exact integral_add (gaussianMomentOrbit_integrable period a v f)
      (gaussianMomentOrbit_integrable period a v g)
  simp only [lineHeatDerivative, h, smul_add]

theorem lineHeatDerivative_smul (a : LiftTangent) (v : ℝ≥0) (c : ℝ) (f : LiftL2 period) :
    lineHeatDerivative period a v (c • f) = c • lineHeatDerivative period a v f := by
  simp only [lineHeatDerivative, lineOrbit, map_smul]
  have he : (fun x : ℝ => x • c • translation period (translationPath period a x) f) =
      fun x : ℝ => c • x • translation period (translationPath period a x) f := by
    funext x
    exact smul_comm x c _
  rw [he, integral_smul, smul_comm]

/-- The bounded moment operator used to close the derivative graph. -/
def lineHeatDerivativeOperator (a : LiftTangent) (v : ℝ≥0) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := lineHeatDerivative period a v
      map_add' := lineHeatDerivative_add period a v
      map_smul' := lineHeatDerivative_smul period a v }
    ((v : ℝ)⁻¹ * gaussianAbsMoment v) (lineHeatDerivative_norm_le period a v)

@[simp] theorem lineHeatDerivativeOperator_apply (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    lineHeatDerivativeOperator period a v f = lineHeatDerivative period a v f := rfl

/-- Genuine cylinder mollifications are differentiable along every one-parameter translation orbit. -/
theorem mollify_lineOrbit_differentiable (a : LiftTangent) (n : ℕ) (f : LiftL2 period) :
    Differentiable ℝ (lineOrbit period a (mollify period n f)) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => orbit period (mollify period n f) (coordinateEquiv.symm (t •
    a))) :=
    (mollify_orbit_contDiff period n f).comp (coordinateEquiv.symm.contDiff.comp (contDiff_id.smul
      contDiff_const))
  have he : (fun t : ℝ => orbit period (mollify period n f) (coordinateEquiv.symm (t • a))) =
      lineOrbit period a (mollify period n f) := by
    funext t
    simp only [orbit, euclideanCover, lineOrbit, translationPath, Function.comp_apply,
      coordinateEquiv.apply_symm_apply]
  rw [he] at h
  exact h.differentiable (by simp)

/-- For positive variance the Gaussian average of every L² field has the stated strong derivative. -/
theorem lineHeat_hasDerivAt (a : LiftTangent) {v : ℝ≥0} (hv : 0 < v) (f : LiftL2 period) :
    HasDerivAt (lineOrbit period a (lineHeat period a v f)) (lineHeatDerivative period a v f) 0 :=
      by
  let fn := fun n => mollify period n f
  let gn := fun n => deriv (lineOrbit period a (fn n)) 0
  have hDn (n : ℕ) : HasDerivAt (lineOrbit period a (fn n)) (gn n) 0 :=
    (mollify_lineOrbit_differentiable period a n f 0).hasDerivAt
  have hmem (n : ℕ) : (lineHeat period a v (fn n), lineHeatDerivative period a v (fn n)) ∈
      translationDerivativeGraph period a := by
    have h := lineHeat_strongDerivative period a a v (fn n) (gn n) (hDn n)
    rw [lineHeat_derivative_identity period a hv.ne' (fn n) (gn n) (hDn n)] at h
    exact h
  have hlim : Filter.Tendsto (fun n => (lineHeat period a v (fn n), lineHeatDerivative period a v
    (fn n)))
      Filter.atTop (𝓝 (lineHeat period a v f, lineHeatDerivative period a v f)) :=
    ((lineHeatOperator period a v).continuous.continuousAt.tendsto.comp (mollify_tendsto period
      f)).prodMk_nhds
      ((lineHeatDerivativeOperator period a v).continuous.continuousAt.tendsto.comp
        (mollify_tendsto period f))
  exact (translationDerivativeGraph_closed period a).mem_of_tendsto hlim
    (Filter.Eventually.of_forall hmem)

/-- Actual one-derivative smoothing, with both the derivative witness and its parabolic bound. -/
theorem lineHeat_one_derivative (a : LiftTangent) {v : ℝ≥0} (hv : 0 < v) (f : LiftL2 period) :
    ∃ g : LiftL2 period,
      HasDerivAt (lineOrbit period a (lineHeat period a v f)) g 0 ∧
      ‖g‖ ≤ (gaussianAbsMoment 1 / Real.sqrt (v : ℝ)) * ‖f‖ :=
  ⟨lineHeatDerivative period a v f, lineHeat_hasDerivAt period a hv f,
    lineHeatDerivative_smoothing_bound period a hv f⟩

/-- The derivative of the heat average commutes with every cylinder translation. -/
theorem lineHeatDerivative_translation (a : LiftTangent) (v : ℝ≥0) (b : LiftDomain period) (f :
  LiftL2 period) :
    translation period b (lineHeatDerivative period a v f) =
      lineHeatDerivative period a v (translation period b f) := by
  simp only [lineHeatDerivative, map_smul]
  congr 1
  change (translation period b).toContinuousLinearMap
      (∫ x : ℝ, x • lineOrbit period a f x ∂gaussianReal 0 v) = _
  rw [← (translation period b).toContinuousLinearMap.integral_comp_comm
    (gaussianMomentOrbit_integrable period a v f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change translation period b (x • translation period (translationPath period a x) f) =
    x • translation period (translationPath period a x) (translation period b f)
  rw [map_smul, translation_add, translation_add, add_comm b]

end EulerGaussianCylinderHeat
