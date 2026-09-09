/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatGenerator
import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatTotal

/-! Differentiation of jointly continuous operator families without operator-norm differentiability.
-/

@[expose] public section


noncomputable section

namespace EulerStrongOperatorDerivative

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact slope decomposition for a varying bounded linear operator and a varying input. -/
theorem slope_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t s : ℝ) :
    slope (fun r => A r (u r)) t s = A s (slope u t s) + slope (fun r => A r (u t)) t s := by
  simp only [slope, vsub_eq_sub, map_smul, map_sub]
  rw [← smul_add]
  congr 1
  abel

/-- A product rule requiring joint strong continuity only at the limiting derivative vector. -/
theorem hasDerivAt_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t : ℝ) (u' : E) (a' : F)
    (hu : HasDerivAt u u' t) (ha : HasDerivAt (fun s => A s (u t)) a' t)
    (hc : ContinuousAt (fun p : ℝ × E => A p.1 p.2) (t, u')) :
    HasDerivAt (fun s => A s (u s)) (A t u' + a') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hfirst : Tendsto (fun s => A s (slope u t s)) (𝓝[≠] t) (𝓝 (A t u')) :=
    hc.tendsto.comp ((show Tendsto (fun r : ℝ => r) (𝓝[≠] t) (𝓝 t) from
        nhdsWithin_le_nhds).prodMk_nhds hu.tendsto_slope)
  exact (hfirst.add ha.tendsto_slope).congr'
    (Filter.Eventually.of_forall (fun s => (slope_apply A u t s).symm))

/-- The same product rule for a one-sided derivative. -/
theorem hasDerivWithinAt_apply (A : ℝ → E →L[ℝ] F) (u : ℝ → E) (t : ℝ) (s : Set ℝ) (u' : E) (a' : F)
    (hu : HasDerivWithinAt u u' s t) (ha : HasDerivWithinAt (fun r => A r (u t)) a' s t)
    (hc : ContinuousAt (fun p : ℝ × E => A p.1 p.2) (t, u')) :
    HasDerivWithinAt (fun r => A r (u r)) (A t u' + a') s t := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hfirst : Tendsto (fun r => A r (slope u t r)) (𝓝[s \ {t}] t) (𝓝 (A t u')) :=
    hc.tendsto.comp ((show Tendsto (fun r : ℝ => r) (𝓝[s \ {t}] t) (𝓝 t) from
        nhdsWithin_le_nhds).prodMk_nhds
      (hasDerivWithinAt_iff_tendsto_slope.mp hu))
  exact (hfirst.add (hasDerivWithinAt_iff_tendsto_slope.mp ha)).congr'
    (Filter.Eventually.of_forall (fun r => (slope_apply A u t r).symm))

end EulerStrongOperatorDerivative

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
    EulerStrongOperatorDerivative
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The real extension is the nonnegative-variance heat operator evaluated at the positive part. -/
theorem realLineHeat_eq_toNNReal (a : LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realLineHeat period a t f = lineHeat period a t.toNNReal f := by
  rw [realLineHeat, lineHeat_eq_standardGaussian]
  have hs : Real.sqrt (t.toNNReal : ℝ) = Real.sqrt t := by simp only [Real.sqrt, Real.toNNReal_coe]
  rw [hs]

/-- Real-parameter version of the actual bounded heat operator. -/
def realLineHeatOperator (a : LiftTangent) (t : ℝ) : LiftL2 period →L[ℝ] LiftL2 period :=
  lineHeatOperator period a t.toNNReal

@[simp] theorem realLineHeatOperator_apply (a : LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realLineHeatOperator period a t f = realLineHeat period a t f :=
  (realLineHeat_eq_toNNReal period a t f).symm

theorem realLineHeat_joint_continuous (a : LiftTangent) :
    Continuous (fun p : ℝ × LiftL2 period => realLineHeat period a p.1 p.2) := by
  simp_rw [realLineHeat_eq_toNNReal]
  exact (lineHeat_joint_continuous period a).comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

/-- Product rule for the real heat operator applied to a differentiable input curve. -/
theorem realLineHeat_varying_input (a : LiftTangent) (u : ℝ → LiftL2 period) (t : ℝ)
    (u' g h : LiftL2 period) (ht : 0 < t) (hu : HasDerivAt u u' t)
    (hD : HasDerivAt (lineOrbit period a (u t)) g 0)
    (hDD : HasDerivAt (lineOrbit period a g) h 0) :
    HasDerivAt (fun s => realLineHeat period a s (u s))
      (realLineHeat period a t u' + (1/2 : ℝ) • realLineHeat period a t h) t := by
  have h := hasDerivAt_apply (realLineHeatOperator period a) u t u'
    ((1/2 : ℝ) • realLineHeat period a t h) hu
    (by
        simpa only [realLineHeatOperator_apply] using realLineHeat_generator_pos period a (u t) g h
            hD hDD ht)
    (by
        simpa only [realLineHeatOperator_apply] using (realLineHeat_joint_continuous period
            a).continuousAt (x := (t,u')))
  simpa only [realLineHeatOperator_apply] using h

end EulerGaussianCylinderHeat
