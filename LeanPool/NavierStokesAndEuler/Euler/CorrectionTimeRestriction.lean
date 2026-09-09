/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal

/-! Actual correction coefficient data restricted along continuous time maps. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionOperators

open Set EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerSobolevCoefficientPressure
  EulerQuadraticSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Restrict the actual spatial coefficient and its jet along a continuous parameter map. -/
def CoefficientPath.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (A : CoefficientPath period q T) (f : C(U, T)) : CoefficientPath period q U where
  coefficient t := A.coefficient (f t)
  jet t := A.jet (f t)
  continuous := A.continuous.comp f.continuous

/-- Restrict every actual coefficient, background field, and residual along the same time map. -/
def CorrectionData.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U, T)) : CorrectionData period q U where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := D.metric.comp period f
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos t := D.metric_pos (f t)
  linear := D.linear.comp period f
  quadratic i := (D.quadratic i).comp period f
  approximation := D.approximation.comp f
  residual := D.residual.comp f

/-- The restricted correction source is the original actual source at the restricted time. -/
theorem CorrectionData.comp_source {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U, T)) (hq : 6 ≤ q)
    (t : U) (u : SobolevSpace period (q + 1)) :
    ((D.comp period f).coefficients period hq).apply t u =
      (D.coefficients period hq).apply (f t) u := rfl

/-- Restricting the concrete data gives precisely the same nonlinear mild equation on a shorter
interval. -/
theorem CorrectionData.comp_quadraticDuhamel {q : ℕ} (hq : 6 ≤ q)
    (ν : ℝ) (hν : 0 < ν) {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (u₀ : SobolevSpace period (q + 1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (t : Icc (0 : ℝ) T) :
    quadraticDuhamel period ν hν hT le_rfl
        ((D.comp period (timeInclusion hTS)).coefficients period hq) u₀ u t =
      quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) u₀ u t := rfl

end EulerCorrectionOperators
