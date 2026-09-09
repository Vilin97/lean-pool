/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleTime
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-! Exact Jacobian composition for the child displacement. -/

noncomputable section

namespace EulerChildParticleTime

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem displacement_jacobian (P D : SmoothTimeField K E E) (t : K) (x : E) :
    ContinuousLinearMap.id ℝ E + fderiv ℝ ((displacement P D).field t : E → E) x =
      (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).comp
        (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x) := by
  have hi := (hasFDerivAt_id x).add ((D.smooth t).differentiable (by simp) x).hasFDerivAt
  have ho := (hasFDerivAt_id (x+D.field t x)).add
    ((P.smooth t).differentiable (by simp) (x+D.field t x)).hasFDerivAt
  have hc := ho.comp x hi
  have hh := (hasFDerivAt_id x).add
    (((displacement P D).smooth t).differentiable (by simp) x).hasFDerivAt
  apply hh.unique
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => map_composition P D t y)

theorem displacement_det_one [FiniteDimensional ℝ E]
    (P D : SmoothTimeField K E E) (t : K)
    (hP : ∀ y, (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) y).det=1)
    (hD : ∀ y, (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) y).det=1)
    (x : E) :
    (ContinuousLinearMap.id ℝ E + fderiv ℝ ((displacement P D).field t : E → E) x).det=1 := by
  rw [displacement_jacobian]
  change LinearMap.det
    ((ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).toLinearMap.comp
      (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x).toLinearMap)=1
  rw [LinearMap.det_comp]
  change (ContinuousLinearMap.id ℝ E + fderiv ℝ (P.field t : E → E) (x+D.field t x)).det *
    (ContinuousLinearMap.id ℝ E + fderiv ℝ (D.field t : E → E) x).det=1
  rw [hP,hD,mul_one]

end EulerChildParticleTime
