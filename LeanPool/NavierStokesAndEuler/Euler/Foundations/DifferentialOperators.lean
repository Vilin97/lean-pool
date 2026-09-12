/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Coordinate trace and divergence on the physical three-dimensional Euclidean space. -/

@[expose] public section

noncomputable section

namespace EulerSmoothLimit

/-- The physical three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The trace of a continuous linear map, written in the standard Euclidean coordinates. -/
noncomputable def coordinateTrace : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single i 1))

/-- The coordinate formula is exactly the basis-independent linear-algebraic trace. -/
theorem coordinateTrace_eq_linearTrace (A : Space →L[ℝ] Space) :
    coordinateTrace A = LinearMap.trace ℝ Space A.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [coordinateTrace, Matrix.trace, LinearMap.toMatrix_apply]

/-- Classical divergence, defined canonically as the trace of the Fréchet derivative. -/
noncomputable def divergence (f : Space → Space) (x : Space) : ℝ :=
  LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap

theorem divergence_eq_coordinate_sum (f : Space → Space) (x : Space) :
    divergence f x = ∑ i : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) i := by
  rw [divergence, ← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace]

theorem divergence_eq_trace (f : Space → Space) (x : Space) :
    divergence f x = LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap :=
  rfl

end EulerSmoothLimit
