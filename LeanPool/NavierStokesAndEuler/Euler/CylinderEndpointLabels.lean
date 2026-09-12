/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseSourceCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates

/-! Evaluation of the actual cylinder coefficients at a spatial label. -/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerVolterraConvolution
  EulerTransverseSourceCoefficientPath EulerTransverseEndpointCoordinates
open scoped BoundedContinuousFunction

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- Label frame, given by `pathEvaluation x D.Q`. -/
def labelFrame (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q
/-- Label frame derivative, given by `pathEvaluation x D.Q₁`. -/
def labelFrameDerivative (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q₁
/-- Label frame second, given by `pathEvaluation x D.Q₂`. -/
def labelFrameSecond (x : Space) : C(Icc (0 : ℝ) T,U →L[ℝ] E) := pathEvaluation x D.Q₂
/-- Label hessian, given by `pathEvaluation x D.H`. -/
def labelHessian (x : Space) : C(Icc (0 : ℝ) T,E →L[ℝ] E) := pathEvaluation x D.H

omit [CompleteSpace U] [CompleteSpace E] in
theorem labelFrame_lower (x : Space) (t : Icc (0 : ℝ) T) (v : U) :
    D.lower*‖v‖^2 ≤ ‖D.labelFrame x t v‖^2 := D.lower_bound t x v

omit [CompleteSpace U] [CompleteSpace E] in
theorem labelFrame_derivative (x : Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.labelFrame x))
      (D.labelFrameDerivative x t) (Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt (fun s => D.Q (projIcc 0 T D.time_pos.le s) x)
    (D.Q₁ t x) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem D.time_pos.le t.property] using D.derivative t t.property x

omit [CompleteSpace U] [CompleteSpace E] in
theorem labelFrame_second_derivative (x : Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.labelFrameDerivative x))
      (D.labelFrameSecond x t) (Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt (fun s => D.Q₁ (projIcc 0 T D.time_pos.le s) x)
    (D.Q₂ t x) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem D.time_pos.le t.property] using D.second_derivative t
      t.property x

omit [CompleteSpace U] [CompleteSpace E] in
theorem labelFrame_equation (x : Space) (t : Icc (0 : ℝ) T) :
    D.labelFrameSecond x t = -((D.labelHessian x t).comp (D.labelFrame x t)) := by
  apply ContinuousLinearMap.ext
  intro v
  exact D.jacobi t x v

omit [CompleteSpace U] [CompleteSpace E] in
theorem labelHessian_upper (x : Space) (t : Icc (0 : ℝ) T) (v : E) :
    ⟪D.labelHessian x t v,v⟫_ℝ ≤ D.potential*‖v‖^2 := D.potential_bound t x v

/-- The already constructed finite-dimensional stationary history, at this
label, applied to an ordinary terminal coordinate. -/
def labelCoordinate (x : Space) : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  continuousCoordinateVelocity T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small

/-- Label velocity, constructed using `historyVelocity`. -/
def labelVelocity (x : Space) : U →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  historyVelocity T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small

theorem labelVelocity_apply (x : Space) (Y : U) (t : Icc (0 : ℝ) T) :
    D.labelVelocity x Y t = D.Q t x (D.labelCoordinate x Y t) := rfl

end EulerCylinderDirichlet.Coefficients
