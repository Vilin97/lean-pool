/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint

/-! The actual history solve commutes with all mixed spatial/angular translations. -/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerLiftedGradientSpace EulerLpCylinderTranslation
    EulerMeanCoefficients
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fullOperator_translation_back (a : LiftTangent) (Q : EulerSmoothLimit.Space →ᵇ U →L[ℝ] E)
    (u : CylinderL2 P U) :
    fullOperatorMap P Q (((translate P a).toContinuousLinearMap).adjoint u) =
      ((translate P a).toContinuousLinearMap).adjoint
        (fullOperatorMap P (translated Q a.1) u) := by
  rw [translate_adjoint,translate_adjoint]
  change fullOperatorMap P Q (translate P (-a) u) =
    translate P (-a) (fullOperatorMap P (translated Q a.1) u)
  have he := congrArg (translate (V := E) P (-a))
    (fullOperator_translation P a Q (translate P (-a) u))
  simpa only [translate_add,add_neg_cancel,neg_add_cancel,translate_zero] using he.symm

end EulerLpCylinderRectangular

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerVolterraConvolution EulerMeanCoefficients
open scoped BoundedContinuousFunction

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- The actual translated coefficient fields, with their inherited pointwise
time derivatives and unchanged coercivity constants. -/
def shifted (a : Space) : Coefficients T U E where
  time_pos := D.time_pos
  Q := translateCoefficientPath D.Q a
  Q₁ := translateCoefficientPath D.Q₁ a
  Q₂ := translateCoefficientPath D.Q₂ a
  H := translateCoefficientPath D.H a
  lower := D.lower
  lower_pos := D.lower_pos
  lower_bound t x v := D.lower_bound t (x+a) v
  derivative t ht x := D.derivative t ht (x+a)
  second_derivative t ht x := D.second_derivative t ht (x+a)
  jacobi t x v := D.jacobi t (x+a) v
  potential := D.potential
  potential_nonneg := D.potential_nonneg
  potential_bound t x v := D.potential_bound t (x+a) v
  small := D.small

variable (P : ℝ) [Fact (0 < P)]

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_frame (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    (D.shifted a.1).frame P t (translate P a u) = translate P a (D.frame P t u) :=
  fullOperator_translation P a (D.Q t) u

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_frameDerivative (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    (D.shifted a.1).frameDerivative P t (translate P a u) = translate P a (D.frameDerivative P t u)
        :=
  fullOperator_translation P a (D.Q₁ t) u

omit [CompleteSpace U] [CompleteSpace E] in
theorem shifted_hessian (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P E) :
    (D.shifted a.1).hessian P t (translate P a u) = translate P a (D.hessian P t u) :=
  fullOperator_translation P a (D.H t) u

theorem shifted_frame_back (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frame P t (((translate P a).toContinuousLinearMap).adjoint u) =
      ((translate P a).toContinuousLinearMap).adjoint ((D.shifted a.1).frame P t u) :=
  fullOperator_translation_back P a (D.Q t) u

theorem shifted_frameDerivative_back (a : LiftTangent) (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frameDerivative P t (((translate P a).toContinuousLinearMap).adjoint u) =
      ((translate P a).toContinuousLinearMap).adjoint ((D.shifted a.1).frameDerivative P t u) :=
  fullOperator_translation_back P a (D.Q₁ t) u

theorem velocityLp_translation (a : LiftTangent) (f : TimeLp T (CylinderL2 P E)) :
    (D.shifted a.1).velocityLp P (timeLift T (translate P a).toContinuousLinearMap f) =
      timeLift T (translate P a).toContinuousLinearMap (D.velocityLp P f) :=
  D.velocityLp_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f

theorem velocityPath_translation (a : LiftTangent) (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ)
    T) :
    (D.shifted a.1).velocityPath P (timeLift T (translate P a).toContinuousLinearMap f) t =
      translate P a (D.velocityPath P f t) :=
  D.velocityPath_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f t

theorem continuousVelocity_translation (a : LiftTangent)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    (D.shifted a.1).velocityPath P (pathLp T D.time_pos.le (pathTranslate P a f)) t =
      translate P a (D.velocityPath P (pathLp T D.time_pos.le f) t) :=
  D.continuousVelocity_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f t

theorem accelerationPath_translation (a : LiftTangent)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    (D.shifted a.1).accelerationPath P (pathTranslate P a f) t = translate P a (D.accelerationPath
        P f t) :=
  D.accelerationPath_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f t

theorem physicalVelocity_translation (a : LiftTangent)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    (D.shifted a.1).physicalVelocity P (pathTranslate P a f) t = translate P a (D.physicalVelocity
        P f t) :=
  D.physicalVelocity_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f t

theorem physicalDerivative_translation (a : LiftTangent)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    (D.shifted a.1).physicalDerivative P (pathTranslate P a f) t = translate P a
        (D.physicalDerivative P f t) :=
  D.physicalDerivative_intertwines P (D.shifted a.1)
    (translate P a).toContinuousLinearMap (translate P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f t

end EulerCylinderDirichlet.Coefficients
