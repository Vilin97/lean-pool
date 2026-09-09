/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedClassical
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime
import LeanPool.NavierStokesAndEuler.Euler.LpOperatorFieldAlgebra

/-!
# The actual history inverse on the spatial-angular cylinder

The data below are pointwise coefficient hypotheses: a lower frame bound,
the two time derivatives of the frame, its Jacobi equation and the Hessian
upper bound. They construct the Dirichlet inverse on genuine cylinder L².
Pointwise tangency is encoded by the frame range, not by orthogonality to one
vector in L². No solution or operator inverse is part of the input data.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerVolterraConvolution EulerTimeH1FrameTransport
  EulerTransverseFixedSpaceInverse EulerTransverseGramInverse
open scoped BoundedContinuousFunction

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pointwise moving-frame data for the genuine history problem. -/
structure Coefficients (T : ℝ) (U E : Type*)
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  time_pos : 0 < T
  /-- Scale parameter of `Coefficients`, of type `C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)`. -/
  Q : C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)
  /-- Q₁ of `Coefficients`, of type `C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)`. -/
  Q₁ : C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)
  /-- Q₂ of `Coefficients`, of type `C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)`. -/
  Q₂ : C(Icc (0 : ℝ) T,Space →ᵇ U →L[ℝ] E)
  /-- H of `Coefficients`, of type `C(Icc (0 : ℝ) T,Space →ᵇ E →L[ℝ] E)`. -/
  H : C(Icc (0 : ℝ) T,Space →ᵇ E →L[ℝ] E)
  /-- Lower of `Coefficients`, of type `ℝ`. -/
  lower : ℝ
  lower_pos : 0 < lower
  lower_bound : ∀ t x v, lower*‖v‖^2 ≤ ‖Q t x v‖^2
  derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath (Y := Space →ᵇ U →L[ℝ] E) T time_pos.le Q s x)
      (extendPath (Y := Space →ᵇ U →L[ℝ] E) T time_pos.le Q₁ t x) (Icc (0 : ℝ) T) t
  second_derivative : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath (Y := Space →ᵇ U →L[ℝ] E) T time_pos.le Q₁ s x)
      (extendPath (Y := Space →ᵇ U →L[ℝ] E) T time_pos.le Q₂ t x) (Icc (0 : ℝ) T) t
  jacobi : ∀ t x v, Q₂ t x v = -(H t x (Q t x v))
  /-- Potential of `Coefficients`, of type `ℝ`. -/
  potential : ℝ
  potential_nonneg : 0 ≤ potential
  potential_bound : ∀ t x v, ⟪H t x v,v⟫_ℝ ≤ potential*‖v‖^2
  small : potential*(T^2/2) ≤ 1/2

namespace Coefficients

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} (D : Coefficients T U E)

/-- Frame, given by `fullPathMap P D.Q`. -/
def frame : C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := fullPathMap P D.Q
/-- Frame derivative, given by `fullPathMap P D.Q₁`. -/
def frameDerivative : C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := fullPathMap P D.Q₁
/-- Frame second, given by `fullPathMap P D.Q₂`. -/
def frameSecond : C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := fullPathMap P D.Q₂
/-- Hessian, given by `fullPathMap P D.H`. -/
def hessian : C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := fullPathMap P D.H

omit [CompleteSpace U] [CompleteSpace E] in
theorem frame_lower (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.lower*‖u‖^2 ≤ ‖D.frame P t u‖^2 :=
  EulerLpOperatorField.full_norm_sq_lower (liftMeasure P) (fieldLift P (D.Q t))
    D.lower D.lower_pos.le (fun x v => D.lower_bound t x.1 v) u

omit [CompleteSpace U] in
theorem frame_derivative (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.frame P))
      (D.frameDerivative P t) (Icc (0 : ℝ) T) t :=
  fullPath_hasDerivWithinAt P T D.time_pos.le D.Q D.Q₁ D.derivative t

omit [CompleteSpace U] in
theorem frame_second_derivative (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.frameDerivative P))
      (D.frameSecond P t) (Icc (0 : ℝ) T) t :=
  fullPath_hasDerivWithinAt P T D.time_pos.le D.Q₁ D.Q₂ D.second_derivative t

omit [CompleteSpace U] [CompleteSpace E] in
theorem frame_equation (t : Icc (0 : ℝ) T) :
    D.frameSecond P t = -((D.hessian P t).comp (D.frame P t)) :=
  EulerLpOperatorField.full_eq_neg_comp (liftMeasure P) (fieldLift P (D.Q₂ t))
    (fieldLift P (D.H t)) (fieldLift P (D.Q t)) (fun x v => D.jacobi t x.1 v)

omit [CompleteSpace U] [CompleteSpace E] in
theorem hessian_upper (t : Icc (0 : ℝ) T) (u : CylinderL2 P E) :
    ⟪D.hessian P t u,u⟫_ℝ ≤ D.potential*‖u‖^2 :=
  EulerLpOperatorField.full_quadratic_upper (liftMeasure P) (fieldLift P (D.H t))
    D.potential (fun x v => D.potential_bound t x.1 v) u

/-- The fixed-space coercive construction, with every L² hypothesis derived
from the actual pointwise fields. -/
def coordinateSolver : TimeLp T (CylinderL2 P E) →L[ℝ]
    zeroTraceDerivatives (U := CylinderL2 P U) T D.time_pos.le :=
  fixedFrameSolver T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- Velocity Lᵖ, constructed using `EulerTransverseFixedEvolution.velocityLp`. -/
def velocityLp : TimeLp T (CylinderL2 P E) →L[ℝ] TimeLp T (CylinderL2 P U) :=
  EulerTransverseFixedEvolution.velocityLp T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- Acceleration Lᵖ, constructed using `EulerTransverseFixedEvolution.accelerationLp`. -/
def accelerationLp : TimeLp T (CylinderL2 P E) →L[ℝ] TimeLp T (CylinderL2 P U) :=
  EulerTransverseFixedEvolution.accelerationLp T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- Velocity path, constructed using `EulerTransverseFixedEvolution.velocityPath`. -/
def velocityPath : TimeLp T (CylinderL2 P E) →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  EulerTransverseFixedEvolution.velocityPath T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- Acceleration path, constructed using `EulerTransverseFixedEvolution.classicalAcceleration`. -/
def accelerationPath (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) : C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  EulerTransverseFixedEvolution.classicalAcceleration T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

/-- Displacement path, constructed using `EulerTransverseFixedEvolution.displacementPath`. -/
def displacementPath (f : TimeLp T (CylinderL2 P E)) : C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  EulerTransverseFixedEvolution.displacementPath T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

/-- Physical velocity, constructed using `EulerTransverseFixedEvolution.physicalVelocityPath`. -/
def physicalVelocity (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) : C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  EulerTransverseFixedEvolution.physicalVelocityPath T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

/-- Physical derivative, constructed using
`EulerTransverseFixedEvolution.physicalDerivativePath`. -/
def physicalDerivative (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) : C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  EulerTransverseFixedEvolution.physicalDerivativePath T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

theorem displacement_initial (f : TimeLp T (CylinderL2 P E)) :
    D.displacementPath P f ⟨0,le_rfl,D.time_pos.le⟩ = 0 :=
  EulerTransverseFixedEvolution.displacementPath_initial T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

theorem displacement_terminal (f : TimeLp T (CylinderL2 P E)) :
    D.displacementPath P f ⟨T,D.time_pos.le,le_rfl⟩ = 0 :=
  EulerTransverseFixedEvolution.displacementPath_terminal T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f

theorem velocity_hasDerivWithinAt (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.velocityPath P (pathLp T D.time_pos.le f)))
      (D.accelerationPath P f t) (Icc (0 : ℝ) T) t :=
  EulerTransverseFixedEvolution.velocityPath_hasDerivWithinAt T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (D.frameSecond P) (D.frame_second_derivative P) (D.frame_equation P) D.time_pos f t

theorem displacement_hasDerivWithinAt (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.displacementPath P (pathLp T D.time_pos.le f)))
      (D.velocityPath P (pathLp T D.time_pos.le f) t) (Icc (0 : ℝ) T) t :=
  EulerTransverseFixedEvolution.displacementPath_hasDerivWithinAt T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (D.frameSecond P) (D.frame_second_derivative P) (D.frame_equation P) D.time_pos f t

theorem physicalVelocity_hasDerivWithinAt (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T)
    :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.physicalVelocity P f))
      (D.physicalDerivative P f t) (Icc (0 : ℝ) T) t :=
  EulerTransverseFixedEvolution.physicalVelocityPath_hasDerivWithinAt T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (D.frameSecond P) (D.frame_second_derivative P) (D.frame_equation P) D.time_pos f t

/-- The exact projected equation (10), now as an equality of actual spatial -
angular L² fields at every time. -/
theorem projected_equation (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    gram (D.frame P t) (D.accelerationPath P f t) =
      (D.frame P t).adjoint (f t-(2 : ℝ) • D.frameDerivative P t
        (D.velocityPath P (pathLp T D.time_pos.le f) t)) :=
  EulerTransverseFixedEvolution.classicalAcceleration_equation T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small f t

end Coefficients
end EulerCylinderDirichlet
