/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowDeformation

/-! Actual continuous bounded coefficient paths for the graph-flow
displacement, velocity, and acceleration. No extra supremum estimate on
the time derivative of the lifted velocity is required. -/

@[expose] public section


noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerSmoothBanachFlow EulerSmoothFlowGevrey
  EulerGraphInvariantFlow EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)

/-- Cover displacement coefficient, given by `displacementCoefficient T G.time_nonneg G.A G.B
G.R G.B_nonneg G.R_pos G.small G.sup_bound`. -/
def coverDisplacementCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  displacementCoefficient T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound

/-- Cover velocity coefficient, given by `G.A.compDisplacement G.coverDisplacementCoefficient`. -/
def coverVelocityCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  G.A.compDisplacement G.coverDisplacementCoefficient

/-- Cover acceleration coefficient, given by `accelerationCoefficient T G.time_nonneg G.A G.B
G.R G.B_nonneg G.R_pos G.small G.sup_bound G.A₁`. -/
def coverAccelerationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  accelerationCoefficient T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound G.A₁

@[simp] theorem coverDisplacementCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverDisplacementCoefficient.field t x = (flowData T G.time_nonneg G.A).forward t x-x := rfl

@[simp] theorem coverVelocityCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverVelocityCoefficient.field t x = velocityFamily T G.time_nonneg G.A x t := by
  change G.A.field t (x+G.coverDisplacementCoefficient.field t x) = _
  rw [G.coverDisplacementCoefficient_apply]
  have he : x+((flowData T G.time_nonneg G.A).forward t x-x) =
      (flowData T G.time_nonneg G.A).forward t x := by abel
  rw [he]
  rfl

@[simp] theorem coverAccelerationCoefficient_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.coverAccelerationCoefficient.field t x = accelerationFamily T G.time_nonneg G.A G.A₁ x t :=
  accelerationCoefficient_apply T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small G.sup_bound
      G.A₁ t x

theorem coverDisplacementCoefficient_time : SmoothTimeField.TimeDerivative T G.time_nonneg
    G.coverDisplacementCoefficient G.coverVelocityCoefficient := by
  intro t x
  have he : (fun s => G.coverDisplacementCoefficient.realField T G.time_nonneg s x) =
      extendPath T G.time_nonneg (displacementFamily T G.time_nonneg G.A x) := rfl
  rw [he,G.coverVelocityCoefficient_apply]
  exact displacementFamily_time_derivative T G.time_nonneg G.A x t

theorem coverVelocityCoefficient_time : SmoothTimeField.TimeDerivative T G.time_nonneg
    G.coverVelocityCoefficient G.coverAccelerationCoefficient := by
  intro t x
  have he : (fun s => G.coverVelocityCoefficient.realField T G.time_nonneg s x) =
      extendPath T G.time_nonneg (velocityFamily T G.time_nonneg G.A x) := by
    funext s
    exact G.coverVelocityCoefficient_apply (projIcc 0 T G.time_nonneg s) x
  rw [he,G.coverAccelerationCoefficient_apply]
  exact velocityFamily_time_derivative T G.time_nonneg G.A G.A₁ G.time_derivative x t

/-- Physical displacement coefficient, given by `physicalCoefficient k m T
G.coverDisplacementCoefficient ell`. -/
def physicalDisplacementCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverDisplacementCoefficient ell

/-- Physical velocity coefficient, given by `physicalCoefficient k m T
G.coverVelocityCoefficient ell`. -/
def physicalVelocityCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverVelocityCoefficient ell

/-- Physical acceleration coefficient, given by `physicalCoefficient k m T
G.coverAccelerationCoefficient ell`. -/
def physicalAccelerationCoefficient (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  physicalCoefficient k m T G.coverAccelerationCoefficient ell

theorem physicalDisplacementCoefficient_time (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField.TimeDerivative T G.time_nonneg
      (G.physicalDisplacementCoefficient k m ell) (G.physicalVelocityCoefficient k m ell) :=
  physicalCoefficient_timeDerivative k m T G.time_nonneg
    G.coverDisplacementCoefficient G.coverVelocityCoefficient ell
        G.coverDisplacementCoefficient_time

theorem physicalVelocityCoefficient_time (k : ℝ) (m : Vector3) (ell : ℝ) :
    SmoothTimeField.TimeDerivative T G.time_nonneg
      (G.physicalVelocityCoefficient k m ell) (G.physicalAccelerationCoefficient k m ell) :=
  physicalCoefficient_timeDerivative k m T G.time_nonneg
    G.coverVelocityCoefficient G.coverAccelerationCoefficient ell G.coverVelocityCoefficient_time

theorem physicalDisplacementCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalDisplacementCoefficient k m ell).field t x = (G.displacementField k m ell hell
        t).field x := by
  rw [physicalDisplacementCoefficient, physicalCoefficient_apply,
      G.coverDisplacementCoefficient_apply]
  change ell • ((flowData T G.time_nonneg G.A).forward t _ - _).1 =
    ell • (displacement T G.time_nonneg G.A t _).1
  rw [displacement_eq]
  simp only [graphLinear_apply,EulerGraphPullback.graphMap_apply]

theorem physicalVelocityCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalVelocityCoefficient k m ell).field t x = (G.velocityField k m ell hell t).field x :=
        by
  rw [physicalVelocityCoefficient,physicalCoefficient_apply,G.coverVelocityCoefficient_apply]
  rfl

theorem physicalAccelerationCoefficient_eq (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalAccelerationCoefficient k m ell).field t x = (G.accelerationFieldL2 k m ell hell
        t).field x := by
  rw [physicalAccelerationCoefficient, physicalCoefficient_apply,
      G.coverAccelerationCoefficient_apply]
  rw [accelerationFamily_apply]
  rfl

end EulerPhysicalGraphFlowBounds.Data
