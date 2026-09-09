/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator

@[expose] public section

/-! Actual cylinder witnesses for the total high-solve operator and its literal corrector. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerCylinderSmoothOrbit EulerLpCylinderPaths

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField)

def highSolveDerivative : VectorField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then (Classical.choice h).vectorDerivative I else 0

def highSolveCorrectorDerivative : VectorField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then (Classical.choice h).correctorDerivative I else 0

variable (h : Nonempty (Forcing P D raw))

def highSolveField : Field P D.T (highSolve P D I raw).1 where
  path := (Classical.choice h).fullVelocityPath I
  orbit := (Classical.choice h).velocityPath_orbit I
  raw_eq t x θ := by
    rw [highSolve_of_admissible D I raw h]
    exact ((Classical.choice h).vectorField I).raw_eq t x θ

def highSolveDerivativeField : Field P D.T (highSolveDerivative P D I raw) where
  path := (Classical.choice h).fullDerivativePath I
  orbit := (Classical.choice h).derivativePath_orbit I
  raw_eq t x θ := by
    simp only [highSolveDerivative, dite_eq_left h]
    exact ((Classical.choice h).vectorDerivativeField I).raw_eq t x θ

theorem highSolveField_time :
    TimeDerivative D.T_pos.le (highSolveField P D I raw h) (highSolveDerivativeField P D I raw h) :=
  (Classical.choice h).fullVelocityPath_time I

def highSolveCorrectorField : Field P D.T (D.curlCorrector P (highSolve P D I raw).1) where
  path := (Classical.choice h).correctorPath I
  orbit := (Classical.choice h).correctorPath_orbit I
  raw_eq t x θ := by
    rw [highSolve_of_admissible D I raw h]
    exact ((Classical.choice h).curlCorrectorField I).raw_eq t x θ

def highSolveCorrectorDerivativeField : Field P D.T (highSolveCorrectorDerivative P D I raw) where
  path := (Classical.choice h).correctorTimePath I
  orbit := (Classical.choice h).correctorTimePath_orbit I
  raw_eq t x θ := by
    simp only [highSolveCorrectorDerivative, dite_eq_left h]
    exact ((Classical.choice h).correctorDerivativeField I).raw_eq t x θ

theorem highSolveCorrectorField_time :
    TimeDerivative D.T_pos.le (highSolveCorrectorField P D I raw h)
      (highSolveCorrectorDerivativeField P D I raw h) :=
  (Classical.choice h).correctorPath_time I

theorem highSolveField_supported (t : Icc (0 : ℝ) D.T) :
    (highSolveField P D I raw h).path t ∈ Supported P Space D.support D.support_measurable :=
  ((Classical.choice h).velocityPath I t).property

theorem highSolveDerivativeField_supported (t : Icc (0 : ℝ) D.T) :
    (highSolveDerivativeField P D I raw h).path t ∈ Supported P Space D.support
      D.support_measurable :=
  ((Classical.choice h).derivativePath I t).property

theorem highSolveCorrectorField_supported (t : Icc (0 : ℝ) D.T) :
    (highSolveCorrectorField P D I raw h).path t ∈ Supported P Space D.support D.support_measurable
      :=
  (Classical.choice h).correctorPath_supported I t

theorem highSolveCorrectorDerivativeField_supported (t : Icc (0 : ℝ) D.T) :
    (highSolveCorrectorDerivativeField P D I raw h).path t ∈
      Supported P Space D.support D.support_measurable :=
  (Classical.choice h).correctorTimePath_supported I t

include h in
theorem highSolveCorrector_mean_zero (t : Icc (0 : ℝ) D.T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, D.curlCorrector P (highSolve P D I raw).1 (t,(x,θ))) = 0 := by
  rw [highSolve_of_admissible D I raw h]
  exact (Classical.choice h).curlCorrector_mean_zero I t x

end EulerTransversePacketProvider
