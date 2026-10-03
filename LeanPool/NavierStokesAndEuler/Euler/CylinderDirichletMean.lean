/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint
import LeanPool.NavierStokesAndEuler.Euler.LpOperatorFieldAlgebra

/-!
# Actual zero angular mean of the history solution

Angle-independent coefficients commute with the genuine cylinder average,
including the adjoint test maps. The constructed inverse and its continuous
velocity therefore preserve zero mean. No pointwise mean condition is assumed
on the solution.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderAngleAverage
  EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fullOperatorMap_adjoint (Q : Space →ᵇ U →L[ℝ] E) :
    adjoint (𝕜 := ℝ) (E := CylinderL2 P U) (F := CylinderL2 P E)
        (fullOperatorMap (E := U) (F := E) P Q) =
      fullOperatorMap (E := E) (F := U) P (adjointMap (α := Space) (U := U) (E := E) Q) :=
  EulerLpOperatorField.full_adjoint (liftMeasure P) (fieldLift (W := U →L[ℝ] E) P Q)

theorem average_fullOperator_back (Q : Space →ᵇ U →L[ℝ] E) (u : CylinderL2 P U) :
    fullOperatorMap (E := U) (F := E) P Q
        (adjoint (𝕜 := ℝ) (E := CylinderL2 P U) (F := CylinderL2 P U)
          (EulerCylinderAngleAverage.average (V := U) P) u) =
      adjoint (𝕜 := ℝ) (E := CylinderL2 P E) (F := CylinderL2 P E)
        (EulerCylinderAngleAverage.average (V := E) P)
        (fullOperatorMap (E := U) (F := E) P Q u) := by
  apply ext_inner_right ℝ
  intro v
  have hc := average_fullOperator P (adjointMap (α := Space) (U := U) (E := E) Q) v
  rw [← fullOperatorMap_adjoint] at hc
  exact (adjoint_inner_right _ _ v).symm.trans <| (adjoint_inner_left _ _ u).trans <|
    (congrArg (inner ℝ u) hc).trans <|
      (adjoint_inner_right _ u _).trans (adjoint_inner_left _ v _).symm

end EulerLpCylinderRectangular

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAngleAverage EulerTimeLp EulerTimeLpBoundedMap
  EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

theorem velocityPath_average (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.velocityPath P (timeLift T (EulerCylinderAngleAverage.average (V := E) P) f) t =
      EulerCylinderAngleAverage.average (V := U) P (D.velocityPath P f t) :=
  D.velocityPath_intertwines P D (EulerCylinderAngleAverage.average P)
    (EulerCylinderAngleAverage.average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem accelerationPath_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.accelerationPath P (pathAverage (K := Icc (0 : ℝ) T) (V := E) P f) t =
      EulerCylinderAngleAverage.average (V := U) P (D.accelerationPath P f t) :=
  D.accelerationPath_intertwines P D (EulerCylinderAngleAverage.average P)
    (EulerCylinderAngleAverage.average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem physicalVelocity_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.physicalVelocity P (pathAverage (K := Icc (0 : ℝ) T) (V := E) P f) t =
      EulerCylinderAngleAverage.average (V := E) P (D.physicalVelocity P f t) :=
  D.physicalVelocity_intertwines P D (EulerCylinderAngleAverage.average P)
    (EulerCylinderAngleAverage.average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem physicalDerivative_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.physicalDerivative P (pathAverage (K := Icc (0 : ℝ) T) (V := E) P f) t =
      EulerCylinderAngleAverage.average (V := E) P (D.physicalDerivative P f t) :=
  D.physicalDerivative_intertwines P D (EulerCylinderAngleAverage.average P)
    (EulerCylinderAngleAverage.average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem velocityPath_pathLp_zero (t : Icc (0 : ℝ) T) :
    D.velocityPath P (pathLp T D.time_pos.le 0) t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator (E := CylinderL2 P E) T D.time_pos.le)
  simp only [hz, map_zero, ContinuousMap.zero_apply]

theorem accelerationPath_zero (t : Icc (0 : ℝ) T) : D.accelerationPath P 0 t = 0 := by
  have h := EulerContinuousGramAcceleration.accelerationPath_apply T (D.frame P)
    (D.frameDerivative P) D.lower D.lower_pos (D.frame_lower P)
    (D.velocityPath P (pathLp T D.time_pos.le 0)) 0 t
  simp only [D.velocityPath_pathLp_zero P t, ContinuousMap.zero_apply, map_zero, smul_zero,
    sub_zero] at h
  exact h

theorem physicalVelocity_zero (t : Icc (0 : ℝ) T) : D.physicalVelocity P 0 t = 0 :=
  (congrArg (D.frame P t) (D.velocityPath_pathLp_zero P t)).trans (map_zero _)

theorem physicalDerivative_zero (t : Icc (0 : ℝ) T) : D.physicalDerivative P 0 t = 0 := by
  change D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le 0) t) +
    D.frame P t (D.accelerationPath P 0 t) = 0
  simp only [D.velocityPath_pathLp_zero P t, D.accelerationPath_zero P t, map_zero, add_zero]

variable (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
  (hf : ∀ t, EulerCylinderAngleAverage.average (V := E) P (f t) = 0)

omit [CompleteSpace E] in
include hf in
private theorem averagedPath_zero : pathAverage (K := Icc (0 : ℝ) T) (V := E) P f = 0 := by
  apply ContinuousMap.ext
  intro t
  exact hf t

include hf in
theorem velocityPath_mean_zero (t : Icc (0 : ℝ) T) :
    EulerCylinderAngleAverage.average (V := U) P
      (D.velocityPath P (pathLp T D.time_pos.le f) t) = 0 := by
  have hz : timeLift T (EulerCylinderAngleAverage.average (V := E) P)
      (pathLp T D.time_pos.le f) = 0 :=
    (pathLp_timeLift T D.time_pos.le _ f).symm.trans <|
      (congrArg (pathLp T D.time_pos.le) (averagedPath_zero P f hf)).trans
        (map_zero (pathLpOperator (E := CylinderL2 P E) T D.time_pos.le))
  exact (D.velocityPath_average P (pathLp T D.time_pos.le f) t).symm.trans
    (by simp only [hz, map_zero, ContinuousMap.zero_apply])

include hf in
theorem accelerationPath_mean_zero (t : Icc (0 : ℝ) T) :
    EulerCylinderAngleAverage.average (V := U) P (D.accelerationPath P f t) = 0 := by
  rw [← D.accelerationPath_average P f t,averagedPath_zero P f hf,D.accelerationPath_zero P t]

include hf in
theorem physicalVelocity_mean_zero (t : Icc (0 : ℝ) T) :
    EulerCylinderAngleAverage.average (V := E) P (D.physicalVelocity P f t) = 0 := by
  rw [← D.physicalVelocity_average P f t,averagedPath_zero P f hf,D.physicalVelocity_zero P t]

include hf in
theorem physicalDerivative_mean_zero (t : Icc (0 : ℝ) T) :
    EulerCylinderAngleAverage.average (V := E) P (D.physicalDerivative P f t) = 0 := by
  rw [← D.physicalDerivative_average P f t,averagedPath_zero P f hf,D.physicalDerivative_zero P t]

end EulerCylinderDirichlet.Coefficients
