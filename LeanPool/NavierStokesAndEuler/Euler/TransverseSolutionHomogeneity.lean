/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation

/-! Exact scalar homogeneity of the constructed history and forward paths. -/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerTimeLp EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E) (a : ℝ) (f : C(Icc (0 : ℝ) T, CylinderL2 P E))

theorem continuousVelocity_smul :
    D.velocityPath P (pathLp T D.time_pos.le (a • f)) =
      a • D.velocityPath P (pathLp T D.time_pos.le f) := by
  rw [pathLp_smul,map_smul]

theorem accelerationPath_smul : D.accelerationPath P (a • f) = a • D.accelerationPath P f := by
  apply ContinuousMap.ext
  intro t
  change gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
    ((D.frame P t).adjoint ((a • f) t-(2 : ℝ) • D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t))) =
    a • gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
      ((D.frame P t).adjoint (f t-(2 : ℝ) • D.frameDerivative P t
        (D.velocityPath P (pathLp T D.time_pos.le f) t)))
  rw [D.continuousVelocity_smul P a f]
  simp only [ContinuousMap.smul_apply,map_smul]
  rw [smul_comm (2 : ℝ) a,← smul_sub,map_smul,map_smul]

theorem physicalVelocity_smul : D.physicalVelocity P (a • f) = a • D.physicalVelocity P f := by
  apply ContinuousMap.ext
  intro t
  change D.frame P t (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t) =
    a • D.frame P t (D.velocityPath P (pathLp T D.time_pos.le f) t)
  rw [D.continuousVelocity_smul P a f,ContinuousMap.smul_apply,map_smul]

theorem physicalDerivative_smul : D.physicalDerivative P (a • f) = a • D.physicalDerivative P f :=
    by
  apply ContinuousMap.ext
  intro t
  change D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le (a • f)) t) +
    D.frame P t (D.accelerationPath P (a • f) t) =
    a • (D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le f) t) +
      D.frame P t (D.accelerationPath P f t))
  rw [D.continuousVelocity_smul P a f,D.accelerationPath_smul P a f]
  simp only [ContinuousMap.smul_apply,map_smul,smul_add]

end EulerCylinderDirichlet.Coefficients

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerLpCylinderRectangular EulerSourceCylinderForward
  EulerSourceCylinderForcing EulerLinearDuhamel
open scoped BoundedContinuousFunction

private theorem solution_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, X →L[ℝ] X)}
    (W : Evolution T hT B) (a : ℝ) (f : C(Icc (0 : ℝ) T, X)) (a₀ : X) :
    W.solution (a • f) (a • a₀) = a • W.solution f a₀ := by
  simp only [Evolution.solution_eq_operators, map_smul, smul_add]

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (a : ℝ) (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

theorem coordinates_smul :
    coordinates P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • coordinates P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold coordinates projectedForcing
  rw [map_smul]
  exact solution_smul (X := Supported P U S hS) _ a _ a₀

theorem velocity_smul :
    velocity P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • velocity P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold velocity physicalVelocity
  rw [coordinates_smul,map_smul]

theorem velocityDerivative_smul :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ (a • f) (a • a₀) =
      a • velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ := by
  unfold velocityDerivative coordinateDerivative projectedForcing
  rw [coordinates_smul]
  simp only [map_smul,smul_add,map_add]

end EulerSourceCylinderEquation
