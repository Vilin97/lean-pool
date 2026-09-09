/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageEvolution

/-! The actual source transverse solve preserves the angular zero mode constraint. -/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceForwardCoefficient EulerSourceCylinderForcing
  EulerSourceCylinderForward EulerCylinderAngleAverage
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

theorem projectedForcing_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0) (t : Icc (0 : ℝ) T) :
    average P (projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) = 0 := by
  change average P (fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = 0
  rw [average_fullOperator, hf t, map_zero]

/-- The real Gram-projected Duhamel coordinate solution has zero angular mean. -/
theorem coordinates_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) = 0 :=
  solution_full_average_zero P S hS T hT (sourceGenerator Q Q₁ c hc hQ)
    (evolution P T hT Q Q₁ c hc hQ S hS)
    (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_average_zero P S hS T Q c hc hQ f hf) ha₀ t

/-- Physical reconstruction by the true frame preserves the same zero mode. -/
theorem velocity_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) = 0 := by
  change average P (fullOperatorMap P (Q.field t)
    (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = 0
  rw [average_fullOperator, coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    map_zero]

theorem coordinateDerivative_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) = 0 := by
  change average P (fullOperatorMap P (sourceGenerator Q Q₁ c hc hQ t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
    fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = 0
  rw [map_add, average_fullOperator, average_fullOperator,
    coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t, hf t,
    map_zero, map_zero, add_zero]

/-- The actual within-time derivative also has zero mean, as follows from its equation. -/
theorem velocityDerivative_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) = 0 := by
  change average P (fullOperatorMap P (Q₁.field t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
    fullOperatorMap P (Q.field t)
      (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = 0
  rw [map_add, average_fullOperator, average_fullOperator,
    coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    coordinateDerivative_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    map_zero, map_zero, add_zero]

end EulerSourceCylinderEquation
