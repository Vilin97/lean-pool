/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderWeight

@[expose] public section

/-! The bounded time-right-side estimate applies to the actual PDE time derivative divided by g. -/

noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceCylinderTimeBounds EulerSourceCylinderForwardSobolev EulerContinuousTimeWeight
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported P E S hS)) (a₀ : Supported P U S hS)

theorem velocityDerivative_eq_physicalRhs :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ =
      physicalRhs P S hS Q Q₁ c hc hQ f (coordinates P S hS T hT Q Q₁ c hc hQ f a₀) := rfl

variable (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)

/-- This is A_t/g, obtained from the actual equation rather than differentiating A/g. -/
def normalizedVelocityDerivative : C(Icc (0 : ℝ) T,Supported P E S hS) :=
  physicalRhs P S hS Q Q₁ c hc hQ f
    (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀)

theorem velocityDerivative_weight_eq :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ =
      weight g (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) := by
  rw [velocityDerivative_eq_physicalRhs,coordinates_weight_eq]
  exact physicalRhs_weight P S hS Q Q₁ c hc hQ f _ g

theorem normalized_full_velocityDerivative_eq :
    normalize g hg (includePath P S hS
      (velocityDerivative P S hS T hT Q Q₁ c hc hQ (weight g f) a₀)) =
      includePath P S hS (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) := by
  rw [velocityDerivative_weight_eq,include_weight,normalize_weight]

end EulerSourceCylinderEquation
