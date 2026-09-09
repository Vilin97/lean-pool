/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureField
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderWeight

/-!
# The pressure estimate is for the actual normalized PDE pressure

All identities are algebraic identities of genuine continuous L² paths.
They use no derivative, extremum, or reciprocal bound for the time profile.
-/

@[expose] public section


noncomputable section

namespace EulerSourceNormalResidualBounds

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerSourceNormalCoefficient EulerCylinderScalarPrimitive EulerContinuousTimeWeight
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (M : SmoothCoefficientPath K (Space →L[ℝ] Space)) (m : SmoothCoefficientPath K Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)
  (g : C(K, ℝ)) (f v : C(K, CylinderL2 P Space))

theorem sourceResidual_weight :
    sourceResidual P M m cm hcm hm (weight g f) (weight g v) =
      weight g (sourceResidual P M m cm hcm hm f v) := by
  apply ContinuousMap.ext
  intro t
  change fullOperatorMap P (normalFunctional m cm hcm hm t)
      (g t • f t - (2 : ℝ) • fullOperatorMap P (M.field t) (g t • v t)) =
    g t • fullOperatorMap P (normalFunctional m cm hcm hm t)
      (f t - (2 : ℝ) • fullOperatorMap P (M.field t) (v t))
  simp only [map_sub, map_smul, smul_sub, smul_smul]
  rw [mul_comm (2 : ℝ) (g t)]

theorem sourcePressure_weight :
    sourcePressure P M m cm hcm hm (weight g f) (weight g v) =
      weight g (sourcePressure P M m cm hcm hm f v) := by
  unfold sourcePressure
  rw [sourceResidual_weight]
  apply ContinuousMap.ext
  intro t
  exact (primitive P).map_smul (g t) (sourceResidual P M m cm hcm hm f v t)

end EulerSourceNormalResidualBounds

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceCylinderForwardSobolev
  EulerSourceNormalResidualBounds EulerContinuousTimeWeight
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P Space S hS)) (a₀ : Supported P U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖ ^ 2)

/-- The bounded pressure used in the coefficient estimate is exactly the PDE pressure. -/
theorem pressurePath_eq_sourcePressure :
    pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm =
      sourcePressure P M m cm hcm hm (includePath P S hS f)
        (includePath P S hS (velocity P S hS T hT Q Q₁ c hc hQ f a₀)) := rfl

variable (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

/-- The actual pressure path divided by g, written in terms of the normalized
physical forcing and the already constructed normalized physical velocity. -/
def normalizedPressure : C(Icc (0 : ℝ) T,CylinderL2 P ℝ) :=
  sourcePressure P M m cm hcm hm (includePath P S hS f)
    (includePath P S hS (normalizedVelocity P T hT S hS Q Q₁ c hc hQ g hg f a₀))

theorem pressurePath_weight_eq :
    pressurePath P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ M m cm hcm hm =
      weight g (normalizedPressure P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm g hg) := by
  rw [pressurePath_eq_sourcePressure, velocity_weight_eq, include_weight, include_weight]
  exact sourcePressure_weight P M m cm hcm hm g _ _

theorem normalized_full_pressure_eq :
    normalize g hg (pressurePath P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ M m cm hcm hm) =
      normalizedPressure P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm g hg := by
  rw [pressurePath_weight_eq, normalize_weight]

end EulerSourceCylinderEquation
