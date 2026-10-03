/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight

/-!
# The profile estimate belongs to the actual unnormalized PDE solution

The weighted construction is exactly division of the genuine solution with
physical forcing g f by g. This is an algebraic identity of continuous paths;
it does not differentiate g or introduce its extrema into any estimate.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerSourceCylinderForcing EulerSourceCylinderForward
  EulerSourceCylinderForwardSobolev EulerContinuousTimeWeight EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T, Supported period E S hS)) (a₀ : Supported period U S hS)

/-- The normalized coordinate estimate is for this exact raw Duhamel solution. -/
theorem coordinates_weight_eq :
    coordinates period S hS T hT Q Q₁ c hc hQ (weight (E := Supported period E S hS) g f) a₀ =
      weight (E := Supported period U S hS) g
        (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀) := by
  exact (congrArg ((evolution period T hT Q Q₁ c hc hQ S hS).solution · a₀)
    (supportedMultiplier_weight period S hS g (sourceForcing Q c hc hQ) f)).trans
      (weight_normalize (E := Supported period U S hS) g hg _).symm

/-- The physical reconstruction has the same exact profile identity. -/
theorem velocity_weight_eq :
    velocity period S hS T hT Q Q₁ c hc hQ (weight (E := Supported period E S hS) g f) a₀ =
      weight (E := Supported period E S hS) g
        (normalizedVelocity period T hT S hS Q Q₁ c hc hQ g hg f a₀) := by
  change supportedMultiplierMap (K := Icc (0 : ℝ) T) (E := U) (F := E) period S hS Q.field
      (coordinates period S hS T hT Q Q₁ c hc hQ
        (weight (E := Supported period E S hS) g f) a₀) =
    weight (E := Supported period E S hS) g
      (supportedMultiplierMap (K := Icc (0 : ℝ) T) (E := U) (F := E) period S hS Q.field
        (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀))
  exact (congrArg (supportedMultiplierMap (K := Icc (0 : ℝ) T) (E := U) (F := E) period S hS
      Q.field) (coordinates_weight_eq period S hS T hT Q Q₁ c hc hQ g hg f a₀)).trans
      (supportedMultiplier_weight period S hS g Q.field _)

/-- Therefore the proved fixed-radius bound is literally the normalized
full-cylinder orbit of the actual physical solution. -/
theorem normalized_full_velocity_eq :
    EulerContinuousTimeWeight.normalize (E := CylinderL2 period E) g hg
        (includePath (K := Icc (0 : ℝ) T) (V := E) period S hS
          (velocity period S hS T hT Q Q₁ c hc hQ
            (weight (E := Supported period E S hS) g f) a₀)) =
      includePath (K := Icc (0 : ℝ) T) (V := E) period S hS
        (normalizedVelocity period T hT S hS Q Q₁ c hc hQ g hg f a₀) := by
  exact (congrArg (fun x => EulerContinuousTimeWeight.normalize (E := CylinderL2 period E) g hg
      (includePath (K := Icc (0 : ℝ) T) (V := E) period S hS x))
      (velocity_weight_eq period S hS T hT Q Q₁ c hc hQ g hg f a₀)).trans
    ((congrArg (EulerContinuousTimeWeight.normalize (E := CylinderL2 period E) g hg)
      (include_weight period S hS g _)).trans (normalize_weight g hg _))

end EulerSourceCylinderEquation
