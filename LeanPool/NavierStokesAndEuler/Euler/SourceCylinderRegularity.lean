/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderUnweightedForward

@[expose] public section

/-!
# Genuine mixed regularity of the solved physical forward fields

The actual coordinate solve and its ordinary right side have smooth mixed
translation orbits. Applying the physical frame then gives this same
regularity for the velocity and its true time derivative. These statements
are proved from the data, not included in the solution interface.
-/

noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerSourceCylinderForcing
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported period E S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))

include hSc hf ha₀

theorem coordinates_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (coordinates period S hS T hT Q Q₁ c hc hQ f a₀))) :=
  EulerLpCylinderRegularForward.unweighted_solution_contDiff period T hT S hS hSc
    (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ)
    (projectedForcing period S hS Q c hc hQ f) a₀
    (projectedForcing_contDiff period S hS Q c hc hQ f hf) ha₀

theorem coordinateDerivative_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀))) := by
  have hu := coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have hp := supported_product_orbit_contDiff period (sourceGenerator Q Q₁ c hc hQ)
    (sourceGenerator_translation_contDiff Q Q₁ c hc hQ) S hS
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) hu
  have hpf := projectedForcing_contDiff period S hS Q c hc hQ f hf
  simpa only [coordinateDerivative,map_add] using hp.add hpf

theorem velocity_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀))) :=
  physicalVelocity_contDiff period S hS Q (coordinates period S hS T hT Q Q₁ c hc hQ f a₀)
    (coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)

theorem velocityDerivative_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀))) := by
  have hu := coordinates_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have ha := coordinateDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀
  have h₁ := supported_product_orbit_contDiff period Q₁.field Q₁.translation_contDiff S hS
    (coordinates period S hS T hT Q Q₁ c hc hQ f a₀) hu
  have h₂ := supported_product_orbit_contDiff period Q.field Q.translation_contDiff S hS
    (coordinateDerivative period S hS T hT Q Q₁ c hc hQ f a₀) ha
  simpa only [velocityDerivative,map_add] using h₁.add h₂

end EulerSourceCylinderEquation
