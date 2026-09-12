/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight

/-! Actual scalar time weighting commutes with cylinder inclusion, translations, and rectangular
multiplication. -/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerContinuousTimeWeight
open scoped BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (S : Set Space) (hS : MeasurableSet S) (g : C(K, ℝ))

theorem supportedMultiplier_weight (A : C(K, Space →ᵇ E →L[ℝ] F))
    (u : C(K, Supported period E S hS)) :
    supportedMultiplierMap period S hS A (weight g u) =
      weight g (supportedMultiplierMap period S hS A u) := by
  apply ContinuousMap.ext
  intro t
  exact (supportedOperatorMap period S hS (A t)).map_smul (g t) (u t)

theorem supportedMultiplier_normalize (hg : ∀ t, 0 < g t)
    (A : C(K, Space →ᵇ E →L[ℝ] F)) (u : C(K, Supported period E S hS)) :
    supportedMultiplierMap period S hS A (normalize g hg u) =
      normalize g hg (supportedMultiplierMap period S hS A u) :=
  supportedMultiplier_weight period S hS (reciprocal g hg) A u

theorem include_weight (u : C(K, Supported period E S hS)) :
    includePath period S hS (weight g u) = weight g (includePath period S hS u) := rfl

theorem include_normalize (hg : ∀ t, 0 < g t) (u : C(K, Supported period E S hS)) :
    includePath period S hS (normalize g hg u) = normalize g hg (includePath period S hS u) := rfl

theorem translate_weight (a : LiftTangent) (u : C(K, CylinderL2 period E)) :
    pathTranslate period a (weight g u) = weight g (pathTranslate period a u) := by
  apply ContinuousMap.ext
  intro t
  exact (translate period a).map_smul (g t) (u t)

theorem translate_normalize (hg : ∀ t, 0 < g t) (a : LiftTangent) (u : C(K, CylinderL2 period E)) :
    pathTranslate period a (normalize g hg u) = normalize g hg (pathTranslate period a u) :=
  translate_weight period (reciprocal g hg) a u

end EulerLpCylinderRectangular
