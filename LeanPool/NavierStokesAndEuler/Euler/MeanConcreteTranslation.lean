/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientSpatial
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryTranslation

@[expose] public section

/-!
# Identification of the translated mean coefficients

Literal L² operator conjugation agrees with translation of the actual bounded
matrix fields and the actual smooth compact cutoffs in the Newtonian boundary
operator. These identities connect the fixed inverse to spatial coefficient
calculus.
-/

noncomputable section

namespace EulerMeanOperatorTranslation

open ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerMeanCoefficients
  EulerMeanBoundary

/-- Conjugation of the genuine multiplier is multiplication by the translated field. -/
theorem translateOperator_multiplier (a : Space) (A : Field) :
    translateOperator a (multiplier A) = multiplier (translated A a) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := multiplier_translation A a (translation (-a) u)
  change translateOperator a (multiplier A) u = _ at h
  simpa only [translation_add, add_neg_cancel, translation_zero] using h

/-- The actual uniformly continuous coefficient path translates by spatial conjugation. -/
theorem translatePath_operatorPath (T : ℝ)
    (A : C(Set.Icc (0 : ℝ) T, Field)) (a : Space) :
    translatePath T a (operatorPath T A) = operatorPath T (translatedPath T A a) := by
  apply ContinuousMap.ext
  intro t
  exact translateOperator_multiplier a (A t)

/-- Conjugation translates both actual cutoffs in the Newtonian boundary operator. -/
theorem translateOperator_mixedBoundary (a : Space) (χ ψ : Cutoff) :
    translateOperator a (mixedBoundaryOperator χ ψ) =
      mixedBoundaryOperator (χ.translate a) (ψ.translate a) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := mixedBoundaryOperator_translation a χ ψ (translation (-a) u)
  change translateOperator a (mixedBoundaryOperator χ ψ) u = _ at h
  simpa only [translation_add, add_neg_cancel, translation_zero] using h

/-- The source's diagonal boundary operator is exactly translated in the fixed inverse. -/
theorem translateOperator_boundary (a : Space) (χ : Cutoff) :
    translateOperator a (boundaryOperator χ) = boundaryOperator (χ.translate a) :=
  translateOperator_mixedBoundary a χ χ

end EulerMeanOperatorTranslation
