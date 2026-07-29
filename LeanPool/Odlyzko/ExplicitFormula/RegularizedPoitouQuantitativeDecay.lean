/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouProfileDerivative
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarDecay
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Regularized Poitou Quantitative Decay

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform Real

namespace NumberField.Odlyzko

theorem differentiable_regularizedPoitouVerticalProfile
    (y δ σ : ℝ) :
    Differentiable ℝ (regularizedPoitouVerticalProfile y δ σ) := by
  intro x
  unfold regularizedPoitouVerticalProfile
  exact (hasDerivAt_poitouVerticalProfile
    (hasDerivAt_regularizedScaledTartar y δ) σ x).differentiableAt

theorem deriv_regularizedPoitouVerticalProfile
    (y δ σ x : ℝ) :
    deriv (regularizedPoitouVerticalProfile y δ σ) x =
      poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ x := by
  unfold regularizedPoitouVerticalProfile
  exact (hasDerivAt_poitouVerticalProfile
    (hasDerivAt_regularizedScaledTartar y δ) σ x).deriv

theorem fourier_poitouVerticalProfileDerivative_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) w =
      (2 * Real.pi * I * w) •
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w := by
  have hderiv :
      deriv (regularizedPoitouVerticalProfile y δ σ) =
        poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ := by
    funext x
    exact deriv_regularizedPoitouVerticalProfile y δ σ x
  have h :=
    congrFun (Real.fourier_deriv
      (regularizedPoitouVerticalProfile_integrable hδ σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ)
      (by
        rw [hderiv]
        exact
          poitouVerticalProfileDerivative_regularized_integrable
            hδ y σ)) w
  simp_all

end NumberField.Odlyzko
