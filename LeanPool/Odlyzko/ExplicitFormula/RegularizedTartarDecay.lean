/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Regularized Tartar Decay

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace NumberField.Odlyzko

/-- A regularized poitou vertical profile used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouVerticalProfile
    (y δ σ x : ℝ) : ℂ :=
  (poitouKernel (regularizedScaledTartar y δ) x : ℂ) *
    Complex.exp ((σ - 1 / 2) * x)

theorem regularizedPoitouVerticalProfile_integrable
    {y δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    Integrable (regularizedPoitouVerticalProfile y δ σ) := by
  exact (poitouTransformIntegrand_regularizedScaledTartar_integrable
    hδ (σ : ℂ)).congr (ae_of_all _ fun x ↦
      (by rw [regularizedPoitouVerticalProfile, poitouTransformIntegrand]))

theorem poitouTransform_regularizedScaledTartar_eq_fourier
    (y δ σ t : ℝ) :
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I) =
      𝓕 (regularizedPoitouVerticalProfile y δ σ)
        (-t / (2 * Real.pi)) := by
  rw [poitouTransform, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [poitouTransformIntegrand, regularizedPoitouVerticalProfile,
    smul_eq_mul]
  have hexp :
      Complex.exp ((σ + t * I - 1 / 2) * (x : ℂ)) =
        Complex.exp ((-2 * Real.pi * x *
          (-t / (2 * Real.pi)) : ℝ) * I) *
          Complex.exp ((σ - 1 / 2) * (x : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
  grind

end NumberField.Odlyzko
