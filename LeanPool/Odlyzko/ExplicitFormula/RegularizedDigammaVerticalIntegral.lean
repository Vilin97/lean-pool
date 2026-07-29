/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaEqDigamma
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedGaussFullFubini

/-!
# Regularized Digamma Vertical Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem integral_gaussDigammaIntegrand_eq_digamma_add_euler
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x) =
      Complex.digamma s + Real.eulerMascheroniConstant := by
  have hgauss := gaussDigamma_eq_digamma hs
  unfold gaussDigamma at hgauss
  grind

theorem integrable_poitouTransform_regularized_mul_digamma_add_euler
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) := by
  have hdouble :=
    integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
      hδ y hσ
  have hinter := hdouble.integral_prod_left
  apply hinter.congr
  filter_upwards [] with t
  change
    (∫ x : ℝ in Ioi 0,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x) =
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)
  rw [integral_const_mul,
    integral_gaussDigammaIntegrand_eq_digamma_add_euler
      (by simpa using hσ)]

theorem integral_poitouTransform_regularized_mul_digamma_add_euler
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) =
      ∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  rw [←
    integral_poitouTransform_regularized_mul_integral_gaussDigammaIntegrand_Ioi
      hδ y hσ]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [integral_gaussDigammaIntegrand_eq_digamma_add_euler
    (by simpa using hσ)]

end NumberField.Odlyzko
