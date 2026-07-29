/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticLittleO

/-!
# Regularized Poitou Uniform Quadratic Decay

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real

namespace NumberField.Odlyzko

/-- A regularized poitou profile second derivative majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouProfileSecondDerivativeMajorant
    (y δ M x : ℝ) : ℝ :=
  Real.exp (M ^ 2 / (2 * δ)) *
    ((y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
        2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
        2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
        M ^ 2 +
        (8 * δ * |y| * tartarAmplitudeDerivativeBound +
          2 * δ + 4 * M * δ) * |x| +
        4 * δ ^ 2 * x ^ 2) *
      Real.exp (-(δ / 2) * x ^ 2))

/-- A regularized poitou strip quadratic decay constant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouStripQuadraticDecayConstant
    (y δ a b : ℝ) : ℝ :=
  ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
    (max |a - 1 / 2| |b - 1 / 2|) x

theorem regularizedPoitouProfileSecondDerivativeMajorant_integrable
    {δ : ℝ} (hδ : 0 < δ) (y M : ℝ) :
    Integrable (regularizedPoitouProfileSecondDerivativeMajorant y δ M) := by
  let A :=
    y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
      2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
      2 * M * (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
      M ^ 2
  let B :=
    8 * δ * |y| * tartarAmplitudeDerivativeBound +
      2 * δ + 4 * M * δ
  let C := 4 * δ ^ 2
  have hquad :=
    integrable_quadratic_abs_mul_exp_neg_mul_sq
      (show 0 < δ / 2 by positivity) A B C
  have hconst :
      Integrable (fun x : ℝ ↦
        Real.exp (M ^ 2 / (2 * δ)) *
          ((A + B * |x| + C * x ^ 2) *
            Real.exp (-(δ / 2) * x ^ 2))) :=
    hquad.const_mul _
  apply hconst.congr
  filter_upwards with x
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  grind

theorem norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (y : ℝ) {σ : ℝ} (hσ : |σ - 1 / 2| ≤ M) (x : ℝ) :
    ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖ ≤
      regularizedPoitouProfileSecondDerivativeMajorant y δ M x := by
  refine (norm_poitouVerticalProfileSecondDerivative_regularized_le
    hδ y σ x).trans ?_
  unfold regularizedPoitouProfileSecondDerivativeMajorant
  have hA := tartarAmplitudeDerivativeBound_nonneg
  have hA₂ := tartarTestFunctionSecondDerivativeBound_nonneg
  have hexp :
      Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) ≤
        Real.exp (M ^ 2 / (2 * δ)) := by
    gcongr
  apply mul_le_mul
  · simp_all
  · gcongr
  · positivity
  · positivity

theorem sq_abs_mul_norm_poitouTransform_regularized_le_strip
    {δ a b : ℝ} (hδ : 0 < δ) (y t : ℝ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      ∫ x : ℝ, regularizedPoitouProfileSecondDerivativeMajorant y δ
        (max |a - 1 / 2| |b - 1 / 2|) x := by
  refine (sq_abs_mul_norm_poitouTransform_regularized_le hδ y σ t).trans ?_
  apply integral_mono
  · exact (poitouVerticalProfileSecondDerivative_regularized_integrable
      hδ y σ).norm
  · exact regularizedPoitouProfileSecondDerivativeMajorant_integrable hδ y _
  · intro x
    apply norm_poitouVerticalProfileSecondDerivative_regularized_le_majorant
      hδ ((abs_nonneg (a - 1 / 2)).trans (le_max_left _ _)) y
    grind

end NumberField.Odlyzko
