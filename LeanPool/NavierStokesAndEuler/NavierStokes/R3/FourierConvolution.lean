/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# An inverse Fourier multiplier as a convolution

For integrable `A` and `ψ`, the inverse Fourier transform of `A * Fourier ψ`
is the convolution of `inverseFourier A` with `ψ`.  Absolute product
integrability also proves that the spatial convolution exists at every point;
no global integrability of `inverseFourier A` is required.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem integrable_inverseFourierProduct {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun p : Space × Space =>
      Real.fourierChar ⟪p.1, x - p.2⟫ • (A p.1 * ψ p.2))
      ((volume : Measure Space).prod (volume : Measure Space)) := by
  have hp : Continuous (fun p : Space × Space => Real.fourierChar ⟪p.1, x - p.2⟫) :=
    Real.continuous_fourierChar.comp
      (continuous_fst.inner (continuous_const.sub continuous_snd))
  refine (hA.norm.mul_prod hψ.norm).mono' ?_ ?_
  · exact hp.aestronglyMeasurable.smul
      (hA.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable.comp_snd)
  · exact Filter.Eventually.of_forall fun p => by
      simp only [Circle.norm_smul, norm_mul, le_refl]

private theorem inverseFourierProduct_integral_frequency (A ψ : Space → ℂ)
    (x y : Space) :
    (∫ ξ : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      FourierTransform.fourierInv A (x - y) * ψ y := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

private theorem inverseFourierProduct_integral_space (A ψ : Space → ℂ)
    (x ξ : Space) :
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      Real.fourierChar ⟪ξ, x⟫ • (A ξ * FourierTransform.fourier ψ ξ) := by
  rw [Real.fourier_eq]
  calc
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
        ∫ y : Space, Real.fourierChar ⟪ξ, x⟫ •
          (A ξ * (Real.fourierChar (-⟪y, ξ⟫) • ψ y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hphase : Real.fourierChar ⟪ξ, x - y⟫ =
          Real.fourierChar ⟪ξ, x⟫ * Real.fourierChar (-⟪y, ξ⟫) := by
        rw [← Real.fourierChar.map_add_eq_mul]
        congr 1
        rw [inner_sub_right, real_inner_comm y ξ]
        ring
      rw [hphase, mul_smul]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = Real.fourierChar ⟪ξ, x⟫ •
        (A ξ * ∫ y : Space, Real.fourierChar (-⟪y, ξ⟫) • ψ y) := by
      simp only [Circle.smul_def, smul_eq_mul, integral_const_mul]

/-- Convolution with an inverse Fourier transform is integrable at every fixed point. -/
theorem integrable_fourierIntegralInv_convolution {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun y : Space => FourierTransform.fourierInv A (x - y) * ψ y) := by
  apply (integrable_inverseFourierProduct hA hψ x).integral_prod_right.congr
  exact Filter.Eventually.of_forall fun y =>
    inverseFourierProduct_integral_frequency A ψ x y

/-- Multiplication by an integrable Fourier multiplier becomes a spatial convolution. -/
theorem fourierIntegralInv_mul_fourier {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
      ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
  calc
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
        ∫ ξ : Space, ∫ y : Space,
          Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ =>
        (inverseFourierProduct_integral_space A ψ x ξ).symm
    _ = ∫ y : Space, ∫ ξ : Space,
        Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) :=
      integral_integral_swap (integrable_inverseFourierProduct hA hψ x)
    _ = ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        inverseFourierProduct_integral_frequency A ψ x y

end NavierStokesR3.Comparison
