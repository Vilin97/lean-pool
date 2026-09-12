/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup

/-!
# Fourier pairings and Parseval on Schwartz functions

These identities concern the ordinary Fourier integral on Euclidean space.
They use Fourier inversion on Schwartz functions, without introducing an
extension of the Fourier transform to all of `L²`.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexConjugate RealInnerProductSpace

namespace NavierStokesR3.SchwartzParseval

open ProblemStatement Comparison

/-- Fourier duality for two integrable complex functions. -/
theorem integral_fourier_mul {f g : Space → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : Space, 𝓕 (f : Space → ℂ) ξ * g ξ) = ∫ x : Space, f x * 𝓕 (g : Space → ℂ) x := by
  simpa only [FourierTransform.fourier, smul_eq_mul, flip_innerₗ] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (L := innerₗ Space)
      (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf hg)

/-- Conjugation changes the sign in the Fourier kernel. -/
theorem fourier_conj_apply (f : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕⁻ (f : Space → ℂ) ξ) := by
  rw [Real.fourier_eq, Real.fourierInv_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Circle.starRingEnd_addChar]

/-- The Hermitian pairing of two Schwartz functions is preserved by Fourier transform. -/
theorem integral_fourier_mul_conj (f g : ComplexTest) :
    (∫ ξ : Space, 𝓕 (f : Space → ℂ) ξ * conj (𝓕 (g : Space → ℂ) ξ)) =
      ∫ x : Space, f x * conj (g x) := by
  change (∫ ξ : Space, 𝓕 f ξ * conj (𝓕 g ξ)) =
      ∫ x : Space, f x * conj (g x)
  have hg : Integrable (fun ξ : Space => conj (𝓕 g ξ)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
      (FourierTransform.fourierCLE ℂ ComplexTest g).integrable
  simp only [SchwartzMap.fourier_coe] at hg ⊢
  rw [integral_fourier_mul f.integrable hg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fourier_conj_apply,
    g.continuous.fourierInv_fourier_eq g.integrable
      (FourierTransform.fourierCLE ℂ ComplexTest g).integrable]

/-- The convention with conjugation on the first factor, used by complex inner products. -/
theorem integral_conj_fourier_mul (f g : ComplexTest) :
    (∫ ξ : Space, conj (𝓕 (f : Space → ℂ) ξ) * 𝓕 (g : Space → ℂ) ξ) =
      ∫ x : Space, conj (f x) * g x := by
  change (∫ ξ : Space, conj (𝓕 f ξ) * 𝓕 g ξ) =
      ∫ x : Space, conj (f x) * g x
  simpa only [mul_comm, SchwartzMap.fourier_coe] using integral_fourier_mul_conj g f

/-- A Schwartz function has a finite squared `L²` norm. -/
theorem integrable_norm_sq (f : ComplexTest) :
    Integrable (fun x : Space => ‖f x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (f.memLp 2)

/-- The Fourier transform of a Schwartz function has a finite squared `L²` norm. -/
theorem integrable_norm_sq_fourier (f : ComplexTest) :
    Integrable (fun ξ : Space => ‖𝓕 (f : Space → ℂ) ξ‖ ^ 2) := by
  change Integrable (fun ξ : Space => ‖𝓕 f ξ‖ ^ 2)
  exact integrable_norm_sq (FourierTransform.fourierCLE ℂ ComplexTest f)

/-- Parseval's identity for the real squared `L²` norm of a Schwartz function. -/
theorem integral_norm_sq_fourier (f : ComplexTest) :
    (∫ ξ : Space, ‖𝓕 (f : Space → ℂ) ξ‖ ^ 2) = ∫ x : Space, ‖f x‖ ^ 2 := by
  change (∫ ξ : Space, ‖𝓕 f ξ‖ ^ 2) = ∫ x : Space, ‖f x‖ ^ 2
  have h := integral_fourier_mul_conj f f
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- Parseval for the inverse Fourier transform of a Schwartz function. -/
theorem integral_norm_sq_fourierInv (f : ComplexTest) :
    (∫ ξ : Space, ‖EulerSobolev.schwartzFourier f (-ξ)‖ ^ 2) = ∫ x : Space, ‖f x‖ ^ 2 := by
  change (∫ ξ : Space, ‖𝓕⁻ f ξ‖ ^ 2) = ∫ x : Space, ‖f x‖ ^ 2
  have h := integral_norm_sq_fourier (FourierTransform.fourierInv f)
  change (∫ ξ : Space, ‖(𝓕 (𝓕⁻ f : ComplexTest)) ξ‖ ^ 2) =
    ∫ x : Space, ‖(𝓕⁻ f : ComplexTest) x‖ ^ 2 at h
  simpa only [FourierTransform.fourier_fourierInv_eq] using h.symm


end NavierStokesR3.SchwartzParseval
