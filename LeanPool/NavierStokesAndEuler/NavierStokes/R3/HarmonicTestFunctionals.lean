/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierSobolevWeights
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HilbertFunctionalExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeakFourierUniqueness
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzCompactApproximation

@[expose] public section

/-!
# Harmonic functionals bounded in an inhomogeneous Fourier Sobolev norm

A complex-linear Schwartz functional bounded by the Fourier `H³` norm is
represented in polynomially weighted `L²`. If it annihilates Laplacians, its
representing function vanishes away from the origin. Since volume has no atom
at the origin, the whole functional vanishes.
-/


noncomputable section

open MeasureTheory

namespace NavierStokesR3.HarmonicTestFunctionals

open ProblemStatement Comparison

abbrev FrequencyL2 := Lp ℂ 2 (volume : Measure Space)

/-- The `H³` bound supplies a Hilbert-space representative after a polynomial
Fourier embedding. No Fourier transform of arbitrary `L²` functions is needed. -/
theorem exists_inner_representation_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    ∃ q : FrequencyL2, ∀ ψ : ComplexTest,
      F ψ = @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ) := by
  apply HilbertFunctionalExtension.exists_inner_representation
    FourierSobolevWeights.B FourierSobolevWeights.B_injective F
  intro ψ
  exact (hbound ψ).trans (mul_le_mul_of_nonneg_left
    (FourierSobolevWeights.sqrt_fourierHNormSq_three_le_norm_B ψ) hC)

/-- In particular, a functional with the stated Fourier bound is continuous
for the Schwartz topology. -/
theorem continuous_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    Continuous F := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hc : Continuous (fun ψ : ComplexTest =>
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ)) :=
    continuous_const.inner FourierSobolevWeights.continuous_B
  exact hc.congr fun ψ => (hq ψ).symm

/-- A weighted `L²` representative that annihilates ordinary Laplacians is zero. -/
theorem representative_eq_zero_of_harmonic
    (q : FrequencyL2)
    (hq : ∀ ψ : ComplexTest,
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B (laplacianCLM ψ)) = 0) :
    q = 0 := by
  apply WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero q
  intro φ
  let ψ : ComplexTest := (FourierTransform.fourierCLE ℂ ComplexTest).symm φ
  have hzero := hq ψ
  rw [FourierSobolevWeights.inner_B_eq_integral] at hzero
  let c : ℂ := -(4 * (Real.pi : ℂ) ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply neg_ne_zero.mpr
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  have hi : (fun ξ : Space => star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ) ξ) =
      (fun ξ : Space => c • (star (q ξ) *
        (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ)) := by
    funext ξ
    rw [fourier_laplacianCLM_apply]
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, c]
    ring
  rw [hi, integral_smul] at hzero
  change c * (∫ ξ : Space, star (q ξ) *
    (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ) = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- A harmonic Schwartz functional bounded in Fourier `H⁻³` vanishes. -/
theorem eq_zero_of_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, F (laplacianCLM ψ) = 0) : F = 0 := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hqzero : q = 0 := representative_eq_zero_of_harmonic q (fun ψ => by
    rw [← hq]
    exact hharmonic ψ)
  ext ψ
  change F ψ = 0
  rw [hq, hqzero]
  simp

/-- The pressure-recovery form: harmonicity need only be known against compactly
supported tests. The Fourier bound supplies the continuity needed to pass to
all Schwartz tests. No pressure pairing outside compact support is assumed. -/
theorem eq_zero_of_compact_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) →
      F (laplacianCLM ψ) = 0) : F = 0 := by
  apply eq_zero_of_harmonic F hC hbound
  intro ψ
  exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (fun φ : ComplexTest => F (laplacianCLM φ))
    ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
    hharmonic ψ

end NavierStokesR3.HarmonicTestFunctionals
