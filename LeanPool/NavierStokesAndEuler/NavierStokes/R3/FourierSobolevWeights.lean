/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup

/-!
# A polynomially weighted Fourier embedding

The weight is constructed by coordinate multiplication on Schwartz space.
Consequently the resulting Fourier expressions belong to ordinary `L²`.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace NavierStokesR3.FourierSobolevWeights

open ProblemStatement Comparison

/-- Multiplication by a real coordinate, acting complex linearly on tests. -/
def coordinateMul (i : Fin 3) : ComplexTest →L[ℂ] ComplexTest :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasTemperateGrowth)

@[simp] theorem coordinateMul_apply (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
    coordinateMul i ψ ξ = (ξ i : ℂ) * ψ ξ := by
  change ψ ξ * (ξ i : ℂ) = (ξ i : ℂ) * ψ ξ
  exact mul_comm _ _

/-- Multiplication by `1 + ‖ξ‖²`, preserving Schwartz space. -/
def oneAddNormSqMul : ComplexTest →L[ℂ] ComplexTest :=
  ContinuousLinearMap.id ℂ ComplexTest +
    (coordinateMul 0).comp (coordinateMul 0) +
    (coordinateMul 1).comp (coordinateMul 1) +
    (coordinateMul 2).comp (coordinateMul 2)

@[simp] theorem oneAddNormSqMul_apply (ψ : ComplexTest) (ξ : Space) :
    oneAddNormSqMul ψ ξ = ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * ψ ξ := by
  have hnorm : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
  simp only [oneAddNormSqMul, _root_.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, coordinateMul_apply]
  rw [hnorm]
  push_cast
  ring

/-- Multiplication by the fourth-order Sobolev weight on Schwartz space. -/
def weightedSchwartz : ComplexTest →L[ℂ] ComplexTest :=
  oneAddNormSqMul.comp oneAddNormSqMul

@[simp] theorem weightedSchwartz_apply (ψ : ComplexTest) (ξ : Space) :
    weightedSchwartz ψ ξ = (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ψ ξ := by
  simp only [weightedSchwartz, ContinuousLinearMap.comp_apply, oneAddNormSqMul_apply]
  push_cast
  ring

theorem weightedSchwartz_injective : Function.Injective weightedSchwartz := by
  intro ψ φ h
  apply SchwartzMap.ext
  intro ξ
  have hξ := congrArg (fun f : ComplexTest => f ξ) h
  simp only [weightedSchwartz_apply] at hξ
  exact mul_left_cancel₀ (by
    exact_mod_cast (sq_pos_of_pos (show (0 : ℝ) < 1 + ‖ξ‖ ^ 2 by positivity)).ne') hξ

/-- Weighted Fourier embedding of tests into ordinary complex `L²`. -/
def BCLM : ComplexTest →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
    (weightedSchwartz.comp EulerSobolev.schwartzFourierCLM)

/-- The linear map underlying the continuous weighted Fourier embedding. -/
def B : ComplexTest →ₗ[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  BCLM.toLinearMap

theorem continuous_B : Continuous B := BCLM.continuous

theorem B_ae_eq (ψ : ComplexTest) :
    B ψ =ᵐ[volume] fun ξ : Space =>
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * (EulerSobolev.schwartzFourier ψ) ξ := by
  change B ψ =ᵐ[volume] fun ξ : Space =>
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ
  exact (SchwartzMap.coeFn_toLp (weightedSchwartz
    (FourierTransform.fourierCLE ℂ ComplexTest ψ)) 2 volume).trans
      (Filter.Eventually.of_forall (weightedSchwartz_apply _))

theorem B_injective : Function.Injective B := by
  intro ψ φ h
  apply (FourierTransform.fourierCLE ℂ ComplexTest).injective
  apply weightedSchwartz_injective
  exact SchwartzMap.injective_toLp 2 volume h

theorem norm_weightedSchwartz_apply_sq (ψ : ComplexTest) (ξ : Space) :
    ‖weightedSchwartz ψ ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ 4 * ‖ψ ξ‖ ^ 2 := by
  rw [weightedSchwartz_apply, norm_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  ring

theorem integrable_fourierHNormSq_four (ψ : ComplexTest) :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 4 *
      ‖(EulerSobolev.schwartzFourier ψ) ξ‖ ^ 2) volume := by
  change Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 4 *
      ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2) volume
  simpa only [norm_weightedSchwartz_apply_sq] using
    ((weightedSchwartz (FourierTransform.fourierCLE ℂ ComplexTest ψ)).memLp 2
        volume).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)

theorem fourierHNormSq_three_integrand_le_four (ψ : ComplexTest) (ξ : Space) :
    (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(EulerSobolev.schwartzFourier ψ) ξ‖ ^ 2 ≤
      (1 + ‖ξ‖ ^ 2) ^ 4 * ‖(EulerSobolev.schwartzFourier ψ) ξ‖ ^ 2 := by
  change (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2 ≤
      (1 + ‖ξ‖ ^ 2) ^ 4 * ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg ‖ξ‖)) (by decide)

theorem integrable_fourierHNormSq_three (ψ : ComplexTest) :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖(EulerSobolev.schwartzFourier ψ) ξ‖ ^ 2) volume := by
  change Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2) volume
  apply (integrable_fourierHNormSq_four ψ).mono'
  · exact ((continuous_const.add (continuous_norm.pow 2)).pow 3 |>.mul
      ((FourierTransform.fourierCLE ℂ ComplexTest ψ).continuous.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact fourierHNormSq_three_integrand_le_four ψ ξ

theorem norm_B_eq_sqrt (ψ : ComplexTest) :
    ‖B ψ‖ = Real.sqrt (fourierHNormSq 4 ψ) := by
  change ‖(weightedSchwartz (FourierTransform.fourierCLE ℂ ComplexTest ψ)).toLp 2 volume‖ = _
  rw [SchwartzMap.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    ((weightedSchwartz (FourierTransform.fourierCLE ℂ ComplexTest ψ)).memLp 2 volume)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedSchwartz_apply_sq]
  have hi : 0 ≤ ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ 4 *
      ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hi _), Real.sqrt_eq_rpow]
  simp only [fourierHNormSq, one_div]
  rfl

theorem norm_B_sq (ψ : ComplexTest) :
    ‖B ψ‖ ^ 2 = fourierHNormSq 4 ψ := by
  rw [norm_B_eq_sqrt]
  apply Real.sq_sqrt
  exact integral_nonneg fun ξ => by positivity

theorem fourierHNormSq_three_le_norm_B_sq (ψ : ComplexTest) :
    fourierHNormSq 3 ψ ≤ ‖B ψ‖ ^ 2 := by
  rw [norm_B_sq]
  exact integral_mono (integrable_fourierHNormSq_three ψ)
    (integrable_fourierHNormSq_four ψ) (fourierHNormSq_three_integrand_le_four ψ)

theorem sqrt_fourierHNormSq_three_le_norm_B (ψ : ComplexTest) :
    Real.sqrt (fourierHNormSq 3 ψ) ≤ ‖B ψ‖ := by
  rw [norm_B_eq_sqrt]
  apply Real.sqrt_le_sqrt
  exact integral_mono (integrable_fourierHNormSq_three ψ)
    (integrable_fourierHNormSq_four ψ) (fourierHNormSq_three_integrand_le_four ψ)

theorem inner_B_eq_integral (q : Lp ℂ 2 (volume : Measure Space)) (ψ : ComplexTest) :
    @inner ℂ _ _ q (B ψ) = ∫ ξ : Space, star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * (EulerSobolev.schwartzFourier ψ) ξ := by
  change @inner ℂ _ _ q (B ψ) = ∫ ξ : Space, star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [B_ae_eq ψ] with ξ hξ
  rw [hξ]
  simp only [RCLike.inner_apply', mul_assoc]
  rfl

end NavierStokesR3.FourierSobolevWeights
