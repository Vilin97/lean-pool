/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup

/-!
# Bounded Riesz symbols and smooth Riesz transforms of test functions

The multiplier is defined at the origin by the ordinary totalized real quotient.
Its bound by one gives integrability of every polynomial moment of a multiplied
Schwartz transform, hence smoothness and boundedness of its inverse Fourier integral.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement Comparison

theorem norm_rieszSymbol_le (i j : Fin 3) (ξ : Space) :
    ‖rieszSymbol i j ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [hξ, rieszSymbol]
  have hpos : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξ) _
  rw [rieszSymbol, norm_div, norm_neg, norm_mul,
    Real.norm_of_nonneg (sq_nonneg ‖ξ‖)]
  apply (div_le_one hpos).mpr
  simpa only [pow_two] using
    mul_le_mul (PiLp.norm_apply_le ξ i) (PiLp.norm_apply_le ξ j)
      (norm_nonneg (ξ j)) (norm_nonneg ξ)

theorem abs_rieszSymbol_le (i j : Fin 3) (ξ : Space) :
    |rieszSymbol i j ξ| ≤ 1 :=
  norm_rieszSymbol_le i j ξ

theorem norm_rieszSymbol_complex_le (i j : Fin 3) (ξ : Space) :
    ‖(rieszSymbol i j ξ : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real] using norm_rieszSymbol_le i j ξ

theorem measurable_rieszSymbol (i j : Fin 3) : Measurable (rieszSymbol i j) := by
  exact (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable.mul
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.measurable).neg).div
      (continuous_norm.measurable.pow_const 2)

@[simp] theorem rieszSymbol_neg (i j : Fin 3) (ξ : Space) :
    rieszSymbol i j (-ξ) = rieszSymbol i j ξ := by
  simp [rieszSymbol]

theorem rieszSymbol_mul_norm_sq (i j : Fin 3) (ξ : Space) :
    rieszSymbol i j ξ * ‖ξ‖ ^ 2 = -(ξ i * ξ j) := by
  by_cases hξ : ξ = 0
  · simp [hξ, rieszSymbol]
  · exact div_mul_cancel₀ _ (ne_of_gt (pow_pos (norm_pos_iff.mpr hξ) 2))

theorem measurable_rieszMultiplier (i j : Fin 3) (ψ : ComplexTest) :
    Measurable (fun ξ : Space =>
      (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
  exact (Complex.continuous_ofReal.measurable.comp (measurable_rieszSymbol i j)).mul
    (FourierTransform.fourierCLE ℂ ComplexTest ψ).continuous.measurable

theorem norm_rieszMultiplier_le (i j : Fin 3) (ψ : ComplexTest) (ξ : Space) :
    ‖(rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ ≤
      ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_rieszSymbol_complex_le i j ξ)

theorem integrable_rieszMultiplier (i j : Fin 3) (ψ : ComplexTest) :
    Integrable (fun ξ : Space =>
      (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
  refine (FourierTransform.fourierCLE ℂ ComplexTest ψ).integrable.norm.mono'
    (measurable_rieszMultiplier i j ψ).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (norm_rieszMultiplier_le i j ψ)

theorem integrable_pow_mul_norm_rieszMultiplier (i j : Fin 3) (ψ : ComplexTest)
    (n : ℕ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ n *
      ‖(rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖) := by
  refine ((FourierTransform.fourierCLE ℂ ComplexTest ψ).integrable_pow_mul volume n).mono'
    ((continuous_norm.measurable.pow_const n).mul
      (measurable_rieszMultiplier i j ψ).norm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) n) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (norm_rieszMultiplier_le i j ψ ξ)
    (pow_nonneg (norm_nonneg ξ) n)

theorem contDiff_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    ContDiff ℝ ∞ (rieszTest i j ψ) := by
  have hF : ContDiff ℝ ∞ (FourierTransform.fourier (fun ξ : Space =>
      (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)) :=
    Real.contDiff_fourier fun n _ => integrable_pow_mul_norm_rieszMultiplier i j ψ n
  have heq : rieszTest i j ψ = fun x : Space => FourierTransform.fourier
      (fun ξ : Space =>
        (rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [heq]
  exact hF.comp contDiff_id.neg

theorem continuous_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    Continuous (rieszTest i j ψ) :=
  (contDiff_rieszTest i j ψ).continuous

theorem norm_rieszTest_le_integral_multiplier (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    ‖rieszTest i j ψ x‖ ≤
      ∫ ξ : Space, ‖(rieszSymbol i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem norm_rieszTest_le_integral (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    ‖rieszTest i j ψ x‖ ≤ ∫ ξ : Space, ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖ := by
  apply (norm_rieszTest_le_integral_multiplier i j ψ x).trans
  exact integral_mono (integrable_rieszMultiplier i j ψ).norm
    (FourierTransform.fourierCLE ℂ ComplexTest ψ).integrable.norm (norm_rieszMultiplier_le i j ψ)

theorem exists_bound_rieszTest (i j : Fin 3) (ψ : ComplexTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖rieszTest i j ψ x‖ ≤ C := by
  exact ⟨∫ ξ : Space, ‖(FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ‖,
    integral_nonneg fun _ => norm_nonneg _, norm_rieszTest_le_integral i j ψ⟩

end NavierStokesR3.RieszTestOperators
