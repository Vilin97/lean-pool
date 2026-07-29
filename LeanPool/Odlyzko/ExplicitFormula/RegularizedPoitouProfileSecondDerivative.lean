/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouKernelSecondDerivative
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuantitativeDecay
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarSecondDerivative

/-!
# Regularized Poitou Profile Second Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real

namespace NumberField.Odlyzko

theorem hasDerivAt_regularizedPoitouVerticalProfileDerivative
    (y δ σ x : ℝ) :
    HasDerivAt
      (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ)
      (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x) x :=
  hasDerivAt_poitouVerticalProfileDerivative
    (hasDerivAt_regularizedScaledTartar y δ)
    (hasDerivAt_regularizedScaledTartarDerivative y δ) σ x

theorem differentiable_regularizedPoitouVerticalProfileDerivative
    (y δ σ : ℝ) :
    Differentiable ℝ
      (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) :=
  fun x ↦
    (hasDerivAt_regularizedPoitouVerticalProfileDerivative
      y δ σ x).differentiableAt

theorem deriv_regularizedPoitouVerticalProfileDerivative
    (y δ σ x : ℝ) :
    deriv
      (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) x =
      poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x :=
  (hasDerivAt_regularizedPoitouVerticalProfileDerivative
    y δ σ x).deriv

theorem integrable_quadratic_abs_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (A B C : ℝ) :
    Integrable (fun x : ℝ ↦
      (A + B * |x| + C * x ^ 2) * Real.exp (-b * x ^ 2)) := by
  have hzero :
      Integrable (fun x : ℝ ↦
        A * Real.exp (-b * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul A
  have hone :
      Integrable (fun x : ℝ ↦
        B * (|x| * Real.exp (-b * x ^ 2))) := by
    have h := (integrable_mul_exp_neg_mul_sq hb).norm.const_mul B
    simp_all
  have htwo :
      Integrable (fun x : ℝ ↦
        C * (x ^ 2 * Real.exp (-b * x ^ 2))) := by
    have h :=
      (integrable_rpow_mul_exp_neg_mul_sq hb
        (s := 2) (by norm_num)).const_mul C
    simp_all
  exact (hzero.add hone |>.add htwo).congr
    (ae_of_all _ fun x ↦ by
      simp only [Pi.add_apply]
      ring)

theorem norm_poitouVerticalProfileSecondDerivative_regularized_le
    {δ : ℝ} (hδ : 0 < δ) (y σ x : ℝ) :
    ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖ ≤
      Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) *
        ((y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
            2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
            2 * |σ - 1 / 2| *
              (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
            |σ - 1 / 2| ^ 2 +
            (8 * δ * |y| * tartarAmplitudeDerivativeBound +
              2 * δ + 4 * |σ - 1 / 2| * δ) * |x| +
            4 * δ ^ 2 * x ^ 2) *
          Real.exp (-(δ / 2) * x ^ 2)) := by
  let a : ℝ := |σ - 1 / 2|
  let D₁ : ℝ :=
    2 * |y| * tartarAmplitudeDerivativeBound
  let D₂ : ℝ :=
    y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ
  have ha : 0 ≤ a := abs_nonneg _
  have hD₁ : 0 ≤ D₁ := by
    dsimp [D₁]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (abs_nonneg y))
      tartarAmplitudeDerivativeBound_nonneg
  have hD₂ : 0 ≤ D₂ := by
    dsimp [D₂]
    exact add_nonneg
      (mul_nonneg (sq_nonneg y)
        tartarTestFunctionSecondDerivativeBound_nonneg)
      (mul_nonneg (by norm_num) hδ.le)
  have hphase :
      Real.exp ((σ - 1 / 2) * x) ≤ Real.exp (a * |x|) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    simpa only [abs_mul] using le_abs_self ((σ - 1 / 2) * x)
  have hf := abs_regularizedScaledTartar_le_gaussian y δ x
  have hf' := abs_regularizedScaledTartarDerivative_le hδ.le y x
  have hf'' :=
    abs_regularizedScaledTartarSecondDerivative_le hδ.le y x
  have hk := abs_poitouKernel_regularizedScaledTartar_le_gaussian y δ x
  have hk' :
      |poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) x| ≤
        (D₁ + 2 * δ * |x| + 1 / 2) *
          Real.exp (-δ * x ^ 2) := by
    refine (abs_poitouKernelDerivative_le _ _ x).trans ?_
    grind
  have hk'' :
      |poitouKernelSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) x| ≤
        (D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
            4 * δ ^ 2 * x ^ 2 +
            D₁ + 2 * δ * |x| + 3 / 4) *
          Real.exp (-δ * x ^ 2) := by
    refine (abs_poitouKernelSecondDerivative_le _ _ _ x).trans ?_
    grind
  unfold poitouVerticalProfileSecondDerivative
  calc
    ‖(poitouKernelSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) x : ℂ) *
          Complex.exp ((σ - 1 / 2) * x) +
        2 * (σ - 1 / 2) *
          (poitouKernelDerivative
            (regularizedScaledTartar y δ)
            (regularizedScaledTartarDerivative y δ) x : ℂ) *
          Complex.exp ((σ - 1 / 2) * x) +
        (σ - 1 / 2) ^ 2 *
          (poitouKernel (regularizedScaledTartar y δ) x : ℂ) *
          Complex.exp ((σ - 1 / 2) * x)‖ ≤
      (|poitouKernelSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) x| +
        2 * a * |poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) x| +
        a ^ 2 * |poitouKernel
          (regularizedScaledTartar y δ) x|) *
        Real.exp ((σ - 1 / 2) * x) := by
      calc
        ‖_ + _ + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
            sub_zero]
          norm_num
          have hnorm :
              ‖((σ : ℂ) - 1 / 2)‖ = a := by
            rw [show (σ : ℂ) - 1 / 2 =
                ((σ - 1 / 2 : ℝ) : ℂ) by
              simp,
              Complex.norm_real, Real.norm_eq_abs]
          grind
    _ ≤
      ((D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
          4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
        2 * a * (D₁ + 2 * δ * |x| + 1 / 2) +
        a ^ 2) *
        Real.exp (-δ * x ^ 2) * Real.exp (a * |x|) := by
      let P₂ :=
        D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
          4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4
      let P₁ := D₁ + 2 * δ * |x| + 1 / 2
      have hP₂ : 0 ≤ P₂ := by
        dsimp [P₂]
        have hA := tartarAmplitudeDerivativeBound_nonneg
        positivity
      have hP₁ : 0 ≤ P₁ := by
        dsimp [P₁]
        positivity
      have hP :
          0 ≤
            (D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
                4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
              2 * a * (D₁ + 2 * δ * |x| + 1 / 2) + a ^ 2 := by
        exact add_nonneg
          (add_nonneg hP₂
            (mul_nonneg (mul_nonneg (by norm_num) ha) hP₁))
          (sq_nonneg a)
      apply mul_le_mul
      · calc
          |poitouKernelSecondDerivative
                (regularizedScaledTartar y δ)
                (regularizedScaledTartarDerivative y δ)
                (regularizedScaledTartarSecondDerivative y δ) x| +
              2 * a * |poitouKernelDerivative
                (regularizedScaledTartar y δ)
                (regularizedScaledTartarDerivative y δ) x| +
              a ^ 2 * |poitouKernel
                (regularizedScaledTartar y δ) x| ≤
            P₂ * Real.exp (-δ * x ^ 2) +
              2 * a * (P₁ * Real.exp (-δ * x ^ 2)) +
              a ^ 2 * Real.exp (-δ * x ^ 2) := by
                exact add_le_add
                  (add_le_add hk''
                    (mul_le_mul_of_nonneg_left hk'
                      (mul_nonneg (by norm_num) ha)))
                  (mul_le_mul_of_nonneg_left hk (sq_nonneg a))
          _ =
            ((D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
                4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
              2 * a * (D₁ + 2 * δ * |x| + 1 / 2) + a ^ 2) *
                Real.exp (-δ * x ^ 2) := by
              grind
      · simp_all
      · positivity
      · exact mul_nonneg hP (Real.exp_pos _).le
    _ ≤
      ((D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
          4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
        2 * a * (D₁ + 2 * δ * |x| + 1 / 2) +
        a ^ 2) *
        (Real.exp (a ^ 2 / (2 * δ)) *
          Real.exp (-(δ / 2) * x ^ 2)) := by
      have hP :
          0 ≤
            (D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
                4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
              2 * a * (D₁ + 2 * δ * |x| + 1 / 2) + a ^ 2 := by
        have hP₂ :
            0 ≤ D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
              4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4 := by
          have hA := tartarAmplitudeDerivativeBound_nonneg
          positivity
        have hP₁ : 0 ≤ D₁ + 2 * δ * |x| + 1 / 2 := by positivity
        exact add_nonneg
          (add_nonneg hP₂
            (mul_nonneg (mul_nonneg (by norm_num) ha) hP₁))
          (sq_nonneg a)
      calc
        _ =
            ((D₂ + 8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
                4 * δ ^ 2 * x ^ 2 + D₁ + 2 * δ * |x| + 3 / 4) +
              2 * a * (D₁ + 2 * δ * |x| + 1 / 2) + a ^ 2) *
              Real.exp (-δ * x ^ 2 + a * |x|) := by
                rw [Real.exp_add]
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (exp_neg_mul_sq_add_mul_le hδ a x) hP
    _ = _ := by grind

theorem poitouVerticalProfileSecondDerivative_regularized_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable
      (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ) := by
  let A :=
    y ^ 2 * tartarTestFunctionSecondDerivativeBound + 2 * δ +
      2 * |y| * tartarAmplitudeDerivativeBound + 3 / 4 +
      2 * |σ - 1 / 2| *
        (2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2) +
      |σ - 1 / 2| ^ 2
  let B :=
    8 * δ * |y| * tartarAmplitudeDerivativeBound +
      2 * δ + 4 * |σ - 1 / 2| * δ
  let C := 4 * δ ^ 2
  let E := Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ))
  have hmajor :=
    (integrable_quadratic_abs_mul_exp_neg_mul_sq
      (half_pos hδ) A B C).const_mul E
  apply hmajor.mono'
  · exact aestronglyMeasurable_deriv
      (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) volume
      |>.congr (ae_of_all _ fun x ↦
        (deriv_regularizedPoitouVerticalProfileDerivative
          y δ σ x))
  · filter_upwards [] with x
    refine (norm_poitouVerticalProfileSecondDerivative_regularized_le
      hδ y σ x).trans_eq ?_
    grind

end NumberField.Odlyzko
