/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouKernelDerivative
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform
public import LeanPool.Odlyzko.TestFunction.TartarDerivativeBounds

/-!
# Regularized Poitou Profile Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real

namespace NumberField.Odlyzko

theorem abs_regularizedScaledTartar_le_gaussian
    (y δ x : ℝ) :
    |regularizedScaledTartar y δ x| ≤ Real.exp (-δ * x ^ 2) := by
  rw [abs_of_nonneg (regularizedScaledTartar_nonneg y δ x)]
  unfold regularizedScaledTartar
  exact mul_le_of_le_one_left (Real.exp_pos _).le
    (tartarTestFunction_le_one _)

theorem abs_poitouKernel_regularizedScaledTartar_le_gaussian
    (y δ x : ℝ) :
    |poitouKernel (regularizedScaledTartar y δ) x| ≤
      Real.exp (-δ * x ^ 2) := by
  rw [poitouKernel, abs_div, abs_of_pos (Real.cosh_pos _)]
  exact (div_le_iff₀ (Real.cosh_pos _)).2
    ((abs_regularizedScaledTartar_le_gaussian y δ x).trans
      (by
        simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_cosh (x / 2))
          (Real.exp_pos (-δ * x ^ 2)).le))

theorem norm_poitouVerticalProfileDerivative_regularized_le
    {δ : ℝ} (hδ : 0 < δ) (y σ x : ℝ) :
    ‖poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ x‖ ≤
      Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) *
        ((2 * |y| * tartarAmplitudeDerivativeBound +
            2 * δ * |x| + 1 / 2 + |σ - 1 / 2|) *
          Real.exp (-(δ / 2) * x ^ 2)) := by
  let a : ℝ := |σ - 1 / 2|
  let C : ℝ := 2 * |y| * tartarAmplitudeDerivativeBound
  have ha : 0 ≤ a := abs_nonneg _
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (by norm_num) (abs_nonneg y))
    tartarAmplitudeDerivativeBound_nonneg
  have hf := abs_regularizedScaledTartar_le_gaussian y δ x
  have hk :=
    abs_poitouKernel_regularizedScaledTartar_le_gaussian y δ x
  have hfd :=
    abs_regularizedScaledTartarDerivative_le hδ.le y x
  have hkd :
      |poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) x| ≤
        (C + 2 * δ * |x| + 1 / 2) *
          Real.exp (-δ * x ^ 2) := by
    refine (abs_poitouKernelDerivative_le _ _ x).trans ?_
    grind
  have hphase :
      Real.exp ((σ - 1 / 2) * x) ≤
        Real.exp (a * |x|) := by
    dsimp [a]
    have h := le_abs_self ((σ - 1 / 2) * x)
    simp_all
  calc
    ‖poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ x‖ ≤
      ‖((poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) x : ℝ) : ℂ) *
          Complex.exp ((σ - 1 / 2) * x)‖ +
        ‖((poitouKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) *
          ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x))‖ := by
      unfold poitouVerticalProfileDerivative
      exact norm_add_le _ _
    ‖((poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) x : ℝ) : ℂ) *
          Complex.exp ((σ - 1 / 2) * x)‖ +
        ‖((poitouKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) *
          ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x))‖ ≤
      ((C + 2 * δ * |x| + 1 / 2) *
          Real.exp (-δ * x ^ 2) +
        a * Real.exp (-δ * x ^ 2)) *
          Real.exp (a * |x|) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
        sub_zero]
      norm_num
      have hnorm :
          ‖((σ : ℂ) - 1 / 2)‖ = a := by
        rw [show (σ : ℂ) - 1 / 2 = ((σ - 1 / 2 : ℝ) : ℂ) by
          simp, Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      calc
        |poitouKernelDerivative
              (regularizedScaledTartar y δ)
              (regularizedScaledTartarDerivative y δ) x| *
              Real.exp ((σ - 1 / 2) * x) +
            |poitouKernel (regularizedScaledTartar y δ) x| *
              (a * Real.exp ((σ - 1 / 2) * x)) ≤
          ((C + 2 * δ * |x| + 1 / 2) *
              Real.exp (-δ * x ^ 2)) * Real.exp (a * |x|) +
            Real.exp (-δ * x ^ 2) *
              (a * Real.exp (a * |x|)) := by
          apply add_le_add
          · exact mul_le_mul hkd hphase
              (Real.exp_pos _).le
              (by positivity)
          · exact mul_le_mul hk
              (mul_le_mul_of_nonneg_left hphase ha)
              (by positivity) (by positivity)
        _ = ((C + 2 * δ * |x| + 1 / 2) *
              Real.exp (-δ * x ^ 2) +
            a * Real.exp (-δ * x ^ 2)) *
              Real.exp (a * |x|) := by ring
        _ = ((C + 2 * δ * |x| + 1 / 2) *
              Real.exp (-(δ * x ^ 2)) +
            a * Real.exp (-(δ * x ^ 2))) *
              Real.exp (a * |x|) := by simp
    _ = (C + 2 * δ * |x| + 1 / 2 + a) *
        Real.exp (-δ * x ^ 2 + a * |x|) := by
      rw [Real.exp_add]
      ring
    _ ≤ (C + 2 * δ * |x| + 1 / 2 + a) *
        (Real.exp (a ^ 2 / (2 * δ)) *
          Real.exp (-(δ / 2) * x ^ 2)) := by
      gcongr
      exact exp_neg_mul_sq_add_mul_le hδ a x
    _ = _ := by grind

theorem poitouVerticalProfileDerivative_regularized_integrable
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable
      (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) := by
  let A : ℝ :=
    2 * |y| * tartarAmplitudeDerivativeBound + 1 / 2 + |σ - 1 / 2|
  let K : ℝ := Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ))
  have hzero :
      Integrable (fun x : ℝ ↦
        K * (A * Real.exp (-(δ / 2) * x ^ 2))) :=
    ((integrable_exp_neg_mul_sq (half_pos hδ)).const_mul A).const_mul K
  have hone :
      Integrable (fun x : ℝ ↦
        K * ((2 * δ) *
          (|x| * Real.exp (-(δ / 2) * x ^ 2)))) := by
    have h := (integrable_mul_exp_neg_mul_sq (half_pos hδ)).norm
    have h' := h.const_mul (2 * δ) |>.const_mul K
    simp_all
  apply (hzero.add hone).mono'
  · have hfcont := continuous_regularizedScaledTartar y δ
    have hfdcont :=
      continuous_regularizedScaledTartarDerivative y δ
    have hcosh : Continuous (fun x : ℝ ↦ Real.cosh (x / 2)) := by
      fun_prop
    have hcoshne : ∀ x : ℝ, Real.cosh (x / 2) ≠ 0 :=
      fun x ↦ (Real.cosh_pos _).ne'
    have hkcont :
        Continuous (poitouKernel (regularizedScaledTartar y δ)) := by
      unfold poitouKernel
      exact hfcont.div hcosh hcoshne
    have hkdcont :
        Continuous (poitouKernelDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)) := by
      unfold poitouKernelDerivative
      exact (hfdcont.div hcosh hcoshne).sub
        (((hfcont.mul (by fun_prop)).div
          ((continuous_const.mul (hcosh.pow 2)))
          (fun x ↦ by positivity)))
    unfold poitouVerticalProfileDerivative
    exact (((Complex.continuous_ofReal.comp hkdcont).mul
      (by fun_prop)).add
        ((Complex.continuous_ofReal.comp hkcont).mul
          (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with x
    refine (norm_poitouVerticalProfileDerivative_regularized_le
      hδ y σ x).trans_eq ?_
    simp only [Pi.add_apply]
    grind

end NumberField.Odlyzko
