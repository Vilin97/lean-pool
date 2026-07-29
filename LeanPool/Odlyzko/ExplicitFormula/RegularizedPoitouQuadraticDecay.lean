/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouTransform
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform
public import LeanPool.Odlyzko.TestFunction.TartarDerivativeBounds
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Regularized Poitou Quadratic Decay

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A tartar amplitude second derivative integrand used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeSecondDerivativeIntegrand (x t : ℝ) : ℝ :=
  -(t ^ 2) * Tartar.weight t * Real.cos (x * t)

theorem hasDerivAt_tartarAmplitudeDerivativeIntegrand (x t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ tartarAmplitudeDerivativeIntegrand z t)
      (tartarAmplitudeSecondDerivativeIntegrand x t) x := by
  unfold tartarAmplitudeDerivativeIntegrand
    tartarAmplitudeSecondDerivativeIntegrand
  have h := (((hasDerivAt_id x).mul_const t).sin.const_mul
    (-t * Tartar.weight t))
  grind

theorem sq_mul_tartarWeight_integrable :
    Integrable (fun t : ℝ ↦ t ^ 2 * Tartar.weight t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_id.pow 2).mul tartarWeight_continuous
  · exact tartarWeight_hasCompactSupport.mul_left

theorem norm_tartarAmplitudeSecondDerivativeIntegrand_le (x t : ℝ) :
    ‖tartarAmplitudeSecondDerivativeIntegrand x t‖ ≤
      t ^ 2 * Tartar.weight t := by
  rw [tartarAmplitudeSecondDerivativeIntegrand, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg, abs_pow,
    abs_of_nonneg (tartarWeight_nonneg t), sq_abs]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x * t))
      (mul_nonneg (sq_nonneg t) (tartarWeight_nonneg t))

theorem hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand (x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t)
      (∫ t : ℝ, tartarAmplitudeSecondDerivativeIntegrand x t) x := by
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (x₀ := x) (s := Set.univ)
      (F := tartarAmplitudeDerivativeIntegrand)
      (F' := tartarAmplitudeSecondDerivativeIntegrand)
      (bound := fun t : ℝ ↦ t ^ 2 * Tartar.weight t)
      univ_mem
      (by
        filter_upwards [] with z
        exact
          ((continuous_id.neg.mul tartarWeight_continuous).mul
            (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (by
        exact abs_mul_tartarWeight_integrable.mono'
          (by
            exact
              ((continuous_id.neg.mul tartarWeight_continuous).mul
                (Real.continuous_sin.comp
                  (continuous_const.mul continuous_id))).aestronglyMeasurable)
          (by
            filter_upwards [] with t
            exact norm_tartarAmplitudeDerivativeIntegrand_le x t))
      (by
        exact
          (((continuous_id.pow 2).neg.mul tartarWeight_continuous).mul
            (Real.continuous_cos.comp
              (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (by
        filter_upwards [] with t z _
        exact norm_tartarAmplitudeSecondDerivativeIntegrand_le z t)
      sq_mul_tartarWeight_integrable
      (by
        filter_upwards [] with t z _
        exact hasDerivAt_tartarAmplitudeDerivativeIntegrand z t)).2

/-- A tartar amplitude second derivative used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeSecondDerivative (x : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    ∫ t : ℝ, tartarAmplitudeSecondDerivativeIntegrand x t

theorem hasDerivAt_deriv_tartarAmplitude (x : ℝ) :
    HasDerivAt (deriv Tartar.amplitude)
      (tartarAmplitudeSecondDerivative x) x := by
  rw [show deriv Tartar.amplitude =
      fun z : ℝ ↦ (3 / 4 : ℝ) *
        ∫ t : ℝ, tartarAmplitudeDerivativeIntegrand z t by
    funext z
    exact deriv_tartarAmplitude z]
  exact (hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand x).const_mul _

theorem abs_tartarAmplitudeSecondDerivative_le (x : ℝ) :
    |tartarAmplitudeSecondDerivative x| ≤
      (3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t := by
  unfold tartarAmplitudeSecondDerivative
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  gcongr
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le sq_mul_tartarWeight_integrable
    (.of_forall fun t ↦ norm_tartarAmplitudeSecondDerivativeIntegrand_le x t)

/-- A tartar test function second derivative bound used in the Odlyzko-bound argument. -/
noncomputable def tartarTestFunctionSecondDerivativeBound : ℝ :=
  2 * tartarAmplitudeDerivativeBound ^ 2 +
    2 * ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t)

theorem tartarTestFunctionSecondDerivativeBound_nonneg :
    0 ≤ tartarTestFunctionSecondDerivativeBound := by
  unfold tartarTestFunctionSecondDerivativeBound
  have hint : 0 ≤ ∫ t : ℝ, t ^ 2 * Tartar.weight t :=
    integral_nonneg fun t ↦
      mul_nonneg (sq_nonneg t) (tartarWeight_nonneg t)
  positivity

/-- A tartar test function second derivative used in the Odlyzko-bound argument. -/
noncomputable def tartarTestFunctionSecondDerivative (x : ℝ) : ℝ :=
  2 * deriv Tartar.amplitude x ^ 2 +
    2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x

theorem hasDerivAt_deriv_tartarTestFunction (x : ℝ) :
    HasDerivAt (deriv Tartar.testFunction)
      (tartarTestFunctionSecondDerivative x) x := by
  rw [show deriv Tartar.testFunction =
      fun z : ℝ ↦ 2 * Tartar.amplitude z * deriv Tartar.amplitude z by
    funext z
    exact deriv_tartarTestFunction z]
  unfold tartarTestFunctionSecondDerivative
  have ha : HasDerivAt Tartar.amplitude (deriv Tartar.amplitude x) x := by
    convert hasDerivAt_tartarAmplitude x using 1
    exact deriv_tartarAmplitude x
  have h := (ha.const_mul 2).mul
    (hasDerivAt_deriv_tartarAmplitude x)
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z ↦ rfl)).congr_deriv ?_
  ring

theorem abs_tartarTestFunctionSecondDerivative_le (x : ℝ) :
    |tartarTestFunctionSecondDerivative x| ≤
      tartarTestFunctionSecondDerivativeBound := by
  unfold tartarTestFunctionSecondDerivative
    tartarTestFunctionSecondDerivativeBound
  calc
    |2 * deriv Tartar.amplitude x ^ 2 +
        2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x| ≤
      |2 * deriv Tartar.amplitude x ^ 2| +
        |2 * Tartar.amplitude x * tartarAmplitudeSecondDerivative x| :=
      abs_add_le _ _
    _ ≤ 2 * tartarAmplitudeDerivativeBound ^ 2 +
        2 * ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      apply add_le_add
      · gcongr
        exact abs_deriv_tartarAmplitude_le x
      · calc
          2 * |Tartar.amplitude x| *
              |tartarAmplitudeSecondDerivative x| ≤
            2 * 1 *
              ((3 / 4 : ℝ) * ∫ t : ℝ, t ^ 2 * Tartar.weight t) := by
                gcongr
                · exact abs_tartarAmplitude_le_one x
                · exact abs_tartarAmplitudeSecondDerivative_le x
          _ = _ := by ring

end NumberField.Odlyzko

end

section

open Complex

namespace NumberField.Odlyzko

theorem abs_sinh_le_cosh (x : ℝ) :
    |Real.sinh x| ≤ Real.cosh x := by
  have hid := Real.cosh_sq_sub_sinh_sq x
  have hsq : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by
    nlinarith
  have habssq : |Real.sinh x| ^ 2 ≤ Real.cosh x ^ 2 := by simp_all
  exact ((sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos x).le)).mp habssq

/-- A poitou kernel derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouKernelDerivative
    (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f' x / Real.cosh (x / 2) -
    f x * Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2)

theorem hasDerivAt_poitouKernel
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (poitouKernel f)
      (poitouKernelDerivative f f' x) x := by
  unfold poitouKernel poitouKernelDerivative
  have hden :
      HasDerivAt (fun z : ℝ ↦ Real.cosh (z / 2))
        (Real.sinh (x / 2) / 2) x := by
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have h := (hf x).div hden (Real.cosh_pos (x / 2)).ne'
  exact h.congr_deriv (by
    grind)

theorem abs_poitouKernelDerivative_le
    (f f' : ℝ → ℝ) (x : ℝ) :
    |poitouKernelDerivative f f' x| ≤ |f' x| + |f x| / 2 := by
  unfold poitouKernelDerivative
  have hc : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hcpos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  calc
    |f' x / Real.cosh (x / 2) -
        f x * Real.sinh (x / 2) /
          (2 * Real.cosh (x / 2) ^ 2)| ≤
      |f' x / Real.cosh (x / 2)| +
        |f x * Real.sinh (x / 2) /
          (2 * Real.cosh (x / 2) ^ 2)| :=
      abs_sub _ _
    _ ≤ |f' x| + |f x| / 2 := by
      rw [abs_div, abs_div, abs_mul,
        abs_of_pos hcpos, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, abs_of_pos hcpos]
      apply add_le_add
      · exact (div_le_iff₀ hcpos).2
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hc (abs_nonneg (f' x)))
      · have hratio :
            |Real.sinh (x / 2)| / Real.cosh (x / 2) ^ 2 ≤ 1 := by
          apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
          simpa only [one_mul] using (show
              |Real.sinh (x / 2)| ≤ Real.cosh (x / 2) ^ 2 by
            calc
            |Real.sinh (x / 2)| ≤ Real.cosh (x / 2) :=
              abs_sinh_le_cosh _
            _ ≤ Real.cosh (x / 2) ^ 2 := by
              nlinarith)
        calc
          |f x| * |Real.sinh (x / 2)| /
                (2 * Real.cosh (x / 2) ^ 2) =
              |f x| / 2 *
                (|Real.sinh (x / 2)| / Real.cosh (x / 2) ^ 2) := by
            ring
          _ ≤ |f x| / 2 * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = |f x| / 2 := mul_one _

/-- A poitou vertical profile derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouVerticalProfileDerivative
    (f f' : ℝ → ℝ) (σ x : ℝ) : ℂ :=
  (poitouKernelDerivative f f' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    (poitouKernel f x : ℂ) *
      ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x))

theorem hasDerivAt_poitouVerticalProfile
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (σ x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦
        (poitouKernel f z : ℂ) *
          Complex.exp ((σ - 1 / 2) * z))
      (poitouVerticalProfileDerivative f f' σ x) x := by
  have hk := (hasDerivAt_poitouKernel hf x).ofReal_comp
  have he :
      HasDerivAt (fun z : ℝ ↦
        Complex.exp ((σ - 1 / 2) * z))
        ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x)) x := by
    have hlin :=
      ((hasDerivAt_id x).const_mul (σ - 1 / 2)).ofReal_comp
    convert hlin.cexp using 1 <;>
      simp only [id_eq] <;> push_cast <;> ring
  exact hk.mul he

end NumberField.Odlyzko

end

section

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

end

section

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

end

section

open Complex MeasureTheory
open scoped FourierTransform Real

namespace NumberField.Odlyzko

theorem differentiable_regularizedPoitouVerticalProfile
    (y δ σ : ℝ) :
    Differentiable ℝ (regularizedPoitouVerticalProfile y δ σ) := by
  intro x
  unfold regularizedPoitouVerticalProfile
  exact (hasDerivAt_poitouVerticalProfile
    (hasDerivAt_regularizedScaledTartar y δ) σ x).differentiableAt

theorem deriv_regularizedPoitouVerticalProfile
    (y δ σ x : ℝ) :
    deriv (regularizedPoitouVerticalProfile y δ σ) x =
      poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ x := by
  unfold regularizedPoitouVerticalProfile
  exact (hasDerivAt_poitouVerticalProfile
    (hasDerivAt_regularizedScaledTartar y δ) σ x).deriv

theorem fourier_poitouVerticalProfileDerivative_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ) σ) w =
      (2 * Real.pi * I * w) •
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w := by
  have hderiv :
      deriv (regularizedPoitouVerticalProfile y δ σ) =
        poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ := by
    funext x
    exact deriv_regularizedPoitouVerticalProfile y δ σ x
  have h :=
    congrFun (Real.fourier_deriv
      (regularizedPoitouVerticalProfile_integrable hδ σ)
      (differentiable_regularizedPoitouVerticalProfile y δ σ)
      (by
        rw [hderiv]
        exact
          poitouVerticalProfileDerivative_regularized_integrable
            hδ y σ)) w
  simp_all

end NumberField.Odlyzko

end

section

open Complex Filter
open scoped Topology

namespace NumberField.Odlyzko

/-- A poitou kernel second derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouKernelSecondDerivative
    (f f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f'' x / Real.cosh (x / 2) -
    f' x * Real.sinh (x / 2) / Real.cosh (x / 2) ^ 2 -
    f x / (4 * Real.cosh (x / 2)) +
    f x * Real.sinh (x / 2) ^ 2 /
      (2 * Real.cosh (x / 2) ^ 3)

theorem hasDerivAt_poitouKernelDerivative
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (x : ℝ) :
    HasDerivAt (poitouKernelDerivative f f')
      (poitouKernelSecondDerivative f f' f'' x) x := by
  let c : ℝ → ℝ := fun z ↦ Real.cosh (z / 2)
  let sh : ℝ → ℝ := fun z ↦ Real.sinh (z / 2)
  have hc : HasDerivAt c (sh x / 2) x := by
    dsimp [c, sh]
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have hsh : HasDerivAt sh (c x / 2) x := by
    dsimp [c, sh]
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).sinh
  have hcne : c x ≠ 0 := by
    dsimp [c]
    exact (Real.cosh_pos _).ne'
  have hfirst := (hf' x).div hc hcne
  have hsecond :=
    (((hf x).mul hsh).div
      ((hc.mul hc).const_mul 2)
      (by
        simp_all))
  have h := hfirst.sub hsecond
  have he :
      HasDerivAt (poitouKernelDerivative f f')
        (poitouKernelSecondDerivative f f' f'' x) x := by
    have hevent :
        poitouKernelDerivative f f' =ᶠ[𝓝 x]
          (f' / c - (f * sh) / (fun z ↦ 2 * (c * c) z)) :=
      Filter.Eventually.of_forall fun z ↦ by
        unfold poitouKernelDerivative
        dsimp [c, sh]
        ring
    have hfun := h.congr_of_eventuallyEq hevent
    refine hfun.congr_deriv ?_
    unfold poitouKernelSecondDerivative
    dsimp [c, sh]
    field_simp [(Real.cosh_pos (x / 2)).ne']
    ring
  grind

theorem abs_poitouKernelSecondDerivative_le
    (f f' f'' : ℝ → ℝ) (x : ℝ) :
    |poitouKernelSecondDerivative f f' f'' x| ≤
      |f'' x| + |f' x| + 3 * |f x| / 4 := by
  let c := Real.cosh (x / 2)
  let sh := Real.sinh (x / 2)
  have hc : 1 ≤ c := Real.one_le_cosh _
  have hcpos : 0 < c := Real.cosh_pos _
  have hsh : |sh| ≤ c := abs_sinh_le_cosh _
  unfold poitouKernelSecondDerivative
  change
    |f'' x / c - f' x * sh / c ^ 2 -
        f x / (4 * c) + f x * sh ^ 2 / (2 * c ^ 3)| ≤ _
  calc
    |f'' x / c - f' x * sh / c ^ 2 -
        f x / (4 * c) + f x * sh ^ 2 / (2 * c ^ 3)| ≤
      |f'' x / c| + |f' x * sh / c ^ 2| +
        |f x / (4 * c)| + |f x * sh ^ 2 / (2 * c ^ 3)| := by
      have h₁ := abs_add_le
        (f'' x / c - f' x * sh / c ^ 2 - f x / (4 * c))
        (f x * sh ^ 2 / (2 * c ^ 3))
      have h₂ := abs_sub
        (f'' x / c - f' x * sh / c ^ 2) (f x / (4 * c))
      have h₃ := abs_sub (f'' x / c) (f' x * sh / c ^ 2)
      linarith
    _ ≤ |f'' x| + |f' x| + |f x| / 4 + |f x| / 2 := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · rw [abs_div, abs_of_pos hcpos]
            exact (div_le_iff₀ hcpos).2
              (by simpa using mul_le_mul_of_nonneg_left hc (abs_nonneg (f'' x)))
          · rw [abs_div, abs_mul,
              abs_of_pos (pow_pos hcpos 2)]
            apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
            calc
              |f' x| * |sh| ≤ |f' x| * c :=
                mul_le_mul_of_nonneg_left hsh (abs_nonneg _)
              _ ≤ |f' x| * c ^ 2 := by
                gcongr
                nlinarith
              _ = |f' x| * c ^ 2 := rfl
        · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
            abs_of_pos hcpos]
          apply (div_le_iff₀ (mul_pos (by norm_num) hcpos)).2
          nlinarith [abs_nonneg (f x)]
      · rw [abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hcpos]
        apply (div_le_iff₀ (mul_pos (by norm_num) (pow_pos hcpos 3))).2
        have hsq : |sh| ^ 2 ≤ c ^ 2 := by gcongr
        have hc3 : c ^ 2 ≤ c ^ 3 := by
          nlinarith [sq_nonneg c]
        nlinarith [abs_nonneg (f x)]
    _ = _ := by ring

/-- A poitou vertical profile second derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouVerticalProfileSecondDerivative
    (f f' f'' : ℝ → ℝ) (σ x : ℝ) : ℂ :=
  (poitouKernelSecondDerivative f f' f'' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    2 * (σ - 1 / 2) *
      (poitouKernelDerivative f f' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    (σ - 1 / 2) ^ 2 * (poitouKernel f x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x)

theorem hasDerivAt_poitouVerticalProfileDerivative
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (σ x : ℝ) :
    HasDerivAt (poitouVerticalProfileDerivative f f' σ)
      (poitouVerticalProfileSecondDerivative f f' f'' σ x) x := by
  let a : ℝ := σ - 1 / 2
  have hk :=
    (hasDerivAt_poitouKernel hf x).ofReal_comp
  have hk' :=
    (hasDerivAt_poitouKernelDerivative hf hf' x).ofReal_comp
  have he :
      HasDerivAt (fun z : ℝ ↦ Complex.exp (a * z))
        (a * Complex.exp (a * x)) x := by
    convert (((hasDerivAt_id x).const_mul a).ofReal_comp.cexp) using 1 <;>
      simp only [id_eq] <;> push_cast <;> ring
  unfold poitouVerticalProfileDerivative
    poitouVerticalProfileSecondDerivative
  dsimp [a] at he ⊢
  have hleft := hk'.mul he
  have hright := hk.mul
    (he.const_mul (((σ - 1 / 2 : ℝ) : ℂ)))
  have h := hleft.add hright
  have h' : HasDerivAt
      (poitouVerticalProfileDerivative f f' σ)
      (poitouVerticalProfileSecondDerivative f f' f'' σ x) x := by
    have hevent :
        poitouVerticalProfileDerivative f f' σ =ᶠ[𝓝 x]
          (((fun z : ℝ ↦ (poitouKernelDerivative f f' z : ℂ)) *
              fun z : ℝ ↦ Complex.exp
                (((σ - 1 / 2 : ℝ) : ℂ) * (z : ℂ))) +
            (fun z : ℝ ↦ (poitouKernel f z : ℂ)) *
              fun z : ℝ ↦ ((σ - 1 / 2 : ℝ) : ℂ) *
                Complex.exp (((σ - 1 / 2 : ℝ) : ℂ) * (z : ℂ))) :=
      Filter.Eventually.of_forall fun z ↦ by
        unfold poitouVerticalProfileDerivative
        simp
    have hfun := h.congr_of_eventuallyEq hevent
    refine hfun.congr_deriv ?_
    unfold poitouVerticalProfileSecondDerivative
    push_cast
    ring
  exact h'

end NumberField.Odlyzko

end

section

open MeasureTheory Real

namespace NumberField.Odlyzko

/-- A regularized scaled tartar second derivative used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartarSecondDerivative
    (y δ x : ℝ) : ℝ :=
  (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
      2 * δ * scaledTartarTestFunction y x -
      4 * δ * x * (y * deriv Tartar.testFunction (y * x)) +
      4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x) *
    Real.exp (-δ * x ^ 2)

private theorem hasDerivAt_scaledTartarTestFunctionDerivative (y x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ y * deriv Tartar.testFunction (y * z))
      (y ^ 2 * tartarTestFunctionSecondDerivative (y * x)) x := by
  have h := (hasDerivAt_deriv_tartarTestFunction (y * x)).comp x
    ((hasDerivAt_id x).const_mul y)
  exact h.const_mul y |>.congr_deriv (by ring)

theorem hasDerivAt_regularizedScaledTartarDerivative (y δ x : ℝ) :
    HasDerivAt (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ x) x := by
  let f : ℝ → ℝ := scaledTartarTestFunction y
  let f' : ℝ → ℝ := fun z ↦ y * deriv Tartar.testFunction (y * z)
  let g : ℝ → ℝ := fun z ↦ Real.exp (-δ * z ^ 2)
  have hf : HasDerivAt f (f' x) x := by
    exact hasDerivAt_scaledTartarTestFunction y x
  have hf' : HasDerivAt f'
      (y ^ 2 * tartarTestFunctionSecondDerivative (y * x)) x := by
    exact hasDerivAt_scaledTartarTestFunctionDerivative y x
  have hg : HasDerivAt g (-2 * δ * x * g x) x := by
    dsimp [g]
    have h := (((hasDerivAt_id x).pow 2).const_mul (-δ)).exp
    convert h using 1 <;> simp only [Pi.pow_apply, id_eq]
    ring
  have hinside :
      HasDerivAt (fun z ↦ f' z - 2 * δ * z * f z)
        (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
          2 * δ * f x - 2 * δ * x * f' x) x := by
    have h := hf'.sub ((((hasDerivAt_id x).const_mul (2 * δ)).mul hf))
    have he :
        HasDerivAt (fun z ↦ f' z - 2 * δ * z * f z)
          (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
            (2 * δ * 1 * f x + 2 * δ * x * f' x)) x :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z ↦ rfl)
    grind
  have hprod := hinside.mul hg
  unfold regularizedScaledTartarDerivative
    regularizedScaledTartarSecondDerivative
  dsimp [f, f', g] at hprod
  exact hprod.congr_deriv (by ring)

theorem abs_regularizedScaledTartarSecondDerivative_le
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    |regularizedScaledTartarSecondDerivative y δ x| ≤
      (y ^ 2 * tartarTestFunctionSecondDerivativeBound +
        2 * δ +
        8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
        4 * δ ^ 2 * x ^ 2) *
      Real.exp (-δ * x ^ 2) := by
  unfold regularizedScaledTartarSecondDerivative
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  calc
    |y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
        2 * δ * scaledTartarTestFunction y x -
        4 * δ * x * (y * deriv Tartar.testFunction (y * x)) +
        4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x| ≤
      |y ^ 2 * tartarTestFunctionSecondDerivative (y * x)| +
        |2 * δ * scaledTartarTestFunction y x| +
        |4 * δ * x * (y * deriv Tartar.testFunction (y * x))| +
        |4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x| := by grind
    _ ≤ y ^ 2 * tartarTestFunctionSecondDerivativeBound +
        2 * δ +
        8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
        4 * δ ^ 2 * x ^ 2 := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hδ,
        abs_of_nonneg (scaledTartarTestFunction_nonneg y x),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · rw [sq_abs]
            exact mul_le_mul_of_nonneg_left
              (abs_tartarTestFunctionSecondDerivative_le (y * x))
              (sq_nonneg y)
          · simpa only [scaledTartarTestFunction, mul_one] using
              mul_le_mul_of_nonneg_left
                (tartarTestFunction_le_one (y * x))
                (show 0 ≤ 2 * δ from mul_nonneg (by norm_num) hδ)
        · have hd :=
            abs_deriv_tartarTestFunction_le (y * x)
          have hcoef :
              0 ≤ 4 * δ * |x| * |y| := by positivity
          nlinarith
      · have hf := tartarTestFunction_le_one (y * x)
        change
          4 * δ ^ 2 * |x| ^ 2 * Tartar.testFunction (y * x) ≤
            4 * δ ^ 2 * x ^ 2
        rw [sq_abs]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hf
            (show 0 ≤ 4 * δ ^ 2 * x ^ 2 by positivity)

end NumberField.Odlyzko

end

section

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

end

section

open Complex MeasureTheory
open scoped FourierTransform Real

namespace NumberField.Odlyzko

theorem fourier_poitouVerticalProfileSecondDerivative_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ) w =
      (2 * Real.pi * I * w) •
        𝓕 (poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ) w := by
  have hderiv :
      deriv
        (poitouVerticalProfileDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ) σ) =
        poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ := by
    funext x
    exact deriv_regularizedPoitouVerticalProfileDerivative y δ σ x
  have h :=
    congrFun (Real.fourier_deriv
      (poitouVerticalProfileDerivative_regularized_integrable hδ y σ)
      (differentiable_regularizedPoitouVerticalProfileDerivative y δ σ)
      (by
        rw [hderiv]
        exact
          poitouVerticalProfileSecondDerivative_regularized_integrable
            hδ y σ)) w
  simp_all

theorem fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
    {δ : ℝ} (hδ : 0 < δ) (y σ w : ℝ) :
    𝓕 (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ) w =
      ((2 * Real.pi * I * w) ^ 2) •
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w := by
  rw [fourier_poitouVerticalProfileSecondDerivative_regularized hδ,
    fourier_poitouVerticalProfileDerivative_regularized hδ]
  simp only [smul_smul]
  ring

theorem sq_abs_mul_norm_poitouTransform_regularized_le
    {δ : ℝ} (hδ : 0 < δ) (y σ t : ℝ) :
    |t| ^ 2 *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      ∫ x : ℝ,
        ‖poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ x‖ := by
  let w : ℝ := -t / (2 * Real.pi)
  have hfourier :=
    fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq
      hδ y σ w
  have hfactor :
      ‖(((2 * Real.pi : ℂ) * I * (w : ℂ)) ^ 2)‖ = |t| ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    dsimp [w]
    norm_num
    field_simp [Real.pi_ne_zero]
    simp
  have hnorm :
      |t| ^ 2 * ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ =
        ‖𝓕 (poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ) w‖ := by simp_all
  rw [poitouTransform_regularizedScaledTartar_eq_fourier]
  change |t| ^ 2 *
      ‖𝓕 (regularizedPoitouVerticalProfile y δ σ) w‖ ≤ _
  rw [hnorm, Real.fourier_real_eq]
  calc
    ‖∫ v : ℝ, 𝐞 (-(v * w)) •
        poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ v‖ ≤
      ∫ v : ℝ, ‖𝐞 (-(v * w)) •
        poitouVerticalProfileSecondDerivative
          (regularizedScaledTartar y δ)
          (regularizedScaledTartarDerivative y δ)
          (regularizedScaledTartarSecondDerivative y δ) σ v‖ :=
        norm_integral_le_integral_norm _
    _ = _ := by simp

end NumberField.Odlyzko

end
