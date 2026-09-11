/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.NavierStokes.AxisReference
public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalAxisBridge
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisCoefficientSpace
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual natural profiles in the original radial variable

This module reconstructs the unscaled natural profiles from the actual smooth
solutions of the coefficient-space problem. Derivative identities refer to
ordinary derivatives of the reconstructed real functions.
-/

section

/-!
# The actual fixed coefficients of the natural-axis problem

The pressure comes from its proved holomorphic integral extension. A common
complex neighborhood is chosen by compactness and nonvanishing of the two
actual denominators. Every fixed field is then embedded in the same complete
space of compatible coefficient functions.
-/

section

/-!
# The fixed real natural-axis data

The small parameters are quantitative. The unique zero of `H` is proved,
not postulated. The pressure is an input with explicit real smoothness,
negativity, and derivative-sign hypotheses; its construction and complex
analytic estimates are separate results.
-/

section

/-!
# The pressure datum from a nonnegative weighted schedule

The clock weights and bounded exponents are fixed input functions. Regularity
of the pressure is deduced from the integral, not assumed as an input.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PressureDatum

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

/-- Real form of `(1 + η²)^(-2a)`. -/
def kernel (a η : ℝ) : ℝ := Real.exp (-2 * a * Real.log (1 + η ^ 2))

/-- Pressure, given by `-(1 / 2 : ℝ) * ∫ y, g y * kernel (a y) η`. -/
def pressure (g a : ℝ → ℝ) (η : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ y, g y * kernel (a y) η

/-- Sufficient hypotheses on the fixed clock data. No pressure derivatives occur here. -/
structure Admissible (g a : ℝ → ℝ) (A : ℝ) : Prop where
  cap_nonneg : 0 ≤ A
  integrable : Integrable g
  nonneg : ∀ y, 0 ≤ g y
  measurable : Measurable a
  exponent_nonneg : ∀ y, 0 ≤ a y
  exponent_le : ∀ y, a y ≤ A

theorem kernel_eq_rpow (a η : ℝ) : kernel a η = (1 + η ^ 2) ^ (-2 * a) := by
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + η ^ 2)]
  simp [kernel, mul_comm]

theorem kernel_pos (a η : ℝ) : 0 < kernel a η := Real.exp_pos _

theorem kernel_le_one {a : ℝ} (ha : 0 ≤ a) (η : ℝ) : kernel a η ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hl : 0 ≤ Real.log (1 + η ^ 2) := Real.log_nonneg (by linarith [sq_nonneg η])
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hl

theorem kernel_antitone {a b : ℝ} (hab : a ≤ b) (η : ℝ) :
    kernel b η ≤ kernel a η := by
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log (1 + η ^ 2) := Real.log_nonneg (by linarith [sq_nonneg η])
  exact mul_le_mul_of_nonneg_right (by linarith) hl

@[simp] theorem kernel_neg (a η : ℝ) : kernel a (-η) = kernel a η := by
  simp [kernel]

@[simp] theorem pressure_neg (g a : ℝ → ℝ) (η : ℝ) :
    pressure g a (-η) = pressure g a η := by simp [pressure]

theorem kernel_measurable {a : ℝ → ℝ} (ha : Measurable a) (η : ℝ) :
    Measurable (fun y => kernel (a y) η) := by
  exact (Real.continuous_exp.measurable.comp
    ((measurable_const.mul ha).mul_const (Real.log (1 + η ^ 2))))

theorem integrable_kernel {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (η : ℝ) : Integrable (fun y => g y * kernel (a y) η) := by
  apply h.integrable.mono'
    (h.integrable.aestronglyMeasurable.mul (kernel_measurable h.measurable η).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖g y * kernel (a y) η‖ ≤ g y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h.nonneg y) (kernel_pos _ _).le)]
    exact mul_le_of_le_one_right (h.nonneg y) (kernel_le_one (h.exponent_nonneg y) η)

theorem pressure_nonpos {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (η : ℝ) : pressure g a η ≤ 0 := by
  apply mul_nonpos_of_nonpos_of_nonneg (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  exact integral_nonneg fun y => mul_nonneg (h.nonneg y) (kernel_pos _ _).le

theorem pressure_le_mass {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (η : ℝ) :
    pressure g a η ≤ -(1 / 2 : ℝ) * kernel A η * ∫ y, g y := by
  have hm : (∫ y, g y * kernel A η) ≤ ∫ y, g y * kernel (a y) η :=
    integral_mono (h.integrable.mul_const _) (integrable_kernel h η)
      (fun y => mul_le_mul_of_nonneg_left (kernel_antitone (h.exponent_le y) η) (h.nonneg y))
  rw [integral_mul_const] at hm
  dsimp [pressure]
  linarith

/-- Shifting the logarithmic clock leaves the datum unchanged. -/
theorem pressure_translate (g a : ℝ → ℝ) (c η : ℝ) :
    pressure (fun y => g (y + c)) (fun y => a (y + c)) η = pressure g a η := by
  unfold pressure
  rw [integral_add_right_eq_self (fun y => g y * kernel (a y) η) c]

/-- A strip containing the complete real axis and therefore `[-1,1]`. -/
def strip : Set ℂ := {z | |z.im| < (1 / 2 : ℝ)}

theorem strip_open : IsOpen strip :=
  isOpen_lt (Complex.continuous_im.abs) continuous_const

@[simp] theorem real_mem_strip (η : ℝ) : (η : ℂ) ∈ strip := by
  norm_num [strip]

theorem base_mem_slitPlane {z : ℂ} (hz : z ∈ strip) :
    1 + z ^ 2 ∈ Complex.slitPlane := by
  apply Or.inl
  have him := abs_lt.mp (show |z.im| < (1 / 2 : ℝ) from hz)
  simp only [Complex.add_re, Complex.one_re, pow_two, Complex.mul_re]
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1 / 2), sq_nonneg (z.im + 1 / 2)]

/-- Complex kernel, given by `Complex.exp ((-2 * (a : ℂ)) * Complex.log (1 + z ^ 2))`. -/
def complexKernel (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-2 * (a : ℂ)) * Complex.log (1 + z ^ 2))

/-- Complex kernel derivative, given by `complexKernel a z * ((-2 * (a : ℂ)) * ((1 + z ^ 2)⁻¹ *
(2 * z)))`. -/
def complexKernelDeriv (a : ℝ) (z : ℂ) : ℂ :=
  complexKernel a z * ((-2 * (a : ℂ)) * ((1 + z ^ 2)⁻¹ * (2 * z)))

theorem hasDerivAt_complexKernel (a : ℝ) {z : ℂ} (hz : z ∈ strip) :
    HasDerivAt (complexKernel a) (complexKernelDeriv a z) z := by
  have hb : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * z) z := by
    simpa using ((hasDerivAt_id z).pow 2).const_add (1 : ℂ)
  exact (((Complex.hasDerivAt_log (base_mem_slitPlane hz)).comp z hb).const_mul
    (-2 * (a : ℂ))).cexp

theorem continuous_complexKernel_parameter (z : ℂ) :
    Continuous (fun b : ℝ => complexKernel b z) := by
  unfold complexKernel
  fun_prop

theorem continuous_complexKernelDeriv_parameter (z : ℂ) :
    Continuous (fun b : ℝ => complexKernelDeriv b z) := by
  unfold complexKernelDeriv complexKernel
  fun_prop

theorem continuousOn_complexKernel {s : Set (ℝ × ℂ)}
    (hs : ∀ p ∈ s, p.2 ∈ strip) :
    ContinuousOn (fun p : ℝ × ℂ => complexKernel p.1 p.2) s := by
  have hb : Continuous (fun p : ℝ × ℂ => 1 + p.2 ^ 2) := by fun_prop
  have ha : Continuous (fun p : ℝ × ℂ => -2 * (p.1 : ℂ)) := by fun_prop
  exact (ha.continuousOn.mul (hb.continuousOn.clog
    (fun p hp => base_mem_slitPlane (hs p hp)))).cexp

theorem continuousOn_complexKernelDeriv {s : Set (ℝ × ℂ)}
    (hs : ∀ p ∈ s, p.2 ∈ strip) :
    ContinuousOn (fun p : ℝ × ℂ => complexKernelDeriv p.1 p.2) s := by
  have hb : Continuous (fun p : ℝ × ℂ => 1 + p.2 ^ 2) := by fun_prop
  have ha : Continuous (fun p : ℝ × ℂ => -2 * (p.1 : ℂ)) := by fun_prop
  have hz : Continuous (fun p : ℝ × ℂ => 2 * p.2) := by fun_prop
  exact (continuousOn_complexKernel hs).mul (ha.continuousOn.mul
    ((hb.continuousOn.inv₀ (fun p hp => Complex.slitPlane_ne_zero
      (base_mem_slitPlane (hs p hp)))).mul hz.continuousOn))

theorem measurable_weighted_parameter {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) {k : ℝ → ℂ} (hk : Continuous k) :
    AEStronglyMeasurable (fun y => (g y : ℂ) * k (a y)) := by
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
    h.integrable.aestronglyMeasurable).mul
      (hk.measurable.comp h.measurable).aestronglyMeasurable

/-- Compactness of the bounded exponent interval supplies the dominating constant. -/
theorem integrable_weighted_parameter {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) {k : ℝ → ℂ} (hk : Continuous k) :
    Integrable (fun y => (g y : ℂ) * k (a y)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 A) hk.continuousOn
  apply (h.integrable.mul_const M).mono' (measurable_weighted_parameter h hk)
  exact Filter.Eventually.of_forall fun y => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hM (a y) ⟨h.exponent_nonneg y, h.exponent_le y⟩)
      (h.nonneg y)

/-- Complex pressure, given by `-(1 / 2 : ℂ) * ∫ y, (g y : ℂ) * complexKernel (a y) z`. -/
def complexPressure (g a : ℝ → ℝ) (z : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * ∫ y, (g y : ℂ) * complexKernel (a y) z

theorem integrable_complexKernel {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (z : ℂ) :
    Integrable (fun y => (g y : ℂ) * complexKernel (a y) z) :=
  integrable_weighted_parameter h (continuous_complexKernel_parameter z)

theorem hasDerivAt_complexPressure {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) {z : ℂ} (hz : z ∈ strip) :
    HasDerivAt (complexPressure g a)
      (-(1 / 2 : ℂ) * ∫ y, (g y : ℂ) * complexKernelDeriv (a y) z) z := by
  obtain ⟨ε, hε, hεs⟩ : ∃ ε, 0 < ε ∧ closedBall z ε ⊆ strip :=
    nhds_basis_closedBall.mem_iff.mp (strip_open.mem_nhds hz)
  have hc : IsCompact (Icc (0 : ℝ) A ×ˢ closedBall z ε) :=
    isCompact_Icc.prod (isCompact_closedBall z ε)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn
    (continuousOn_complexKernelDeriv (fun p hp => hεs hp.2))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun w y => (g y : ℂ) * complexKernel (a y) w)
    (F' := fun w y => (g y : ℂ) * complexKernelDeriv (a y) w)
    (bound := fun y => g y * M) (Metric.ball_mem_nhds _ hε)
    (Filter.Eventually.of_forall fun w => measurable_weighted_parameter h
      (continuous_complexKernel_parameter w))
    (integrable_complexKernel h z)
    (measurable_weighted_parameter h (continuous_complexKernelDeriv_parameter z))
    (Filter.Eventually.of_forall fun y w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.nonneg y)]
      exact mul_le_mul_of_nonneg_left
        (hM (a y, w) ⟨⟨h.exponent_nonneg y, h.exponent_le y⟩, ball_subset_closedBall hw⟩)
        (h.nonneg y))
    (h.integrable.mul_const M)
    (Filter.Eventually.of_forall fun y w hw =>
      (hasDerivAt_complexKernel (a y) (hεs (ball_subset_closedBall hw))).const_mul (g y : ℂ))
  exact hd.2.const_mul (-(1 / 2 : ℂ))

/-- Holomorphic extension is proved by dominated differentiation on the strip. -/
theorem complexPressure_analytic {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) : AnalyticOnNhd ℂ (complexPressure g a) strip := by
  apply DifferentiableOn.analyticOnNhd _ strip_open
  intro z hz
  exact (hasDerivAt_complexPressure h hz).differentiableAt.differentiableWithinAt

@[simp] theorem complexKernel_ofReal (a η : ℝ) :
    complexKernel a (η : ℂ) = (kernel a η : ℂ) := by
  have hb : (1 : ℂ) + (η : ℂ) ^ 2 = ((1 + η ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [complexKernel, hb, ← Complex.ofReal_log (by positivity : 0 ≤ 1 + η ^ 2)]
  have he : (-2 * (a : ℂ)) * (Real.log (1 + η ^ 2) : ℂ) =
      ((-2 * a * Real.log (1 + η ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  rfl

@[simp] theorem complexPressure_ofReal (g a : ℝ → ℝ) (η : ℝ) :
    complexPressure g a (η : ℂ) = (pressure g a η : ℂ) := by
  unfold complexPressure pressure
  have hi : (∫ y, (g y : ℂ) * complexKernel (a y) (η : ℂ)) =
      ((∫ y, g y * kernel (a y) η : ℝ) : ℂ) := by
    calc
      _ = ∫ y, ((g y * kernel (a y) η : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by simp
      _ = _ := integral_ofReal
  rw [hi]
  push_cast
  rfl

/-- Smoothness follows from the proved complex extension, for every finite order at once. -/
theorem pressure_contDiff {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) : ContDiff ℝ ∞ (pressure g a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro η
  have hc : ContDiffAt ℂ ∞ (complexPressure g a) (η : ℂ) :=
    (complexPressure_analytic h (η : ℂ) (real_mem_strip η)).contDiffAt
  simpa only [complexPressure_ofReal, Complex.ofReal_re] using hc.real_of_complex

theorem complexPressure_bounded_on_compact {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) {s : Set ℂ} (hs : IsCompact s) (hss : s ⊆ strip) :
    ∃ M : ℝ, ∀ z ∈ s, ‖complexPressure g a z‖ ≤ M := by
  apply hs.exists_bound_of_continuousOn
  intro z hz
  exact ((hasDerivAt_complexPressure h (hss hz)).continuousAt).continuousWithinAt

theorem integrable_exponent_weight {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) : Integrable (fun y => g y * a y) := by
  apply (h.integrable.mul_const A).mono'
    (h.integrable.aestronglyMeasurable.mul h.measurable.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖g y * a y‖ ≤ g y * A
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h.nonneg y) (h.exponent_nonneg y))]
    exact mul_le_mul_of_nonneg_left (h.exponent_le y) (h.nonneg y)

theorem exponent_weight_admissible {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) : Admissible (fun y => g y * a y) a A where
  cap_nonneg := h.cap_nonneg
  integrable := integrable_exponent_weight h
  nonneg := fun y => mul_nonneg (h.nonneg y) (h.exponent_nonneg y)
  measurable := h.measurable
  exponent_nonneg := h.exponent_nonneg
  exponent_le := h.exponent_le

theorem exponent_mass_pos_of_active {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A)
    (hactive : 0 < volume {y | 0 < g y ∧ 0 < a y}) :
    0 < ∫ y, g y * a y := by
  apply (integral_pos_iff_support_of_nonneg
    (fun y => mul_nonneg (h.nonneg y) (h.exponent_nonneg y))
    (integrable_exponent_weight h)).mpr
  have heq : Function.support (fun y => g y * a y) = {y | 0 < g y ∧ 0 < a y} := by
    ext y
    simp only [Function.mem_support, mem_ofPred_eq, ne_eq, mul_eq_zero, not_or]
    constructor
    · rintro ⟨hg, ha⟩
      exact ⟨lt_of_le_of_ne (h.nonneg y) (Ne.symm hg),
        lt_of_le_of_ne (h.exponent_nonneg y) (Ne.symm ha)⟩
    · rintro ⟨hg, ha⟩
      exact ⟨ne_of_gt hg, ne_of_gt ha⟩
  rwa [heq]

theorem complexKernelDeriv_ofReal (a η : ℝ) :
    complexKernelDeriv a (η : ℂ) =
      ((kernel a η * (-4 * a * η / (1 + η ^ 2)) : ℝ) : ℂ) := by
  rw [complexKernelDeriv, complexKernel_ofReal]
  push_cast
  ring

/-- The derivative is the positive radial factor times the weighted positive-exponent mass. -/
theorem hasDerivAt_pressure {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (η : ℝ) :
    HasDerivAt (pressure g a)
      ((2 * η / (1 + η ^ 2)) * ∫ y, g y * a y * kernel (a y) η) η := by
  have hc := (hasDerivAt_complexPressure h (real_mem_strip η)).real_of_complex
  have hi : (∫ y, (g y : ℂ) * complexKernelDeriv (a y) (η : ℂ)) =
      (((-4 * η / (1 + η ^ 2)) * ∫ y, g y * a y * kernel (a y) η : ℝ) : ℂ) := by
    calc
      _ = ∫ y, ((g y * (kernel (a y) η * (-4 * a y * η / (1 + η ^ 2))) : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change (g y : ℂ) * complexKernelDeriv (a y) (η : ℂ) = _
          rw [complexKernelDeriv_ofReal]
          push_cast
          rfl
      _ = ((∫ y, g y * (kernel (a y) η * (-4 * a y * η / (1 + η ^ 2))) : ℝ) : ℂ) :=
        integral_ofReal
      _ = _ := by
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
  rw [hi] at hc
  have hr : (-(1 / 2 : ℂ) *
      (((-4 * η / (1 + η ^ 2)) * ∫ y, g y * a y * kernel (a y) η : ℝ) : ℂ)).re =
      (2 * η / (1 + η ^ 2)) * ∫ y, g y * a y * kernel (a y) η := by
    have hhalf : -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hhalf, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hr] at hc
  simpa only [complexPressure_ofReal, Complex.ofReal_re] using hc

theorem deriv_pressure {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (η : ℝ) :
    deriv (pressure g a) η =
      (2 * η / (1 + η ^ 2)) * ∫ y, g y * a y * kernel (a y) η :=
  (hasDerivAt_pressure h η).deriv

theorem weighted_kernel_pos {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (hmass : 0 < ∫ y, g y * a y) (η : ℝ) :
    0 < ∫ y, g y * a y * kernel (a y) η := by
  have hp := pressure_le_mass (exponent_weight_admissible h) η
  have hpos := mul_pos (kernel_pos A η) hmass
  dsimp [pressure] at hp
  linarith

theorem deriv_pressure_pos {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (hmass : 0 < ∫ y, g y * a y)
    {η : ℝ} (hη : 0 < η) : 0 < deriv (pressure g a) η := by
  rw [deriv_pressure h]
  exact mul_pos (div_pos (by positivity) (by positivity)) (weighted_kernel_pos h hmass η)

theorem deriv_pressure_pos_of_active {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A)
    (hactive : 0 < volume {y | 0 < g y ∧ 0 < a y})
    {η : ℝ} (hη : 0 < η) : 0 < deriv (pressure g a) η :=
  deriv_pressure_pos h (exponent_mass_pos_of_active h hactive) hη

theorem deriv_pressure_neg {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) (hmass : 0 < ∫ y, g y * a y)
    {η : ℝ} (hη : η < 0) : deriv (pressure g a) η < 0 := by
  rw [deriv_pressure h]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by positivity))
    (weighted_kernel_pos h hmass η)

theorem deriv_pressure_zero {g a : ℝ → ℝ} {A : ℝ}
    (h : Admissible g a A) : deriv (pressure g a) 0 = 0 := by simp [deriv_pressure h]

/-- An arbitrary measurable positive prefix contributes its exact constant-exponent mass. -/
theorem pressure_le_prefix {g a : ℝ → ℝ} {A b : ℝ}
    (h : Admissible g a A) {s : Set ℝ} (hs : MeasurableSet s)
    (ha : ∀ y ∈ s, a y = b) (η : ℝ) :
    pressure g a η ≤ -(1 / 2 : ℝ) * kernel b η * ∫ y in s, g y := by
  have hp := setIntegral_le_integral (s := s) (integrable_kernel h η)
    (Filter.Eventually.of_forall fun y => mul_nonneg (h.nonneg y) (kernel_pos _ _).le)
  have heq : (∫ y in s, g y * kernel (a y) η) = (∫ y in s, g y) * kernel b η := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hs] with y hy
    rw [ha y hy]
  rw [heq] at hp
  dsimp [pressure]
  linarith

theorem pressure_le_prefix_mass {g a : ℝ → ℝ} {A b m : ℝ}
    (h : Admissible g a A) {s : Set ℝ} (hs : MeasurableSet s)
    (ha : ∀ y ∈ s, a y = b) (hm : m ≤ ∫ y in s, g y) (η : ℝ) :
    pressure g a η ≤ -(1 / 2 : ℝ) * m * kernel b η := by
  have hp := pressure_le_prefix h hs ha η
  have hk := mul_le_mul_of_nonneg_left hm (kernel_pos b η).le
  linarith

theorem kernel_one (η : ℝ) : kernel 1 η = (1 + η ^ 2)⁻¹ ^ 2 := by
  rw [kernel_eq_rpow]
  have hb : 0 ≤ 1 + η ^ 2 := by positivity
  norm_num only [mul_one]
  rw [Real.rpow_neg hb, Real.rpow_two, inv_pow]

/-- The manuscript's ideal prefix has exponent one and mass `5 P²`. -/
theorem manuscript_prefix_bound {g a : ℝ → ℝ} {A P : ℝ}
    (h : Admissible g a A) {s : Set ℝ} (hs : MeasurableSet s)
    (ha : ∀ y ∈ s, a y = 1) (hm : 5 * P ^ 2 ≤ ∫ y in s, g y) (η : ℝ) :
    pressure g a η ≤ -(5 / 2 : ℝ) * P ^ 2 * ((1 + η ^ 2)⁻¹) ^ 2 := by
  have hp := pressure_le_prefix_mass h hs ha hm η
  rw [kernel_one] at hp
  linarith

/-- Exact integral of the ideal clock prefix `P² exp(y/5)`. -/
theorem ideal_prefix_mass (P : ℝ) :
    (∫ y in Iic (0 : ℝ), P ^ 2 * Real.exp ((1 / 5 : ℝ) * y)) = 5 * P ^ 2 := by
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : 0 < (1 / 5 : ℝ))]
  norm_num
  ring

theorem prefix_mass_eq {g : ℝ → ℝ} {P : ℝ}
    (hg : ∀ y ≤ 0, g y = P ^ 2 * Real.exp ((1 / 5 : ℝ) * y)) :
    (∫ y in Iic (0 : ℝ), g y) = 5 * P ^ 2 := by
  rw [← ideal_prefix_mass P]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  exact hg y hy

/-- The exact manuscript lower bound, with the prefix integral evaluated. -/
theorem pressure_le_of_ideal_prefix {g a : ℝ → ℝ} {A P : ℝ}
    (h : Admissible g a A)
    (hg : ∀ y ≤ 0, g y = P ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) (η : ℝ) :
    pressure g a η ≤ -(5 / 2 : ℝ) * P ^ 2 * ((1 + η ^ 2)⁻¹) ^ 2 := by
  exact manuscript_prefix_bound h measurableSet_Iic ha (prefix_mass_eq hg).ge η

theorem exponent_mass_pos_of_ideal_prefix {g a : ℝ → ℝ} {A P : ℝ}
    (h : Admissible g a A) (hP : 0 < P)
    (hg : ∀ y ≤ 0, g y = P ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) : 0 < ∫ y, g y * a y := by
  have hp := setIntegral_le_integral (s := Iic (0 : ℝ)) (integrable_exponent_weight h)
    (Filter.Eventually.of_forall fun y => mul_nonneg (h.nonneg y) (h.exponent_nonneg y))
  have heq : (∫ y in Iic (0 : ℝ), g y * a y) = 5 * P ^ 2 := by
    rw [← prefix_mass_eq hg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    rw [ha y hy, mul_one]
  rw [heq] at hp
  exact lt_of_lt_of_le (by positivity) hp

theorem pressure_neg_of_ideal_prefix {g a : ℝ → ℝ} {A P : ℝ}
    (h : Admissible g a A) (hP : 0 < P)
    (hg : ∀ y ≤ 0, g y = P ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) (η : ℝ) : pressure g a η < 0 := by
  apply lt_of_le_of_lt (pressure_le_of_ideal_prefix h hg ha η)
  have hb : 0 < ((1 + η ^ 2)⁻¹) ^ 2 := by positivity
  have hneg : -(5 / 2 : ℝ) * P ^ 2 < 0 := mul_neg_of_neg_of_pos (by norm_num) (by positivity)
  exact mul_neg_of_neg_of_pos hneg hb

end NavierStokes.PressureDatum

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.NaturalAxisData

open Set
open scoped ContDiff Topology

/-- D, given by `1 / 2 - h`. -/
def D (h : ℝ) : ℝ := 1 / 2 - h
/-- A, given by `1 / 2 + h`. -/
def A (h : ℝ) : ℝ := 1 / 2 + h
/-- D, given by `1 - η ^ 2`. -/
def d (η : ℝ) : ℝ := 1 - η ^ 2
/-- L, given by `1 - 2 * h * η ^ 2`. -/
def L (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2
/-- U, given by `4 * η + j`. -/
def U (j η : ℝ) : ℝ := 4 * η + j
/-- H, given by `D h * η + d η * U j η`. -/
def H (h j η : ℝ) : ℝ := D h * η + d η * U j η
/-- W, given by `1 - 4 * d η - 2 * D h * η * U j η`. -/
def W (h j η : ℝ) : ℝ := 1 - 4 * d η - 2 * D h * η * U j η
/-- Z, given by `-A h * (1 - 2 * η * U j η) * U j η - H h j η * 4 - d η * deriv P η + 4 * A h *
η * P η`. -/
def Z (h j : ℝ) (P : ℝ → ℝ) (η : ℝ) : ℝ :=
  -A h * (1 - 2 * η * U j η) * U j η - H h j η * 4 -
    d η * deriv P η + 4 * A h * η * P η

/-- Chi, given by `(H h j η) ^ 2 / ((H h j η) ^ 2 + σ ^ 2)`. -/
def chi (h j σ η : ℝ) : ℝ := (H h j η) ^ 2 / ((H h j η) ^ 2 + σ ^ 2)

/-- A concrete range of choices permitted by the manuscript's smallness order. -/
structure SmallParameters (h j : ℝ) : Prop where
  h_pos : 0 < h
  h_le : h ≤ 1 / 1000
  j_pos : 0 < j
  j_le : j ≤ 1 / 1000

theorem D_bounds {h j : ℝ} (p : SmallParameters h j) :
    499 / 1000 ≤ D h ∧ D h < 1 / 2 := by
  unfold D
  constructor <;> linarith [p.h_pos, p.h_le]

theorem D_pos {h j : ℝ} (p : SmallParameters h j) : 0 < D h := by
  linarith [(D_bounds p).1]

theorem A_bounds {h j : ℝ} (p : SmallParameters h j) :
    1 / 2 < A h ∧ A h ≤ 501 / 1000 := by
  unfold A
  constructor <;> linarith [p.h_pos, p.h_le]

theorem A_pos {h j : ℝ} (p : SmallParameters h j) : 0 < A h := by
  linarith [(A_bounds p).1]

theorem d_nonneg {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : 0 ≤ d η := by
  have hp := mul_nonneg (sub_nonneg.mpr hη.2)
    (show 0 ≤ η + 1 by linarith [hη.1])
  unfold d
  linarith

theorem L_lower_bound {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 499 / 500 ≤ L h η := by
  have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
  dsimp [d, L] at *
  linarith [p.h_le]

theorem L_pos {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 0 < L h η := by
  linarith [L_lower_bound p hη]

theorem neg_W_formula (h j η : ℝ) :
    -W h j η = 3 - 8 * h * η ^ 2 + 2 * D h * j * η := by
  unfold W U d D
  ring

/-- The proof gives 2.991, stronger than the manuscript's 2.8. -/
theorem neg_W_lower_bound {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 2991 / 1000 ≤ -W h j η := by
  have hDj : 0 ≤ 2 * D h * j :=
    mul_nonneg (mul_nonneg (by norm_num) (D_pos p).le) p.j_pos.le
  have hDjle : 2 * D h * j ≤ j := by
    linarith [mul_nonneg (show 0 ≤ 1 - 2 * D h by linarith [(D_bounds p).2]) p.j_pos.le]
  have hηDj : -(2 * D h * j) ≤ 2 * D h * j * η := by
    linarith [mul_nonneg hDj (show 0 ≤ η + 1 by linarith [hη.1])]
  have hhη : h * η ^ 2 ≤ h := by
    have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
    dsimp [d] at hp
    linarith
  rw [neg_W_formula]
  linarith [p.h_le, p.j_le]

theorem neg_W_gt {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 14 / 5 < -W h j η := by
  linarith [neg_W_lower_bound p hη]

theorem H_contDiff (h j : ℝ) : ContDiff ℝ ∞ (H h j) := by
  unfold H U d
  exact (contDiff_const.mul contDiff_id).add
    ((contDiff_const.sub (contDiff_id.pow 2)).mul
      ((contDiff_const.mul contDiff_id).add contDiff_const))

theorem H_at_left (h j : ℝ) : H h j (-j / 4) = -(D h * j) / 4 := by
  unfold H U d
  ring

theorem H_at_right (h j : ℝ) :
    H h j (-j / 5) = (j / 5) * (1 - D h - j ^ 2 / 25) := by
  unfold H U d
  ring

theorem H_left_neg {h j : ℝ} (p : SmallParameters h j) : H h j (-j / 4) < 0 := by
  rw [H_at_left]
  have hp := mul_pos (D_pos p) p.j_pos
  linarith

theorem H_right_pos {h j : ℝ} (p : SmallParameters h j) : 0 < H h j (-j / 5) := by
  rw [H_at_right]
  apply mul_pos (div_pos p.j_pos (by norm_num))
  have hj1 : j ≤ 1 := by linarith [p.j_le]
  have hj2 : j ^ 2 ≤ 1 := by
    linarith [mul_nonneg (sub_nonneg.mpr hj1) (show 0 ≤ j + 1 by linarith [p.j_pos])]
  linarith [(D_bounds p).2]

theorem H_pos_of_nonneg {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hη0 : 0 ≤ η) : 0 < H h j η := by
  rcases eq_or_lt_of_le hη0 with heq | hpos
  · subst η
    simpa [H, U, d] using p.j_pos
  · have hU : 0 ≤ U j η := by dsimp [U]; linarith [p.j_pos]
    exact add_pos_of_pos_of_nonneg (mul_pos (D_pos p) hpos)
      (mul_nonneg (d_nonneg hη) hU)

theorem H_neg_of_le_left {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hleft : η ≤ -j / 4) : H h j η < 0 := by
  have hη0 : η < 0 := by linarith [p.j_pos]
  have hU : U j η ≤ 0 := by dsimp [U]; linarith
  exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (D_pos p) hη0)
    (mul_nonpos_of_nonneg_of_nonpos (d_nonneg hη) hU)

theorem root_negative {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hzero : H h j η = 0) : η < 0 := by
  by_contra hn
  have hp := H_pos_of_nonneg p hη (le_of_not_gt hn)
  linarith

theorem cross_identity (h j x y : ℝ) :
    H h j x * d y - H h j y * d x =
      (x - y) * (D h * (1 + x * y) + 4 * d x * d y) := by
  unfold H U d
  ring

/-- Uniqueness is proved algebraically from the actual polynomial. -/
theorem root_unique {h j x y : ℝ} (p : SmallParameters h j)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hx0 : H h j x = 0) (hy0 : H h j y = 0) : x = y := by
  have hxn := root_negative p hx hx0
  have hyn := root_negative p hy hy0
  have hxy : 0 < x * y := mul_pos_of_neg_of_neg hxn hyn
  have hp : 0 < D h * (1 + x * y) + 4 * d x * d y :=
    add_pos_of_pos_of_nonneg (mul_pos (D_pos p) (by linarith))
      (mul_nonneg (mul_nonneg (by norm_num) (d_nonneg hx)) (d_nonneg hy))
  have hid := cross_identity h j x y
  rw [hx0, hy0] at hid
  have hprod : (x - y) * (D h * (1 + x * y) + 4 * d x * d y) = 0 := by
    linarith
  have heq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hp)
  linarith

/-- The unique zero lies strictly between `-j/4` and `-j/5`. -/
theorem exists_unique_root {h j : ℝ} (p : SmallParameters h j) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  have hab : -j / 4 ≤ -j / 5 := by linarith [p.j_pos]
  obtain ⟨η₀, hη₀, hz⟩ :=
    intermediate_value_Ioo (f := H h j) hab (H_contDiff h j).continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (H h j (-j / 4)) (H h j (-j / 5)) from
        ⟨H_left_neg p, H_right_pos p⟩)
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_le, p.j_pos]
  exact ⟨η₀, hη₀, hz, fun η hη hzero => root_unique p hη hI hzero hz⟩

/-- Real pressure hypotheses provided by the separately constructed datum.
The derivative-sign condition is weak, so zero derivative is permitted. -/
structure PressureData (P : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ P
  negative : ∀ η ∈ Icc (-1 : ℝ) 1, P η ≤ -1
  derivative_sign : ∀ η ∈ Icc (-1 : ℝ) 1, 0 ≤ η * deriv P η

theorem PressureData.deriv_nonpos {P : ℝ → ℝ} (pP : PressureData P)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hn : η < 0) : deriv P η ≤ 0 := by
  by_contra hp
  have hm := mul_neg_of_neg_of_pos hn (lt_of_not_ge hp)
  exact (not_lt_of_ge (pP.derivative_sign η hη)) hm

/-- A quantitative version of the crucial nonzero-root assertion:
pressure at most minus one is already sufficient. -/
theorem Z_at_root_lower {h j η : ℝ} {P : ℝ → ℝ} (p : SmallParameters h j)
    (hη : η ∈ Ioo (-j / 4) (-j / 5)) (hz : H h j η = 0)
    (hP : P η ≤ -1) (hP' : deriv P η ≤ 0) : j / 5 < Z h j P η := by
  have hηn : η < 0 := by linarith [hη.2, p.j_pos]
  have hI : η ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη.1, hη.2, p.j_pos, p.j_le]
  have hU : 0 < U j η := by dsimp [U]; linarith [hη.1]
  have hUj : U j η < j / 5 := by dsimp [U]; linarith [hη.2]
  have hrU : -η * U j η ≤ U j η := by
    simpa using mul_le_mul_of_nonneg_right (show -η ≤ 1 by linarith [hI.1]) hU.le
  have hfactor : 1 - 2 * η * U j η ≤ 2 := by linarith [p.j_le]
  have hadverse : (1 - 2 * η * U j η) * U j η < 2 * j / 5 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfactor hU.le) (by linarith)
  have hpressure := mul_le_mul_of_nonpos_left hP hηn.le
  have hcore : 2 * j / 5 < -(1 - 2 * η * U j η) * U j η + 4 * η * P η := by
    linarith [hη.2]
  have hderiv : d η * deriv P η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (d_nonneg hI) hP'
  calc
    j / 5 ≤ A h * (2 * j / 5) := by
      linarith [mul_nonneg (show 0 ≤ A h - 1 / 2 by linarith [(A_bounds p).1]) p.j_pos.le]
    _ < A h * (-(1 - 2 * η * U j η) * U j η + 4 * η * P η) :=
      mul_lt_mul_of_pos_left hcore (A_pos p)
    _ ≤ Z h j P η := by
      unfold Z
      rw [hz]
      linarith

theorem Z_continuous (h j : ℝ) {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) :
    Continuous (Z h j P) := by
  have hc : Continuous P := hP.continuous
  have hd : Continuous (deriv P) := hP.continuous_deriv
    (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  unfold Z H U d
  fun_prop

/-- The true fixed data have a unique negative root at which `Z` is bounded
strictly away from zero. No root property is an input hypothesis. -/
theorem exists_root_with_positive_Z {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j P η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  obtain ⟨η₀, hη₀, hz, huniq⟩ := exists_unique_root p
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_pos, p.j_le]
  have hn : η₀ < 0 := by linarith [hη₀.2, p.j_pos]
  exact ⟨η₀, hη₀, hz, Z_at_root_lower p hη₀ hz (pP.negative η₀ hI)
    (pP.deriv_nonpos hI hn), huniq⟩

/-- On the actual compact low-`Z` set, `H²` has a strictly positive uniform
minimum. The threshold is the explicit choice `δ_* = j/10`. -/
theorem low_Z_has_H_margin {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ m : ℝ, 0 < m ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → m ≤ (H h j η) ^ 2 := by
  obtain ⟨η₀, hη₀, hz, hZpos, huniq⟩ := exists_root_with_positive_Z p pP
  let K : Set ℝ := Icc (-1) 1 ∩ {η | |Z h j P η| ≤ j / 10}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le (Z_continuous h j pP.smooth).abs continuous_const)
  have hnonzero : ∀ η ∈ K, H h j η ≠ 0 := by
    intro η hη hzero
    have heq := huniq η hη.1 hzero
    have hbound : Z h j P η ≤ j / 10 := (le_abs_self _).trans hη.2
    rw [heq] at hbound
    linarith [p.j_pos]
  have hpositive : ∀ η ∈ K, 0 < (H h j η) ^ 2 :=
    fun η hη => sq_pos_of_ne_zero (hnonzero η hη)
  obtain ⟨m, hm, hbound⟩ := hK.exists_forall_le'
    ((H_contDiff h j).continuous.pow 2).continuousOn hpositive
  exact ⟨m, hm, fun η hη hZ => hbound η ⟨hη, hZ⟩⟩

theorem chi_contDiff (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ContDiff ℝ ∞ (chi h j σ) := by
  unfold chi
  apply ((H_contDiff h j).pow 2).div (((H_contDiff h j).pow 2).add contDiff_const)
  intro η
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hσ))

theorem chi_bounds (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) (η : ℝ) :
    0 ≤ chi h j σ η ∧ chi h j σ η < 1 := by
  have hsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hden : 0 < (H h j η) ^ 2 + σ ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hsq
  constructor
  · exact div_nonneg (sq_nonneg _) hden.le
  · exact (div_lt_one hden).mpr (lt_add_of_pos_right _ hsq)

/-- Construct the cutoff scale after the root-separation proof. The proof
chooses `σ_* = sqrt(m)/20` from the actual compact minimum bound. -/
theorem exists_sigma {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → 99 / 100 < chi h j σ η := by
  obtain ⟨m, hm, hbound⟩ := low_Z_has_H_margin p pP
  let σ : ℝ := Real.sqrt m / 20
  have hσ : 0 < σ := div_pos (Real.sqrt_pos.mpr hm) (by norm_num)
  have hsq : σ ^ 2 = m / 400 := by
    dsimp [σ]
    rw [div_pow, Real.sq_sqrt hm.le]
    norm_num
  refine ⟨σ, hσ, ?_⟩
  intro η hη hZ
  have hH := hbound η hη hZ
  have hden : 0 < (H h j η) ^ 2 + σ ^ 2 := by linarith [sq_nonneg σ]
  unfold chi
  apply (lt_div_iff₀ hden).mpr
  linarith

/-- The requested fixed positive choices, with no input separation premise. -/
theorem exists_cutoff_parameters {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, |Z h j P η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) := by
  obtain ⟨σ, hσ, hcut⟩ := exists_sigma p pP
  exact ⟨j / 10, σ, div_pos p.j_pos (by norm_num), hσ, hcut, chi_contDiff h j hσ⟩

/-- The actual integral pressure datum satisfies the real axis hypotheses.
The ideal-prefix amplitude `B ≥ 2` suffices uniformly on `[-1,1]`. -/
theorem pressureData_of_ideal_prefix {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    PressureData (PressureDatum.pressure g a) := by
  have hBpos : 0 < B := by linarith
  have hmass := PressureDatum.exponent_mass_pos_of_ideal_prefix hp hBpos hg ha
  refine ⟨PressureDatum.pressure_contDiff hp, ?_, ?_⟩
  · intro η hη
    have hηsq : η ^ 2 ≤ 1 := by
      have hd := d_nonneg hη
      dsimp [d] at hd
      linarith
    have hden : 0 < 1 + η ^ 2 := by positivity
    have hi : 1 / 2 ≤ (1 + η ^ 2)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hden).mpr
      linarith
    have hisq : (1 / 4 : ℝ) ≤ ((1 + η ^ 2)⁻¹) ^ 2 := by
      linarith [sq_nonneg ((1 + η ^ 2)⁻¹ - 1 / 2)]
    have hBsq : (4 : ℝ) ≤ B ^ 2 := by nlinarith
    have hprod : (1 : ℝ) ≤ B ^ 2 * ((1 + η ^ 2)⁻¹) ^ 2 := by
      have hm := mul_le_mul hBsq hisq (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg B)
      linarith
    have hpressure := PressureDatum.pressure_le_of_ideal_prefix hp hg ha η
    linarith
  · intro η hη
    rcases lt_trichotomy η 0 with hn | rfl | hpη
    · exact (mul_pos_of_neg_of_neg hn (PressureDatum.deriv_pressure_neg hp hmass hn)).le
    · simp
    · exact (mul_pos hpη (PressureDatum.deriv_pressure_pos hp hmass hpη)).le

/-- End-to-end real cutoff construction from the actual weighted pressure
integral and its ideal prefix, rather than assumed pressure conclusions. -/
theorem ideal_prefix_cutoff_parameters {h j : ℝ} (p : SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |Z h j (PressureDatum.pressure g a) η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) :=
  exists_cutoff_parameters p (pressureData_of_ideal_prefix hp hB hg ha)

theorem ideal_prefix_root_positive {h j : ℝ} (p : SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j (PressureDatum.pressure g a) η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ :=
  exists_root_with_positive_Z p (pressureData_of_ideal_prefix hp hB hg ha)

end NavierStokes.NaturalAxisData

end
end

end

section

/-!
# Uniform analytic input for the natural-axis coefficient space

The hypotheses concern one common complex neighborhood of the entire real
parameter interval. Cauchy's integral formula supplies bounds on actual
derivatives; the derivative bounds are not hypotheses of the construction.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.AnalyticCoefficientBounds

open Set Metric Filter Complex
open scoped Topology ContDiff NNReal
open AxisCoefficientSpace

/-- The closed radius-`ρ` neighborhood of the real parameter interval. -/
def closedTube (I : Window) (ρ : ℝ) : Set ℂ :=
  {z | ∃ x ∈ I.interval, dist z (x : ℂ) ≤ ρ}

theorem closedBall_subset_closedTube (I : Window) (ρ : ℝ)
    {x : ℝ} (hx : x ∈ I.interval) :
    closedBall (x : ℂ) ρ ⊆ closedTube I ρ :=
  fun _ hz => ⟨x, hx, hz⟩

theorem real_mem_closedTube (I : Window) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : ℝ} (hx : x ∈ I.interval) : (x : ℂ) ∈ closedTube I ρ :=
  ⟨x, hx, by simpa using hρ⟩

/-- A uniform complex value bound, with holomorphy on a neighborhood of
the same closed tube. No derivative estimates occur in this predicate. -/
structure UnitHolomorphic (I : Window) (ρ : ℝ) (f : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ f (closedTube I ρ)
  norm_le_one : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ 1

/-- Bound one Cauchy coefficient directly by its circle integral. -/
theorem norm_cauchyCoefficient_le {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hb : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ 1) (m : ℕ) :
    ‖cauchyPowerSeries f c ρ m (fun _ => 1)‖ ≤ (ρ⁻¹) ^ m := by
  rw [cauchyPowerSeries_apply]
  have hbound : ∀ z ∈ sphere c ρ,
      ‖(1 / (z - c)) ^ m • (z - c)⁻¹ • f z‖ ≤ (ρ⁻¹) ^ m * ρ⁻¹ := by
    intro z hz
    have hz' : ‖z - c‖ = ρ := by simpa only [mem_sphere, dist_eq_norm] using hz
    rw [norm_smul, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hz', one_div]
    calc
      (ρ⁻¹) ^ m * (ρ⁻¹ * ‖f z‖) ≤ (ρ⁻¹) ^ m * (ρ⁻¹ * 1) := by
        gcongr
        exact hb z hz
      _ = (ρ⁻¹) ^ m * ρ⁻¹ := by ring
  calc
    _ ≤ ρ * ((ρ⁻¹) ^ m * ρ⁻¹) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hbound
    _ = (ρ⁻¹) ^ m := by
      calc
        ρ * ((ρ⁻¹) ^ m * ρ⁻¹) = (ρ⁻¹) ^ m * (ρ * ρ⁻¹) := by ring
        _ = (ρ⁻¹) ^ m := by rw [mul_inv_cancel₀ hρ.ne', mul_one]

/-- Cauchy's estimate for every genuine complex derivative, derived from
the circle-integral coefficients and the factorial derivative identity. -/
theorem norm_iteratedDeriv_le {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (closedBall c ρ))
    (hb : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ 1) (m : ℕ) :
    ‖iteratedDeriv m f c‖ ≤ (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  let r : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hp := (show DifferentiableOn ℂ f (closedBall c (r : ℝ)) from hf).hasFPowerSeriesOnBall
    (show 0 < r from hρ)
  have heq : iteratedDeriv m f c =
      m.factorial • cauchyPowerSeries f c ρ m (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    exact (hp.factorial_smul (1 : ℂ) m).symm
  rw [heq, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_cauchyCoefficient_le hρ hb m) (by positivity)

/-- The real part of a genuine complex jet, evaluated on the real axis. -/
def realJet (f : ℂ → ℂ) (m : ℕ) (x : ℝ) : ℝ :=
  (iteratedDeriv m f (x : ℂ)).re

theorem hasDerivAt_realJet {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (m : ℕ) :
    HasDerivAt (realJet f m) (realJet f (m + 1) x) x := by
  have hm : AnalyticAt ℂ (iteratedDeriv m f) (x : ℂ) := by
    simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv m
  unfold realJet
  simpa only [iteratedDeriv_succ] using hm.differentiableAt.hasDerivAt.real_of_complex

/-- The real-axis jets really are the ordinary iterated real derivatives. -/
theorem iteratedDeriv_realPart {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => (f t).re) x = realJet f m x := by
  induction m generalizing x with
  | zero => simp [realJet]
  | succ m ih =>
      have heq : iteratedDeriv m (fun t : ℝ => (f t).re) =ᶠ[𝓝 x] realJet f m := by
        filter_upwards [(Complex.continuous_ofReal.tendsto x).eventually
          hf.eventually_analyticAt] with y hy
        exact ih hy
      rw [iteratedDeriv_succ, heq.deriv_eq]
      exact (hasDerivAt_realJet hf m).deriv

theorem UnitHolomorphic.abs_realJet_le {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    |realJet f m x| ≤ (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  apply (Complex.abs_re_le_norm _).trans
  apply norm_iteratedDeriv_le hρ
  · exact hf.analytic.differentiableOn.mono (closedBall_subset_closedTube I ρ hx)
  · intro z hz
    exact hf.norm_le_one z (closedBall_subset_closedTube I ρ hx
      (sphere_subset_closedBall hz))

theorem UnitHolomorphic.abs_iteratedDeriv_le {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDeriv m (fun t : ℝ => (f t).re) x| ≤
      (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
  rw [iteratedDeriv_realPart (hf.analytic x (real_mem_closedTube I hρ.le hx))]
  exact hf.abs_realJet_le hρ m hx

/-- The loss in passing from a complex radius to the coefficient radius. -/
def radiusLoss (q : ℝ) : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ 2 * q ^ m

theorem summable_radiusLoss {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 2 * q ^ m) := by
  have hn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_geometric_of_norm_lt_one hn
  convert! (h2.add (h1.mul_left 2)).add h0 using 1
  ext m
  ring

theorem radiusLoss_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ radiusLoss q :=
  tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq _))

theorem term_le_radiusLoss {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ((m : ℝ) + 1) ^ 2 * q ^ m ≤ radiusLoss q :=
  (summable_radiusLoss hq hq1).le_tsum m
    (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg hq _))

/-- The Cauchy bound fits the exact degree-zero manuscript weight. -/
theorem cauchy_bound_le_weight {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (m : ℕ) :
    (m.factorial : ℝ) * (ρ⁻¹) ^ m ≤
      radiusLoss (ε / ρ) * AxisWeightEstimates.weight ε 0 m := by
  have hρ : 0 < ρ := hε.trans hερ
  have hq : 0 ≤ ε / ρ := (div_pos hε hρ).le
  have hq1 : ε / ρ < 1 := (div_lt_one hρ).mpr hερ
  have hpow : (ε / ρ) ^ m * (ε⁻¹) ^ m = (ρ⁻¹) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hsq : ((m : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have heq : ((m : ℝ) + 1) ^ 2 * (ε / ρ) ^ m *
      AxisWeightEstimates.weight ε 0 m = (m.factorial : ℝ) * (ρ⁻¹) ^ m := by
    simp only [AxisWeightEstimates.weight, pow_zero, Nat.choose_self,
      Nat.cast_zero, Nat.cast_one, zero_add, one_pow, one_mul, mul_one]
    calc
      ((m : ℝ) + 1) ^ 2 * (ε / ρ) ^ m *
          ((ε⁻¹) ^ m * (m.factorial : ℝ) / ((m : ℝ) + 1) ^ 2) =
          ((ε / ρ) ^ m * (ε⁻¹) ^ m) * (m.factorial : ℝ) := by
            field_simp
      _ = (m.factorial : ℝ) * (ρ⁻¹) ^ m := by rw [hpow, mul_comm]
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (term_le_radiusLoss hq hq1 m)
    (AxisWeightEstimates.weight_pos hε 0 m).le

/-- A coefficient family concentrated at radial degree zero. -/
def degreeZeroJet (f : ℂ → ℂ) (n m : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then realJet f m x else 0

theorem UnitHolomorphic.degreeZeroJet_continuous {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (n m : ℕ) :
    ContinuousOn (degreeZeroJet f n m) I.interval := by
  change ContinuousOn (fun x => if n = 0 then realJet f m x else 0) I.interval
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte]
    intro x hx
    exact (hasDerivAt_realJet
      (hf.analytic x (real_mem_closedTube I hρ.le hx)) m).continuousAt.continuousWithinAt
  · simpa only [degreeZeroJet, ite_eq_right hn] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) I.interval)

theorem UnitHolomorphic.degreeZeroJet_hasDerivWithinAt
    {I : Window} {ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hρ : 0 < ρ) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (degreeZeroJet f n m) (degreeZeroJet f n (m + 1) x) I.interval x := by
  change HasDerivWithinAt (fun y => if n = 0 then realJet f m y else 0)
    (if n = 0 then realJet f (m + 1) x else 0) I.interval x
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte]
    exact (hasDerivAt_realJet
      (hf.analytic x (real_mem_closedTube I hρ.le hx)) m).hasDerivWithinAt
  · simpa only [degreeZeroJet, ite_eq_right hn] using
      (hasDerivWithinAt_const x I.interval (0 : ℝ))

theorem UnitHolomorphic.degreeZeroJet_bound {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |degreeZeroJet f n m x| ≤
      radiusLoss (ε / ρ) * AxisWeightEstimates.weight ε n m := by
  by_cases hn : n = 0
  · subst n
    simpa only [degreeZeroJet, ↓reduceIte] using
      (hf.abs_realJet_le (hε.trans hερ) m hx).trans (cauchy_bound_le_weight hε hερ m)
  · simp only [degreeZeroJet, ite_eq_right hn, abs_zero]
    exact mul_nonneg (radiusLoss_nonneg (div_nonneg hε.le (hε.trans hερ).le))
      (AxisWeightEstimates.weight_pos hε n m).le

/-- A bounded holomorphic function supplies an actual degree-zero element
of the compatible coefficient Banach space. -/
def UnitHolomorphic.toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ) : AxisSpace I ε :=
  ofJetFamily I (AxisWeightEstimates.weight ε) (AxisWeightEstimates.weight_pos hε)
    (degreeZeroJet f) (hf.degreeZeroJet_continuous (hε.trans hερ))
    (fun n m _ hx => hf.degreeZeroJet_hasDerivWithinAt (hε.trans hερ) n m hx)
    (radiusLoss (ε / ρ)) (radiusLoss_nonneg (div_nonneg hε.le (hε.trans hερ).le))
    (fun n m _ hx => hf.degreeZeroJet_bound hε hερ n m hx)

theorem UnitHolomorphic.norm_toAxisSpace_le {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ) :
    ‖hf.toAxisSpace hε hερ‖ ≤ radiusLoss (ε / ρ) := by
  unfold UnitHolomorphic.toAxisSpace
  exact norm_ofJetFamily_le _ _ _ _ _ _ _ _ _

theorem UnitHolomorphic.coefficient_toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (AxisWeightEstimates.weight ε) (hf.toAxisSpace hε hερ) n x =
      if n = 0 then (f (x : ℂ)).re else 0 := by
  unfold UnitHolomorphic.toAxisSpace
  rw [coefficient_ofJetFamily _ _ _ _ _ _ _ _ _ n hx]
  simp only [degreeZeroJet, realJet, iteratedDeriv_zero]

theorem UnitHolomorphic.jet_toAxisSpace {I : Window} {ε ρ : ℝ} {f : ℂ → ℂ}
    (hf : UnitHolomorphic I ρ f) (hε : 0 < ε) (hερ : ε < ρ)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I (AxisWeightEstimates.weight ε) (hf.toAxisSpace hε hερ).1 n m x =
      if n = 0 then iteratedDeriv m (fun t : ℝ => (f t).re) x else 0 := by
  unfold UnitHolomorphic.toAxisSpace
  rw [jet_ofJetFamily _ _ _ _ _ _ _ _ _ n m hx]
  rw [iteratedDeriv_realPart (hf.analytic x (real_mem_closedTube I (hε.trans hερ).le hx))]
  rfl

/-- The normalized axis exponential, defined on the whole complex plane
but bounded using the common complex neighborhood. -/
def normalizedExp (F : ℂ → ℂ) (Λ C : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Λ : ℂ) * F z) / (C : ℂ)

/-- One lower bound on `C` supplies all derivative bounds simultaneously.
The upper bound on `Re F` is imposed on the complex tube, not just its real axis. -/
theorem normalizedExp_unitHolomorphic {I : Window} {ρ Λ C M : ℝ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (closedTube I ρ))
    (hM : ∀ z ∈ closedTube I ρ, (F z).re ≤ M)
    (hΛ : 0 ≤ Λ) (hC : Real.exp (Λ * M) ≤ C) :
    UnitHolomorphic I ρ (normalizedExp F Λ C) := by
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
  constructor
  · intro z hz
    unfold normalizedExp
    exact ((analyticAt_const.mul (hF z hz)).cexp).div analyticAt_const hCne
  · intro z hz
    simp only [normalizedExp, norm_div, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hCpos, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    apply (div_le_one hCpos).mpr
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM z hz) hΛ)).trans hC

/-- Supremum over a fixed compact complex set, used for the literal
normalization threshold `exp(Λ sup Re F)`. -/
def realPartSup (F : ℂ → ℂ) (K : Set ℂ) : ℝ :=
  sSup ((fun z => (F z).re) '' K)

theorem re_le_realPartSup {F : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) {z : ℂ} (hz : z ∈ K) :
    (F z).re ≤ realPartSup F K :=
  le_csSup (hK.bddAbove_image (Complex.continuous_re.comp_continuousOn hF))
    (mem_image_of_mem (fun z => (F z).re) hz)

/-- A compact wider complex neighborhood is enough: every radius-`ρ`
closed disc about a real parameter must lie inside it. -/
theorem normalizedExp_unitHolomorphic_of_compact
    {I : Window} {ρ Λ C : ℝ} {F : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : AnalyticOnNhd ℂ F K)
    (hcover : ∀ x ∈ I.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hΛ : 0 ≤ Λ) (hC : Real.exp (Λ * realPartSup F K) ≤ C) :
    UnitHolomorphic I ρ (normalizedExp F Λ C) := by
  have hsub : closedTube I ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  exact normalizedExp_unitHolomorphic (hF.mono hsub)
    (fun z hz => re_le_realPartSup hK hF.continuousOn (hsub hz)) hΛ hC

theorem normalizedExp_re_of_real {F : ℂ → ℂ} {Λ C x : ℝ}
    (hreal : (F (x : ℂ)).im = 0) :
    (normalizedExp F Λ C (x : ℂ)).re = Real.exp (Λ * (F (x : ℂ)).re) / C := by
  have heq : F (x : ℂ) = ((F (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  rw [normalizedExp, heq, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

/-- Uniform degree-zero data for every admissible pair `(Λ,C)`.
The element is constructed from compatible actual derivatives, and its
norm bound depends only on the two radii. -/
theorem uniform_normalizedExp_axisData
    {I : Window} {ε ρ M : ℝ} {F : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ)
    (hF : AnalyticOnNhd ℂ F (closedTube I ρ))
    (hM : ∀ z ∈ closedTube I ρ, (F z).re ≤ M)
    (hreal : ∀ x ∈ I.interval, (F (x : ℂ)).im = 0) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, Real.exp (Λ * M) ≤ C →
      ∃ a : AxisSpace I ε,
        ‖a‖ ≤ radiusLoss (ε / ρ) ∧
        (∀ x ∈ I.interval, coefficient I (AxisWeightEstimates.weight ε) a 0 x =
          Real.exp (Λ * (F (x : ℂ)).re) / C) ∧
        (∀ n : ℕ, n ≠ 0 → ∀ x ∈ I.interval,
          coefficient I (AxisWeightEstimates.weight ε) a n x = 0) := by
  intro Λ hΛ C hC
  let hf := normalizedExp_unitHolomorphic hF hM hΛ hC
  refine ⟨hf.toAxisSpace hε hερ, hf.norm_toAxisSpace_le hε hερ, ?_, ?_⟩
  · intro x hx
    rw [hf.coefficient_toAxisSpace hε hερ 0 hx, ite_eq_left rfl]
    exact normalizedExp_re_of_real (hreal x hx)
  · intro n hn x hx
    rw [hf.coefficient_toAxisSpace hε hερ n hx, ite_eq_right hn]

/-- The compact-neighborhood form uses exactly `C ≥ exp(Λ sup Re F)`.
The order is: fix `I, ε, ρ, K, F`, then choose `Λ` and any sufficiently
large `C`; the coefficient norm threshold remains the same. -/
theorem uniform_normalizedExp_axisData_of_compact
    {I : Window} {ε ρ : ℝ} {F : ℂ → ℂ} {K : Set ℂ}
    (hε : 0 < ε) (hερ : ε < ρ)
    (hK : IsCompact K) (hF : AnalyticOnNhd ℂ F K)
    (hcover : ∀ x ∈ I.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hreal : ∀ x ∈ I.interval, (F (x : ℂ)).im = 0) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, Real.exp (Λ * realPartSup F K) ≤ C →
      ∃ a : AxisSpace I ε,
        ‖a‖ ≤ radiusLoss (ε / ρ) ∧
        (∀ x ∈ I.interval, coefficient I (AxisWeightEstimates.weight ε) a 0 x =
          Real.exp (Λ * (F (x : ℂ)).re) / C) ∧
        (∀ n : ℕ, n ≠ 0 → ∀ x ∈ I.interval,
          coefficient I (AxisWeightEstimates.weight ε) a n x = 0) := by
  have hsub : closedTube I ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  exact uniform_normalizedExp_axisData hε hερ (hF.mono hsub)
    (fun z hz => re_le_realPartSup hK hF.continuousOn (hsub hz)) hreal

end NavierStokes.AnalyticCoefficientBounds

end
end

end

section

/-!
# An actual holomorphic primitive on a convex open set

The primitive is the radial segment integral. Its derivative is proved by
differentiating under a uniformly dominated integral on a compact local product,
then applying the real fundamental theorem of calculus along the segment.
No disk containing the entire domain and no assumed primitive are required.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.AnalyticPrimitive

open Set Filter MeasureTheory Metric
open scoped Topology Interval ContDiff

/-- Integration along the straight segment from zero to `z`. -/
def primitive (g : ℂ → ℂ) (z : ℂ) : ℂ := z * ∫ t in (0 : ℝ)..1, g ((t : ℂ) * z)

@[simp] theorem primitive_zero (g : ℂ → ℂ) : primitive g 0 = 0 := by
  simp [primitive]

theorem primitive_eq_integral (g : ℂ → ℂ) (z : ℂ) :
    primitive g z = ∫ t in (0 : ℝ)..1, z * g ((t : ℂ) * z) := by
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem segment_mem {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * z ∈ U := by
  simpa only [Complex.real_smul] using hU.smul_mem_of_zero_mem h0 hz ht

theorem continuousOn_segment {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => g ((t : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  exact hg.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun _ ht => segment_mem hU h0 hz ht)

/-- The complex derivative of the parameter-dependent integrand. -/
def integrandDerivative (g : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  g ((t : ℂ) * z) + ((t : ℂ) * z) * deriv g ((t : ℂ) * z)

theorem integrand_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun w : ℂ => w * g ((t : ℂ) * w)) (integrandDerivative g z t) z := by
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! (hasDerivAt_id z).mul (hgd.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (t : ℂ))) using 1
  simp only [integrandDerivative, Function.comp_apply, id_eq, mul_one, one_mul]
  ring

theorem integrandDerivative_continuousOn_segment {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (integrandDerivative g z) (Icc (0 : ℝ) 1) := by
  exact (continuousOn_segment hU h0 hg.continuousOn hz).add
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn.mul
      (continuousOn_segment hU h0 (hg.deriv ho).continuousOn hz))

/-- The same derivative integrand is the real derivative of `t*g(t*z)`. -/
theorem segment_product_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
      (integrandDerivative g z t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! ht.mul (hgd.hasDerivAt.comp t (ht.mul_const z)) using 1
  simp only [integrandDerivative, Function.comp_apply, one_mul]
  ring

theorem integral_integrandDerivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    (∫ t in (0 : ℝ)..1, integrandDerivative g z t) = g z := by
  have hint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
    (f' := integrandDerivative g z) (a := 0) (b := 1)
    (fun t ht => segment_product_hasDerivAt ho hg
      (segment_mem hU h0 hz (by simpa only [uIcc_of_le zero_le_one] using ht))) hint
  simpa using he

/-- An actual holomorphic primitive on any convex open neighborhood of zero. -/
theorem hasDerivAt_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (primitive g) (g z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hz)
  let K : Set (ℂ × ℝ) := closedBall z r ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  have hm : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst
  have hmU : MapsTo (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) K U := by
    intro p hp
    exact segment_mem hU h0 (hrU hp.1) hp.2
  have hcont : ContinuousOn (fun p : ℂ × ℝ => integrandDerivative g p.1 p.2) K := by
    exact (hg.continuousOn.comp hm.continuousOn hmU).add
      (hm.continuousOn.mul ((hg.deriv ho).continuousOn.comp hm.continuousOn hmU))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hFint : ∀ w ∈ U, IntervalIntegrable (fun t : ℝ => w * g ((t : ℂ) * w))
      volume 0 1 := by
    intro w hw
    exact (continuousOn_const.mul
      (continuousOn_segment hU h0 hg.continuousOn hw)).intervalIntegrable_of_Icc (by norm_num)
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => w * g ((t : ℂ) * w)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    simpa only [uIoc_of_le zero_le_one] using
      (hFint w (hrU (ball_subset_closedBall hw))).aestronglyMeasurable
  have hDint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hDmeas : AEStronglyMeasurable (integrandDerivative g z)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using hDint.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      ‖integrandDerivative g w t‖ ≤ C := by
    filter_upwards [] with t
    intro ht w hw
    apply hC (w, t)
    exact ⟨ball_subset_closedBall hw,
      by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ => v * g ((t : ℂ) * v)) (integrandDerivative g w t) w := by
    filter_upwards [] with t
    intro ht w hw
    exact integrand_hasDerivAt ho hg (segment_mem hU h0
      (hrU (ball_subset_closedBall hw))
      (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => w * g ((t : ℂ) * w)) (F' := integrandDerivative g)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hr) hFmeas (hFint z hz) hDmeas hbound
    intervalIntegrable_const hdiff).2
  rw [integral_integrandDerivative ho hU h0 hg hz] at hd
  simpa only [← primitive_eq_integral] using hd

theorem differentiableOn_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (primitive g) U := by
  intro z hz
  exact (hasDerivAt_primitive ho hU h0 hg hz).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : AnalyticOnNhd ℂ (primitive g) U :=
  (differentiableOn_primitive ho hU h0 hg).analyticOnNhd ho

/-- Reality is local to the real points of the given convex domain. -/
theorem primitive_im_eq_zero {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (g x).im = 0)
    {x : ℝ} (hx : (x : ℂ) ∈ U) : (primitive g x).im = 0 := by
  have heq : (∫ t in (0 : ℝ)..1, g ((t : ℂ) * (x : ℂ))) =
      ∫ t in (0 : ℝ)..1, ((g ((t : ℂ) * (x : ℂ))).re : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htx := segment_mem hU h0 hx
      (show t ∈ Icc (0 : ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
    have him : (g ((t : ℂ) * (x : ℂ))).im = 0 := by
      simpa only [Complex.ofReal_mul] using hreal (t * x)
        (by simpa only [Complex.ofReal_mul] using htx)
    apply Complex.ext
    · simp
    · simpa using him
  rw [primitive, heq, intervalIntegral.integral_ofReal]
  simp

/-- If the integrand extends a real function, its segment primitive extends
the corresponding real segment integral exactly. -/
theorem primitive_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (x : ℝ) :
    primitive g x = ((x * ∫ t in (0 : ℝ)..1, f (t * x) : ℝ) : ℂ) := by
  have heq : (fun t : ℝ => g ((t : ℂ) * (x : ℂ))) =
      fun t : ℝ => (f (t * x) : ℂ) := by
    funext t
    rw [← Complex.ofReal_mul, hreal]
  rw [primitive, heq, intervalIntegral.integral_ofReal, Complex.ofReal_mul]

theorem hasDerivAt_real_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    HasDerivAt (fun y : ℝ => (primitive g y).re) (g x).re x :=
  (hasDerivAt_primitive ho hU h0 hg hx).real_of_complex

/-- The normalized exponential built from the actual segment primitive. -/
def amplitude (g : ℂ → ℂ) (Λ C : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Λ * primitive g z) / C

@[simp] theorem amplitude_zero (g : ℂ → ℂ) (Λ C : ℂ) : amplitude g Λ C 0 = 1 / C := by
  simp [amplitude]

theorem amplitude_ne_zero (g : ℂ → ℂ) (Λ : ℂ) {C : ℂ} (hC : C ≠ 0) (z : ℂ) :
    amplitude g Λ C z ≠ 0 :=
  div_ne_zero (Complex.exp_ne_zero _) hC

/-- Normalization is constant in the spatial variable, so the differential
equation is valid for any normalization scalar. -/
theorem hasDerivAt_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ C : ℂ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (amplitude g Λ C) ((Λ * g z) * amplitude g Λ C z) z := by
  have hd := (((hasDerivAt_primitive ho hU h0 hg hz).const_mul Λ).cexp).div_const C
  convert! hd using 1
  unfold amplitude
  ring

theorem analyticOnNhd_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ C : ℂ) : AnalyticOnNhd ℂ (amplitude g Λ C) U := by
  apply DifferentiableOn.analyticOnNhd _ ho
  intro z hz
  exact (hasDerivAt_amplitude ho hU h0 hg Λ C hz).differentiableAt.differentiableWithinAt

/-- The actual logarithmic derivative of the nonvanishing normalized
exponential is the prescribed scaled holomorphic gradient. -/
theorem amplitude_log_derivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ : ℂ) {C : ℂ} (hC : C ≠ 0)
    {z : ℂ} (hz : z ∈ U) :
    deriv (amplitude g Λ C) z / amplitude g Λ C z = Λ * g z := by
  rw [(hasDerivAt_amplitude ho hU h0 hg Λ C hz).deriv]
  exact mul_div_cancel_right₀ _ (amplitude_ne_zero g Λ hC z)

theorem amplitude_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ C x : ℝ) :
    amplitude g Λ C x =
      ((Real.exp (Λ * (x * ∫ t in (0 : ℝ)..1, f (t * x))) / C : ℝ) : ℂ) := by
  rw [amplitude, primitive_ofReal g f hreal x, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_div]

theorem amplitude_real_pos (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ : ℝ) {C : ℝ} (hC : 0 < C) (x : ℝ) :
    0 < (amplitude g Λ C x).re := by
  rw [amplitude_ofReal g f hreal Λ C x, Complex.ofReal_re]
  exact div_pos (Real.exp_pos _) hC

theorem hasDerivAt_real_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ C : ℝ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    HasDerivAt (fun y : ℝ => (amplitude g Λ C y).re)
      ((Λ * f x) * (amplitude g Λ C x).re) x := by
  have hd := (hasDerivAt_amplitude ho hU h0 hg Λ C hx).real_of_complex
  simpa only [hreal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero] using hd

theorem real_amplitude_log_derivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ : ℝ) {C : ℝ} (hC : 0 < C)
    {x : ℝ} (hx : (x : ℂ) ∈ U) :
    deriv (fun y : ℝ => (amplitude g Λ C y).re) x / (amplitude g Λ C x).re = Λ * f x := by
  rw [(hasDerivAt_real_amplitude ho hU h0 hg f hreal Λ C hx).deriv]
  exact mul_div_cancel_right₀ _ (ne_of_gt (amplitude_real_pos g f hreal Λ hC x))

end NavierStokes.AnalyticPrimitive

end

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.NaturalAxisCoefficients

open Set Metric Filter Complex
open scoped Topology ContDiff BigOperators
open AxisCoefficientSpace AnalyticCoefficientBounds

/-- A fixed, slightly enlarged real parameter interval. -/
def window : Window := ⟨-11 / 10, 11 / 10, by norm_num⟩

theorem original_interval_interior :
    Icc (-1 : ℝ) 1 ⊆ Ioo window.left window.right := by
  intro x hx
  dsimp [window]
  constructor <;> linarith [hx.1, hx.2]

/-- Complex D, given by `1 - z ^ 2`. -/
def complexD (z : ℂ) : ℂ := 1 - z ^ 2
/-- Complex L, given by `1 - 2 * (h : ℂ) * z ^ 2`. -/
def complexL (h : ℝ) (z : ℂ) : ℂ := 1 - 2 * (h : ℂ) * z ^ 2
/-- Complex U, given by `4 * z + (j : ℂ)`. -/
def complexU (j : ℝ) (z : ℂ) : ℂ := 4 * z + (j : ℂ)
/-- Complex H, given by `(NaturalAxisData.D h : ℂ) * z + complexD z * complexU j z`. -/
def complexH (h j : ℝ) (z : ℂ) : ℂ :=
  (NaturalAxisData.D h : ℂ) * z + complexD z * complexU j z
/-- Complex W, given by `1 - 4 * complexD z - 2 * (NaturalAxisData.D h : ℂ) * z * complexU j z`. -/
def complexW (h j : ℝ) (z : ℂ) : ℂ :=
  1 - 4 * complexD z - 2 * (NaturalAxisData.D h : ℂ) * z * complexU j z
/-- Denominator, given by `complexH h j z ^ 2 + (σ : ℂ) ^ 2`. -/
def denominator (h j σ : ℝ) (z : ℂ) : ℂ := complexH h j z ^ 2 + (σ : ℂ) ^ 2
/-- Complex Z as an element of `ℂ`. -/
def complexZ (h j : ℝ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(NaturalAxisData.A h : ℂ) * (1 - 2 * z * complexU j z) * complexU j z -
    complexH h j z * 4 - complexD z * deriv P z +
    4 * (NaturalAxisData.A h : ℂ) * z * P z
/-- Complex chi, given by `complexH h j z ^ 2 / denominator h j σ z`. -/
def complexChi (h j σ : ℝ) (z : ℂ) : ℂ :=
  complexH h j z ^ 2 / denominator h j σ z
/-- Complex gradient, given by `-complexL h z * complexH h j z / denominator h j σ z`. -/
def complexGradient (h j σ : ℝ) (z : ℂ) : ℂ :=
  -complexL h z * complexH h j z / denominator h j σ z
/-- Real gradient, given by `-NaturalAxisData.L h x * NaturalAxisData.H h j x /
(NaturalAxisData.H h j x ^ 2 + σ ^ 2)`. -/
def realGradient (h j σ x : ℝ) : ℝ :=
  -NaturalAxisData.L h x * NaturalAxisData.H h j x /
    (NaturalAxisData.H h j x ^ 2 + σ ^ 2)

@[simp] theorem complexL_ofReal (h x : ℝ) :
    complexL h (x : ℂ) = (NaturalAxisData.L h x : ℂ) := by
  simp [complexL, NaturalAxisData.L]

@[simp] theorem complexH_ofReal (h j x : ℝ) :
    complexH h j (x : ℂ) = (NaturalAxisData.H h j x : ℂ) := by
  simp [complexH, complexD, complexU, NaturalAxisData.H, NaturalAxisData.d,
    NaturalAxisData.U]

@[simp] theorem denominator_ofReal (h j σ x : ℝ) :
    denominator h j σ (x : ℂ) = (NaturalAxisData.H h j x ^ 2 + σ ^ 2 : ℝ) := by
  simp [denominator]

@[simp] theorem complexGradient_ofReal (h j σ x : ℝ) :
    complexGradient h j σ (x : ℂ) = (realGradient h j σ x : ℂ) := by
  simp [complexGradient, realGradient, denominator]

theorem L_pos_on_window {h j : ℝ} (hp : NaturalAxisData.SmallParameters h j)
    {x : ℝ} (hx : x ∈ window.interval) : 0 < NaturalAxisData.L h x := by
  have hx' : -(11 / 10 : ℝ) ≤ x ∧ x ≤ 11 / 10 := by
    simpa [window, Window.interval, neg_div] using hx
  have hs : x ^ 2 ≤ 2 := by
    linarith [mul_nonneg (sub_nonneg.mpr hx'.2) (show 0 ≤ x + 11 / 10 by linarith [hx'.1])]
  have hh := mul_le_mul_of_nonneg_left hs hp.h_pos.le
  dsimp [NaturalAxisData.L]
  linarith [hp.h_le]

theorem denominator_ne_zero_on_real (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    denominator h j σ (x : ℂ) ≠ 0 := by
  rw [denominator_ofReal]
  exact_mod_cast ne_of_gt (add_pos_of_nonneg_of_pos
    (sq_nonneg (NaturalAxisData.H h j x)) (sq_pos_of_pos hσ))

/-- The open region where all fixed rational expressions and pressure are analytic. -/
def regularSet (h j σ : ℝ) : Set ℂ :=
  PressureDatum.strip ∩ {z | complexL h z ≠ 0} ∩ {z | denominator h j σ z ≠ 0}

theorem regularSet_open (h j σ : ℝ) : IsOpen (regularSet h j σ) := by
  have hL : Continuous (complexL h) := by unfold complexL; fun_prop
  have hden : Continuous (denominator h j σ) := by
    unfold denominator complexH complexD complexU
    fun_prop
  exact (PressureDatum.strip_open.inter (isOpen_ne_fun hL continuous_const)).inter
    (isOpen_ne_fun hden continuous_const)

theorem real_mem_regularSet {h j σ : ℝ} (hp : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) {x : ℝ} (hx : x ∈ window.interval) :
    (x : ℂ) ∈ regularSet h j σ := by
  refine ⟨⟨PressureDatum.real_mem_strip x, ?_⟩, denominator_ne_zero_on_real h j hσ x⟩
  change complexL h (x : ℂ) ≠ 0
  rw [complexL_ofReal]
  exact_mod_cast (L_pos_on_window hp hx).ne'

theorem complexGradient_analytic (h j σ : ℝ) :
    AnalyticOnNhd ℂ (complexGradient h j σ) (regularSet h j σ) := by
  intro z hz
  have hden : denominator h j σ z ≠ 0 := hz.2
  change AnalyticAt ℂ (fun w => complexGradient h j σ w) z
  dsimp [complexGradient, denominator, complexH, complexD, complexU, complexL]
  fun_prop (disch := assumption)

/-- Field data for natural axis coefficients. -/
inductive Field
  | one | eta | d | inverseL | uStar | uStarEta | wStar | hStar | zStar | chi | gradient
  deriving DecidableEq

instance : Fintype Field :=
  ⟨{.one, .eta, .d, .inverseL, .uStar, .uStarEta, .wStar, .hStar, .zStar, .chi, .gradient},
    by intro x; cases x <;> simp⟩

/-- Complex field used in natural axis coefficients. -/
def complexField (h j σ : ℝ) (P : ℂ → ℂ) : Field → ℂ → ℂ
  | .one => fun _ => 1
  | .eta => fun z => z
  | .d => complexD
  | .inverseL => fun z => (complexL h z)⁻¹
  | .uStar => complexU j
  | .uStarEta => fun _ => 4
  | .wStar => complexW h j
  | .hStar => complexH h j
  | .zStar => complexZ h j P
  | .chi => complexChi h j σ
  | .gradient => complexGradient h j σ

/-- Real field used in natural axis coefficients. -/
def realField (h j σ : ℝ) (P : ℝ → ℝ) : Field → ℝ → ℝ
  | .one => fun _ => 1
  | .eta => fun x => x
  | .d => NaturalAxisData.d
  | .inverseL => fun x => (NaturalAxisData.L h x)⁻¹
  | .uStar => NaturalAxisData.U j
  | .uStarEta => fun _ => 4
  | .wStar => NaturalAxisData.W h j
  | .hStar => NaturalAxisData.H h j
  | .zStar => NaturalAxisData.Z h j P
  | .chi => NaturalAxisData.chi h j σ
  | .gradient => realGradient h j σ

theorem deriv_complexPressure_ofReal {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (x : ℝ) :
    deriv (PressureDatum.complexPressure g a) (x : ℂ) =
      ((deriv (PressureDatum.pressure g a) x : ℝ) : ℂ) := by
  have hc := ((PressureDatum.complexPressure_analytic hp (x : ℂ)
    (PressureDatum.real_mem_strip x)).differentiableAt.hasDerivAt).comp_ofReal
  have hr := (PressureDatum.hasDerivAt_pressure hp x).differentiableAt.hasDerivAt.ofReal_comp
  have hc' : HasDerivAt (fun t : ℝ => (PressureDatum.pressure g a t : ℂ))
      (deriv (PressureDatum.complexPressure g a) (x : ℂ)) x := by
    simpa only [PressureDatum.complexPressure_ofReal] using hc
  exact hc'.unique hr

theorem complexField_ofReal {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (h j σ : ℝ) (k : Field) (x : ℝ) :
    complexField h j σ (PressureDatum.complexPressure g a) k (x : ℂ) =
      (realField h j σ (PressureDatum.pressure g a) k x : ℂ) := by
  cases k <;>
    simp [complexField, realField, complexD, complexL, complexU, complexH, complexW,
      complexZ, complexChi, complexGradient, denominator, realGradient,
      NaturalAxisData.d, NaturalAxisData.L, NaturalAxisData.U, NaturalAxisData.H,
      NaturalAxisData.W, NaturalAxisData.Z, NaturalAxisData.chi,
      deriv_complexPressure_ofReal hp]

theorem complexField_analytic {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap) (h j σ : ℝ) (k : Field) :
    AnalyticOnNhd ℂ (complexField h j σ (PressureDatum.complexPressure g a) k)
      (regularSet h j σ) := by
  intro z hz
  have hL : complexL h z ≠ 0 := hz.1.2
  have hden : denominator h j σ z ≠ 0 := hz.2
  have hP := PressureDatum.complexPressure_analytic hp z hz.1.1
  have hP' := hP.deriv
  change AnalyticAt ℂ
    (fun w => complexField h j σ (PressureDatum.complexPressure g a) k w) z
  cases k <;>
    dsimp [complexField, complexD, complexL, complexU, complexH, complexW,
      complexZ, complexChi, complexGradient, denominator] <;>
    fun_prop (disch := assumption)

/-- One compact complex neighborhood for the whole finite family. -/
theorem exists_common_neighborhood {h j σ : ℝ}
    (hp : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : Set ℂ, IsCompact K ∧
      (∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K) ∧ K ⊆ regularSet h j σ := by
  let R : Set ℂ := Complex.ofReal '' window.interval
  have hR : IsCompact R := isCompact_Icc.image Complex.continuous_ofReal
  have hsub : R ⊆ regularSet h j σ := by
    rintro z ⟨x, hx, rfl⟩
    exact real_mem_regularSet hp hσ hx
  obtain ⟨ρ, hρ, hρU⟩ := hR.exists_cthickening_subset_open (regularSet_open h j σ) hsub
  refine ⟨ρ, hρ, cthickening ρ R, hR.cthickening, ?_, hρU⟩
  intro x hx
  exact closedBall_subset_cthickening (mem_image_of_mem Complex.ofReal hx) ρ

/-- A convex open outer neighborhood and compact inner neighborhood.
The inner radius can be used for both the fixed fields and an analytic primitive. -/
theorem exists_convex_common_neighborhood {h j σ : ℝ}
    (hp : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ U K : Set ℂ,
      IsOpen U ∧ Convex ℝ U ∧ (0 : ℂ) ∈ U ∧ IsCompact K ∧
      (∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K) ∧
      K ⊆ U ∧ U ⊆ regularSet h j σ := by
  let R : Set ℂ := Complex.ofReal '' window.interval
  have hR : IsCompact R := isCompact_Icc.image Complex.continuous_ofReal
  have hRconv : Convex ℝ R :=
    (convex_Icc window.left window.right).linear_image Complex.ofRealCLM.toLinearMap
  have hRzero : (0 : ℂ) ∈ R := by
    refine ⟨0, ?_, by simp⟩
    norm_num [window, Window.interval]
  have hsub : R ⊆ regularSet h j σ := by
    rintro z ⟨x, hx, rfl⟩
    exact real_mem_regularSet hp hσ hx
  obtain ⟨δ, hδ, hδU⟩ := hR.exists_cthickening_subset_open (regularSet_open h j σ) hsub
  refine ⟨δ / 2, half_pos hδ, thickening δ R, cthickening (δ / 2) R,
    isOpen_thickening, hRconv.thickening δ, self_subset_thickening hδ R hRzero,
    hR.cthickening, ?_, cthickening_subset_thickening' hδ (half_lt_self hδ) R,
    (thickening_subset_cthickening δ R).trans hδU⟩
  intro x hx
  exact closedBall_subset_cthickening (mem_image_of_mem Complex.ofReal hx) (δ / 2)

/-- Compactness and finiteness give one common value bound for all inputs. -/
theorem finite_family_bound {ι : Type*} [Finite ι]
    {K : Set ℂ} (hK : IsCompact K) (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i z, z ∈ K → ‖f i z‖ ≤ B := by
  classical
  let := Fintype.ofFinite ι
  choose b hb using fun i => hK.exists_bound_of_continuousOn (hf i)
  let B : ℝ := 1 + ∑ i, |b i|
  have hsum : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro i z hz
  have hi : |b i| ≤ ∑ i, |b i| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ i)
  exact (hb i z hz).trans ((le_abs_self _).trans (by dsimp [B]; linarith))

theorem unitHolomorphic_of_bound {I : Window} {ρ B : ℝ} {f : ℂ → ℂ}
    (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) :
    UnitHolomorphic I ρ (fun z => f z / (B : ℂ)) := by
  have hBne : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  constructor
  · intro z hz
    exact (hf z hz).div analyticAt_const hBne
  · intro z hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact (div_le_one hB).mpr (hb z hz)

theorem coefficient_smul (I : Window) (ε c : ℝ) (a : AxisSpace I ε) (n : ℕ) (x : ℝ) :
    coefficient I (AxisWeightEstimates.weight ε) (c • a) n x =
      c * coefficient I (AxisWeightEstimates.weight ε) a n x := by
  exact jet_smul I (AxisWeightEstimates.weight ε) c a.1 n 0 x

/-- An arbitrary finite complex bound is reduced to the unit-bound Cauchy constructor. -/
def boundedAxisElement {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) : AxisSpace I ε :=
  B • (unitHolomorphic_of_bound hB hf hb).toAxisSpace hε hερ

theorem boundedAxisElement_norm {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B) :
    ‖boundedAxisElement hε hερ hB hf hb‖ ≤ B * radiusLoss (ε / ρ) := by
  unfold boundedAxisElement
  calc
    _ ≤ ‖B‖ * ‖(unitHolomorphic_of_bound hB hf hb).toAxisSpace hε hερ‖ :=
      NormedSpace.norm_smul_le B _
    _ ≤ B * radiusLoss (ε / ρ) := by
      rw [Real.norm_eq_abs, abs_of_pos hB]
      exact mul_le_mul_of_nonneg_left
        ((unitHolomorphic_of_bound hB hf hb).norm_toAxisSpace_le hε hερ) hB.le

theorem boundedAxisElement_coefficient {I : Window} {ε ρ B : ℝ} {f : ℂ → ℂ}
    (hε : 0 < ε) (hερ : ε < ρ) (hB : 0 < B)
    (hf : AnalyticOnNhd ℂ f (closedTube I ρ))
    (hb : ∀ z ∈ closedTube I ρ, ‖f z‖ ≤ B)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (AxisWeightEstimates.weight ε) (boundedAxisElement hε hερ hB hf hb) n x =
      if n = 0 then (f (x : ℂ)).re else 0 := by
  rw [boundedAxisElement, coefficient_smul,
    (unitHolomorphic_of_bound hB hf hb).coefficient_toAxisSpace hε hερ n hx]
  by_cases hn : n = 0
  · rw [ite_eq_left hn, ite_eq_left hn, Complex.div_ofReal_re]
    exact mul_div_cancel₀ _ hB.ne'
  · rw [ite_eq_right hn, ite_eq_right hn, mul_zero]

/-- A finite family of actual degree-zero fields, all using the same
positive parameter radius and the same finite norm bound. -/
structure CoefficientFamily (h j σ : ℝ) (P : ℝ → ℝ) where
  /-- Epsilon of `CoefficientFamily`, of type `ℝ`. -/
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  /-- Elements of `CoefficientFamily`, of type `Field → AxisSpace window epsilon`. -/
  elements : Field → AxisSpace window epsilon
  /-- Bound of `CoefficientFamily`, of type `ℝ`. -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ k, ‖elements k‖ ≤ bound
  coefficient_eq : ∀ k n x, x ∈ window.interval →
    coefficient window (AxisWeightEstimates.weight epsilon) (elements k) n x =
      if n = 0 then realField h j σ P k x else 0

theorem exists_coefficientFamily_on_neighborhood {h j σ ρ : ℝ}
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap)
    (hρ : 0 < ρ) {K : Set ℂ} (hK : IsCompact K)
    (hcover : ∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K)
    (hKU : K ⊆ regularSet h j σ) :
    ∃ v : CoefficientFamily h j σ (PressureDatum.pressure g a), v.epsilon = ρ / 2 := by
  have hsub : closedTube window ρ ⊆ K := by
    rintro z ⟨x, hx, hz⟩
    exact hcover x hx hz
  let f := complexField h j σ (PressureDatum.complexPressure g a)
  have hf : ∀ k, AnalyticOnNhd ℂ (f k) (closedTube window ρ) :=
    fun k => (complexField_analytic hp h j σ k).mono (hsub.trans hKU)
  obtain ⟨B, hB, hb⟩ := finite_family_bound hK f
    (fun k => ((complexField_analytic hp h j σ k).mono hKU).continuousOn)
  have hb' : ∀ k z, z ∈ closedTube window ρ → ‖f k z‖ ≤ B :=
    fun k z hz => hb k z (hsub hz)
  have hε : 0 < ρ / 2 := half_pos hρ
  have hερ : ρ / 2 < ρ := half_lt_self hρ
  let v : Field → AxisSpace window (ρ / 2) :=
    fun k => boundedAxisElement hε hερ hB (hf k) (hb' k)
  refine ⟨{
    epsilon := ρ / 2
    epsilon_pos := hε
    elements := v
    bound := B * radiusLoss ((ρ / 2) / ρ)
    bound_nonneg := mul_nonneg hB.le
      (radiusLoss_nonneg (div_nonneg hε.le hρ.le))
    norm_le := fun k => boundedAxisElement_norm hε hερ hB (hf k) (hb' k)
    coefficient_eq := ?_
  }, rfl⟩
  intro k n x hx
  rw [boundedAxisElement_coefficient hε hερ hB (hf k) (hb' k) n hx]
  simp only [f, complexField_ofReal hp, Complex.ofReal_re]

theorem exists_coefficientFamily {h j σ : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    Nonempty (CoefficientFamily h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨ρ, hρ, K, hK, hcover, hKU⟩ := exists_common_neighborhood hsmall hσ
  obtain ⟨v, _⟩ := exists_coefficientFamily_on_neighborhood hp hρ hK hcover hKU
  exact ⟨v⟩

/-- The coefficient family and the open convex domain for its primitive
can be chosen together, with an explicit strict gap between the two radii. -/
theorem exists_coefficientFamily_with_convex_domain {h j σ : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    ∃ v : CoefficientFamily h j σ (PressureDatum.pressure g a),
      ∃ ρ : ℝ, v.epsilon < ρ ∧ ∃ U K : Set ℂ,
      IsOpen U ∧ Convex ℝ U ∧ (0 : ℂ) ∈ U ∧ IsCompact K ∧
      (∀ x ∈ window.interval, closedBall (x : ℂ) ρ ⊆ K) ∧
      K ⊆ U ∧ U ⊆ regularSet h j σ := by
  obtain ⟨ρ, hρ, U, K, hUopen, hUconv, hUzero, hK, hcover, hKU, hUreg⟩ :=
    exists_convex_common_neighborhood hsmall hσ
  obtain ⟨v, hv⟩ := exists_coefficientFamily_on_neighborhood hp hρ hK hcover (hKU.trans hUreg)
  exact ⟨v, ρ, hv ▸ half_lt_self hρ, U, K, hUopen, hUconv, hUzero, hK,
    hcover, hKU, hUreg⟩

/-- Axis data, bundling `A`, `D`, `h`, `one` and the required compatibility proofs. -/
def CoefficientFamily.axisData {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) : AxisContraction.AxisData (AxisSpace window v.epsilon) where
  A := NaturalAxisData.A h
  D := NaturalAxisData.D h
  h := h
  one := v.elements .one
  eta := v.elements .eta
  d := v.elements .d
  inverseL := v.elements .inverseL
  uStar := v.elements .uStar
  uStarEta := v.elements .uStarEta
  wStar := v.elements .wStar
  hStar := v.elements .hStar
  normalizedGradient := v.elements .gradient
  zStar := v.elements .zStar

theorem CoefficientFamily.radiallyConstant {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) (k : Field) :
    NaturalAxisBridge.RadiallyConstant window v.epsilon (v.elements k) := by
  intro n hn x hx
  rw [v.coefficient_eq k n x hx, ite_eq_right hn]

theorem CoefficientFamily.value {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) (k : Field) {x : ℝ} (hx : x ∈ window.interval) :
    NaturalAxisBridge.inputValue window v.epsilon (v.elements k) x =
      realField h j σ P k x := by
  exact (v.coefficient_eq k 0 x hx).trans (ite_eq_left rfl)

theorem CoefficientFamily.compatible {h j σ : ℝ} {P : ℝ → ℝ}
    (v : CoefficientFamily h j σ P) :
    NaturalAxisBridge.CompatibleData window v.epsilon (v.elements .chi) v.axisData := by
  refine {
    chi_radial := v.radiallyConstant .chi
    one_radial := v.radiallyConstant .one
    eta_radial := v.radiallyConstant .eta
    d_radial := v.radiallyConstant .d
    inverseL_radial := v.radiallyConstant .inverseL
    uStar_radial := v.radiallyConstant .uStar
    uStarEta_radial := v.radiallyConstant .uStarEta
    wStar_radial := v.radiallyConstant .wStar
    hStar_radial := v.radiallyConstant .hStar
    gradient_radial := v.radiallyConstant .gradient
    zStar_radial := v.radiallyConstant .zStar
    one_value := fun x hx => v.value .one hx
    eta_value := fun x hx => v.value .eta hx
    uStarEta_value := ?_
  }
  intro x hx
  have hx' : x ∈ window.interval := ⟨hx.1.le, hx.2.le⟩
  change NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStarEta) x =
    deriv (NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStar)) x
  rw [v.value .uStarEta hx']
  have heq : NaturalAxisBridge.inputValue window v.epsilon (v.elements .uStar) =ᶠ[𝓝 x]
      NaturalAxisData.U j := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact v.value .uStar hy
  rw [heq.deriv_eq]
  symm
  change deriv (fun y : ℝ => 4 * y + j) x = 4
  simp

theorem ideal_prefix_fixed_coefficients {h j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ x ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) x| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ x) ∧
      Nonempty (CoefficientFamily h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, _⟩ :=
    NaturalAxisData.ideal_prefix_cutoff_parameters hsmall hp hB hg ha
  exact ⟨δ, σ, hδ, hσ, hcut, exists_coefficientFamily hsmall hσ hp⟩

/-- The actual normalized logarithmic phase, as a complex segment integral. -/
def axisPhase (h j σ : ℝ) : ℂ → ℂ :=
  AnalyticPrimitive.primitive (complexGradient h j σ)

/-- Real phase, given by `x * ∫ t in (0 : ℝ)..1, realGradient h j σ (t * x)`. -/
def realPhase (h j σ x : ℝ) : ℝ :=
  x * ∫ t in (0 : ℝ)..1, realGradient h j σ (t * x)

@[simp] theorem axisPhase_zero (h j σ : ℝ) : axisPhase h j σ 0 = 0 := by
  simp [axisPhase]

@[simp] theorem axisPhase_ofReal (h j σ x : ℝ) :
    axisPhase h j σ (x : ℂ) = (realPhase h j σ x : ℂ) :=
  AnalyticPrimitive.primitive_ofReal (complexGradient h j σ) (realGradient h j σ)
    (complexGradient_ofReal h j σ) x

/-- The fixed coefficient family and its actual analytic phase on one
common compact neighborhood. No primitive or coefficient record is assumed
by the existence theorem below. -/
structure AnalyticInputs (h j σ : ℝ) (P : ℝ → ℝ) where
  /-- Coefficients of `AnalyticInputs`, of type `CoefficientFamily h j σ P`. -/
  coefficients : CoefficientFamily h j σ P
  /-- Radius of `AnalyticInputs`, of type `ℝ`. -/
  radius : ℝ
  radius_gap : coefficients.epsilon < radius
  /-- Compact set of `AnalyticInputs`, of type `Set ℂ`. -/
  compactSet : Set ℂ
  isCompact : IsCompact compactSet
  covers : ∀ x ∈ window.interval, closedBall (x : ℂ) radius ⊆ compactSet
  phase_analytic : AnalyticOnNhd ℂ (axisPhase h j σ) compactSet
  phase_derivative : ∀ z ∈ compactSet,
    HasDerivAt (axisPhase h j σ) (complexGradient h j σ z) z

theorem exists_analyticInputs {h j σ : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    Nonempty (AnalyticInputs h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨v, ρ, hgap, U, K, hUopen, hUconv, hUzero, hK, hcover, hKU, hUreg⟩ :=
    exists_coefficientFamily_with_convex_domain hsmall hσ hp
  have hg : DifferentiableOn ℂ (complexGradient h j σ) U :=
    ((complexGradient_analytic h j σ).mono hUreg).differentiableOn
  refine ⟨{
    coefficients := v
    radius := ρ
    radius_gap := hgap
    compactSet := K
    isCompact := hK
    covers := hcover
    phase_analytic := (AnalyticPrimitive.analyticOnNhd_primitive hUopen hUconv hUzero hg).mono hKU
    phase_derivative := fun z hz =>
      AnalyticPrimitive.hasDerivAt_primitive hUopen hUconv hUzero hg (hKU hz)
  }⟩

theorem AnalyticInputs.radius_pos {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : 0 < d.radius :=
  d.coefficients.epsilon_pos.trans d.radius_gap

theorem AnalyticInputs.real_mem_compact {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) {x : ℝ} (hx : x ∈ window.interval) :
    (x : ℂ) ∈ d.compactSet :=
  d.covers x hx (mem_closedBall_self d.radius_pos.le)

theorem AnalyticInputs.realPhase_hasDerivAt {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) {x : ℝ} (hx : x ∈ window.interval) :
    HasDerivAt (realPhase h j σ) (realGradient h j σ x) x := by
  simpa only [axisPhase_ofReal, complexGradient_ofReal, Complex.ofReal_re] using
    (d.phase_derivative (x : ℂ) (d.real_mem_compact hx)).real_of_complex

/-- Real amplitude, given by `Real.exp (Λ * realPhase h j σ x) / C`. -/
def realAmplitude (h j σ Λ C x : ℝ) : ℝ := Real.exp (Λ * realPhase h j σ x) / C

theorem AnalyticInputs.realAmplitude_hasDerivAt {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ C : ℝ) {x : ℝ} (hx : x ∈ window.interval) :
    HasDerivAt (realAmplitude h j σ Λ C)
      ((Λ * realGradient h j σ x) * realAmplitude h j σ Λ C x) x := by
  have hd := (((d.realPhase_hasDerivAt hx).const_mul Λ).exp).div_const C
  convert! hd using 1
  unfold realAmplitude
  ring

theorem realAmplitude_pos (h j σ Λ : ℝ) {C : ℝ} (hC : 0 < C) (x : ℝ) :
    0 < realAmplitude h j σ Λ C x :=
  div_pos (Real.exp_pos _) hC

/-- The true logarithmic derivative is the prescribed `ξ₀=Λκ`. -/
theorem AnalyticInputs.realAmplitude_logDerivative {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ : ℝ) {C : ℝ} (hC : 0 < C)
    {x : ℝ} (hx : x ∈ window.interval) :
    deriv (realAmplitude h j σ Λ C) x / realAmplitude h j σ Λ C x =
      Λ * realGradient h j σ x := by
  rw [(d.realAmplitude_hasDerivAt Λ C hx).deriv]
  exact mul_div_cancel_right₀ _ (realAmplitude_pos h j σ Λ hC x).ne'

/-- Normalization threshold, given by `Real.exp (Λ * realPartSup (axisPhase h j σ)
d.compactSet)`. -/
def AnalyticInputs.normalizationThreshold {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) (Λ : ℝ) : ℝ :=
  Real.exp (Λ * realPartSup (axisPhase h j σ) d.compactSet)

/-- Amplitude bound, given by `radiusLoss (d.coefficients.epsilon / d.radius)`. -/
def AnalyticInputs.amplitudeBound {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : ℝ :=
  radiusLoss (d.coefficients.epsilon / d.radius)

theorem AnalyticInputs.amplitudeBound_nonneg {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) : 0 ≤ d.amplitudeBound :=
  radiusLoss_nonneg (div_nonneg d.coefficients.epsilon_pos.le d.radius_pos.le)

/-- The actual `φ*/C` belongs to exactly the same coefficient space as
all fixed data, uniformly for every allowed large parameter and normalization. -/
theorem AnalyticInputs.uniformAmplitude {h j σ : ℝ} {P : ℝ → ℝ}
    (d : AnalyticInputs h j σ P) :
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ C : ℝ, d.normalizationThreshold Λ ≤ C →
      ∃ a : AxisSpace window d.coefficients.epsilon,
        ‖a‖ ≤ d.amplitudeBound ∧
        NaturalAxisBridge.RadiallyConstant window d.coefficients.epsilon a ∧
        ∀ x ∈ window.interval,
          NaturalAxisBridge.inputValue window d.coefficients.epsilon a x =
            realAmplitude h j σ Λ C x := by
  intro Λ hΛ C hC
  obtain ⟨a, ha, hvalue, hzero⟩ :=
    uniform_normalizedExp_axisData_of_compact d.coefficients.epsilon_pos d.radius_gap
      d.isCompact d.phase_analytic d.covers
      (fun x _ => by simp only [axisPhase_ofReal, Complex.ofReal_im]) Λ hΛ C hC
  refine ⟨a, ha, hzero, ?_⟩
  intro x hx
  simpa only [NaturalAxisBridge.inputValue, realAmplitude, axisPhase_ofReal,
    Complex.ofReal_re] using hvalue x hx

/-- End-to-end fixed analytic input construction from the actual pressure
integral and ideal prefix, including the normalized amplitude source. -/
theorem ideal_prefix_analytic_inputs {h j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ x ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) x| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ x) ∧
      Nonempty (AnalyticInputs h j σ (PressureDatum.pressure g a)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, _⟩ :=
    NaturalAxisData.ideal_prefix_cutoff_parameters hsmall hp hB hg ha
  exact ⟨δ, σ, hδ, hσ, hcut, exists_analyticInputs hsmall hσ hp⟩

end NavierStokes.NaturalAxisCoefficients

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.NaturalProfile

open Set Filter NaturalAxisBridge NaturalAxisCoefficients
open scoped Topology ContDiff

/-- Rescale point, given by `(Λ * p.1, p.2)`. -/
def rescalePoint (Λ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Λ * p.1, p.2)

/-- Domain, given by `rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20`. -/
def domain (Λ : ℝ) : Set (ℝ × ℝ) :=
  rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20

/-- Pullback, given by `F (rescalePoint Λ p)`. -/
def pullback (Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F (rescalePoint Λ p)

/-- Affine profile, given by `b p.2 + c * pullback Λ F p`. -/
def affineProfile (b : ℝ → ℝ) (c Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  b p.2 + c * pullback Λ F p

/-- Angular profile, given by `a p.2 * pullback Λ Φ p`. -/
def angularProfile (a : ℝ → ℝ) (Λ : ℝ) (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p.2 * pullback Λ Φ p

theorem contDiff_rescalePoint (Λ : ℝ) : ContDiff ℝ ∞ (rescalePoint Λ) := by
  exact (contDiff_const.mul contDiff_fst).prodMk contDiff_snd

theorem domain_isOpen (Λ : ℝ) : IsOpen (domain Λ) :=
  (AxisEvaluation.strip_isOpen window 20).preimage (contDiff_rescalePoint Λ).continuous

theorem pullback_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20)) (Λ : ℝ) :
    ContDiffOn ℝ ∞ (pullback Λ F) (domain Λ) :=
  hF.comp (contDiff_rescalePoint Λ).contDiffOn (fun _ hp => hp)

theorem affineProfile_smooth {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioo window.left window.right))
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) : ContDiffOn ℝ ∞ (affineProfile b c Λ F) (domain Λ) := by
  exact (hb.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).add
    (contDiffOn_const.mul (pullback_smooth hF Λ))

theorem angularProfile_smooth {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo window.left window.right))
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) : ContDiffOn ℝ ∞ (angularProfile a Λ Φ) (domain Λ) := by
  exact (ha.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).mul (pullback_smooth hΦ Λ)

theorem sliceY_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun Y : ℝ => F (Y, p.2)) p.1 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)

theorem sliceEta_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun η : ℝ => F (p.1, η)) p.2 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.2
    (contDiffAt_const.prodMk contDiffAt_id)

theorem pullback_hasDerivAt_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    HasDerivAt (fun X : ℝ => pullback Λ F (X, p.2))
      (Λ * partialY F (rescalePoint Λ p)) p.1 := by
  have hf := (sliceY_smooth hF hp).differentiableAt (by norm_num)
  have hd := hf.hasDerivAt.comp p.1 ((hasDerivAt_id p.1).const_mul Λ)
  simp only [Function.comp_def, mul_one] at hd
  convert! hd using 1; simp only [rescalePoint, partialY, mul_comm]

theorem pullback_partialY {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (pullback Λ F) p = Λ * partialY F (rescalePoint Λ p) :=
  (pullback_hasDerivAt_Y hF Λ hp).deriv

theorem pullback_partialEta (Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    partialEta (pullback Λ F) p = partialEta F (rescalePoint Λ p) := rfl

theorem pullback_second_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    iteratedDeriv 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 =
      Λ ^ 2 * iteratedDeriv 2 (fun Y : ℝ => F (Y, p.2)) (Λ * p.1) := by
  have hs := sliceY_smooth hF hp
  have hs' : ContDiffAt ℝ 1 (deriv (fun Y : ℝ => F (Y, p.2))) (Λ * p.1) := by
    exact (hs.fderiv_right (m := 1)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).clm_apply
        contDiffAt_const
  have hd := ((hs'.differentiableAt (by norm_num)).hasDerivAt.comp p.1
    ((hasDerivAt_id p.1).const_mul Λ)).const_mul Λ
  have heq : deriv (fun X : ℝ => pullback Λ F (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X : ℝ => Λ * deriv (fun Y : ℝ => F (Y, p.2)) (Λ * X)) := by
    have hc : Continuous (fun X : ℝ => (Λ * X, p.2)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)] with X hX
    exact (pullback_hasDerivAt_Y hF Λ (p := (X, p.2)) hX).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  convert! hd.deriv using 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem pullback_radialDifferential {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (pullback Λ F) p =
      Λ * radialDifferential r F (rescalePoint Λ p) := by
  unfold radialDifferential
  rw [pullback_second_Y hF Λ hp, pullback_partialY hF Λ hp]
  dsimp [rescalePoint]
  ring

theorem affineProfile_partialY {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (affineProfile b c Λ F) p = c * Λ * partialY F (rescalePoint Λ p) := by
  simpa only [affineProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hF Λ hp).const_mul c).const_add (b p.2) |>.deriv

theorem affineProfile_partialEta {b : ℝ → ℝ} {b' : ℝ}
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hb : HasDerivAt b b' p.2) :
    partialEta (affineProfile b c Λ F) p = b' + c * partialEta F (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hF hp).differentiableAt (by norm_num)
  exact (hb.add (hf.hasDerivAt.const_mul c)).deriv

theorem affineProfile_radialDifferential {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (affineProfile b c Λ F) p =
      c * Λ * radialDifferential r F (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 := by
    exact ((sliceY_smooth hF hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [affineProfile_partialY hF b c Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => b p.2 + c * pullback Λ F (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ)),
    iteratedDeriv_const_mul c hs, pullback_second_Y hF Λ hp]
  dsimp [rescalePoint]
  ring

theorem angularProfile_partialY {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (angularProfile a Λ Φ) p = a p.2 * Λ * partialY Φ (rescalePoint Λ p) := by
  simpa only [angularProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hΦ Λ hp).const_mul (a p.2)).deriv

theorem angularProfile_partialEta {a : ℝ → ℝ} {a' : ℝ}
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : HasDerivAt a a' p.2) :
    partialEta (angularProfile a Λ Φ) p =
      a' * Φ (rescalePoint Λ p) + a p.2 * partialEta Φ (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hΦ hp).differentiableAt (by norm_num)
  exact (ha.mul hf.hasDerivAt).deriv

theorem angularProfile_radialDifferential {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (angularProfile a Λ Φ) p =
      a p.2 * Λ * radialDifferential r Φ (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ Φ (X, p.2)) p.1 := by
    exact ((sliceY_smooth hΦ hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [angularProfile_partialY hΦ a Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => a p.2 * pullback Λ Φ (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_mul (a p.2) hs, pullback_second_Y hΦ Λ hp]
  dsimp [rescalePoint]
  ring

/-- The fixed polynomial and pressure fields, interpreted as real functions. -/
def actualData (h j σ : ℝ) (P0 : ℝ → ℝ) : ParameterData where
  A := NaturalAxisData.A h
  D := NaturalAxisData.D h
  h := h
  chi := NaturalAxisData.chi h j σ
  d := NaturalAxisData.d
  inverseL := fun η => (NaturalAxisData.L h η)⁻¹
  uStar := NaturalAxisData.U j
  uStarEta := fun _ => 4
  wStar := NaturalAxisData.W h j
  hStar := NaturalAxisData.H h j
  kappa := realGradient h j σ
  zStar := NaturalAxisData.Z h j P0

/-- Replace all coefficient evaluations by their proved concrete values. -/
theorem materialize_scaled {h j σ t : ℝ} {P0 a₀ : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (a : AxisCoefficientSpace.AxisSpace window v.epsilon)
    (ha : ∀ η ∈ window.interval, inputValue window v.epsilon a η = a₀ η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window
      (parameters window v.epsilon (v.elements .chi) v.axisData) t
      (inputValue window v.epsilon a) Φ u B P) :
    IsScaledSolution window (actualData h j σ P0) t a₀ Φ u B P := by
  refine {
    phi_smooth := hs.phi_smooth
    u_smooth := hs.u_smooth
    average_smooth := hs.average_smooth
    pressure_smooth := hs.pressure_smooth
    phi_axis := hs.phi_axis
    u_axis := hs.u_axis
    average_axis := hs.average_axis
    pressure_axis := hs.pressure_axis
    average_equation := hs.average_equation
    average_integral := hs.average_integral
    pressure_equation := ?_
    pressure_integral := ?_
    angular_equation := ?_
    axial_equation := ?_
  }
  · intro p hp
    rw [hs.pressure_equation p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    rw [hs.pressure_integral p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [angularRemainder, reconstructedW, reconstructedU, reconstructedH,
      actualData, parameters, CoefficientFamily.axisData, hv, realField] using
      hs.angular_equation p hp
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [axialRemainder, reconstructedW, actualData, parameters,
      CoefficientFamily.axisData, hv, realField] using hs.axial_equation p hp

theorem amplitude_smooth {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) :
    ContDiffOn ℝ ∞ (realAmplitude h j σ Λ C) (Ioo window.left window.right) := by
  intro η hη
  have hc : ContDiffAt ℂ ∞ (axisPhase h j σ) (η : ℂ) :=
    (d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)).contDiffAt
  have hr : ContDiffAt ℝ ∞ (realPhase h j σ) η := by
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using hc.real_of_complex
  exact (((contDiffAt_const.mul hr).exp).mul contDiffAt_const).contDiffWithinAt

theorem uStar_hasDerivAt (j η : ℝ) : HasDerivAt (NaturalAxisData.U j) 4 η := by
  change HasDerivAt (fun x : ℝ => 4 * x + j) 4 η
  simpa only [mul_one, id_eq] using ((hasDerivAt_id η).const_mul 4).add_const j

theorem uStar_smooth (j : ℝ) : ContDiff ℝ ∞ (NaturalAxisData.U j) := by
  exact (contDiff_const.mul contDiff_id).add contDiff_const

/-- The natural transport coefficient recovered from the true radial average. -/
def transportW (h : ℝ) (V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - 2 * NaturalAxisData.D h * p.2 * V p - NaturalAxisData.d p.2 * partialEta V p

/-- Transport H, given by `NaturalAxisData.D h * p.2 + NaturalAxisData.d p.2 * U p`. -/
def transportH (h : ℝ) (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  NaturalAxisData.D h * p.2 + NaturalAxisData.d p.2 * U p

theorem transportW_reconstruct {h j σ Λ : ℝ} (P0 : ℝ → ℝ) {B : ℝ × ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p =
      reconstructedW (actualData h j σ P0) (1 / Λ) B (rescalePoint Λ p) := by
  unfold transportW
  rw [affineProfile_partialEta hB (1 / Λ) Λ hp (uStar_hasDerivAt j p.2)]
  simp only [affineProfile, pullback, reconstructedW, actualData, rescalePoint,
    NaturalAxisData.W]
  ring

theorem transportH_reconstruct (h j σ Λ : ℝ) (P0 : ℝ → ℝ) (u : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) :
    transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p) := by
  simp only [transportH, affineProfile, pullback, reconstructedH, actualData,
    rescalePoint, NaturalAxisData.H]
  ring

theorem gradient_identity (h j σ η : ℝ) :
    NaturalAxisData.H h j η * realGradient h j σ η =
      -NaturalAxisData.L h η * NaturalAxisData.chi h j σ η := by
  unfold realGradient NaturalAxisData.chi
  ring

/-- The actual unscaled system, with all derivatives taken on real functions. -/
structure IsNaturalSolution (h j Λ : ℝ) (P0 a₀ : ℝ → ℝ)
    (f U V Pr : ℝ × ℝ → ℝ) : Prop where
  f_smooth : ContDiffOn ℝ ∞ f (domain Λ)
  U_smooth : ContDiffOn ℝ ∞ U (domain Λ)
  average_smooth : ContDiffOn ℝ ∞ V (domain Λ)
  pressure_smooth : ContDiffOn ℝ ∞ Pr (domain Λ)
  f_axis : ∀ η ∈ Ioo window.left window.right, f (0, η) = a₀ η
  U_axis : ∀ η ∈ Ioo window.left window.right, U (0, η) = NaturalAxisData.U j η
  average_axis : ∀ η ∈ Ioo window.left window.right, V (0, η) = NaturalAxisData.U j η
  pressure_axis : ∀ η ∈ Ioo window.left window.right, Pr (0, η) = P0 η
  average_equation : ∀ p ∈ domain Λ, V p + p.1 * partialY V p = U p
  pressure_equation : ∀ p ∈ domain Λ, partialY Pr p = (f p) ^ 2
  average_integral : ∀ p ∈ domain Λ,
    p.1 * V p = ∫ X in (0 : ℝ)..p.1, U (X, p.2)
  pressure_integral : ∀ p ∈ domain Λ,
    Pr p - P0 p.2 = ∫ X in (0 : ℝ)..p.1, (f (X, p.2)) ^ 2
  angular_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 f p =
      transportW h V p * (p.1 * partialY f p + f p) +
      h * (1 - 2 * p.2 * U p) * f p + transportH h U p * partialEta f p
  axial_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 1 U p =
      transportW h V p * (p.1 * partialY U p) +
      NaturalAxisData.A h * (1 - 2 * p.2 * U p) * U p +
      transportH h U p * partialEta U p + NaturalAxisData.d p.2 * partialEta Pr p -
      4 * NaturalAxisData.A h * p.2 * Pr p - 2 * p.2 * p.1 * partialY Pr p

private theorem angular_rescale_identity
    {Λ L X η h d u U W H Hs κ χ a φ φY φEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0) (hχ : Hs * κ = -L * χ)
    (hH : H = Hs + (1 / Λ) * d * u)
    (heq : 2 * R = -χ * φ + (1 / Λ) * L⁻¹ *
      ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
        W * (Λ * X * φY) + H * φEta)) :
    2 * L * (a * Λ * R) = W * (X * (a * Λ * φY) + a * φ) +
      h * (1 - 2 * η * U) * (a * φ) + H * ((Λ * κ) * a * φ + a * φEta) := by
  calc
    _ = a * Λ * L * (2 * R) := by ring
    _ = a * Λ * L * (-χ * φ + (1 / Λ) * L⁻¹ *
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by rw [heq]
    _ = a * (Λ * (Hs * κ) * φ +
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by
      rw [hχ]
      field_simp
    _ = _ := by
      rw [hH]
      field_simp; ring

private theorem axial_rescale_identity
    {Λ L X η A d Us UsEta Hs W u uY uEta P0 P0Eta P PY PEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0)
    (heq : 2 * R = -L⁻¹ *
      (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
      (1 / Λ) * L⁻¹ *
        (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
          W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
          (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta - 2 * η * (Λ * X * PY))) :
    2 * L * R = W * (X * uY) +
      A * (1 - 2 * η * (Us + (1 / Λ) * u)) * (Us + (1 / Λ) * u) +
      (Hs + (1 / Λ) * d * u) * (UsEta + (1 / Λ) * uEta) +
      d * (P0Eta + (1 / Λ) * PEta) - 4 * A * η * (P0 + (1 / Λ) * P) -
      2 * η * X * PY := by
  calc
    _ = L * (2 * R) := by ring
    _ = L * (-L⁻¹ *
        (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
        (1 / Λ) * L⁻¹ *
          (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
            W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
            (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta -
            2 * η * (Λ * X * PY))) := by rw [heq]
    _ = _ := by
      field_simp; ring

theorem angular_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hΛ : Λ ≠ 0)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    (ha : HasDerivAt a₀ ((Λ * realGradient h j σ p.2) * a₀ p.2) p.2) :
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 (angularProfile a₀ Λ Φ) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (angularProfile a₀ Λ Φ) p + angularProfile a₀ Λ Φ p) +
      h * (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        angularProfile a₀ Λ Φ p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (angularProfile a₀ Λ Φ) p := by
  rw [angularProfile_radialDifferential hs.phi_smooth a₀ Λ 2 hp,
    angularProfile_partialY hs.phi_smooth a₀ Λ hp,
    angularProfile_partialEta hs.phi_smooth Λ hp ha,
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  · have hL : NaturalAxisData.L h p.2 ≠ 0 :=
      (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
    apply angular_rescale_identity hΛ hL (gradient_identity h j σ p.2)
      (H := reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p))
      (Hs := NaturalAxisData.H h j p.2)
    · rfl
    · simpa only [angularRemainder, actualData, reconstructedU, rescalePoint,
        affineProfile, pullback, mul_assoc] using hs.angular_equation (rescalePoint Λ p) hp

theorem axial_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hΛ : Λ ≠ 0)
    (hP0 : ContDiff ℝ ∞ P0) {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    2 * NaturalAxisData.L h p.2 *
        radialDifferential 1 (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p) +
      NaturalAxisData.A h *
        (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p +
      NaturalAxisData.d p.2 * partialEta (affineProfile P0 (1 / Λ) Λ P) p -
      4 * NaturalAxisData.A h * p.2 * affineProfile P0 (1 / Λ) Λ P p -
      2 * p.2 * p.1 * partialY (affineProfile P0 (1 / Λ) Λ P) p := by
  rw [affineProfile_radialDifferential hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ 1 hp,
    affineProfile_partialY hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
    affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
    affineProfile_partialEta hs.u_smooth (1 / Λ) Λ hp (uStar_hasDerivAt j p.2),
    affineProfile_partialEta hs.pressure_smooth (1 / Λ) Λ hp
      ((hP0.differentiable (by norm_num)).differentiableAt.hasDerivAt),
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  · simp only [one_div_mul_cancel hΛ, one_mul]
    have hL : NaturalAxisData.L h p.2 ≠ 0 :=
      (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
    apply axial_rescale_identity hΛ hL
    simpa only [axialRemainder, actualData, NaturalAxisData.Z, reconstructedH,
      rescalePoint, affineProfile, pullback, mul_assoc] using
        hs.axial_equation (rescalePoint Λ p) hp

theorem domain_segment {Λ : ℝ} (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    {X : ℝ} (hX : X ∈ uIcc (0 : ℝ) p.1) : (X, p.2) ∈ domain Λ := by
  change (-20 < Λ * X ∧ Λ * X < 20) ∧ p.2 ∈ Ioo window.left window.right
  change (-20 < Λ * p.1 ∧ Λ * p.1 < 20) ∧ _ at hp
  refine ⟨?_, hp.2⟩
  rcases le_total 0 p.1 with hpos | hneg
  · rw [uIcc_of_le hpos]
      at hX
    constructor
    · have := mul_nonneg hΛ.le hX.1
      linarith
    · exact (mul_le_mul_of_nonneg_left hX.2 hΛ.le).trans_lt hp.1.2
  · rw [uIcc_of_ge hneg]
      at hX
    constructor
    · exact hp.1.1.trans_le (mul_le_mul_of_nonneg_left hX.1 hΛ.le)
    · have := mul_nonpos_of_nonneg_of_nonpos hΛ.le hX.2
      linarith

theorem average_integral_reconstruct {Λ : ℝ} (hΛ : 0 < Λ)
    (b : ℝ → ℝ) (c : ℝ) {u B : ℝ × ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (AxisEvaluation.strip window 20))
    (havg : ∀ q ∈ AxisEvaluation.strip window 20,
      q.1 * B q = ∫ Y in (0 : ℝ)..q.1, u (Y, q.2))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    p.1 * affineProfile b c Λ B p =
      ∫ X in (0 : ℝ)..p.1, affineProfile b c Λ u (X, p.2) := by
  have hi : IntervalIntegrable (fun X : ℝ => pullback Λ u (X, p.2))
      MeasureTheory.volume 0 p.1 := by
    apply ContinuousOn.intervalIntegrable
    exact (pullback_smooth hu Λ).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx => domain_segment hΛ hp hx)
  have hchange := intervalIntegral.integral_comp_mul_left
    (fun Y : ℝ => u (Y, p.2)) hΛ.ne' (a := 0) (b := p.1)
  change p.1 * (b p.2 + c * B (rescalePoint Λ p)) =
    ∫ X in (0 : ℝ)..p.1, b p.2 + c * pullback Λ u (X, p.2)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul c),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  change _ = (p.1 - 0) * b p.2 + c * ∫ X in (0 : ℝ)..p.1, u (Λ * X, p.2)
  rw [hchange]
  simp only [mul_zero, smul_eq_mul, sub_zero]
  have hav := havg (rescalePoint Λ p) hp
  dsimp only [rescalePoint] at hav
  rw [← hav]
  dsimp [rescalePoint]
  field_simp

/-- Reconstruction preserves the full differential and integral system. -/
theorem reconstruct_solution {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hΛ : 0 < Λ)
    (hP0 : ContDiff ℝ ∞ P0)
    (haSmooth : ContDiffOn ℝ ∞ a₀ (Ioo window.left window.right))
    (ha : ∀ η ∈ Ioo window.left window.right,
      HasDerivAt a₀ ((Λ * realGradient h j σ η) * a₀ η) η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P) :
    IsNaturalSolution h j Λ P0 a₀ (angularProfile a₀ Λ Φ)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B)
      (affineProfile P0 (1 / Λ) Λ P) := by
  refine {
    f_smooth := angularProfile_smooth haSmooth hs.phi_smooth Λ
    U_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.u_smooth (1 / Λ) Λ
    average_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.average_smooth (1 / Λ) Λ
    pressure_smooth := affineProfile_smooth hP0.contDiffOn hs.pressure_smooth (1 / Λ) Λ
    f_axis := ?_
    U_axis := ?_
    average_axis := ?_
    pressure_axis := ?_
    average_equation := ?_
    pressure_equation := ?_
    average_integral := fun p hp => average_integral_reconstruct hΛ (NaturalAxisData.U j)
      (1 / Λ) hs.u_smooth hs.average_integral hp
    pressure_integral := ?_
    angular_equation := fun p hp => angular_equation_reconstruct hsmall hΛ.ne' hs hp (ha p.2 hp.2)
    axial_equation := fun p hp => axial_equation_reconstruct hsmall hΛ.ne' hP0 hs hp
  }
  · intro η hη
    simp only [angularProfile, pullback, rescalePoint, mul_zero, hs.phi_axis η hη, mul_one]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.average_axis η hη,
      hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.pressure_axis η hη, add_zero]
  · intro p hp
    rw [affineProfile_partialY hs.average_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul]
    change NaturalAxisData.U j p.2 + (1 / Λ) * B (rescalePoint Λ p) +
      p.1 * partialY B (rescalePoint Λ p) =
        NaturalAxisData.U j p.2 + (1 / Λ) * u (rescalePoint Λ p)
    have he := hs.average_equation (rescalePoint Λ p) hp
    dsimp [rescalePoint] at he ⊢
    apply (mul_left_cancel₀ hΛ.ne')
    field_simp
    linear_combination he
  · intro p hp
    rw [affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul, hs.pressure_equation (rescalePoint Λ p) hp]
    simp only [angularProfile, pullback, rescalePoint, mul_pow]
  · intro p hp
    change P0 p.2 + (1 / Λ) * P (rescalePoint Λ p) - P0 p.2 = _
    rw [add_sub_cancel_left, hs.pressure_integral (rescalePoint Λ p) hp]
    have he := intervalIntegral.integral_comp_mul_left
      (fun Y : ℝ => (a₀ p.2) ^ 2 * (Φ (Y, p.2)) ^ 2) hΛ.ne' (a := 0) (b := p.1)
    simpa only [angularProfile, pullback, rescalePoint, mul_zero, smul_eq_mul, mul_pow,
      one_div] using he.symm

theorem angularProfile_log_slope_at_four {Λ : ℝ} (hΛ : 0 < Λ)
    {a : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    {η : ℝ} (hη : η ∈ Ioo window.left window.right)
    (ha : 0 < a η) (hval : 0 < Φ (4, η)) :
    -2 * (4 / Λ) * partialY (angularProfile a Λ Φ) (4 / Λ, η) /
        angularProfile a Λ Φ (4 / Λ, η) =
      -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hrad : Λ * (4 / Λ) = 4 := by field_simp
  have hp : (4 / Λ, η) ∈ domain Λ := by
    change (Λ * (4 / Λ), η) ∈ AxisEvaluation.strip window 20
    rw [hrad]
    exact ⟨by norm_num, hη⟩
  rw [angularProfile_partialY hΦ a Λ hp]
  simp only [angularProfile, pullback, rescalePoint, hrad]
  field_simp; ring

/-- Profile error constant, constructed using `errorConstant`. -/
def profileErrorConstant {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) : ℝ :=
  errorConstant window d.coefficients.epsilon_pos (d.coefficients.elements .chi)
    d.coefficients.axisData d.amplitudeBound d.amplitudeBound_nonneg

/-- The functions and estimates obtained from one actual coefficient-space
fixed point. All unscaled functions are explicit expressions in these fields. -/
structure ProfileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) where
  /-- Phi of `ProfileFamily`, of type `ℝ × ℝ → ℝ`. -/
  phi : ℝ × ℝ → ℝ
  /-- U of `ProfileFamily`, of type `ℝ × ℝ → ℝ`. -/
  u : ℝ × ℝ → ℝ
  /-- Average of `ProfileFamily`, of type `ℝ × ℝ → ℝ`. -/
  average : ℝ × ℝ → ℝ
  /-- Pressure field of `ProfileFamily`, of type `ℝ × ℝ → ℝ`. -/
  pressure : ℝ × ℝ → ℝ
  natural : IsNaturalSolution h j Λ P0 (realAmplitude h j σ Λ C)
    (angularProfile (realAmplitude h j σ Λ C) Λ phi)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ average)
    (affineProfile P0 (1 / Λ) Λ pressure)
  mixed_error : UniformMixedError window d.coefficients.epsilon
    (profileErrorConstant d / (2 * Λ)) phi u
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).1)
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).2)
  positive : ∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 →
    0 < angularProfile (realAmplitude h j σ Λ C) Λ phi p
  slope : ∀ η ∈ Ioo window.left window.right, 99 / 100 ≤ NaturalAxisData.chi h j σ η →
    23 / 10 <
      -2 * (4 / Λ) * partialY (angularProfile (realAmplitude h j σ Λ C) Λ phi) (4 / Λ, η) /
        angularProfile (realAmplitude h j σ Λ C) Λ phi (4 / Λ, η)

/-- F, given by `angularProfile (realAmplitude h j σ Λ C) Λ F.phi`. -/
def ProfileFamily.f {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  angularProfile (realAmplitude h j σ Λ C) Λ F.phi

/-- U, given by `affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.u`. -/
def ProfileFamily.U {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.u

/-- Ubar, given by `affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.average`. -/
def ProfileFamily.Ubar {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.average

/-- Pi, given by `affineProfile P0 (1 / Λ) Λ F.pressure`. -/
def ProfileFamily.Pi {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile P0 (1 / Λ) Λ F.pressure

/-- The scale threshold is uniform over every normalization above the actual
compact-domain exponential threshold. -/
theorem exists_profileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  have hchi : ∀ η ∈ window.interval,
      0 ≤ inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ∧
        inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ≤ 1 := by
    intro η hη
    rw [d.coefficients.value .chi hη]
    exact ⟨(NaturalAxisData.chi_bounds h j hσ η).1, (NaturalAxisData.chi_bounds h j hσ η).2.le⟩
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := AxisReference.exists_positive_scaled_profiles window
    d.coefficients.epsilon_pos (d.coefficients.elements .chi) d.coefficients.axisData
    d.coefficients.compatible hchi d.amplitudeBound d.amplitudeBound_nonneg
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ C hC
  have hΛpos : 0 < Λ := hΛ₀.trans_le hΛ
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  obtain ⟨a, ha, harad, havalue⟩ := d.uniformAmplitude Λ hΛpos.le C hC
  obtain ⟨Φ, u, B, P, hs, herr, hpositive, hslope⟩ := hexists Λ hΛ a ha harad
  have hs' := materialize_scaled d.coefficients a havalue hs
  refine ⟨{
    phi := Φ
    u := u
    average := B
    pressure := P
    natural := reconstruct_solution hsmall hΛpos hP0 (amplitude_smooth d Λ C)
      (fun η hη => d.realAmplitude_hasDerivAt Λ C ⟨hη.1.le, hη.2.le⟩) hs'
    mixed_error := herr
    positive := ?_
    slope := ?_
  }⟩
  · intro p hp hY0 hY1
    exact mul_pos (realAmplitude_pos h j σ Λ hCpos p.2)
      (lt_trans (by norm_num) (hpositive (Λ * p.1) ⟨hY0, hY1⟩ p.2 hp.2))
  · intro η hη hchiη
    rw [angularProfile_log_slope_at_four hΛpos hs.phi_smooth hη
      (realAmplitude_pos h j σ Λ hCpos η)
      (lt_trans (by norm_num) (hpositive 4 (by norm_num) η hη))]
    apply hslope η hη
    rw [d.coefficients.value .chi ⟨hη.1.le, hη.2.le⟩]
    exact hchiη

/-- The pressure integral and ideal prefix yield actual unscaled natural
profiles after selecting the cutoff and common analytic coefficient radius. -/
theorem ideal_prefix_profileFamily {h j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ η) ∧
      ∃ d : AnalyticInputs h j σ (PressureDatum.pressure g a),
        ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
          ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ :=
    ideal_prefix_analytic_inputs hsmall hp hB hg ha
  refine ⟨δ, σ, hδ, hσ, hcut, d, ?_⟩
  exact exists_profileFamily d hsmall hσ (PressureDatum.pressure_contDiff hp)

/-- A direct existence theorem for the unscaled real functions. The cutoff,
analytic input family, large scale, and normalization are all constructed
from the stated pressure assumptions. -/
theorem exists_natural_profiles {h j : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ Λ C : ℝ, 0 < δ ∧ 0 < σ ∧ 0 < Λ ∧ 0 < C ∧
      ∃ f U V Pr : ℝ × ℝ → ℝ,
        IsNaturalSolution h j Λ (PressureDatum.pressure g a)
          (realAmplitude h j σ Λ C) f U V Pr ∧
        (∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 → 0 < f p) ∧
        (∀ η ∈ Icc (-1 : ℝ) 1,
          |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
            23 / 10 < -2 * (4 / Λ) * partialY f (4 / Λ, η) / f (4 / Λ, η)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, d, Λ, hΛ, hexists⟩ :=
    ideal_prefix_profileFamily hsmall hp hB hg ha
  let C := d.normalizationThreshold Λ
  obtain ⟨F⟩ := hexists Λ le_rfl C le_rfl
  refine ⟨δ, σ, Λ, C, hδ, hσ, hΛ, Real.exp_pos _,
    F.f, F.U, F.Ubar, F.Pi, F.natural, F.positive, ?_⟩
  intro η hη hZ
  exact F.slope η (original_interval_interior hη) (hcut η hη hZ).le

end NavierStokes.NaturalProfile

end
