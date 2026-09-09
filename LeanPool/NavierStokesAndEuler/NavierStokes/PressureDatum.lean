/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

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
  have hl : 0 ≤ Real.log (1 + η ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg η])
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hl

theorem kernel_antitone {a b : ℝ} (hab : a ≤ b) (η : ℝ) :
    kernel b η ≤ kernel a η := by
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log (1 + η ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg η])
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
  nlinarith

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
  nlinarith

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
  nlinarith

theorem pressure_le_prefix_mass {g a : ℝ → ℝ} {A b m : ℝ}
    (h : Admissible g a A) {s : Set ℝ} (hs : MeasurableSet s)
    (ha : ∀ y ∈ s, a y = b) (hm : m ≤ ∫ y in s, g y) (η : ℝ) :
    pressure g a η ≤ -(1 / 2 : ℝ) * m * kernel b η := by
  have hp := pressure_le_prefix h hs ha η
  have hk := mul_le_mul_of_nonneg_left hm (kernel_pos b η).le
  nlinarith

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
  nlinarith

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
