/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveDyadicKernel
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivative of the low oscillatory kernel

In the accompanying article ([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)), the low kernel
`K_{λ,B}` is asserted to satisfy
`|K'_{λ,B}(t)| ≲ min {|λ|, 2^(2B)/|t|²}`.  This file records the exact
product/quotient-rule formula away from zero and derives its constants from
the fixed smooth cutoff used by `PositiveDyadicKernel`.
-/

open Function Set
open scoped Topology

namespace QuadraticCarleson


/-- The real derivative of the fixed cutoff has a global finite bound. -/
theorem exists_dyadicCutoff_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv dyadicCutoff x| ≤ C := by
  have hcont : Continuous (fun x : ℝ ↦ |deriv dyadicCutoff x|) := by
    have hs2 : ContDiff ℝ 2 dyadicCutoff := dyadicCutoff_smooth.of_le (by simp)
    exact (hs2.differentiable_deriv_two.continuous).abs
  have hcompact : HasCompactSupport (fun x : ℝ ↦ |deriv dyadicCutoff x|) := by
    exact (dyadicCutoffData.hasCompactSupport.deriv.norm)
  have hbdd : BddAbove (range fun x : ℝ ↦ |deriv dyadicCutoff x|) :=
    hcont.bddAbove_range_of_hasCompactSupport hcompact
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

/-- A concrete finite constant controlling the derivative of the fixed
dyadic cutoff. -/
noncomputable def dyadicCutoffDerivBound : ℝ :=
  Classical.choose exists_dyadicCutoff_deriv_bound

theorem dyadicCutoffDerivBound_nonneg : 0 ≤ dyadicCutoffDerivBound :=
  (Classical.choose_spec exists_dyadicCutoff_deriv_bound).1

theorem abs_deriv_dyadicCutoff_le (x : ℝ) :
    |deriv dyadicCutoff x| ≤ dyadicCutoffDerivBound :=
  (Classical.choose_spec exists_dyadicCutoff_deriv_bound).2 x

theorem hasDerivAt_quadraticPhase_lowKernel (lam t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ phase (lam * u ^ 2))
      (phase (lam * t ^ 2) *
        (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I)) t := by
  unfold phase
  have hpow : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hr : HasDerivAt (fun u : ℝ ↦ 2 * Real.pi * (lam * u ^ 2))
      (4 * Real.pi * lam * t) t := by
    exact ((hpow.const_mul lam).const_mul (2 * Real.pi)).congr_deriv (by ring)
  have hc := hr.ofReal_comp.mul_const Complex.I
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasDerivAt_exp _).comp t hc

/-- The two cutoff scales in the telescoped formula. -/
noncomputable def lowOuterScale (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) : ℝ :=
  (2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ))

noncomputable def lowInnerScale (lam : ℝ) (hlam : lam ≠ 0) : ℝ :=
  (2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1)

/-- Exact scalar derivative of the telescoped cutoff quotient away from zero. -/
noncomputable def lowCutoffQuotientDerivative
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) : ℝ :=
  ((deriv dyadicCutoff (lowOuterScale lam hlam B * t) * lowOuterScale lam hlam B -
      deriv dyadicCutoff (lowInnerScale lam hlam * t) * lowInnerScale lam hlam) * t -
    (dyadicCutoff (lowOuterScale lam hlam B * t) -
      dyadicCutoff (lowInnerScale lam hlam * t))) / t ^ 2

/-- The exact complex derivative displayed by the product rule. -/
noncomputable def paperLowOscillatoryKernelDerivative
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) : ℂ :=
  (lowCutoffQuotientDerivative lam hlam B t : ℂ) * phase (lam * t ^ 2) +
    (((dyadicCutoff (lowOuterScale lam hlam B * t) -
        dyadicCutoff (lowInnerScale lam hlam * t)) / t : ℝ) : ℂ) *
      (phase (lam * t ^ 2) * (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I))

theorem lowCutoffQuotient_deriv
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    deriv (fun u : ℝ ↦
        (dyadicCutoff (lowOuterScale lam hlam B * u) -
          dyadicCutoff (lowInnerScale lam hlam * u)) / u) t =
      lowCutoffQuotientDerivative lam hlam B t := by
  let hd (c : ℝ) := by
    have hc : HasDerivAt (fun u : ℝ ↦ c * u) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    exact ((dyadicCutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt).comp t hc
  have hquot := ((hd (lowOuterScale lam hlam B)).sub
    (hd (lowInnerScale lam hlam))).div (hasDerivAt_id t) ht
  have h := (hquot.congr_deriv (by
    dsimp [lowCutoffQuotientDerivative])).deriv
  have hfun :
      (((dyadicCutoff ∘ fun u : ℝ ↦ lowOuterScale lam hlam B * u) -
          (dyadicCutoff ∘ fun u : ℝ ↦ lowInnerScale lam hlam * u)) / id) =
        (fun u : ℝ ↦
          (dyadicCutoff (lowOuterScale lam hlam B * u) -
            dyadicCutoff (lowInnerScale lam hlam * u)) / u) := by
    rfl
  rw [← hfun]
  unfold lowCutoffQuotientDerivative
  simpa only [mul_one] using h

/-- Exact derivative formula for the paper's low kernel at every nonzero
point. -/
theorem hasDerivAt_paperLowOscillatoryKernel
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (paperLowOscillatoryKernel lam hlam B)
      (paperLowOscillatoryKernelDerivative lam hlam B t) t := by
  let q : ℝ → ℝ := fun u ↦
    (dyadicCutoff (lowOuterScale lam hlam B * u) -
      dyadicCutoff (lowInnerScale lam hlam * u)) / u
  have hqdiff : DifferentiableAt ℝ q t := by
    have hmul (c : ℝ) : DifferentiableAt ℝ (fun u : ℝ ↦ c * u) t :=
      (differentiableAt_const (c := c)).mul differentiableAt_id
    apply DifferentiableAt.div
    · exact ((dyadicCutoff_smooth.differentiable (by simp)).differentiableAt.comp t
          (hmul (lowOuterScale lam hlam B))).sub
        ((dyadicCutoff_smooth.differentiable (by simp)).differentiableAt.comp t
          (hmul (lowInnerScale lam hlam)))
    · exact differentiableAt_id
    · exact ht
  have hqderiv : deriv q t = lowCutoffQuotientDerivative lam hlam B t := by
    simpa [q] using lowCutoffQuotient_deriv hlam B ht
  let hq := hqdiff.hasDerivAt.congr_deriv hqderiv
  have hprod := hq.ofReal_comp.mul (hasDerivAt_quadraticPhase_lowKernel lam t)
  apply hprod.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds ht] with u hu
  rw [paperLowOscillatoryKernel_eq_cutoffDifference hlam B hu]
  rfl

theorem paperLowOscillatoryKernel_deriv
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    deriv (paperLowOscillatoryKernel lam hlam B) t =
      paperLowOscillatoryKernelDerivative lam hlam B t := by
  exact (hasDerivAt_paperLowOscillatoryKernel hlam B ht).deriv

theorem lowOuterScale_pos {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) :
    0 < lowOuterScale lam hlam B := by
  exact zpow_pos (by norm_num) _

theorem lowInnerScale_pos {lam : ℝ} (hlam : lam ≠ 0) :
    0 < lowInnerScale lam hlam := by
  exact zpow_pos (by norm_num) _

theorem lowInnerScale_le_two_sqrt_abs {lam : ℝ} (hlam : lam ≠ 0) :
    lowInnerScale lam hlam ≤ 2 * Real.sqrt |lam| := by
  let j := oscillatoryScaleIndex lam 0 hlam
  have hs := (oscillatoryScaleIndex_spec lam 0 hlam).1
  have hp : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hjinv : lowInnerScale lam hlam = 2 / (2 : ℝ) ^ j := by
    dsimp [lowInnerScale, j]
    rw [inv_zpow, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hjinv]
  apply (div_le_iff₀ hp).2
  nlinarith [hs]

theorem lowOuterScale_le_sqrt_abs_div_pow {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) :
    lowOuterScale lam hlam B ≤ Real.sqrt |lam| / (2 : ℝ) ^ B := by
  let j := oscillatoryScaleIndex lam 0 hlam
  have hs := (oscillatoryScaleIndex_spec lam 0 hlam).1
  have hj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hB : 0 < (2 : ℝ) ^ B := by positivity
  have heq : lowOuterScale lam hlam B = 1 / ((2 : ℝ) ^ j * (2 : ℝ) ^ B) := by
    dsimp [lowOuterScale, j]
    rw [inv_zpow, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    rw [one_div]
  rw [heq]
  rw [show 1 / ((2 : ℝ) ^ j * (2 : ℝ) ^ B) =
      (1 / (2 : ℝ) ^ j) / (2 : ℝ) ^ B by field_simp]
  apply (div_le_div_iff_of_pos_right hB).2
  rw [one_div]
  apply (inv_le_iff_one_le_mul₀' hj).2
  simpa using hs

/-- A single explicit constant used in both Calderón--Zygmund derivative
bounds. -/
noncomputable def lowKernelDerivativeConstant : ℝ :=
  256 * (dyadicCutoffDerivBound + 1 + Real.pi)

theorem lowKernelDerivativeConstant_nonneg : 0 ≤ lowKernelDerivativeConstant := by
  unfold lowKernelDerivativeConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg dyadicCutoffDerivBound_nonneg zero_le_one) Real.pi_pos.le)

theorem abs_dyadicCutoff_sub_le_one (x y : ℝ) :
    |dyadicCutoff x - dyadicCutoff y| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    linarith [dyadicCutoff_nonneg x, dyadicCutoff_le_one x,
      dyadicCutoff_nonneg y, dyadicCutoff_le_one y]

theorem abs_lowCutoffQuotientDerivative_le
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |lowCutoffQuotientDerivative lam hlam B t| ≤
      (dyadicCutoffDerivBound *
          (lowOuterScale lam hlam B + lowInnerScale lam hlam) * |t| + 1) / |t| ^ 2 := by
  let ao := lowOuterScale lam hlam B
  let ai := lowInnerScale lam hlam
  have hao : 0 ≤ ao := (lowOuterScale_pos hlam B).le
  have hai : 0 ≤ ai := (lowInnerScale_pos hlam).le
  have hdo := abs_deriv_dyadicCutoff_le (ao * t)
  have hdi := abs_deriv_dyadicCutoff_le (ai * t)
  have hdiff := abs_dyadicCutoff_sub_le_one (ao * t) (ai * t)
  rw [lowCutoffQuotientDerivative, abs_div, abs_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg |t|)
  calc
    |(deriv dyadicCutoff (ao * t) * ao - deriv dyadicCutoff (ai * t) * ai) * t -
        (dyadicCutoff (ao * t) - dyadicCutoff (ai * t))| ≤
        |deriv dyadicCutoff (ao * t) * ao - deriv dyadicCutoff (ai * t) * ai| * |t| +
          |dyadicCutoff (ao * t) - dyadicCutoff (ai * t)| := by
      simpa only [abs_mul] using
        (abs_sub ((deriv dyadicCutoff (ao * t) * ao -
          deriv dyadicCutoff (ai * t) * ai) * t)
          (dyadicCutoff (ao * t) - dyadicCutoff (ai * t)))
    _ ≤ (|deriv dyadicCutoff (ao * t)| * ao +
          |deriv dyadicCutoff (ai * t)| * ai) * |t| + 1 := by
      gcongr
      simpa [abs_mul, abs_of_nonneg hao, abs_of_nonneg hai, sub_eq_add_neg] using
        abs_add_le (deriv dyadicCutoff (ao * t) * ao)
          (-deriv dyadicCutoff (ai * t) * ai)
    _ ≤ (dyadicCutoffDerivBound * ao + dyadicCutoffDerivBound * ai) * |t| + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_right hdo hao)
            (mul_le_mul_of_nonneg_right hdi hai)) (abs_nonneg t)) le_rfl
    _ = dyadicCutoffDerivBound * (ao + ai) * |t| + 1 := by ring

theorem paperLowOscillatoryKernelDerivative_norm_le_raw
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖paperLowOscillatoryKernelDerivative lam hlam B t‖ ≤
      (dyadicCutoffDerivBound *
          (lowOuterScale lam hlam B + lowInnerScale lam hlam) * |t| + 1) / |t| ^ 2 +
        4 * Real.pi * |lam| := by
  let d : ℝ := dyadicCutoff (lowOuterScale lam hlam B * t) -
    dyadicCutoff (lowInnerScale lam hlam * t)
  have hd : |d| ≤ 1 := abs_dyadicCutoff_sub_le_one _ _
  have htabs : 0 < |t| := abs_pos.mpr ht
  have hphaseTerm :
      ‖(((d / t : ℝ) : ℂ) *
          (phase (lam * t ^ 2) * (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I)))‖ ≤
        4 * Real.pi * |lam| := by
    simp only [norm_mul, norm_phase, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, one_mul, abs_div]
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have hfour : 0 ≤ 4 * Real.pi * |lam| := mul_nonneg (mul_nonneg (by norm_num) hpi) (abs_nonneg _)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hpi]
    calc
      |d| / |t| * (4 * Real.pi * |lam| * |t|) ≤
          1 / |t| * (4 * Real.pi * |lam| * |t|) := by
        gcongr
      _ = 4 * Real.pi * |lam| := by field_simp
  unfold paperLowOscillatoryKernelDerivative
  calc
    ‖(lowCutoffQuotientDerivative lam hlam B t : ℂ) * phase (lam * t ^ 2) +
        (((dyadicCutoff (lowOuterScale lam hlam B * t) -
          dyadicCutoff (lowInnerScale lam hlam * t)) / t : ℝ) : ℂ) *
          (phase (lam * t ^ 2) * (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I))‖ ≤
      ‖(lowCutoffQuotientDerivative lam hlam B t : ℂ) * phase (lam * t ^ 2)‖ +
        ‖(((d / t : ℝ) : ℂ) *
          (phase (lam * t ^ 2) * (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I)))‖ := by
      simpa only [d] using
        (norm_add_le
          ((lowCutoffQuotientDerivative lam hlam B t : ℂ) * phase (lam * t ^ 2))
          ((((dyadicCutoff (lowOuterScale lam hlam B * t) -
            dyadicCutoff (lowInnerScale lam hlam * t)) / t : ℝ) : ℂ) *
            (phase (lam * t ^ 2) * (((4 * Real.pi * lam * t : ℝ) : ℂ) * Complex.I))))
    _ ≤ |lowCutoffQuotientDerivative lam hlam B t| + 4 * Real.pi * |lam| := by
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add le_rfl hphaseTerm
    _ ≤ (dyadicCutoffDerivBound *
          (lowOuterScale lam hlam B + lowInnerScale lam hlam) * |t| + 1) / |t| ^ 2 +
        4 * Real.pi * |lam| :=
      add_le_add (abs_lowCutoffQuotientDerivative_le hlam B ht) le_rfl

theorem paperLowOscillatoryKernelDerivative_eq_zero_of_normalized_lt
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht : |t| * Real.sqrt |lam| < 1 / 8) :
    paperLowOscillatoryKernelDerivative lam hlam B t = 0 := by
  have hevent : ∀ᶠ u in 𝓝 t, |u| * Real.sqrt |lam| < 1 / 8 :=
    ((continuous_abs.continuousAt.mul continuousAt_const).tendsto.eventually_lt_const ht)
  have hz : paperLowOscillatoryKernel lam hlam B =ᶠ[𝓝 t] (fun _ ↦ 0) := by
    filter_upwards [hevent] with u hu
    by_contra hne
    have hs := paperLowOscillatoryKernel_support_normalized lam hlam B
      (show u ∈ support (paperLowOscillatoryKernel lam hlam B) by simpa [mem_support] using hne)
    linarith [hs.1]
  have hder := hz.deriv_eq
  rw [paperLowOscillatoryKernel_deriv hlam B ht0] at hder
  simpa using hder

theorem paperLowOscillatoryKernelDerivative_eq_zero_of_normalized_gt
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht : (2 : ℝ) ^ B < |t| * Real.sqrt |lam|) :
    paperLowOscillatoryKernelDerivative lam hlam B t = 0 := by
  have hevent : ∀ᶠ u in 𝓝 t, (2 : ℝ) ^ B < |u| * Real.sqrt |lam| :=
    (tendsto_order.1
      (continuous_abs.continuousAt.mul continuousAt_const).tendsto).1 _ ht
  have hz : paperLowOscillatoryKernel lam hlam B =ᶠ[𝓝 t] (fun _ ↦ 0) := by
    filter_upwards [hevent] with u hu
    by_contra hne
    have hs := paperLowOscillatoryKernel_support_normalized lam hlam B
      (show u ∈ support (paperLowOscillatoryKernel lam hlam B) by simpa [mem_support] using hne)
    exact (not_lt_of_ge hs.2.le) hu
  have hder := hz.deriv_eq
  rw [paperLowOscillatoryKernel_deriv hlam B ht0] at hder
  simpa using hder

theorem paperLowOscillatoryKernelDerivative_norm_le_abs_lam
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht0 : t ≠ 0) :
    ‖paperLowOscillatoryKernelDerivative lam hlam B t‖ ≤
      lowKernelDerivativeConstant * |lam| := by
  by_cases hsmall : |t| * Real.sqrt |lam| < 1 / 8
  · rw [paperLowOscillatoryKernelDerivative_eq_zero_of_normalized_lt hlam B ht0 hsmall,
      norm_zero]
    exact mul_nonneg lowKernelDerivativeConstant_nonneg (abs_nonneg _)
  have hlow : 1 / 8 ≤ |t| * Real.sqrt |lam| := le_of_not_gt hsmall
  have hT : 0 < |t| := abs_pos.mpr ht0
  have hS : 0 < Real.sqrt |lam| := Real.sqrt_pos.2 (abs_pos.mpr hlam)
  have hSsq : (Real.sqrt |lam|) ^ 2 = |lam| := Real.sq_sqrt (abs_nonneg _)
  have hP : (1 : ℝ) ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have hao := lowOuterScale_le_sqrt_abs_div_pow hlam B
  have hai := lowInnerScale_le_two_sqrt_abs hlam
  have hao' : lowOuterScale lam hlam B ≤ Real.sqrt |lam| := by
    exact hao.trans (div_le_self hS.le hP)
  have hscales : lowOuterScale lam hlam B + lowInnerScale lam hlam ≤
      3 * Real.sqrt |lam| := by linarith
  have hlow_sq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 8) hlow
  have hone : 1 ≤ 64 * |lam| * |t| ^ 2 := by
    nlinarith [hSsq]
  have hscaleT :
      (lowOuterScale lam hlam B + lowInnerScale lam hlam) * |t| ≤
        24 * |lam| * |t| ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hscales hT.le
    have h₂ := mul_le_mul_of_nonneg_right hlow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (mul_nonneg hS.le hT.le))
    nlinarith [hSsq]
  have hraw := paperLowOscillatoryKernelDerivative_norm_le_raw hlam B ht0
  refine hraw.trans ?_
  have hC := dyadicCutoffDerivBound_nonneg
  have hpi := Real.pi_pos.le
  have hscaleC := mul_le_mul_of_nonneg_left hscaleT hC
  unfold lowKernelDerivativeConstant
  refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hT)
  field_simp [abs_ne_zero.mpr ht0]
  nlinarith [mul_nonneg (abs_nonneg lam) (sq_nonneg |t|)]

theorem paperLowOscillatoryKernelDerivative_norm_le_pow_div
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht0 : t ≠ 0) :
    ‖paperLowOscillatoryKernelDerivative lam hlam B t‖ ≤
      lowKernelDerivativeConstant * ((2 : ℝ) ^ (2 * B) / |t| ^ 2) := by
  by_cases hlarge : (2 : ℝ) ^ B < |t| * Real.sqrt |lam|
  · rw [paperLowOscillatoryKernelDerivative_eq_zero_of_normalized_gt hlam B ht0 hlarge,
      norm_zero]
    exact mul_nonneg lowKernelDerivativeConstant_nonneg
      (div_nonneg (by positivity) (sq_nonneg _))
  have hupper : |t| * Real.sqrt |lam| ≤ (2 : ℝ) ^ B := le_of_not_gt hlarge
  have hT : 0 < |t| := abs_pos.mpr ht0
  have hS : 0 < Real.sqrt |lam| := Real.sqrt_pos.2 (abs_pos.mpr hlam)
  have hSsq : (Real.sqrt |lam|) ^ 2 = |lam| := Real.sq_sqrt (abs_nonneg _)
  let P : ℝ := (2 : ℝ) ^ B
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hao := lowOuterScale_le_sqrt_abs_div_pow hlam B
  have hai := lowInnerScale_le_two_sqrt_abs hlam
  have haoP : lowOuterScale lam hlam B * P ≤ Real.sqrt |lam| := by
    exact (le_div_iff₀ hPpos).mp (by simpa [P] using hao)
  have haoT : lowOuterScale lam hlam B * |t| ≤ 1 := by
    have h₁ := mul_le_mul_of_nonneg_right haoP hT.le
    have h₂ : lowOuterScale lam hlam B * |t| ≤
        lowOuterScale lam hlam B * P * |t| := by
      have hao0 := (lowOuterScale_pos hlam B).le
      nlinarith [mul_nonneg hao0 hT.le]
    nlinarith
  have haiT : lowInnerScale lam hlam * |t| ≤ 2 * P := by
    have := mul_le_mul_of_nonneg_right hai hT.le
    dsimp [P]
    nlinarith
  have hscaleT :
      (lowOuterScale lam hlam B + lowInnerScale lam hlam) * |t| ≤ 3 * P := by
    nlinarith
  have hupper_sq := mul_self_le_mul_self
    (mul_nonneg hT.le hS.le) (by simpa [P] using hupper)
  have hlamT : |lam| * |t| ^ 2 ≤ P ^ 2 := by
    nlinarith [hSsq]
  have hone : 1 ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 1)]
  have hraw := paperLowOscillatoryKernelDerivative_norm_le_raw hlam B ht0
  refine hraw.trans ?_
  have hC := dyadicCutoffDerivBound_nonneg
  have hpi := Real.pi_pos.le
  have hscaleC := mul_le_mul_of_nonneg_left hscaleT hC
  unfold lowKernelDerivativeConstant
  rw [show (2 : ℝ) ^ (2 * B) = P ^ 2 by
    dsimp [P]
    rw [show 2 * B = B + B by omega, pow_add]
    ring]
  refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hT)
  field_simp [abs_ne_zero.mpr ht0]
  nlinarith [mul_nonneg (abs_nonneg lam) (sq_nonneg |t|),
    mul_nonneg hC hPpos.le, mul_nonneg hpi hPpos.le]

/-- The precise Calderón--Zygmund derivative estimate asserted in the paper,
with a proved finite constant depending only on the fixed cutoff. -/
theorem paperLowOscillatoryKernelDerivative_norm_le_min
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht0 : t ≠ 0) :
    ‖paperLowOscillatoryKernelDerivative lam hlam B t‖ ≤
      lowKernelDerivativeConstant *
        min |lam| ((2 : ℝ) ^ (2 * B) / |t| ^ 2) := by
  rw [mul_min_of_nonneg _ _ lowKernelDerivativeConstant_nonneg]
  exact le_min
    (paperLowOscillatoryKernelDerivative_norm_le_abs_lam hlam B ht0)
    (paperLowOscillatoryKernelDerivative_norm_le_pow_div hlam B ht0)

theorem paperLowOscillatoryKernel_deriv_norm_le_min
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht0 : t ≠ 0) :
    ‖deriv (paperLowOscillatoryKernel lam hlam B) t‖ ≤
      lowKernelDerivativeConstant *
        min |lam| ((2 : ℝ) ^ (2 * B) / |t| ^ 2) := by
  rw [paperLowOscillatoryKernel_deriv hlam B ht0]
  exact paperLowOscillatoryKernelDerivative_norm_le_min hlam B ht0

end QuadraticCarleson
