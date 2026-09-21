/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison
import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicAtomScales
import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicKernelInfinite
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteRadiusAdapter
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftAction

/-!
# From sharp truncations to the smooth Krause--Lacey pieces

The Krause--Lacey stopping argument is naturally formulated for smooth dyadic
pieces, whereas the paper ultimately needs a maximum of sharp truncations.
This file proves the deterministic part of that passage.

Every positive radius is rounded upward to a dyadic radius lying between
`ε` and `2ε`. The resulting annular error is bounded by eight copies of the
centered Hardy--Littlewood maximal function. At the rounded radius, the
sharp tail is then decomposed exactly into a smooth high-pass cutoff and the
already-controlled cutoff boundary error. Thus the complete loss in the
two deterministic replacements is sixteen copies of the maximal function.

What is *not* asserted here is the analytic Krause--Lacey sparse estimate for
the smooth high-pass maximum. That is precisely the remaining oscillatory
input, rather than an assumption hidden in this adapter.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceySharpSmoothAdapter

open KrauseLaceyFiniteRadiusAdapter
open QuadraticHilbertMaximalMeasurable


noncomputable
section

/-- The half-open dyadic scale immediately below a positive radius. -/
def dyadicFloorScale (ε : ℝ) (hε : 0 < ε) : ℤ :=
  dyadicAtomScaleIndex (fun _ : Unit ↦ ε) (fun _ ↦ hε) ()

/-- Upward dyadic rounding of a positive radius. -/
def dyadicCeilRadius (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (2 : ℝ) ^ (dyadicFloorScale ε hε + 1)

theorem dyadicFloorScale_bounds (ε : ℝ) (hε : 0 < ε) :
    (2 : ℝ) ^ dyadicFloorScale ε hε ≤ ε ∧
      ε < (2 : ℝ) ^ (dyadicFloorScale ε hε + 1) := by
  exact dyadicAtomScaleIndex_mem (fun _ : Unit ↦ ε) (fun _ ↦ hε) ()

theorem dyadicCeilRadius_pos (ε : ℝ) (hε : 0 < ε) :
    0 < dyadicCeilRadius ε hε :=
  zpow_pos (by norm_num) _

theorem lt_dyadicCeilRadius (ε : ℝ) (hε : 0 < ε) :
    ε < dyadicCeilRadius ε hε :=
  (dyadicFloorScale_bounds ε hε).2

theorem dyadicCeilRadius_le_two_mul (ε : ℝ) (hε : 0 < ε) :
    dyadicCeilRadius ε hε ≤ 2 * ε := by
  rw [dyadicCeilRadius, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  nlinarith [dyadicFloorScale_bounds ε hε |>.1]

/-- The rounded radius has exactly the `2^(j-3)` form used by the project's
smooth dyadic-kernel normalization. -/
theorem dyadicCeilRadius_eq_two_pow_scale_sub_three (ε : ℝ) (hε : 0 < ε) :
    dyadicCeilRadius ε hε =
      (2 : ℝ) ^ ((dyadicFloorScale ε hε + 4) - 3) := by
  have h : (dyadicFloorScale ε hε + 4) - 3 =
      dyadicFloorScale ε hε + 1 := by ring
  rw [dyadicCeilRadius, h]

/-- Kernel of the annulus removed when `ε` is rounded upward to `ρ`. -/
def radiusRoundingBoundaryKernel (lam ε ρ t : ℝ) : ℂ :=
  sharpQuadraticTailKernel lam ε t - sharpQuadraticTailKernel lam ρ t

theorem measurable_radiusRoundingBoundaryKernel (lam ε ρ : ℝ) :
    Measurable (radiusRoundingBoundaryKernel lam ε ρ) :=
  (measurable_sharpQuadraticTailKernel lam ε).sub
    (measurable_sharpQuadraticTailKernel lam ρ)

theorem radiusRoundingBoundaryKernel_eq_zero_of_abs_le
    (lam : ℝ) {ε ρ t : ℝ} (hερ : ε ≤ ρ) (ht : |t| ≤ ε) :
    radiusRoundingBoundaryKernel lam ε ρ t = 0 := by
  simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel,
    not_lt.mpr ht, not_lt.mpr (ht.trans hερ)]

theorem radiusRoundingBoundaryKernel_eq_zero_of_rho_lt_abs
    (lam : ℝ) {ε ρ t : ℝ} (hερ : ε ≤ ρ) (ht : ρ < |t|) :
    radiusRoundingBoundaryKernel lam ε ρ t = 0 := by
  have hεt : ε < |t| := lt_of_le_of_lt hερ ht
  simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel, hεt, ht]

theorem radiusRoundingBoundaryKernel_norm_le
    (lam : ℝ) {ε ρ t : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) :
    ‖radiusRoundingBoundaryKernel lam ε ρ t‖ ≤ 1 / ε := by
  by_cases hεt : ε < |t|
  · by_cases hρt : ρ < |t|
    · simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel, hεt, hρt,
        hε.le]
    · simp only [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel,
        ite_eq_left hεt, ite_eq_right hρt, sub_zero, norm_div, norm_phase,
        Complex.norm_real, Real.norm_eq_abs]
      exact one_div_le_one_div_of_le hε hεt.le
  · have htε : |t| ≤ ε := le_of_not_gt hεt
    rw [radiusRoundingBoundaryKernel_eq_zero_of_abs_le lam hερ htε]
    simpa using one_div_nonneg.mpr hε.le

theorem radiusRoundingBoundaryKernel_support_subset
    (lam : ℝ) {ε ρ : ℝ} (hερ : ε ≤ ρ) :
    support (radiusRoundingBoundaryKernel lam ε ρ) ⊆ closedBall 0 ρ := by
  intro t ht
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra h
  exact ht (radiusRoundingBoundaryKernel_eq_zero_of_rho_lt_abs lam hερ (lt_of_not_ge h))

private theorem integrable_kernel_mul
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : Measurable k) (hbound : ∀ t, ‖k t‖ ≤ C) :
    Integrable (fun y ↦ k (x - y) * f y) := by
  apply hfi.bdd_mul
  · exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y ↦ hbound (x - y))

/-- Exact operator identity for upward radius rounding. -/
theorem quadraticHilbertTrunc_sub_rounded_eq_boundary
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x - quadraticHilbertTrunc lam ρ f x =
      ∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y := by
  have hεi : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ε (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_sharpQuadraticTailKernel lam ε)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hε)
  have hρi : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_sharpQuadraticTailKernel lam ρ)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hρ)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    ← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    quadraticHilbertConvolutionTrunc, quadraticHilbertConvolutionTrunc,
    ← integral_sub hεi hρi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    simp only [ radiusRoundingBoundaryKernel, sub_mul])

/-- Rounding a truncation radius upward by at most a factor two costs at
most eight copies of the centered Hardy--Littlewood maximal function. -/
theorem radiusRoundingBoundaryOperator_enorm_le_maximal
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρε : ρ ≤ 2 * ε)
    (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) :
    ‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hρ : 0 < ρ := hε.trans_le hερ
  calc
    ‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in closedBall x (2 * ε),
          ENNReal.ofReal (1 / ε) * ‖f y‖ₑ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall x (2 * ε)
      · simp only [indicator_of_mem hy, enorm_mul]
        apply mul_le_mul'
        · simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
            (radiusRoundingBoundaryKernel_norm_le lam hε hερ)
        · exact le_rfl
      · simp only [indicator, hy, ↓reduceIte]
        have hk : radiusRoundingBoundaryKernel lam ε ρ (x - y) = 0 := by
          apply notMem_support.mp
          intro hmem
          apply hy
          have hs := radiusRoundingBoundaryKernel_support_subset lam hερ hmem
          have hxyρ : |x - y| ≤ ρ := by
            simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hs
          simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hxyρ.trans hρε
        simp [hk]
    _ = 4 * centeredAverage (2 * ε) (fun y ↦ ‖f y‖ₑ) x := by
      rw [MeasureTheory.lintegral_const_mul _ hf.enorm]
      unfold centeredAverage
      have hε0 : ε ≠ 0 := ne_of_gt hε
      rw [show ENNReal.ofReal (1 / ε) =
          4 / ENNReal.ofReal (2 * (2 * ε)) by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp; ring]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ 8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      have h := centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
        (mul_pos (by norm_num : (0 : ℝ) < 2) hε) (fun y ↦ ‖f y‖ₑ) x
      calc
        4 * centeredAverage (2 * ε) (fun y ↦ ‖f y‖ₑ) x ≤
            4 * (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :=
          mul_le_mul' le_rfl h
        _ = _ := by rw [← mul_assoc]; norm_num

/-- Pointwise truncation estimate after dyadic rounding. -/
theorem quadraticHilbertTrunc_enorm_le_dyadicRounded_add_maximal
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ε f x‖ₑ ≤
      ‖quadraticHilbertTrunc lam (dyadicCeilRadius ε hε) f x‖ₑ +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let ρ := dyadicCeilRadius ε hε
  have hρ : 0 < ρ := dyadicCeilRadius_pos ε hε
  have hερ : ε ≤ ρ := (lt_dyadicCeilRadius ε hε).le
  have hρε : ρ ≤ 2 * ε := dyadicCeilRadius_le_two_mul ε hε
  have hid := quadraticHilbertTrunc_sub_rounded_eq_boundary lam hε hρ hfi x
  have hb := radiusRoundingBoundaryOperator_enorm_le_maximal lam hε hερ hρε f hf x
  calc
    ‖quadraticHilbertTrunc lam ε f x‖ₑ =
        ‖quadraticHilbertTrunc lam ρ f x +
          ∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ := by
      congr 1
      linear_combination hid
    _ ≤ ‖quadraticHilbertTrunc lam ρ f x‖ₑ +
          ‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ :=
      enorm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hb

/-- Smooth high-pass truncation kernel at radius `ρ`. For dyadic `ρ` this
is the infinite smooth tail whose scale-localized pieces enter KL18. -/
def smoothQuadraticHighPassKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    ((((1 - dyadicCutoff (t / (4 * ρ))) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2))

theorem dyadicHighPass_cutoff_argument (j : ℤ) (t : ℝ) :
    t / (4 * (2 : ℝ) ^ (j - 3)) = (2⁻¹ : ℝ) ^ (j - 1) * t := by
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [inv_zpow]
  field_simp [zpow_ne_zero]
  have hz : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1) * 2 := by
    rw [show j = (j - 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hz]
  ring

/-- At a dyadic radius, the smooth high-pass kernel is exactly the infinite
sum of the genuine dyadic quadratic kernels entering the KL stopping
recursion. Pointwise the sum has finite support, by
`hasFiniteSupport_dyadicPsi_add_nat`. -/
theorem smoothQuadraticHighPassKernel_two_pow_eq_tsum
    (lam : ℝ) (j : ℤ) (t : ℝ) :
    smoothQuadraticHighPassKernel lam ((2 : ℝ) ^ (j - 3)) t =
      ∑' r : ℕ, (dyadicPsi (j + (r : ℤ)) t : ℂ) * phase (lam * t ^ 2) := by
  by_cases ht : t = 0
  · subst t
    simp [smoothQuadraticHighPassKernel, dyadicPsi_zero]
  · have hr := hasSum_dyadicPsi_add_nat j ht
    have hc : HasSum
        (fun r : ℕ ↦ (dyadicPsi (j + (r : ℤ)) t : ℂ))
        (((1 - dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)) / t : ℝ) : ℂ) :=
      Complex.hasSum_ofReal.mpr hr
    have hm := hc.mul_right (phase (lam * t ^ 2))
    rw [hm.tsum_eq]
    rw [smoothQuadraticHighPassKernel, ite_eq_right ht,
      dyadicHighPass_cutoff_argument]

/-- Rounded-radius version of the exact dyadic-tail identity. -/
theorem smoothQuadraticHighPassKernel_rounded_eq_tsum
    (lam : ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    smoothQuadraticHighPassKernel lam (dyadicCeilRadius ε hε) t =
      ∑' r : ℕ,
        (dyadicPsi (dyadicFloorScale ε hε + 4 + (r : ℤ)) t : ℂ) *
          phase (lam * t ^ 2) := by
  rw [dyadicCeilRadius_eq_two_pow_scale_sub_three]
  exact smoothQuadraticHighPassKernel_two_pow_eq_tsum
    lam (dyadicFloorScale ε hε + 4) t

theorem hasSum_dyadicQuadraticKernel_add_nat
    (lam : ℝ) (j : ℤ) (t : ℝ) :
    HasSum (fun r : ℕ ↦
        (dyadicPsi (j + (r : ℤ)) t : ℂ) * phase (lam * t ^ 2))
      (smoothQuadraticHighPassKernel lam ((2 : ℝ) ^ (j - 3)) t) := by
  rw [smoothQuadraticHighPassKernel_two_pow_eq_tsum]
  exact ((Complex.summable_ofReal.mpr
    (summable_dyadicPsi_add_nat j t)).mul_right _).hasSum

/-- Exact algebra: sharp tail equals smooth high pass plus its compact
transition-boundary kernel. -/
theorem sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary
    (lam ρ t : ℝ) :
    sharpQuadraticTailKernel lam ρ t =
      smoothQuadraticHighPassKernel lam ρ t + cutoffBoundaryKernel lam ρ t := by
  by_cases ht0 : t = 0
  · simp [ht0, sharpQuadraticTailKernel, smoothQuadraticHighPassKernel,
      cutoffBoundaryKernel]
  · rw [smoothQuadraticHighPassKernel, cutoffBoundaryKernel, ite_eq_right ht0, ite_eq_right ht0]
    by_cases ht : ρ < |t|
    · have hnot : ¬ |t| ≤ ρ := not_le.mpr ht
      rw [sharpQuadraticTailKernel, ite_eq_left ht, ite_eq_right hnot]
      push_cast
      field_simp; ring
    · have hle : |t| ≤ ρ := le_of_not_gt ht
      rw [sharpQuadraticTailKernel, ite_eq_right ht, ite_eq_left hle]
      push_cast
      field_simp; ring

/-- Smooth high-pass convolution operator. -/
def smoothQuadraticHighPass
    (lam ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, smoothQuadraticHighPassKernel lam ρ (x - y) * f y

/-- A fixed smooth high pass in the project's test-operator type. -/
def smoothQuadraticHighPassTestOperator (lam ρ : ℝ) : TestOperator :=
  fun f x ↦ smoothQuadraticHighPass lam ρ f x

theorem measurable_smoothQuadraticHighPassKernel (lam ρ : ℝ) :
    Measurable (smoothQuadraticHighPassKernel lam ρ) := by
  have hnum : Measurable (fun t : ℝ ↦ 1 - dyadicCutoff (t / (4 * ρ))) :=
    measurable_const.sub (dyadicCutoff_smooth.continuous.measurable.comp
      (measurable_id.div_const (4 * ρ)))
  have hp : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · exact (Complex.measurable_ofReal.comp (hnum.div measurable_id)).mul hp

theorem smoothQuadraticHighPassKernel_norm_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) :
    ‖smoothQuadraticHighPassKernel lam ρ t‖ ≤ 2 / ρ := by
  have hs := sharpQuadraticTailKernel_norm_le lam (t := t) hρ
  have hb := cutoffBoundaryKernel_norm_le lam (t := t) hρ
  have heq := sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary lam ρ t
  have heq' : smoothQuadraticHighPassKernel lam ρ t =
      sharpQuadraticTailKernel lam ρ t - cutoffBoundaryKernel lam ρ t := by
    exact eq_sub_iff_add_eq.mpr heq.symm
  calc
    ‖smoothQuadraticHighPassKernel lam ρ t‖ =
        ‖sharpQuadraticTailKernel lam ρ t - cutoffBoundaryKernel lam ρ t‖ := by rw [heq']
    _ ≤
        ‖sharpQuadraticTailKernel lam ρ t‖ +
          ‖cutoffBoundaryKernel lam ρ t‖ := norm_sub_le _ _
    _ ≤ 1 / ρ + 1 / ρ := add_le_add hs hb
    _ = 2 / ρ := by ring

theorem smoothQuadraticHighPass_add
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (f g : L0Infinity) (x : ℝ) :
    smoothQuadraticHighPass lam ρ (L0Infinity.add f g) x =
      smoothQuadraticHighPass lam ρ f x + smoothQuadraticHighPass lam ρ g x := by
  have hf : Integrable
      (fun y ↦ smoothQuadraticHighPassKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul f.integrable x
      (measurable_smoothQuadraticHighPassKernel lam ρ)
      (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam (t := t) hρ)
  have hg : Integrable
      (fun y ↦ smoothQuadraticHighPassKernel lam ρ (x - y) * g y) :=
    integrable_kernel_mul g.integrable x
      (measurable_smoothQuadraticHighPassKernel lam ρ)
      (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam (t := t) hρ)
  rw [smoothQuadraticHighPass, smoothQuadraticHighPass,
    smoothQuadraticHighPass, ← integral_add hf hg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    change smoothQuadraticHighPassKernel lam ρ (x - y) * (f y + g y) = _
    ring)

theorem smoothQuadraticHighPass_smul
    (lam : ℝ) {ρ : ℝ} (_hρ : 0 < ρ) (c : ℂ) (f : L0Infinity) (x : ℝ) :
    smoothQuadraticHighPass lam ρ (L0Infinity.smul c f) x =
      c * smoothQuadraticHighPass lam ρ f x := by
  rw [smoothQuadraticHighPass, smoothQuadraticHighPass, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    change smoothQuadraticHighPassKernel lam ρ (x - y) * (c * f y) =
      c * (smoothQuadraticHighPassKernel lam ρ (x - y) * f y)
    ring)

theorem smoothQuadraticHighPassTestOperator_isSublinear
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsSublinear (smoothQuadraticHighPassTestOperator lam ρ) := by
  constructor
  · intro f g x
    rw [smoothQuadraticHighPassTestOperator, smoothQuadraticHighPass_add lam hρ]
    exact norm_add_le _ _
  · intro c f x
    rw [smoothQuadraticHighPassTestOperator, smoothQuadraticHighPass_smul lam hρ,
      norm_mul]
    rfl

theorem dyadicQuadraticKernel_norm_le_scale
    (lam : ℝ) (j : ℤ) (t : ℝ) :
    ‖(dyadicPsi j t : ℂ) * phase (lam * t ^ 2)‖ ≤
      2 / (2 : ℝ) ^ (j - 3) := by
  by_cases hz : dyadicPsi j t = 0
  · rw [hz]
    simp only [Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · have ht : t ≠ 0 := by
      intro ht
      subst t
      exact hz (dyadicPsi_zero j)
    have hs := dyadicPsi_support_subset j hz
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real]
    calc
      ‖dyadicPsi j t‖ ≤ 2 / |t| := norm_dyadicPsi_le j ht
      _ ≤ 2 / (2 : ℝ) ^ (j - 3) := by
        exact div_le_div_of_nonneg_left (by norm_num) (zpow_pos (by norm_num) _)
          hs.1.le

theorem measurable_dyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    Measurable (fun t : ℝ ↦
      (dyadicPsi j t : ℂ) * phase (lam * t ^ 2)) := by
  have hp : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  exact (Complex.measurable_ofReal.comp (dyadicPsi_smooth j).continuous.measurable).mul hp

theorem exists_eventually_zero_dyadicTail_integrands
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ y : ℝ,
      ((dyadicPsi (j + (r : ℤ)) (x - y) : ℂ) *
        phase (lam * (x - y) ^ 2)) * f y = 0 := by
  obtain ⟨S, _, hS⟩ := f.hasCompactSupport_toFun.isBounded.exists_pos_norm_le
  let M : ℝ := |x| + S
  have hM : ∀ y : ℝ, f y ≠ 0 → |x - y| ≤ M := by
    intro y hy
    have hb : |y| ≤ S := by
      simpa only [Real.norm_eq_abs] using hS y (subset_tsupport f hy)
    exact (abs_sub x y).trans (add_le_add le_rfl hb)
  have hp : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ r) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc : 0 < (2 : ℝ) ^ (j - 3) := zpow_pos (by norm_num) _
  have hscale : Tendsto
      (fun r : ℕ ↦ (2 : ℝ) ^ (j + (r : ℤ) - 3))
      Filter.atTop Filter.atTop := by
    convert hp.const_mul_atTop hc using 1
    funext r
    rw [show j + (r : ℤ) - 3 = (j - 3) + (r : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hscale.eventually_gt_atTop M)
  refine ⟨N, ?_⟩
  intro r hr y
  by_cases hy : f y = 0
  · simp [hy]
  · have hz : dyadicPsi (j + (r : ℤ)) (x - y) = 0 :=
      dyadicPsi_eq_zero_of_abs_le ((hM y hy).trans (hN r hr).le)
    simp [hz]

/-- Operator-level completion of the kernel telescoping bridge. For a test
input, compact support makes the sequence of integral summands eventually
zero, so no unproved dominated-convergence premise is hidden here. -/
theorem hasSum_dyadicQuadraticConvolutions_add_nat
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    HasSum (fun r : ℕ ↦ ∫ y,
        ((dyadicPsi (j + (r : ℤ)) (x - y) : ℂ) *
          phase (lam * (x - y) ^ 2)) * f y)
      (smoothQuadraticHighPass lam ((2 : ℝ) ^ (j - 3)) f x) := by
  let F (r : ℕ) (y : ℝ) : ℂ :=
    ((dyadicPsi (j + (r : ℤ)) (x - y) : ℂ) *
      phase (lam * (x - y) ^ 2)) * f y
  have hI (r : ℕ) : Integrable (F r) := by
    apply integrable_kernel_mul f.integrable x
      (measurable_dyadicQuadraticKernel lam (j + (r : ℤ)))
    exact dyadicQuadraticKernel_norm_le_scale lam (j + (r : ℤ))
  obtain ⟨N, hN⟩ := exists_eventually_zero_dyadicTail_integrands lam j f x
  have hn : HasFiniteSupport (fun r : ℕ ↦ ∫ y, ‖F r y‖) := by
    apply (Finset.finite_toSet (Finset.range N)).subset
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hr
    have hz : ∀ y, F r y = 0 := hN r (Nat.le_of_not_gt h)
    simp [hz]
  have hs := hasSum_integral_of_summable_integral_norm hI
    (summable_of_hasFiniteSupport hn)
  have hpoint (y : ℝ) : (∑' r : ℕ, F r y) =
      smoothQuadraticHighPassKernel lam ((2 : ℝ) ^ (j - 3)) (x - y) * f y :=
    ((hasSum_dyadicQuadraticKernel_add_nat lam j (x - y)).mul_right (f y)).tsum_eq
  simp_rw [hpoint] at hs
  exact hs

/-- Every finite positive-half dyadic tail is exactly a sum of three genuine
localized KL tail actions on finite multiscale families. This composes the
three-shift localization with the scale ordering used by the high-pass
series; it is the finite-tree exhaustion bridge needed before invoking the
stopping recursion. -/
theorem exists_threeShift_localizedTailActions_eq_positivePartialSum
    (f : L0Infinity) (j : ℤ) (n : ℕ) :
    ∃ E : ℕ → Finset ℤ, ∀ x : ℝ,
      (∑ shift : Fin 3,
        KrauseLaceyStoppingRecursion.localizedTailAction
          (KrauseLaceyThreeShiftGrid.finiteShiftGridScale
            (j + (n : ℤ) - 1) shift)
          (KrauseLaceyThreeShiftGrid.finiteOneShiftMultiscaleFamily
            (j + (n : ℤ) - 1) (Finset.range n) E shift)
          f j x) =
      ∑ r ∈ Finset.range n, ∫ t,
        annularQuadraticKernel (positiveDyadicAmplitude (j + (r : ℤ))) 1
          (x - t) * f t := by
  obtain ⟨E, hE⟩ :=
    KrauseLaceyThreeShiftGrid.exists_finiteThreeShiftFamily_localization_all_depths
      f (j + (n : ℤ) - 1)
  refine ⟨E, fun x ↦ ?_⟩
  rw [KrauseLaceyThreeShiftGrid.sum_localizedTailAction_eq_finite_globalTail
    f (j + (n : ℤ) - 1) j (Finset.range n) E
    (fun depth _ ↦ (hE depth).2.2) x]
  have hcut : ∀ depth ∈ Finset.range n,
      (2 : ℝ) ^ j ≤
        (2 : ℝ) ^ (j + (n : ℤ) - 1 - (depth : ℤ) + 2) := by
    intro depth hdepth
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2
    have hd : depth < n := Finset.mem_range.mp hdepth
    omega
  calc
    (∑ depth ∈ Finset.range n,
        if (2 : ℝ) ^ j ≤
            (2 : ℝ) ^ (j + (n : ℤ) - 1 - (depth : ℤ) + 2) then
          ∫ t, annularQuadraticKernel
            (positiveDyadicAmplitude (j + (n : ℤ) - 1 - (depth : ℤ))) 1
              (x - t) * f t
        else 0) =
        ∑ depth ∈ Finset.range n, ∫ t, annularQuadraticKernel
          (positiveDyadicAmplitude (j + (n : ℤ) - 1 - (depth : ℤ))) 1
            (x - t) * f t := by
      apply Finset.sum_congr rfl
      intro depth hdepth
      rw [ite_eq_left (hcut depth hdepth)]
    _ = ∑ r ∈ Finset.range n, ∫ t,
        annularQuadraticKernel (positiveDyadicAmplitude (j + (r : ℤ))) 1
          (x - t) * f t := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro depth hdepth
      have hd : depth < n := Finset.mem_range.mp hdepth
      have hdle : depth ≤ n - 1 := Nat.le_sub_one_of_lt hd
      have hnpos : 0 < n := (Nat.zero_le depth).trans_lt hd
      have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        omega
      have hscale :
          j + (n : ℤ) - 1 - (((n - 1 : ℕ) : ℤ) - (depth : ℤ)) =
            j + (depth : ℤ) := by
        rw [hncast]
        ring
      have hrevcast : ((n - 1 - depth : ℕ) : ℤ) =
          ((n - 1 : ℕ) : ℤ) - (depth : ℤ) := by
        omega
      rw [hrevcast, hscale]

/-- Exact operator decomposition at one sharp radius. -/
theorem quadraticHilbertTrunc_eq_smoothHighPass_add_boundary
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℂ}
    (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc lam ρ f x = smoothQuadraticHighPass lam ρ f x +
      ∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y := by
  have hsmooth : Integrable
      (fun y ↦ smoothQuadraticHighPassKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_smoothQuadraticHighPassKernel lam ρ)
      (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam (t := t) hρ)
  have hboundary : Integrable
      (fun y ↦ cutoffBoundaryKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_cutoffBoundaryKernel lam ρ)
      (fun t ↦ cutoffBoundaryKernel_norm_le lam (t := t) hρ)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    quadraticHilbertConvolutionTrunc, smoothQuadraticHighPass, ← integral_add hsmooth hboundary]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [← add_mul, ← sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary])

/-- A sharp truncation is controlled by the corresponding smooth high-pass
operator plus eight copies of the centered maximal function. -/
theorem quadraticHilbertTrunc_enorm_le_smoothHighPass_add_maximal
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ρ f x‖ₑ ≤
      ‖smoothQuadraticHighPass lam ρ f x‖ₑ +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hρ hfi]
  exact (enorm_add_le _ _).trans (add_le_add le_rfl
    (cutoffBoundaryOperator_enorm_le_maximal lam hρ f hf x))

/-- The complete deterministic sharp-to-smooth comparison. Its constant
`16` is the sum of the radius-rounding and cutoff-boundary costs. -/
theorem quadraticHilbertTrunc_enorm_le_dyadicSmoothHighPass_add_maximal
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ε f x‖ₑ ≤
      ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε hε) f x‖ₑ +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hround := quadraticHilbertTrunc_enorm_le_dyadicRounded_add_maximal
    lam hε hf hfi x
  have hsmooth := quadraticHilbertTrunc_enorm_le_smoothHighPass_add_maximal
    lam (dyadicCeilRadius_pos ε hε) hf hfi x
  calc
    ‖quadraticHilbertTrunc lam ε f x‖ₑ ≤
        ‖quadraticHilbertTrunc lam (dyadicCeilRadius ε hε) f x‖ₑ +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := hround
    _ ≤ (‖smoothQuadraticHighPass lam (dyadicCeilRadius ε hε) f x‖ₑ +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      add_le_add hsmooth le_rfl
    _ = _ := by ring

/-- Finite maximum of the smooth high-pass operators at the dyadic radii
obtained by rounding the selected sharp radii. -/
def finiteRadiusSmoothHighPassMaxNNNorm
    (lam : ℝ) (s : Finset densePositiveRadii)
    (f : L0Infinity) (x : ℝ) : NNReal :=
  s.sup fun ε ↦
    ‖smoothQuadraticHighPass lam
      (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊

/-- Complex-valued test-operator packaging of the preceding finite smooth
maximum, parallel to `finiteRadiusQuadraticHilbertMaxTestOperator`. -/
def finiteRadiusSmoothHighPassMaxTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) : TestOperator :=
  fun f x ↦ ((finiteRadiusSmoothHighPassMaxNNNorm lam s f x : ℝ) : ℂ)

@[simp] theorem norm_finiteRadiusSmoothHighPassMaxTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ =
      finiteRadiusSmoothHighPassMaxNNNorm lam s f x := by
  rw [finiteRadiusSmoothHighPassMaxTestOperator, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  exact NNReal.coe_nonneg _

/-- A fixed positive sharp truncation is bounded everywhere by its kernel
supremum times the input mass. -/
theorem quadraticHilbertTrunc_norm_le_inv_radius_mul_integral
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (f : L0Infinity) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ε f x‖ ≤ (1 / ε) * ∫ y, ‖f y‖ := by
  have hi : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ε (x - y) * f y) :=
    integrable_kernel_mul f.integrable x
      (measurable_sharpQuadraticTailKernel lam ε)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hε)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    quadraticHilbertConvolutionTrunc]
  calc
    ‖∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y‖ ≤
        ∫ y, ‖sharpQuadraticTailKernel lam ε (x - y) * f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, (1 / ε) * ‖f y‖ := by
      apply integral_mono hi.norm (f.integrable.norm.const_mul (1 / ε))
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (sharpQuadraticTailKernel_norm_le lam (t := x - y) hε) (norm_nonneg _)
    _ = (1 / ε) * ∫ y, ‖f y‖ := integral_const_mul _ _

/-- The local-integrability clause in
`HasUniformFiniteRadiusQuadraticSparseBound` is elementary and does not
belong to the oscillatory KL input. -/
theorem finiteRadiusQuadraticHilbertMaxTestOperator_locallyIntegrable
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) :
    LocallyIntegrable (finiteRadiusQuadraticHilbertMaxTestOperator lam s f) volume := by
  classical
  have hmeasReal : Measurable (fun x : ℝ ↦
      (finiteRadiusQuadraticHilbertMaxNNNorm lam s f x : ℝ)) := by
    unfold finiteRadiusQuadraticHilbertMaxNNNorm
    induction s using Finset.induction_on with
    | empty => simp
    | @insert ε s hε ih =>
        simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm]
        exact (measurable_quadraticHilbertTrunc lam ε.1.1 f.measurable_toFun).norm.max ih
  have hmeas : Measurable
      (finiteRadiusQuadraticHilbertMaxTestOperator lam s f) := by
    exact Complex.measurable_ofReal.comp hmeasReal
  rw [locallyIntegrable_iff]
  intro K hK
  let C : ℝ := ∑ ε ∈ s, (1 / ε.1.1) * ∫ y, ‖f y‖
  apply IntegrableOn.of_bound hK.measure_lt_top
    hmeas.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [norm_finiteRadiusQuadraticHilbertMaxTestOperator]
    change (↑(s.sup fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) : ℝ) ≤ C
    have hsup : (s.sup fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) ≤
        ∑ ε ∈ s, ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊ := by
      apply Finset.sup_le
      intro ε hεs
      exact Finset.single_le_sum
        (fun δ hδ ↦ (bot_le : (0 : NNReal) ≤
          ‖quadraticHilbertTrunc lam δ.1.1 f x‖₊)) hεs
    calc
      (↑(s.sup fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) : ℝ) ≤
          ∑ ε ∈ s, ‖quadraticHilbertTrunc lam ε.1.1 f x‖ := by
        have hcoe :
            (↑(s.sup fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) : ℝ) ≤
              ↑(∑ ε ∈ s, ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) :=
          NNReal.coe_le_coe.mpr hsup
        rw [NNReal.coe_sum] at hcoe
        simpa only [coe_nnnorm] using hcoe
      _ ≤ ∑ ε ∈ s, (1 / ε.1.1) * ∫ y, ‖f y‖ := by
        apply Finset.sum_le_sum
        intro ε hεs
        exact quadraticHilbertTrunc_norm_le_inv_radius_mul_integral
          lam ε.1.2 f x)

theorem finiteRadiusSmoothHighPassMaxNNNorm_add_le
    (lam : ℝ) (s : Finset densePositiveRadii) (f g : L0Infinity) (x : ℝ) :
    finiteRadiusSmoothHighPassMaxNNNorm lam s (L0Infinity.add f g) x ≤
      finiteRadiusSmoothHighPassMaxNNNorm lam s f x +
        finiteRadiusSmoothHighPassMaxNNNorm lam s g x := by
  classical
  unfold finiteRadiusSmoothHighPassMaxNNNorm
  apply Finset.sup_le
  intro ε hε
  calc
    ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2)
        (L0Infinity.add f g) x‖₊ =
        ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2) f x +
          smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2) g x‖₊ := by
      rw [smoothQuadraticHighPass_add lam (dyadicCeilRadius_pos ε.1.1 ε.1.2)]
    _ ≤ ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊ +
        ‖smoothQuadraticHighPass lam (dyadicCeilRadius ε.1.1 ε.1.2) g x‖₊ :=
      nnnorm_add_le _ _
    _ ≤ (s.sup fun δ ↦ ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius δ.1.1 δ.1.2) f x‖₊) +
        s.sup fun δ ↦ ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius δ.1.1 δ.1.2) g x‖₊ :=
      add_le_add (Finset.le_sup (s := s) (f := fun δ ↦
        ‖smoothQuadraticHighPass lam (dyadicCeilRadius δ.1.1 δ.1.2) f x‖₊) hε)
        (Finset.le_sup (s := s) (f := fun δ ↦
          ‖smoothQuadraticHighPass lam (dyadicCeilRadius δ.1.1 δ.1.2) g x‖₊) hε)

theorem finiteRadiusSmoothHighPassMaxNNNorm_smul
    (lam : ℝ) (s : Finset densePositiveRadii) (c : ℂ)
    (f : L0Infinity) (x : ℝ) :
    finiteRadiusSmoothHighPassMaxNNNorm lam s (L0Infinity.smul c f) x =
      ‖c‖₊ * finiteRadiusSmoothHighPassMaxNNNorm lam s f x := by
  classical
  unfold finiteRadiusSmoothHighPassMaxNNNorm
  calc
    (s.sup fun ε ↦ ‖smoothQuadraticHighPass lam
        (dyadicCeilRadius ε.1.1 ε.1.2) (L0Infinity.smul c f) x‖₊) =
        s.sup fun ε ↦ ‖c * smoothQuadraticHighPass lam
          (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊ := by
      apply Finset.sup_congr rfl
      intro ε _
      rw [smoothQuadraticHighPass_smul lam
        (dyadicCeilRadius_pos ε.1.1 ε.1.2)]
    _ = s.sup fun ε ↦ ‖c‖₊ * ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊ := by
      congr 1
      funext ε
      rw [nnnorm_mul]
    _ = ‖c‖₊ * (s.sup fun ε ↦ ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊) :=
      (NNReal.mul_finset_sup ‖c‖₊ s _).symm

theorem finiteRadiusSmoothHighPassMaxTestOperator_isSublinear
    (lam : ℝ) (s : Finset densePositiveRadii) :
    IsSublinear (finiteRadiusSmoothHighPassMaxTestOperator lam s) := by
  constructor
  · intro f g x
    simp only [norm_finiteRadiusSmoothHighPassMaxTestOperator]
    exact_mod_cast finiteRadiusSmoothHighPassMaxNNNorm_add_le lam s f g x
  · intro c f x
    simp only [norm_finiteRadiusSmoothHighPassMaxTestOperator]
    rw [finiteRadiusSmoothHighPassMaxNNNorm_smul]
    rfl

private theorem coe_nnreal_finset_sup {α : Type*}
    (s : Finset α) (u : α → NNReal) :
    (↑(s.sup u) : ℝ≥0∞) = s.sup fun a ↦ (u a : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sup_insert, ih]

/-- Finite-family form of the complete deterministic comparison. This is
the direct bridge needed after proving a sparse theorem for the genuine
smooth KL maximum: no cardinality-dependent loss appears. -/
theorem finiteRadiusSharpMax_enorm_le_smoothHighPassMax_add_maximal
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ENNReal.ofReal
        ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖ ≤
      ENNReal.ofReal
          ‖finiteRadiusSmoothHighPassMaxTestOperator lam s f x‖ +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  classical
  rw [norm_finiteRadiusQuadraticHilbertMaxTestOperator,
    norm_finiteRadiusSmoothHighPassMaxTestOperator,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  unfold finiteRadiusQuadraticHilbertMaxNNNorm finiteRadiusSmoothHighPassMaxNNNorm
  rw [coe_nnreal_finset_sup, coe_nnreal_finset_sup]
  apply Finset.sup_le
  intro ε hεs
  calc
    (↑‖quadraticHilbertTrunc lam ε.1.1 f x‖₊ : ℝ≥0∞) =
        ‖quadraticHilbertTrunc lam ε.1.1 f x‖ₑ := by
      simp [enorm_eq_nnnorm]
    _ ≤ ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius ε.1.1 ε.1.2) f x‖ₑ +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      quadraticHilbertTrunc_enorm_le_dyadicSmoothHighPass_add_maximal
        lam ε.1.2 f.measurable_toFun f.integrable x
    _ ≤ (s.sup fun δ ↦
          (↑‖smoothQuadraticHighPass lam
            (dyadicCeilRadius δ.1.1 δ.1.2) f x‖₊ : ℝ≥0∞)) +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      apply add_le_add
      · simpa [enorm_eq_nnnorm] using Finset.le_sup (s := s)
          (f := fun δ ↦ (↑‖smoothQuadraticHighPass lam
            (dyadicCeilRadius δ.1.1 δ.1.2) f x‖₊ : ℝ≥0∞)) hεs
      · exact le_rfl
    _ = _ := rfl


end
end KrauseLaceySharpSmoothAdapter
end QuadraticCarleson
