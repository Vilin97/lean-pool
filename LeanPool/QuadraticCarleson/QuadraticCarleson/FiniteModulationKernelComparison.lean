/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveDyadicKernel
public import LeanPool.QuadraticCarleson.QuadraticCarleson.IntervalMaximalComparison

/-!
# The finite low-modulation block versus maximal truncations

This is the elementary pointwise reduction at the start of the proof of the
finite-modulation weak-type corollary in the accompanying article
([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)). A
consecutive block of the paper's smooth dyadic kernels telescopes. Replacing
its two smooth cutoffs by sharp cutoffs produces the difference of two
quadratic Hilbert truncations; the two transition annuli are controlled by
the centered Hardy--Littlewood maximal function.

The later sparse input in the paper is [Krause--Lacey, Theorem 1.1], namely a
uniform sparse `(1,p)` estimate for the maximally truncated quadratic Hilbert
transform. Mathlib has no Carleson or oscillatory sparse-bound development,
and the project currently only defines the abstract sparse premise in
`FiniteSparseMaximal`. Accordingly, this file proves the concrete pointwise
comparison without postulating that external theorem.
-/

@[expose] public section

open Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson


/-- The maximally truncated quadratic Hilbert transform, with the supremum
taken over all positive real truncation radii as in the paper. -/
noncomputable def quadraticHilbertMaximalTruncation
    (lam : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ε : {ε : ℝ // 0 < ε}, ‖quadraticHilbertTrunc lam ε f x‖ₑ

/-- The kernel of one sharp quadratic Hilbert truncation. -/
noncomputable def sharpQuadraticTailKernel (lam ε t : ℝ) : ℂ :=
  if ε < |t| then phase (lam * t ^ 2) / (t : ℂ) else 0

/-- Convolution orientation of a sharp quadratic Hilbert truncation. -/
noncomputable def quadraticHilbertConvolutionTrunc
    (lam ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y

/-- The boundary error made when the smooth cutoff at radius `ρ` is replaced
by the sharp cutoff of the centered interval of radius `ρ`. -/
noncomputable def cutoffBoundaryKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    (((dyadicCutoff (t / (4 * ρ)) - if |t| ≤ ρ then 1 else 0) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2)

/-- The convolution operator associated with a consecutive block of dyadic
quadratic kernels. -/
noncomputable def finiteQuadraticDyadicBlock
    (lam : ℝ) (j : ℤ) (B : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, lowOscillatoryKernel lam B (fun r ↦ j + (r : ℤ)) (x - y) * f y

theorem L0Infinity.integrable (f : L0Infinity) : Integrable f := by
  have hcompact : IsCompact (tsupport f) := f.hasCompactSupport_toFun
  have hfinite : volume (tsupport f) < ∞ := hcompact.measure_lt_top
  rcases f.bounded_toFun with ⟨C, hC⟩
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  exact IntegrableOn.of_bound hfinite
    f.measurable_toFun.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall hC)

/-- An average at an arbitrary positive real radius is controlled by twice
the rational-radius maximal function used in the project. -/
theorem centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
    {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ≥0∞) (x : ℝ) :
    centeredAverage r g x ≤ 2 * centeredHardyLittlewoodMaximal g x := by
  obtain ⟨q0, hrq, hq2r⟩ := exists_rat_btwn (show r < 2 * r by linarith)
  let q : PositiveRational := ⟨q0, by exact_mod_cast hr.trans hrq⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have hsubset : closedBall x r ⊆ closedBall x (q : ℝ) :=
    closedBall_subset_closedBall hrq.le
  have hmass : (∫⁻ y in closedBall x r, g y) ≤
      ∫⁻ y in closedBall x (q : ℝ), g y := lintegral_mono_set hsubset
  have hrden : ENNReal.ofReal (2 * r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hqden : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hqtop : ENNReal.ofReal (2 * (q : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hden : ENNReal.ofReal (2 * (q : ℝ)) ≤ 2 * ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  unfold centeredAverage
  calc
    (∫⁻ y in closedBall x r, g y) / ENNReal.ofReal (2 * r) ≤
        (∫⁻ y in closedBall x (q : ℝ), g y) / ENNReal.ofReal (2 * r) :=
      ENNReal.div_le_div_right hmass _
    _ ≤ 2 * ((∫⁻ y in closedBall x (q : ℝ), g y) /
          ENNReal.ofReal (2 * (q : ℝ))) := by
      apply (ENNReal.div_le_iff hrden ENNReal.ofReal_ne_top).2
      calc
        (∫⁻ y in closedBall x (q : ℝ), g y) =
            ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                ENNReal.ofReal (2 * (q : ℝ)) := by
          exact (ENNReal.div_mul_cancel hqden hqtop).symm
        _ ≤ ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                (2 * ENNReal.ofReal (2 * r)) := mul_le_mul' le_rfl hden
        _ = 2 * ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) * ENNReal.ofReal (2 * r) := by
          ac_rfl
    _ ≤ 2 * centeredHardyLittlewoodMaximal g x := by
      exact mul_le_mul' le_rfl
        (le_iSup (fun q' : PositiveRational ↦ centeredAverage (q' : ℝ) g x) q)

theorem cutoffBoundaryKernel_eq_zero_of_abs_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : |t| ≤ ρ) :
    cutoffBoundaryKernel lam ρ t = 0 := by
  by_cases ht0 : t = 0
  · simp [cutoffBoundaryKernel, ht0]
  · have hden : 0 < 4 * ρ := by positivity
    have harg : |t / (4 * ρ)| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).2
      nlinarith
    rw [cutoffBoundaryKernel, ite_eq_right ht0, ite_eq_left ht,
      dyadicCutoff_eq_one harg]
    simp

theorem cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 2 * ρ ≤ |t|) :
    cutoffBoundaryKernel lam ρ t = 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  have hnball : ¬ |t| ≤ ρ := by linarith
  have hden : 0 < 4 * ρ := by positivity
  have harg : 1 / 2 ≤ |t / (4 * ρ)| := by
    rw [abs_div, abs_of_pos hden]
    apply (le_div_iff₀ hden).2
    nlinarith
  rw [cutoffBoundaryKernel, ite_eq_right ht0, ite_eq_right hnball,
    dyadicCutoff_eq_zero harg]
  simp

theorem cutoffBoundaryKernel_norm_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) :
    ‖cutoffBoundaryKernel lam ρ t‖ ≤ 1 / ρ := by
  by_cases hin : |t| ≤ ρ
  · rw [cutoffBoundaryKernel_eq_zero_of_abs_le lam hρ hin]
    simpa using one_div_nonneg.mpr hρ.le
  · by_cases hout : 2 * ρ ≤ |t|
    · rw [cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs lam hρ hout]
      simpa using one_div_nonneg.mpr hρ.le
    · have ht0 : t ≠ 0 := by
        intro h
        apply hin
        simp [h, hρ.le]
      have hρt : ρ < |t| := lt_of_not_ge hin
      rw [cutoffBoundaryKernel, ite_eq_right ht0, ite_eq_right hin, norm_mul, norm_phase,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
      simp only [sub_zero]
      rw [abs_of_nonneg (dyadicCutoff_nonneg _)]
      calc
        dyadicCutoff (t / (4 * ρ)) / |t| ≤ 1 / |t| :=
          div_le_div_of_nonneg_right (dyadicCutoff_le_one _) (abs_nonneg _)
        _ ≤ 1 / ρ := one_div_le_one_div_of_le hρ hρt.le

theorem measurable_sharpQuadraticTailKernel (lam ε : ℝ) :
    Measurable (sharpQuadraticTailKernel lam ε) := by
  have hp : Continuous (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_norm
  · exact hp.measurable.div (Complex.measurable_ofReal.comp measurable_id)
  · exact measurable_const

theorem sharpQuadraticTailKernel_norm_le
    (lam : ℝ) {ε t : ℝ} (hε : 0 < ε) :
    ‖sharpQuadraticTailKernel lam ε t‖ ≤ 1 / ε := by
  by_cases ht : ε < |t|
  · have ht0 : t ≠ 0 := by
      intro h
      subst t
      exact (not_lt_of_ge hε.le) (by simpa only [abs_zero] using ht)
    rw [sharpQuadraticTailKernel, ite_eq_left ht, norm_div, norm_phase,
      Complex.norm_real, Real.norm_eq_abs]
    exact one_div_le_one_div_of_le hε ht.le
  · rw [sharpQuadraticTailKernel, ite_eq_right ht]
    simpa using one_div_nonneg.mpr hε.le

theorem measurable_cutoffBoundaryKernel (lam ρ : ℝ) :
    Measurable (cutoffBoundaryKernel lam ρ) := by
  have hp : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  have hnum : Measurable (fun t : ℝ ↦
      dyadicCutoff (t / (4 * ρ)) - if |t| ≤ ρ then 1 else 0) :=
    (dyadicCutoff_smooth.continuous.measurable.comp
        (measurable_id.div_const (4 * ρ))).sub
      (measurable_const.ite
        (measurableSet_le measurable_norm measurable_const)
        measurable_const)
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (hnum.div measurable_id)
    · exact hp

private theorem integrable_kernel_mul
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : Measurable k) (hbound : ∀ t, ‖k t‖ ≤ C) :
    Integrable (fun y ↦ k (x - y) * f y) := by
  apply hfi.bdd_mul
  · exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y ↦ hbound (x - y))

/-- The convolution-oriented truncation is exactly the truncation already
defined in `Definitions`. -/
theorem quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc
    (lam ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertConvolutionTrunc lam ε f x =
      quadraticHilbertTrunc lam ε f x := by
  let s : Set ℝ := {u : ℝ | ε < |u|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_norm
  rw [quadraticHilbertConvolutionTrunc, quadraticHilbertTrunc]
  calc
    (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y) =
        ∫ t, s.indicator
          (fun u ↦ f (x - u) * phase (lam * u ^ 2) / (u : ℂ)) t := by
      simpa only [s, sharpQuadraticTailKernel, Set.indicator, sub_sub_cancel,
        Set.mem_ofPred_eq, mul_comm, mul_left_comm, div_eq_mul_inv, mul_ite, mul_zero] using
        (integral_sub_left_eq_self
          (fun t : ℝ ↦ s.indicator
            (fun u ↦ f (x - u) * phase (lam * u ^ 2) / (u : ℂ)) t)
          volume x)
    _ = ∫ t in s, f (x - t) * phase (lam * t ^ 2) / (t : ℂ) :=
      integral_indicator hs

theorem cutoffBoundaryKernel_support_subset
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    support (cutoffBoundaryKernel lam ρ) ⊆ closedBall 0 (2 * ρ) := by
  intro t ht
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra h
  exact ht (cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs lam hρ (le_of_not_ge h))

/-- Each smooth-to-sharp cutoff error contributes at most eight copies of the
project's measurable centered maximal function. -/
theorem cutoffBoundaryOperator_enorm_le_maximal
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) :
    ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  calc
    ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in closedBall x (2 * ρ),
          ENNReal.ofReal (1 / ρ) * ‖f y‖ₑ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall x (2 * ρ)
      · simp only [Set.indicator_of_mem hy]
        rw [enorm_mul]
        apply mul_le_mul'
        · simpa only [← ofReal_norm] using
            ENNReal.ofReal_le_ofReal (cutoffBoundaryKernel_norm_le lam hρ)
        · exact le_rfl
      · simp only [Set.indicator, hy, ↓reduceIte]
        have hk : cutoffBoundaryKernel lam ρ (x - y) = 0 := by
          apply notMem_support.mp
          intro hmem
          apply hy
          have hs := cutoffBoundaryKernel_support_subset lam hρ hmem
          simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hs
        simp [hk]
    _ = ENNReal.ofReal (1 / ρ) *
          ∫⁻ y in closedBall x (2 * ρ), ‖f y‖ₑ := by
      rw [MeasureTheory.lintegral_const_mul _ hf.enorm]
    _ = 4 * centeredAverage (2 * ρ) (fun y ↦ ‖f y‖ₑ) x := by
      unfold centeredAverage
      have hρ0 : ρ ≠ 0 := ne_of_gt hρ
      rw [show ENNReal.ofReal (1 / ρ) =
          4 / ENNReal.ofReal (2 * (2 * ρ)) by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp; ring]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ 8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      have h := centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
        (mul_pos (by norm_num : (0 : ℝ) < 2) hρ) (fun y ↦ ‖f y‖ₑ) x
      calc
        4 * centeredAverage (2 * ρ) (fun y ↦ ‖f y‖ₑ) x ≤
            4 * (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :=
          mul_le_mul' le_rfl h
        _ = _ := by rw [← mul_assoc]; norm_num

private theorem scale_cutoff_eq_radius_cutoff (s : ℤ) (t : ℝ) :
    dyadicCutoff ((2⁻¹ : ℝ) ^ s * t) =
      dyadicCutoff (t / (4 * (2 : ℝ) ^ (s - 2))) := by
  congr 1
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_zpow]
  field_simp [zpow_ne_zero]

private theorem dyadic_block_innerRadius_le_outerRadius (j : ℤ) (B : ℕ) :
    (2 : ℝ) ^ (j - 3) ≤ (2 : ℝ) ^ (j + (B : ℤ) - 2) := by
  apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2
  omega

/-- Exact kernel algebra behind the comparison: the smooth dyadic block is
two sharp tails plus the two explicitly defined boundary errors. -/
theorem lowOscillatoryKernel_consecutive_eq_truncations_add_boundaries
    (lam : ℝ) (j : ℤ) (B : ℕ) (t : ℝ) :
    lowOscillatoryKernel lam B (fun r ↦ j + (r : ℤ)) t =
      (if (2 : ℝ) ^ (j - 3) < |t| then
          phase (lam * t ^ 2) / (t : ℂ) else 0) -
      (if (2 : ℝ) ^ (j + (B : ℤ) - 2) < |t| then
          phase (lam * t ^ 2) / (t : ℂ) else 0) +
      cutoffBoundaryKernel lam ((2 : ℝ) ^ (j + (B : ℤ) - 2)) t -
      cutoffBoundaryKernel lam ((2 : ℝ) ^ (j - 3)) t := by
  by_cases ht0 : t = 0
  · subst t
    simp [lowOscillatoryKernel, dyadicPsi_zero, cutoffBoundaryKernel]
  · rw [lowOscillatoryKernel]
    rw [show (∑ r ∈ Finset.range (B + 1),
          (dyadicPsi (j + (r : ℤ)) t : ℂ) * phase (lam * t ^ 2)) =
        ((∑ r ∈ Finset.range (B + 1), dyadicPsi (j + (r : ℤ)) t : ℝ) : ℂ) *
          phase (lam * t ^ 2) by
      rw [← Finset.sum_mul]
      push_cast
      rfl]
    rw [sum_dyadicPsi_consecutive j (B + 1) ht0]
    push_cast
    rw [show j + ((B : ℤ) + 1) - 1 = j + (B : ℤ) by ring]
    rw [scale_cutoff_eq_radius_cutoff (j + (B : ℤ)) t,
      scale_cutoff_eq_radius_cutoff (j - 1) t]
    rw [show j - 1 - 2 = j - 3 by ring]
    have hεR := dyadic_block_innerRadius_le_outerRadius j B
    simp only [cutoffBoundaryKernel, ite_eq_right ht0]
    push_cast
    by_cases hε : (2 : ℝ) ^ (j - 3) < |t|
    · have hnε : ¬ |t| ≤ (2 : ℝ) ^ (j - 3) := not_le.mpr hε
      rw [ite_eq_left hε, ite_eq_right hnε]
      by_cases hR : (2 : ℝ) ^ (j + (B : ℤ) - 2) < |t|
      · have hnR : ¬ |t| ≤ (2 : ℝ) ^ (j + (B : ℤ) - 2) := not_le.mpr hR
        rw [ite_eq_left hR, ite_eq_right hnR]
        field_simp; norm_num; ring
      · have hyR : |t| ≤ (2 : ℝ) ^ (j + (B : ℤ) - 2) := le_of_not_gt hR
        rw [ite_eq_right hR, ite_eq_left hyR]
        field_simp; norm_num; ring
    · have hyε : |t| ≤ (2 : ℝ) ^ (j - 3) := le_of_not_gt hε
      have hR : ¬ (2 : ℝ) ^ (j + (B : ℤ) - 2) < |t| :=
        not_lt.mpr (hyε.trans hεR)
      have hyR : |t| ≤ (2 : ℝ) ^ (j + (B : ℤ) - 2) := hyε.trans hεR
      rw [ite_eq_right hε, ite_eq_right hR, ite_eq_left hyε, ite_eq_left hyR]
      field_simp; norm_num; ring

/-- Operator-level exact decomposition of a consecutive smooth dyadic block
into two sharp truncations and two cutoff boundary errors. -/
theorem finiteQuadraticDyadicBlock_eq_truncations_add_boundaries
    (lam : ℝ) (j : ℤ) (B : ℕ) {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) :
    finiteQuadraticDyadicBlock lam j B f x =
      quadraticHilbertTrunc lam ((2 : ℝ) ^ (j - 3)) f x -
      quadraticHilbertTrunc lam ((2 : ℝ) ^ (j + (B : ℤ) - 2)) f x +
      (∫ y, cutoffBoundaryKernel lam
        ((2 : ℝ) ^ (j + (B : ℤ) - 2)) (x - y) * f y) -
      ∫ y, cutoffBoundaryKernel lam ((2 : ℝ) ^ (j - 3)) (x - y) * f y := by
  let ε : ℝ := (2 : ℝ) ^ (j - 3)
  let R : ℝ := (2 : ℝ) ^ (j + (B : ℤ) - 2)
  have hε : 0 < ε := zpow_pos (by norm_num) _
  have hR : 0 < R := zpow_pos (by norm_num) _
  have htailε : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ε (x - y) * f y) :=
    integrable_kernel_mul hfi x
      (measurable_sharpQuadraticTailKernel lam ε)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hε)
  have htailR : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam R (x - y) * f y) :=
    integrable_kernel_mul hfi x
      (measurable_sharpQuadraticTailKernel lam R)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hR)
  have herrε : Integrable
      (fun y ↦ cutoffBoundaryKernel lam ε (x - y) * f y) :=
    integrable_kernel_mul hfi x
      (measurable_cutoffBoundaryKernel lam ε)
      (fun t ↦ cutoffBoundaryKernel_norm_le lam (t := t) hε)
  have herrR : Integrable
      (fun y ↦ cutoffBoundaryKernel lam R (x - y) * f y) :=
    integrable_kernel_mul hfi x
      (measurable_cutoffBoundaryKernel lam R)
      (fun t ↦ cutoffBoundaryKernel_norm_le lam (t := t) hR)
  rw [finiteQuadraticDyadicBlock]
  calc
    (∫ y, lowOscillatoryKernel lam B (fun r ↦ j + (r : ℤ)) (x - y) * f y) =
        ∫ y, (sharpQuadraticTailKernel lam ε (x - y) -
          sharpQuadraticTailKernel lam R (x - y) +
          cutoffBoundaryKernel lam R (x - y) -
          cutoffBoundaryKernel lam ε (x - y)) * f y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y ↦ by
        change lowOscillatoryKernel lam B (fun r ↦ j + (r : ℤ)) (x - y) * f y = _
        rw [lowOscillatoryKernel_consecutive_eq_truncations_add_boundaries]
        simp only [sharpQuadraticTailKernel, ε, R])
    _ = quadraticHilbertConvolutionTrunc lam ε f x -
          quadraticHilbertConvolutionTrunc lam R f x +
          (∫ y, cutoffBoundaryKernel lam R (x - y) * f y) -
          ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y := by
      simp only [sub_mul, add_mul]
      have hsplitOuter := integral_sub ((htailε.sub htailR).add herrR) herrε
      have hsplitMiddle := integral_add (htailε.sub htailR) herrR
      have hsplitInner := integral_sub htailε htailR
      rw [show (∫ y,
          sharpQuadraticTailKernel lam ε (x - y) * f y -
            sharpQuadraticTailKernel lam R (x - y) * f y +
            cutoffBoundaryKernel lam R (x - y) * f y -
            cutoffBoundaryKernel lam ε (x - y) * f y) =
          (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y -
              sharpQuadraticTailKernel lam R (x - y) * f y +
              cutoffBoundaryKernel lam R (x - y) * f y) -
            ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y by
        simpa only [Pi.sub_apply, Pi.add_apply] using hsplitOuter]
      rw [show (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y -
            sharpQuadraticTailKernel lam R (x - y) * f y +
            cutoffBoundaryKernel lam R (x - y) * f y) =
          (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y -
            sharpQuadraticTailKernel lam R (x - y) * f y) +
          ∫ y, cutoffBoundaryKernel lam R (x - y) * f y by
        simpa only [Pi.sub_apply, Pi.add_apply] using hsplitMiddle]
      rw [show (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y -
            sharpQuadraticTailKernel lam R (x - y) * f y) =
          (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y) -
          ∫ y, sharpQuadraticTailKernel lam R (x - y) * f y by
        simpa only [Pi.sub_apply] using hsplitInner]
      rfl
    _ = _ := by
      rw [quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
        quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]

/-- The exact paper-facing pointwise comparison, with explicit constants.
The factor `16` is `8` for each of the two transition annuli; the factor `8`
comes from comparing an arbitrary real radius with the project's countable
rational-radius maximal operator. -/
theorem finiteQuadraticDyadicBlock_enorm_le_maximalTruncation_add_maximal
    (lam : ℝ) (j : ℤ) (B : ℕ) {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖finiteQuadraticDyadicBlock lam j B f x‖ₑ ≤
      2 * quadraticHilbertMaximalTruncation lam f x +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let ε : ℝ := (2 : ℝ) ^ (j - 3)
  let R : ℝ := (2 : ℝ) ^ (j + (B : ℤ) - 2)
  let A : ℂ := quadraticHilbertTrunc lam ε f x
  let D : ℂ := quadraticHilbertTrunc lam R f x
  let E : ℂ := ∫ y, cutoffBoundaryKernel lam R (x - y) * f y
  let F : ℂ := ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y
  let H : ℝ≥0∞ := quadraticHilbertMaximalTruncation lam f x
  let M : ℝ≥0∞ := centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x
  have hε : 0 < ε := zpow_pos (by norm_num) _
  have hR : 0 < R := zpow_pos (by norm_num) _
  have hA : ‖A‖ₑ ≤ H := by
    exact le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
      ‖quadraticHilbertTrunc lam δ f x‖ₑ) ⟨ε, hε⟩
  have hD : ‖D‖ₑ ≤ H := by
    exact le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
      ‖quadraticHilbertTrunc lam δ f x‖ₑ) ⟨R, hR⟩
  have hE : ‖E‖ₑ ≤ 8 * M :=
    cutoffBoundaryOperator_enorm_le_maximal lam hR f hf x
  have hF : ‖F‖ₑ ≤ 8 * M :=
    cutoffBoundaryOperator_enorm_le_maximal lam hε f hf x
  rw [finiteQuadraticDyadicBlock_eq_truncations_add_boundaries lam j B hfi]
  change ‖A - D + E - F‖ₑ ≤ 2 * H + 16 * M
  calc
    ‖A - D + E - F‖ₑ ≤ ‖A - D + E‖ₑ + ‖F‖ₑ := enorm_sub_le
    _ ≤ (‖A - D‖ₑ + ‖E‖ₑ) + ‖F‖ₑ :=
      add_le_add (enorm_add_le (A - D) E) le_rfl
    _ ≤ ((‖A‖ₑ + ‖D‖ₑ) + ‖E‖ₑ) + ‖F‖ₑ :=
      add_le_add (add_le_add enorm_sub_le le_rfl) le_rfl
    _ ≤ ((H + H) + 8 * M) + 8 * M := by
      gcongr
    _ = 2 * H + 16 * M := by ring

/-- The actual low block `sum_{0 ≤ r ≤ B} C_{2,r}^lam f` for nonzero
modulation, expressed using the paper's selected spatial scales. -/
noncomputable def paperLowDyadicOperator
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) : ℂ :=
  ∫ y, paperLowOscillatoryKernel lam hlam B (x - y) * f y

theorem paperLowOscillatoryKernel_eq_consecutive
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) :
    paperLowOscillatoryKernel lam hlam B t =
      lowOscillatoryKernel lam B
        (fun r ↦ oscillatoryScaleIndex lam 0 hlam + (r : ℤ)) t := by
  rw [paperLowOscillatoryKernel, lowOscillatoryKernel, lowOscillatoryKernel]
  apply Finset.sum_congr rfl
  intro r hr
  rw [oscillatoryScaleIndex_eq_add lam r hlam]

theorem paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    paperLowDyadicOperator lam hlam B f x =
      finiteQuadraticDyadicBlock lam (oscillatoryScaleIndex lam 0 hlam) B f x := by
  rw [paperLowDyadicOperator, finiteQuadraticDyadicBlock]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    change paperLowOscillatoryKernel lam hlam B (x - y) * f y = _
    rw [paperLowOscillatoryKernel_eq_consecutive])

/-- Concrete specialization of the pointwise comparison to the exact
frequency-dependent dyadic block used in the positive proof. -/
theorem paperLowDyadicOperator_enorm_le_maximalTruncation_add_maximal
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖paperLowDyadicOperator lam hlam B f x‖ₑ ≤
      2 * quadraticHilbertMaximalTruncation lam f x +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  rw [paperLowDyadicOperator_eq_finiteQuadraticDyadicBlock]
  exact finiteQuadraticDyadicBlock_enorm_le_maximalTruncation_add_maximal
    lam (oscillatoryScaleIndex lam 0 hlam) B f.measurable_toFun f.integrable x


end QuadraticCarleson
