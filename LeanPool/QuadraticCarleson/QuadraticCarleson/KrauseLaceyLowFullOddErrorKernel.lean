/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionMaximal

/-!
# The low full-odd quadratic phase-error kernel

This file isolates the elementary kernel used to compare a complete odd
dyadic block with its zero-phase (ordinary Hilbert) counterpart.
-/

open Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyLowFullOddReduction


noncomputable section

/-- The kernel error obtained by replacing the unit quadratic phase by the
constant phase on a consecutive full-odd dyadic block. -/
def finiteLowFullPhaseErrorKernel (j : ℤ) (n : ℕ) (t : ℝ) : ℂ :=
  (∑ r ∈ Finset.range n, (dyadicPsi (j + (r : ℤ)) t : ℂ)) *
    (phase (t ^ 2) - 1)

/-- The finite low-block phase error is continuous.  This is made explicit
rather than left to automation: every dyadic amplitude is smooth, coercion
from `ℝ` to `ℂ` is continuous, and finite sums and products preserve
continuity. -/
theorem continuous_finiteLowFullPhaseErrorKernel (j : ℤ) (n : ℕ) :
    Continuous (finiteLowFullPhaseErrorKernel j n) := by
  have hsum : Continuous (fun t : ℝ ↦
      ∑ r ∈ Finset.range n, (dyadicPsi (j + (r : ℤ)) t : ℂ)) := by
    apply continuous_finsetSum
    intro r hr
    exact Complex.continuous_ofReal.comp
      (dyadicPsi_smooth (j + (r : ℤ))).continuous
  have hphase : Continuous (fun t : ℝ ↦ phase (t ^ 2) - 1) := by
    unfold phase
    fun_prop
  exact hsum.mul hphase

theorem measurable_finiteLowFullPhaseErrorKernel (j : ℤ) (n : ℕ) :
    Measurable (finiteLowFullPhaseErrorKernel j n) :=
  (continuous_finiteLowFullPhaseErrorKernel j n).measurable

/-- If every scale in the block is at most zero, the phase-error kernel is
supported in the fixed ball of radius `1/2`. -/
theorem finiteLowFullPhaseErrorKernel_support_subset
    {j : ℤ} {n : ℕ} (htop : j + (n : ℤ) ≤ 1) :
    support (finiteLowFullPhaseErrorKernel j n) ⊆
      closedBall 0 (1 / 2 : ℝ) := by
  intro t ht
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra hout
  have habs : (1 / 2 : ℝ) < |t| := lt_of_not_ge hout
  apply ht
  unfold finiteLowFullPhaseErrorKernel
  have hzero : ∀ r ∈ Finset.range n,
      dyadicPsi (j + (r : ℤ)) t = 0 := by
    intro r hr
    apply notMem_support.mp
    intro hmem
    have hsupp := (dyadicPsi_support_subset (j + (r : ℤ))) hmem
    have hrn : r < n := Finset.mem_range.mp hr
    have hscale : j + (r : ℤ) ≤ 0 := by omega
    have hpow : (2 : ℝ) ^ (j + (r : ℤ) - 1) ≤ 1 / 2 := by
      calc
        (2 : ℝ) ^ (j + (r : ℤ) - 1) ≤ (2 : ℝ) ^ (-1 : ℤ) := by
          apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2
          omega
        _ = 1 / 2 := by norm_num
    exact (not_lt_of_ge habs.le) (hsupp.2.trans_le hpow)
  have hsum :
      (∑ r ∈ Finset.range n, (dyadicPsi (j + (r : ℤ)) t : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp only [hzero r hr, Complex.ofReal_zero]
  rw [hsum, zero_mul]

/-- Telescoping of the full odd amplitudes removes the apparent factor `n`:
the unit quadratic phase error is bounded by `4π|t|` for every block
length. -/
theorem finiteLowFullPhaseErrorKernel_norm_le_abs
    (j : ℤ) (n : ℕ) (t : ℝ) :
    ‖finiteLowFullPhaseErrorKernel j n t‖ ≤ 4 * Real.pi * |t| := by
  by_cases ht : t = 0
  · subst t
    simp [finiteLowFullPhaseErrorKernel, dyadicPsi_zero]
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hsum :
        |∑ r ∈ Finset.range n, dyadicPsi (j + (r : ℤ)) t| ≤ 2 / |t| := by
      rw [sum_dyadicPsi_consecutive j n ht, abs_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg t)
      calc
        |dyadicCutoff ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t) -
            dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)| ≤
            |dyadicCutoff ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t)| +
              |dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le
              (dyadicCutoff ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t))
              (-dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t))
        _ = dyadicCutoff ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t) +
              dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t) := by
          rw [abs_of_nonneg (dyadicCutoff_nonneg _),
            abs_of_nonneg (dyadicCutoff_nonneg _)]
        _ ≤ 2 := by
          linarith [dyadicCutoff_le_one
            ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t),
            dyadicCutoff_le_one ((2⁻¹ : ℝ) ^ (j - 1) * t)]
    have hphase := norm_phase_sub_one_le (t ^ 2)
    rw [abs_pow] at hphase
    have hcast :
        (∑ r ∈ Finset.range n, (dyadicPsi (j + (r : ℤ)) t : ℂ)) =
          ((∑ r ∈ Finset.range n, dyadicPsi (j + (r : ℤ)) t : ℝ) : ℂ) := by
      push_cast
      rfl
    unfold finiteLowFullPhaseErrorKernel
    rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |∑ r ∈ Finset.range n, dyadicPsi (j + (r : ℤ)) t| *
          ‖phase (t ^ 2) - 1‖ ≤
          (2 / |t|) * (2 * Real.pi * |t| ^ 2) :=
        mul_le_mul hsum hphase (norm_nonneg _) (by positivity)
      _ = 4 * Real.pi * |t| := by field_simp; ring

/-- On a genuinely low block the phase-error kernel has a uniform global
bound, independent of both its starting scale and its length. -/
theorem finiteLowFullPhaseErrorKernel_norm_le
    {j : ℤ} {n : ℕ} (htop : j + (n : ℤ) ≤ 1) (t : ℝ) :
    ‖finiteLowFullPhaseErrorKernel j n t‖ ≤ 4 * Real.pi := by
  by_cases ht : t ∈ support (finiteLowFullPhaseErrorKernel j n)
  · have habs : |t| ≤ 1 / 2 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using
        finiteLowFullPhaseErrorKernel_support_subset htop ht
    calc
      ‖finiteLowFullPhaseErrorKernel j n t‖ ≤ 4 * Real.pi * |t| :=
        finiteLowFullPhaseErrorKernel_norm_le_abs j n t
      _ ≤ 4 * Real.pi := by
        have hpi : 0 ≤ 4 * Real.pi := by positivity
        exact (mul_le_mul_of_nonneg_left habs hpi).trans
          (by nlinarith [Real.pi_pos])
  · rw [notMem_support.mp ht, norm_zero]
    positivity

/-- Convolution with the complete low-scale phase error is controlled by a
fixed multiple of the centered Hardy--Littlewood maximal function. -/
theorem finiteLowFullPhaseErrorOperator_enorm_le_maximal
    {j : ℤ} {n : ℕ} (htop : j + (n : ℤ) ≤ 1)
    {f : ℝ → ℂ} (hf : Measurable f) (x : ℝ) :
    ‖∫ y, finiteLowFullPhaseErrorKernel j n (x - y) * f y‖ₑ ≤
      ENNReal.ofReal (16 * Real.pi) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  simpa only [show (4 : ℝ) * (4 * Real.pi) = 16 * Real.pi by ring] using
    OscillatoryReduction.bounded_ball_kernel_enorm_le_maximal
      (K := finiteLowFullPhaseErrorKernel j n)
      (C := 4 * Real.pi) (ρ := 1 / 2)
      (by positivity : 0 ≤ 4 * Real.pi) (by norm_num : (0 : ℝ) < 1 / 2)
      (fun t ↦ (finiteLowFullPhaseErrorKernel_norm_le htop t).trans (by
        norm_num [div_eq_mul_inv]
        nlinarith [Real.pi_pos]))
      (finiteLowFullPhaseErrorKernel_support_subset htop) hf x


end
end KrauseLaceyLowFullOddReduction
end QuadraticCarleson
