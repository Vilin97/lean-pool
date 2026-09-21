/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyLowFullOddErrorKernel
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicReflection

/-!
# The low full-odd quadratic block versus the ordinary Hilbert block

At spatial scales below the unit oscillatory scale, the positive spatial
half cannot be estimated independently: doing so discards the cancellation
of the odd kernel. This file keeps the complete odd dyadic sum and compares
its unit quadratic phase with phase zero. Consecutive dyadic amplitudes
telescopically cancel, so the phase error has a compactly supported kernel
whose bound is independent of the number of low scales.
-/

open Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyLowFullOddReduction

open KrauseLaceyFullDyadicReflection


noncomputable
section

/-- The complete odd dyadic quadratic kernel is continuous. -/
theorem continuous_fullDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    Continuous
      (annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam) := by
  apply (Complex.continuous_ofReal.comp (dyadicPsi_smooth j).continuous).mul
  unfold phase
  fun_prop

/-- The complete odd dyadic quadratic kernel is compactly supported in its
natural symmetric annulus. -/
theorem hasCompactSupport_fullDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    HasCompactSupport
      (annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact
      (Icc (-(2 : ℝ) ^ (j - 1)) ((2 : ℝ) ^ (j - 1))))
  intro t ht
  have hpsi : dyadicPsi j t ≠ 0 := by
    intro hz
    exact ht (by simp [annularQuadraticKernel, hz])
  have hsupp := (dyadicPsi_support_subset j) hpsi
  have hout : |t| < (2 : ℝ) ^ (j - 1) := by
    simpa only [mem_ofPred_eq] using hsupp.2
  rw [abs_lt] at hout
  exact ⟨hout.1.le, hout.2.le⟩

/-- A finite full-odd tail is the convolution with the finite sum of its
one-scale kernels. This is the exact finite interchange needed before the
unit phase can be compared with phase zero. -/
theorem finiteFullDyadicTail_eq_integral_kernelSum
    (lam : ℝ) (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTail lam j n f x =
      ∫ y, (∑ r ∈ Finset.range n,
        annularQuadraticKernel
          (fun t ↦ (dyadicPsi (j + (r : ℤ)) t : ℂ)) lam (x - y)) * f y := by
  have hint (r : ℕ) (_hr : r ∈ Finset.range n) : Integrable (fun y ↦
      annularQuadraticKernel
        (fun t ↦ (dyadicPsi (j + (r : ℤ)) t : ℂ)) lam (x - y) * f y) :=
    integrable_convolution_row_of_memLp
      (continuous_fullDyadicQuadraticKernel lam (j + (r : ℤ)))
      (hasCompactSupport_fullDyadicQuadraticKernel lam (j + (r : ℤ))) hf x
  unfold finiteFullDyadicTail fullDyadicConvolution
  rw [← integral_finsetSum (Finset.range n) hint]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Finset.sum_mul]

/-- The complete unit-phase full-odd tail differs from its zero-phase
Hilbert counterpart by convolution with the explicitly controlled phase-error
kernel. -/
theorem finiteFullDyadicTail_one_sub_zero_eq_errorIntegral
    (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTail 1 j n f x - finiteFullDyadicTail 0 j n f x =
      ∫ y, finiteLowFullPhaseErrorKernel j n (x - y) * f y := by
  have hint (lam : ℝ) : Integrable (fun y ↦
      (∑ r ∈ Finset.range n,
        annularQuadraticKernel
          (fun t ↦ (dyadicPsi (j + (r : ℤ)) t : ℂ)) lam (x - y)) * f y) := by
    simpa only [← Finset.sum_mul] using
      (integrable_finsetSum (Finset.range n) fun r hr ↦
        integrable_convolution_row_of_memLp
          (continuous_fullDyadicQuadraticKernel lam (j + (r : ℤ)))
          (hasCompactSupport_fullDyadicQuadraticKernel lam (j + (r : ℤ))) hf x)
  rw [finiteFullDyadicTail_eq_integral_kernelSum 1 j n hf x,
    finiteFullDyadicTail_eq_integral_kernelSum 0 j n hf x,
    ← integral_sub (hint 1) (hint 0)]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold finiteLowFullPhaseErrorKernel annularQuadraticKernel
  simp only [Finset.sum_mul, one_mul, zero_mul, phase_zero, mul_one]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Every complete low unit-phase tail is pointwise controlled by the
corresponding phase-zero Hilbert tail plus a fixed Hardy--Littlewood maximal
error, uniformly in the number of scales. -/
theorem finiteFullDyadicTail_one_enorm_le_zero_add_maximal
    {j : ℤ} {n : ℕ} (htop : j + (n : ℤ) ≤ 1)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) (x : ℝ) :
    ‖finiteFullDyadicTail 1 j n f x‖ₑ ≤
      ‖finiteFullDyadicTail 0 j n f x‖ₑ +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have herr := finiteFullDyadicTail_one_sub_zero_eq_errorIntegral j n hf x
  have heq : finiteFullDyadicTail 1 j n f x =
      finiteFullDyadicTail 0 j n f x +
        ∫ y, finiteLowFullPhaseErrorKernel j n (x - y) * f y := by
    rw [← herr]
    ring
  rw [heq]
  exact (enorm_add_le _ _).trans (add_le_add le_rfl
    (finiteLowFullPhaseErrorOperator_enorm_le_maximal htop hfm x))

/-- The same comparison in the moving-lower-cutoff suffix orientation used by
the Krause--Lacey maximal operator. -/
theorem finiteFullDyadicSuffix_one_enorm_le_zero_add_maximal
    {j : ℤ} {N m : ℕ} (hm : m ≤ N) (htop : j + (N : ℤ) ≤ 1)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) (x : ℝ) :
    ‖finiteFullDyadicSuffix 1 j N m f x‖ₑ ≤
      ‖finiteFullDyadicSuffix 0 j N m f x‖ₑ +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold finiteFullDyadicSuffix
  apply finiteFullDyadicTail_one_enorm_le_zero_add_maximal
    (j := j + (m : ℤ)) (n := N - m) (f := f) (x := x)
  · omega
  · exact hfm
  · exact hf

/-- Taking the maximum over all moving lower cutoffs costs no additional
factor because the same maximal-function error controls every suffix. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_one_le_zero_add_maximal
    {j : ℤ} {N : ℕ} (htop : j + (N : ℤ) ≤ 1)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) ≤
      (finiteFullDyadicSuffixMaxNNNorm 0 j N f x : ℝ≥0∞) +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  simp only [ENNReal.coe_finset_sup]
  apply Finset.sup_le
  intro m hm
  change ‖finiteFullDyadicSuffix 1 j N m f x‖ₑ ≤ _
  have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  exact (finiteFullDyadicSuffix_one_enorm_le_zero_add_maximal
    hmN htop hfm hf x).trans (add_le_add
      (Finset.le_sup (f := fun r ↦
        ‖finiteFullDyadicSuffix 0 j N r f x‖ₑ) hm) le_rfl)


end
end KrauseLaceyLowFullOddReduction
end QuadraticCarleson
