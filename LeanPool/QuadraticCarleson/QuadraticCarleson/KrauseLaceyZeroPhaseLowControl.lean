/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyLowFullOddReduction
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyCompactPairingStabilization

/-!
# The phase-zero term in the low full-odd reduction

The low unit-quadratic block is already reduced to a phase-zero full-odd
block plus a Hardy--Littlewood maximal error.  This file keeps the phase-zero
term common across all lacunary modulations and compares it directly with
the ordinary maximal Hilbert transform.  It therefore does not introduce an
unnecessary sparse-domination theorem for the ordinary Hilbert transform.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyZeroPhaseLowControl

open KrauseLaceySharpSmoothAdapter
open KrauseLaceyCompactPairingStabilization
open KrauseLaceyFullDyadicReflection
open KrauseLaceyLowFullOddReduction


noncomputable section

/-- Reverse direction of the sharp/smooth cutoff comparison.  The difference
is exactly the already controlled compact transition kernel. -/
theorem smoothQuadraticHighPass_enorm_le_hilbertTrunc_add_maximal
    {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖smoothQuadraticHighPass 0 ρ f x‖ₑ ≤
      ‖quadraticHilbertTrunc 0 ρ f x‖ₑ +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have heq := quadraticHilbertTrunc_eq_smoothHighPass_add_boundary 0 hρ hfi x
  have hsmooth : smoothQuadraticHighPass 0 ρ f x =
      quadraticHilbertTrunc 0 ρ f x -
        ∫ y, cutoffBoundaryKernel 0 ρ (x - y) * f y := by
    rw [heq]
    ring
  rw [hsmooth]
  exact enorm_sub_le.trans (add_le_add le_rfl
    (cutoffBoundaryOperator_enorm_le_maximal 0 hρ f hf x))

/-- The two finite-block definitions used by the low comparison and by the
sharp-truncation adapter agree exactly. -/
theorem finiteFullDyadicTail_succ_eq_finiteQuadraticDyadicBlock
    (lam : ℝ) (j : ℤ) (B : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTail lam j (B + 1) f x =
      finiteQuadraticDyadicBlock lam j B f x := by
  rw [finiteFullDyadicTail_eq_integral_kernelSum lam j (B + 1) hf x]
  unfold finiteQuadraticDyadicBlock lowOscillatoryKernel
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [annularQuadraticKernel, Finset.sum_mul]

/-- A single phase-zero suffix is controlled by the genuine ordinary Hilbert
maximal truncation and the common cutoff-boundary maximal error. -/
theorem finiteFullDyadicSuffix_zero_enorm_le_hilbertMaximal_add_maximal
    (j : ℤ) (N m : ℕ) {f : ℝ → ℂ}
    (hfm : Measurable f) (hfi : Integrable f) (hf2 : MemLp f 2) (x : ℝ) :
    ‖finiteFullDyadicSuffix 0 j N m f x‖ₑ ≤
      2 * quadraticHilbertMaximalTruncation 0 f x +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold finiteFullDyadicSuffix
  by_cases hn : N - m = 0
  · simp [hn, finiteFullDyadicTail]
  · have hnpos : 0 < N - m := Nat.pos_of_ne_zero hn
    have hsucc : N - m = (N - m - 1) + 1 := by omega
    rw [hsucc, finiteFullDyadicTail_succ_eq_finiteQuadraticDyadicBlock
      0 (j + (m : ℤ)) (N - m - 1) hf2 x]
    exact finiteQuadraticDyadicBlock_enorm_le_maximalTruncation_add_maximal
      0 (j + (m : ℤ)) (N - m - 1) hfm hfi x

/-- The finite maximum over all phase-zero suffixes has the same pointwise
bound as each individual suffix; no cardinality factor is introduced. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_zero_le_hilbertMaximal_add_maximal
    (j : ℤ) (N : ℕ) {f : ℝ → ℂ}
    (hfm : Measurable f) (hfi : Integrable f) (hf2 : MemLp f 2) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm 0 j N f x : ℝ≥0∞) ≤
      2 * quadraticHilbertMaximalTruncation 0 f x +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  simp only [ENNReal.coe_finset_sup]
  apply Finset.sup_le
  intro m hm
  change ‖finiteFullDyadicSuffix 0 j N m f x‖ₑ ≤ _
  exact finiteFullDyadicSuffix_zero_enorm_le_hilbertMaximal_add_maximal
    j N m hfm hfi hf2 x

/-- Complete pointwise control of an all-low unit-quadratic suffix maximum.
The phase-zero part is paid once through the ordinary maximal Hilbert
transform, and the two cutoff errors are paid through one centered maximal
function. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_one_low_le_hilbertMaximal_add_maximal
    {j : ℤ} {N : ℕ} (htop : j + (N : ℤ) ≤ 1)
    {f : ℝ → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hf2 : MemLp f 2) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) ≤
      (2 * quadraticHilbertMaximalTruncation 0 f x +
        16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  exact (coe_finiteFullDyadicSuffixMaxNNNorm_one_le_zero_add_maximal
    htop hfm hf2 x).trans (add_le_add
      (coe_finiteFullDyadicSuffixMaxNNNorm_zero_le_hilbertMaximal_add_maximal
        j N hfm hfi hf2 x) le_rfl)


end
end KrauseLaceyZeroPhaseLowControl
end QuadraticCarleson
