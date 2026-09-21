/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySharpSmoothAdapter
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingSigned

/-!
# Restoring the negative spatial half of the Krause--Lacey kernel

Krause--Lacey carry out the local argument for the positive half of their odd
dyadic kernel and state that the negative half is symmetric. This file makes
that symmetry exact. A finite full dyadic tail is the positive-half tail on
`f` minus the same positive-half tail on the reflected input, evaluated at the
reflected point. Thus no analytic estimate is duplicated for the negative
half.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyFullDyadicReflection


noncomputable
section

/-- A single positive-half dyadic convolution at scale `j`. -/
def positiveDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y) * f y

/-- The corresponding convolution with the paper's full odd dyadic kernel. -/
def fullDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, annularQuadraticKernel (fun t ↦ (dyadicPsi j t : ℂ)) lam (x - y) * f y

/-- A finite consecutive positive-half dyadic tail. -/
def finitePositiveDyadicTail
    (lam : ℝ) (j : ℤ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range n, positiveDyadicConvolution lam (j + (r : ℤ)) f x

/-- A finite consecutive tail for the genuine full odd dyadic kernel. -/
def finiteFullDyadicTail
    (lam : ℝ) (j : ℤ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range n, fullDyadicConvolution lam (j + (r : ℤ)) f x

/-- Maximum over all initial finite tails of length at most `N`. The value is
kept in `NNReal`, matching the finite-maximal interfaces elsewhere in the
project. -/
def finitePositiveDyadicTailMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePositiveDyadicTail lam j n f x‖₊

/-- The same finite maximum for the genuine full odd dyadic kernel. -/
def finiteFullDyadicTailMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finiteFullDyadicTail lam j n f x‖₊

/-- A suffix ending at the common upper scale `j + N`. Varying `m` is the
finite version of the paper's physical lower-truncation parameter. -/
def finitePositiveDyadicSuffix
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  finitePositiveDyadicTail lam (j + (m : ℤ)) (N - m) f x

/-- The corresponding finite suffix for the full odd kernel. -/
def finiteFullDyadicSuffix
    (lam : ℝ) (j : ℤ) (N m : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  finiteFullDyadicTail lam (j + (m : ℤ)) (N - m) f x

/-- Maximum over the moving lower cutoffs `m ≤ N` for the positive half. -/
def finitePositiveDyadicSuffixMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun m ↦ ‖finitePositiveDyadicSuffix lam j N m f x‖₊

/-- Maximum over moving lower cutoffs for the full odd kernel. -/
def finiteFullDyadicSuffixMaxNNNorm
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : NNReal :=
  (Finset.range (N + 1)).sup fun m ↦ ‖finiteFullDyadicSuffix lam j N m f x‖₊

/-- Supremum of all finite full-tail approximants. -/
def fullDyadicTailSupEnorm
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ‖finiteFullDyadicTail lam j n f x‖ₑ

theorem continuous_positiveDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    Continuous (annularQuadraticKernel (positiveDyadicAmplitude j) lam) := by
  have ha : Continuous (positiveDyadicAmplitude j) :=
    continuous_iff_continuousAt.mpr
      (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
  unfold annularQuadraticKernel phase
  fun_prop

theorem hasCompactSupport_positiveDyadicQuadraticKernel (lam : ℝ) (j : ℤ) :
    HasCompactSupport (annularQuadraticKernel (positiveDyadicAmplitude j) lam) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact
      (Icc ((2 : ℝ) ^ (j - 1) / 4) ((2 : ℝ) ^ (j - 1))))
  intro t ht
  apply positiveDyadicAmplitude_support_subset j
  intro hz
  exact ht (by simp [annularQuadraticKernel, hz])

/-- The phase is even, so the odd dyadic amplitude is literally the positive
kernel minus its spatial reflection. -/
theorem fullDyadicKernel_eq_positive_sub_reflect (lam : ℝ) (j : ℤ) (t : ℝ) :
    annularQuadraticKernel (fun u ↦ (dyadicPsi j u : ℂ)) lam t =
      annularQuadraticKernel (positiveDyadicAmplitude j) lam t -
        annularQuadraticKernel (positiveDyadicAmplitude j) lam (-t) := by
  unfold annularQuadraticKernel
  change (dyadicPsi j t : ℂ) * phase (lam * t ^ 2) =
    positiveDyadicAmplitude j t * phase (lam * t ^ 2) -
      positiveDyadicAmplitude j (-t) * phase (lam * (-t) ^ 2)
  rw [dyadicPsi_eq_positive_sub_reflect]
  simp only [neg_sq]
  ring

/-- Reflection of the positive kernel is the positive operator on the
reflected input at the reflected observation point. -/
theorem reflectedPositiveDyadicConvolution
    (lam : ℝ) (j : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    (∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) =
      positiveDyadicConvolution lam j (fun y ↦ f (-y)) (-x) := by
  unfold positiveDyadicConvolution
  calc
    (∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) =
        ∫ y, annularQuadraticKernel (positiveDyadicAmplitude j) lam
          (-(x - -y)) * f (-y) :=
      (integral_neg_eq_self
        (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y)
        volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 2
      ring

/-- Exact one-scale identity restoring the negative spatial half. -/
theorem fullDyadicConvolution_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    fullDyadicConvolution lam j f x =
      positiveDyadicConvolution lam j f x -
        positiveDyadicConvolution lam j (fun y ↦ f (-y)) (-x) := by
  have hp : Integrable
      (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y) * f y) :=
    integrable_convolution_row_of_memLp
      (continuous_positiveDyadicQuadraticKernel lam j)
      (hasCompactSupport_positiveDyadicQuadraticKernel lam j) hf x
  have hr : Integrable
      (fun y ↦ annularQuadraticKernel (positiveDyadicAmplitude j) lam (-(x - y)) * f y) := by
    have hc := (continuous_positiveDyadicQuadraticKernel lam j).comp continuous_neg
    have hs := (hasCompactSupport_positiveDyadicQuadraticKernel lam j).comp_homeomorph
      (Homeomorph.neg ℝ)
    exact integrable_convolution_row_of_memLp hc hs hf x
  rw [fullDyadicConvolution, positiveDyadicConvolution, ← reflectedPositiveDyadicConvolution]
  rw [← integral_sub hp hr]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← sub_mul, ← fullDyadicKernel_eq_positive_sub_reflect]

/-- Exact finite-tail identity. This is the deterministic justification for
using only the positive spatial half in the local KL argument. -/
theorem finiteFullDyadicTail_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTail lam j n f x =
      finitePositiveDyadicTail lam j n f x -
        finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicTail finitePositiveDyadicTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact fullDyadicConvolution_eq_positive_sub_reflect lam (j + (r : ℤ)) hf x

theorem norm_finiteFullDyadicTail_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (n : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    ‖finiteFullDyadicTail lam j n f x‖ ≤
      ‖finitePositiveDyadicTail lam j n f x‖ +
        ‖finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x)‖ := by
  rw [finiteFullDyadicTail_eq_positive_sub_reflect lam j n hf x]
  exact norm_sub_le _ _

/-- The maximum of the full odd-kernel tails is pointwise controlled by the
positive-half maximum and its reflected-input copy. The estimate is uniform
in the number of scales. -/
theorem finiteFullDyadicTailMaxNNNorm_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicTailMaxNNNorm lam j N f x ≤
      finitePositiveDyadicTailMaxNNNorm lam j N f x +
        finitePositiveDyadicTailMaxNNNorm lam j N (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicTailMaxNNNorm finitePositiveDyadicTailMaxNNNorm
  apply Finset.sup_le
  intro n hn
  calc
    ‖finiteFullDyadicTail lam j n f x‖₊ ≤
        ‖finitePositiveDyadicTail lam j n f x‖₊ +
          ‖finitePositiveDyadicTail lam j n (fun y ↦ f (-y)) (-x)‖₊ := by
      exact_mod_cast norm_finiteFullDyadicTail_le_positive_add_reflect lam j n hf x
    _ ≤ ((Finset.range (N + 1)).sup fun m ↦
          ‖finitePositiveDyadicTail lam j m f x‖₊) +
        (Finset.range (N + 1)).sup fun m ↦
          ‖finitePositiveDyadicTail lam j m (fun y ↦ f (-y)) (-x)‖₊ :=
      add_le_add (Finset.le_sup (f := fun m ↦
        ‖finitePositiveDyadicTail lam j m f x‖₊) hn)
        (Finset.le_sup (f := fun m ↦
          ‖finitePositiveDyadicTail lam j m (fun y ↦ f (-y)) (-x)‖₊) hn)

theorem finiteFullDyadicSuffix_eq_positive_sub_reflect
    (lam : ℝ) (j : ℤ) (N m : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicSuffix lam j N m f x =
      finitePositiveDyadicSuffix lam j N m f x -
        finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x) := by
  exact finiteFullDyadicTail_eq_positive_sub_reflect
    lam (j + (m : ℤ)) (N - m) hf x

/-- Reflection control in the exact suffix orientation of the KL maximal
physical-truncation operator. -/
theorem finiteFullDyadicSuffixMaxNNNorm_le_positive_add_reflect
    (lam : ℝ) (j : ℤ) (N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteFullDyadicSuffixMaxNNNorm lam j N f x ≤
      finitePositiveDyadicSuffixMaxNNNorm lam j N f x +
        finitePositiveDyadicSuffixMaxNNNorm lam j N (fun y ↦ f (-y)) (-x) := by
  unfold finiteFullDyadicSuffixMaxNNNorm finitePositiveDyadicSuffixMaxNNNorm
  apply Finset.sup_le
  intro m hm
  calc
    ‖finiteFullDyadicSuffix lam j N m f x‖₊ ≤
        ‖finitePositiveDyadicSuffix lam j N m f x‖₊ +
          ‖finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x)‖₊ := by
      rw [finiteFullDyadicSuffix_eq_positive_sub_reflect lam j N m hf x]
      exact_mod_cast norm_sub_le
        (finitePositiveDyadicSuffix lam j N m f x)
        (finitePositiveDyadicSuffix lam j N m (fun y ↦ f (-y)) (-x))
    _ ≤ ((Finset.range (N + 1)).sup fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q f x‖₊) +
        (Finset.range (N + 1)).sup fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q (fun y ↦ f (-y)) (-x)‖₊ :=
      add_le_add (Finset.le_sup (f := fun q ↦
        ‖finitePositiveDyadicSuffix lam j N q f x‖₊) hm)
        (Finset.le_sup (f := fun q ↦
          ‖finitePositiveDyadicSuffix lam j N q (fun y ↦ f (-y)) (-x)‖₊) hm)

/-- The finite full tails exhaust the actual smooth high-pass convolution.
Compact support of the test input is used in the underlying operator-level
sum/integral theorem, so this is not a merely formal kernel identity. -/
theorem hasSum_fullDyadicConvolution_add_nat
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    HasSum (fun r : ℕ ↦ fullDyadicConvolution lam (j + (r : ℤ)) f x)
      (KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x) := by
  simpa only [fullDyadicConvolution, annularQuadraticKernel] using
    KrauseLaceySharpSmoothAdapter.hasSum_dyadicQuadraticConvolutions_add_nat
      lam j f x

theorem tendsto_finiteFullDyadicTail_atTop
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ finiteFullDyadicTail lam j n f x) atTop
      (nhds (KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x)) := by
  simpa only [finiteFullDyadicTail] using
    (hasSum_fullDyadicConvolution_add_nat lam j f x).tendsto_sum_nat

/-- The genuine smooth high-pass value is controlled by the supremum of its
finite odd-kernel approximants. This is the pointwise limit bridge used when
passing a uniform finite sparse estimate to the actual operator. -/
theorem smoothQuadraticHighPass_enorm_le_fullDyadicTailSupEnorm
    (lam : ℝ) (j : ℤ) (f : L0Infinity) (x : ℝ) :
    ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x‖ₑ ≤
      fullDyadicTailSupEnorm lam j f x := by
  unfold fullDyadicTailSupEnorm
  have hnorm : Tendsto
      (fun n : ℕ ↦ ‖finiteFullDyadicTail lam j n f x‖)
      atTop
      (nhds ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
        lam ((2 : ℝ) ^ (j - 3)) f x‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_finiteFullDyadicTail_atTop lam j f x)
  have henorm : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal ‖finiteFullDyadicTail lam j n f x‖)
      atTop
      (nhds (ENNReal.ofReal
        ‖KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass
          lam ((2 : ℝ) ^ (j - 3)) f x‖)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  rw [← ofReal_norm]
  apply le_of_tendsto henorm
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa only [ofReal_norm] using
      (le_iSup (fun m : ℕ ↦ ‖finiteFullDyadicTail lam j m f x‖ₑ) n)


end
end KrauseLaceyFullDyadicReflection
end QuadraticCarleson
