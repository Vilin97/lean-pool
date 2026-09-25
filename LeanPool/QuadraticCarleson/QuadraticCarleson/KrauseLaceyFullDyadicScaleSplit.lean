/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyZeroPhaseLowControl

/-!
# Splitting full dyadic suffixes at the unit scale

This file gives the exact finite-sum identities needed to separate the
all-low part of a quadratic suffix from the already controlled positive-scale
part. The identities introduce no analytic hypothesis or estimate.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyFullDyadicScaleSplit

open KrauseLaceyFullDyadicReflection
open KrauseLaceyZeroPhaseLowControl


noncomputable
section

/-- Number of consecutive scales starting at `j` that end immediately before
the positive-scale block beginning at scale `1`. -/
def unitScaleSplitLength (j : ℤ) : ℕ := (1 - j).toNat

theorem add_unitScaleSplitLength (j : ℤ) (hj : j ≤ 1) :
    j + (unitScaleSplitLength j : ℤ) = 1 := by
  unfold unitScaleSplitLength
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj)]
  omega

theorem unitScaleSplitLength_le {j : ℤ} {N : ℕ}
    (hj : j ≤ 1) (hreach : 1 ≤ j + (N : ℤ)) :
    unitScaleSplitLength j ≤ N := by
  have hcast : ((unitScaleSplitLength j : ℕ) : ℤ) = 1 - j := by
    unfold unitScaleSplitLength
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj)]
  exact_mod_cast (show (unitScaleSplitLength j : ℤ) ≤ (N : ℤ) by omega)

/-- A consecutive full-dyadic tail splits exactly after any prescribed
number of terms. -/
theorem finiteFullDyadicTail_add
    (lam : ℝ) (j : ℤ) (a b : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    finiteFullDyadicTail lam j (a + b) f x =
      finiteFullDyadicTail lam j a f x +
        finiteFullDyadicTail lam (j + (a : ℤ)) b f x := by
  unfold finiteFullDyadicTail
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun k : ℤ ↦ fullDyadicConvolution lam k f x)
  omega

/-- Splitting the available scale interval at `L ≤ N` bounds its moving
suffix maximum by the two suffix maxima on the resulting consecutive
subintervals. The estimate has no dependence on either cardinality. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_le_split
    (lam : ℝ) (j : ℤ) {N L : ℕ} (hLN : L ≤ N)
    (f : ℝ → ℂ) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm lam j N f x : ℝ≥0∞) ≤
      (finiteFullDyadicSuffixMaxNNNorm lam j L f x : ℝ≥0∞) +
        (finiteFullDyadicSuffixMaxNNNorm lam (j + (L : ℤ)) (N - L) f x : ℝ≥0∞) := by
  unfold finiteFullDyadicSuffixMaxNNNorm
  simp only [ENNReal.coe_finset_sup, ← enorm_eq_nnnorm]
  apply Finset.sup_le
  intro m hm
  have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  change ‖finiteFullDyadicSuffix lam j N m f x‖ₑ ≤ _
  by_cases hmL : m ≤ L
  · have hlength : N - m = (L - m) + (N - L) := by omega
    have hscale : j + (m : ℤ) + ((L - m : ℕ) : ℤ) = j + (L : ℤ) := by omega
    unfold finiteFullDyadicSuffix
    rw [hlength, finiteFullDyadicTail_add, hscale]
    have hlow := Finset.le_sup (f := fun r : ℕ ↦
        ‖finiteFullDyadicTail lam (j + (r : ℤ)) (L - r) f x‖ₑ)
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hmL))
    have hhigh := Finset.le_sup (f := fun r : ℕ ↦
        ‖finiteFullDyadicTail lam (j + (L : ℤ) + (r : ℤ))
          (N - L - r) f x‖ₑ)
        (Finset.mem_range.mpr (Nat.zero_lt_succ (N - L)))
    apply (enorm_add_le _ _).trans
    exact add_le_add hlow (by simpa using hhigh)
  · have hLm : L ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmL)
    have hscale : j + (m : ℤ) = j + (L : ℤ) + ((m - L : ℕ) : ℤ) := by omega
    have hlength : N - m = N - L - (m - L) := by omega
    have hmshift : m - L < N - L + 1 := by omega
    unfold finiteFullDyadicSuffix
    rw [hscale, hlength]
    calc
      ‖finiteFullDyadicTail lam
          (j + (L : ℤ) + ((m - L : ℕ) : ℤ)) (N - L - (m - L)) f x‖ₑ ≤
          (Finset.range (N - L + 1)).sup (fun r : ℕ ↦
            ‖finiteFullDyadicTail lam (j + (L : ℤ) + (r : ℤ))
              (N - L - r) f x‖ₑ) :=
        Finset.le_sup (f := fun r : ℕ ↦
          ‖finiteFullDyadicTail lam (j + (L : ℤ) + (r : ℤ))
            (N - L - r) f x‖ₑ) (Finset.mem_range.mpr hmshift)
      _ ≤ (Finset.range (L + 1)).sup (fun r : ℕ ↦
            ‖finiteFullDyadicTail lam (j + (r : ℤ)) (L - r) f x‖ₑ) +
          (Finset.range (N - L + 1)).sup (fun r : ℕ ↦
            ‖finiteFullDyadicTail lam (j + (L : ℤ) + (r : ℤ))
              (N - L - r) f x‖ₑ) := by
        exact le_add_left le_rfl

/-- In the crossing case, choose the split length so that the second block
starts at dyadic scale `1`. The first block is then controlled entirely by
the phase-zero Hilbert term and the common maximal-function errors. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_one_le_lowControl_add_high
    {j : ℤ} {N L : ℕ} (hLN : L ≤ N) (hscale : j + (L : ℤ) = 1)
    {f : ℝ → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hf2 : MemLp f 2) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) ≤
      ((2 * quadraticHilbertMaximalTruncation 0 f x +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
        (finiteFullDyadicSuffixMaxNNNorm 1 1 (N - L) f x : ℝ≥0∞) := by
  calc
    (finiteFullDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) ≤
        (finiteFullDyadicSuffixMaxNNNorm 1 j L f x : ℝ≥0∞) +
          (finiteFullDyadicSuffixMaxNNNorm 1 (j + (L : ℤ)) (N - L) f x : ℝ≥0∞) :=
      coe_finiteFullDyadicSuffixMaxNNNorm_le_split 1 j hLN f x
    _ ≤ ((2 * quadraticHilbertMaximalTruncation 0 f x +
            16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          ENNReal.ofReal (16 * Real.pi) *
            centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          (finiteFullDyadicSuffixMaxNNNorm 1 (j + (L : ℤ)) (N - L) f x : ℝ≥0∞) :=
      add_le_add
        (coe_finiteFullDyadicSuffixMaxNNNorm_one_low_le_hilbertMaximal_add_maximal
          hscale.le hfm hfi hf2 x) le_rfl
    _ = ((2 * quadraticHilbertMaximalTruncation 0 f x +
            16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          ENNReal.ofReal (16 * Real.pi) *
            centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          (finiteFullDyadicSuffixMaxNNNorm 1 1 (N - L) f x : ℝ≥0∞) := by
      rw [hscale]

/-- Canonical form of the crossing-scale estimate, with the split length
computed from the starting scale. -/
theorem coe_finiteFullDyadicSuffixMaxNNNorm_one_le_canonicalLowControl_add_high
    {j : ℤ} {N : ℕ} (hj : j ≤ 1) (hreach : 1 ≤ j + (N : ℤ))
    {f : ℝ → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hf2 : MemLp f 2) (x : ℝ) :
    (finiteFullDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) ≤
      ((2 * quadraticHilbertMaximalTruncation 0 f x +
          16 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
        ENNReal.ofReal (16 * Real.pi) *
          centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
        (finiteFullDyadicSuffixMaxNNNorm 1 1
          (N - unitScaleSplitLength j) f x : ℝ≥0∞) := by
  exact coe_finiteFullDyadicSuffixMaxNNNorm_one_le_lowControl_add_high
    (unitScaleSplitLength_le hj hreach) (add_unitScaleSplitLength j hj)
      hfm hfi hf2 x


end
end KrauseLaceyFullDyadicScaleSplit
end QuadraticCarleson
