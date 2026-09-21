/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PositiveNorm

/-! # Discrete Convolution -/

namespace Homogenization

noncomputable section

open scoped BigOperators

/-!
# Finite lower-triangular convolution estimates

This file contains the purely discrete summation step used by the hard
standard-to-overlapping positive comparison.  The analytic estimates produce a
lower-triangular convolution in the depth variables; once the row and column
geometric weights are bounded, the following finite Cauchy-Schwarz argument
turns it into an `l²` estimate.
-/

theorem lowerTriangularConvolution_sq_sum_le
    (N : ℕ) (K : ℝ) (w : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hK_nonneg : 0 ≤ K)
    (hw_nonneg : ∀ j m : ℕ, 0 ≤ w j m)
    (hrow :
      ∀ j ∈ Finset.range (N + 1),
        ∑ m ∈ Finset.range j, w j m ≤ K)
    (hcol :
      ∀ m ∈ Finset.range (N + 1),
        ∑ j ∈ (Finset.range (N + 1)).filter (fun j => m < j), w j m ≤ K) :
    ∑ j ∈ Finset.range (N + 1),
        (∑ m ∈ Finset.range j, w j m * a m) ^ 2
      ≤
        K ^ 2 * ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
  classical
  let J : Finset ℕ := Finset.range (N + 1)
  let T : ℕ → ℝ := fun j => ∑ m ∈ Finset.range j, w j m * (a m) ^ 2
  have hT_nonneg : ∀ j, 0 ≤ T j := by
    intro j
    dsimp [T]
    refine Finset.sum_nonneg ?_
    intro m _hm
    exact mul_nonneg (hw_nonneg j m) (sq_nonneg (a m))
  have hrow_nonneg : ∀ j, 0 ≤ ∑ m ∈ Finset.range j, w j m := by
    intro j
    refine Finset.sum_nonneg ?_
    intro m _hm
    exact hw_nonneg j m
  have hdepth :
      ∀ j ∈ J,
        (∑ m ∈ Finset.range j, w j m * a m) ^ 2 ≤ K * T j := by
    intro j hj
    have hcauchy :
        (∑ m ∈ Finset.range j, w j m * a m) ^ 2 ≤
          (∑ m ∈ Finset.range j, w j m) * T j := by
      dsimp [T]
      exact
        Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
          (s := Finset.range j)
          (r := fun m => w j m * a m)
          (f := fun m => w j m)
          (g := fun m => w j m * (a m) ^ 2)
          (fun m _hm => hw_nonneg j m)
          (fun m _hm => mul_nonneg (hw_nonneg j m) (sq_nonneg (a m)))
          (fun m _hm => le_of_eq (by ring))
    exact hcauchy.trans
      (mul_le_mul_of_nonneg_right (hrow j hj) (hT_nonneg j))
  have hsum_depth :
      ∑ j ∈ J, (∑ m ∈ Finset.range j, w j m * a m) ^ 2
        ≤ ∑ j ∈ J, K * T j := by
    exact Finset.sum_le_sum hdepth
  have hrange_filter :
      ∀ j ∈ J, Finset.range j = J.filter (fun m => m < j) := by
    intro j hj
    ext m
    constructor
    · intro hm
      rw [Finset.mem_filter]
      exact
        ⟨by
          have hj' : j < N + 1 := by
            have : j ∈ Finset.range (N + 1) := hj
            exact Finset.mem_range.mp this
          exact Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hm) hj'),
        Finset.mem_range.mp hm⟩
    · intro h
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp h).2)
  have hT_sum_eq :
      ∑ j ∈ J, T j =
        ∑ m ∈ J, ∑ j ∈ J.filter (fun j => m < j), w j m * (a m) ^ 2 := by
    calc
      ∑ j ∈ J, T j
          =
            ∑ j ∈ J, ∑ m ∈ J.filter (fun m => m < j),
              w j m * (a m) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              dsimp [T]
              rw [hrange_filter j hj]
      _ =
            ∑ j ∈ J, ∑ m ∈ J,
              if m < j then w j m * (a m) ^ 2 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              rw [Finset.sum_filter]
      _ =
            ∑ m ∈ J, ∑ j ∈ J,
              if m < j then w j m * (a m) ^ 2 else 0 := by
              exact Finset.sum_comm
      _ =
            ∑ m ∈ J, ∑ j ∈ J.filter (fun j => m < j),
              w j m * (a m) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro m _hm
              rw [Finset.sum_filter]
  have hT_sum_le :
      ∑ j ∈ J, T j ≤ K * ∑ m ∈ J, (a m) ^ 2 := by
    rw [hT_sum_eq]
    calc
      ∑ m ∈ J, ∑ j ∈ J.filter (fun j => m < j),
          w j m * (a m) ^ 2
          ≤
            ∑ m ∈ J, K * (a m) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro m hm
            calc
              ∑ j ∈ J.filter (fun j => m < j), w j m * (a m) ^ 2
                  =
                    (∑ j ∈ J.filter (fun j => m < j), w j m) *
                      (a m) ^ 2 := by
                    rw [Finset.sum_mul]
              _ ≤ K * (a m) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hcol m hm) (sq_nonneg (a m))
      _ =
            K * ∑ m ∈ J, (a m) ^ 2 := by
            rw [Finset.mul_sum]
  calc
    ∑ j ∈ Finset.range (N + 1),
        (∑ m ∈ Finset.range j, w j m * a m) ^ 2
        =
          ∑ j ∈ J, (∑ m ∈ Finset.range j, w j m * a m) ^ 2 := rfl
    _ ≤ ∑ j ∈ J, K * T j := hsum_depth
    _ = K * ∑ j ∈ J, T j := by
          rw [Finset.mul_sum]
    _ ≤ K * (K * ∑ m ∈ J, (a m) ^ 2) :=
          mul_le_mul_of_nonneg_left hT_sum_le hK_nonneg
    _ = K ^ 2 * ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
          dsimp [J]
          ring

/-- Row sums for the lower-triangular geometric kernel.  The exponent starts at
`1` because `m < j`, but we bound it by the full geometric series starting at
`0`. -/
theorem sum_range_geometric_pow_sub_le_inv {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (j : ℕ) :
    ∑ m ∈ Finset.range j, r ^ (j - m) ≤ (1 - r)⁻¹ := by
  have hreflect :
      (∑ m ∈ Finset.range j, r ^ (j - m)) =
        ∑ m ∈ Finset.range j, r ^ (m + 1) := by
    rw [← Finset.sum_range_reflect (fun m : ℕ => r ^ (m + 1)) j]
    refine Finset.sum_congr rfl ?_
    intro m hm
    congr 1
    have hm_lt : m < j := Finset.mem_range.mp hm
    omega
  calc
    ∑ m ∈ Finset.range j, r ^ (j - m)
        = ∑ m ∈ Finset.range j, r ^ (m + 1) := hreflect
    _ ≤ ∑ m ∈ Finset.range j, r ^ m := by
          refine Finset.sum_le_sum ?_
          intro m _hm
          exact pow_le_pow_of_le_one hr_nonneg hr_lt_one.le (Nat.le_succ m)
    _ = ∑ m ∈ Finset.Ico 0 j, r ^ m := by
          rw [Finset.range_eq_Ico]
    _ ≤ r ^ (0 : ℕ) / (1 - r) :=
          geom_sum_Ico_le_of_lt_one hr_nonneg hr_lt_one
    _ = (1 - r)⁻¹ := by
          simp [div_eq_mul_inv]

/-- Column sums for the lower-triangular geometric kernel. -/
theorem sum_filter_geometric_pow_sub_le_inv {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (N m : ℕ) :
    ∑ j ∈ (Finset.range (N + 1)).filter (fun j => m < j), r ^ (j - m) ≤
      (1 - r)⁻¹ := by
  have hfilter :
      (Finset.range (N + 1)).filter (fun j => m < j) =
        Finset.Ico (m + 1) (N + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro h
      omega
    · intro h
      omega
  calc
    ∑ j ∈ (Finset.range (N + 1)).filter (fun j => m < j), r ^ (j - m)
        = ∑ j ∈ Finset.Ico (m + 1) (N + 1), r ^ (j - m) := by
          rw [hfilter]
    _ =
        ∑ k ∈ Finset.range (N + 1 - (m + 1)), r ^ (k + 1) := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro k _hk
          congr 1
          omega
    _ ≤
        ∑ k ∈ Finset.range (N + 1 - (m + 1)), r ^ k := by
          refine Finset.sum_le_sum ?_
          intro k _hk
          exact pow_le_pow_of_le_one hr_nonneg hr_lt_one.le (Nat.le_succ k)
    _ = ∑ k ∈ Finset.Ico 0 (N + 1 - (m + 1)), r ^ k := by
          rw [Finset.range_eq_Ico]
    _ ≤ r ^ (0 : ℕ) / (1 - r) :=
          geom_sum_Ico_le_of_lt_one hr_nonneg hr_lt_one
    _ = (1 - r)⁻¹ := by
          simp [div_eq_mul_inv]

/-- Finite `l²` boundedness of the lower-triangular geometric convolution. -/
theorem lowerTriangularGeometricConvolution_sq_sum_le
    (N : ℕ) {r : ℝ} (a : ℕ → ℝ)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    ∑ j ∈ Finset.range (N + 1),
        (∑ m ∈ Finset.range j, r ^ (j - m) * a m) ^ 2
      ≤
        ((1 - r)⁻¹) ^ 2 *
          ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
  have hK_nonneg : 0 ≤ (1 - r)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  exact
    lowerTriangularConvolution_sq_sum_le
      (N := N) (K := (1 - r)⁻¹)
      (w := fun j m => r ^ (j - m)) (a := a)
      hK_nonneg
      (fun j m => pow_nonneg hr_nonneg _)
      (fun j _hj => sum_range_geometric_pow_sub_le_inv hr_nonneg hr_lt_one j)
      (fun m _hm => sum_filter_geometric_pow_sub_le_inv hr_nonneg hr_lt_one N m)

/-- Finite-depth summation of a one-depth estimate with a geometric
lower-triangular tail. -/
theorem sq_sum_le_of_le_add_geometric_convolution_sq
    (N : ℕ) {A B r : ℝ} (x a : ℕ → ℝ)
    (hB_nonneg : 0 ≤ B)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        (x j) ^ 2 ≤
          A * (a j) ^ 2 +
            B * (∑ m ∈ Finset.range j, r ^ (j - m) * a m) ^ 2) :
    ∑ j ∈ Finset.range (N + 1), (x j) ^ 2
      ≤
        (A + B * ((1 - r)⁻¹) ^ 2) *
          ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
  let G : ℕ → ℝ :=
    fun j => ∑ m ∈ Finset.range j, r ^ (j - m) * a m
  have hsum_depth :
      ∑ j ∈ Finset.range (N + 1), (x j) ^ 2
        ≤ ∑ j ∈ Finset.range (N + 1), (A * (a j) ^ 2 + B * (G j) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    simpa [G] using hdepth j hj
  have hconv :
      ∑ j ∈ Finset.range (N + 1), (G j) ^ 2
        ≤ ((1 - r)⁻¹) ^ 2 *
          ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
    simpa [G] using
      lowerTriangularGeometricConvolution_sq_sum_le
        (N := N) (r := r) (a := a) hr_nonneg hr_lt_one
  calc
    ∑ j ∈ Finset.range (N + 1), (x j) ^ 2
        ≤ ∑ j ∈ Finset.range (N + 1),
            (A * (a j) ^ 2 + B * (G j) ^ 2) := hsum_depth
    _ =
        A * ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 +
          B * ∑ j ∈ Finset.range (N + 1), (G j) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤
        A * ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 +
          B * (((1 - r)⁻¹) ^ 2 *
            ∑ m ∈ Finset.range (N + 1), (a m) ^ 2) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hconv hB_nonneg)
    _ =
        (A + B * ((1 - r)⁻¹) ^ 2) *
          ∑ m ∈ Finset.range (N + 1), (a m) ^ 2 := by
          ring

end

end Homogenization
