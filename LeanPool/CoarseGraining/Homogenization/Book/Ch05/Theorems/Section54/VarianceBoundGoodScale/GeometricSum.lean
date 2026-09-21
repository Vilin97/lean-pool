/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.Basic

/-! # Geometric Sum -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open scoped BigOperators

noncomputable section

/-!
# Elementary real estimates for the variance-bound sum

This file collects the low-level nonnegativity and square-root estimates used
when summing the beta-weighted fluctuation bounds.
-/

/-- The square root dominates `δ` on `[0, 1]`. -/
theorem le_sqrt_of_nonneg_of_le_one {δ : ℝ} (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1) :
    δ ≤ Real.sqrt δ := by
  have hsq : δ ^ 2 ≤ (Real.sqrt δ) ^ 2 := by
    rw [Real.sq_sqrt hδ_nonneg]
    nlinarith
  exact (sq_le_sq₀ hδ_nonneg (Real.sqrt_nonneg δ)).1 hsq

/-- In the manuscript range `0 < δ ≤ 1/2`, the square root dominates `δ`. -/
theorem le_sqrt_of_pos_of_le_half {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le_half : δ ≤ 1 / 2) :
    δ ≤ Real.sqrt δ :=
  le_sqrt_of_nonneg_of_le_one hδ_pos.le (by linarith)

/-- The square root of an admissible `δ` is nonnegative. -/
theorem sqrt_nonneg_of_pos {δ : ℝ} (_hδ_pos : 0 < δ) :
    0 ≤ Real.sqrt δ :=
  Real.sqrt_nonneg δ

/-- A beta-weighted nonnegative term is nonnegative. -/
theorem varianceWeight_mul_nonneg {β x : ℝ} {m j : ℕ} (hx : 0 ≤ x) :
    0 ≤ varianceWeight β m j * x :=
  mul_nonneg (varianceWeight_nonneg β m j) hx

/-- A finite beta-weighted sum of nonnegative terms is nonnegative. -/
theorem sum_Icc_varianceWeight_mul_nonneg {β : ℝ} {m : ℕ} {f : ℕ → ℝ}
    (hf : ∀ j, j ∈ Finset.Icc 1 m → 0 ≤ f j) :
    0 ≤ ∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * f j := by
  refine Finset.sum_nonneg ?_
  intro j hj
  exact varianceWeight_mul_nonneg (hf j hj)

/-- Multiplication by a beta weight preserves an upper bound between
nonnegative terms. -/
theorem varianceWeight_mul_le_mul {β x y : ℝ} {m j : ℕ}
    (hxy : x ≤ y) :
    varianceWeight β m j * x ≤ varianceWeight β m j * y :=
  mul_le_mul_of_nonneg_left hxy (varianceWeight_nonneg β m j)

/-- Sumwise version of `varianceWeight_mul_le_mul`. -/
theorem sum_Icc_varianceWeight_mul_le_mul {β : ℝ} {m : ℕ} {f g : ℕ → ℝ}
    (hfg : ∀ j, j ∈ Finset.Icc 1 m → f j ≤ g j) :
    (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * f j) ≤
      ∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * g j := by
  refine Finset.sum_le_sum ?_
  intro j hj
  exact varianceWeight_mul_le_mul (hfg j hj)

/-- A constant can be pulled through a beta-weighted finite sum. -/
theorem sum_Icc_varianceWeight_mul_const (β c : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * c) =
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) * c := by
  rw [Finset.sum_mul]

/-- If `C` is nonnegative, enlarging a beta-weighted sum by a nonnegative
constant preserves inequalities. -/
theorem sum_Icc_varianceWeight_mul_le_const_mul {β C : ℝ} {m : ℕ} {f : ℕ → ℝ}
    (hf : ∀ j, j ∈ Finset.Icc 1 m → f j ≤ C) :
    (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j * f j) ≤
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) * C := by
  rw [← sum_Icc_varianceWeight_mul_const β C m]
  exact sum_Icc_varianceWeight_mul_le_mul hf

/-- The finite beta-weight sum is bounded by the full geometric tail. -/
theorem sum_Icc_varianceWeight_le_inv_geometricDiscount {β : ℝ} (hβ : 0 < β)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) ≤
      (geometricDiscount β 1)⁻¹ := by
  classical
  let f : ℕ → ℝ := fun k => Real.rpow (3 : ℝ) (-β * (k : ℝ))
  let s : Finset ℕ := (Finset.Icc 1 m).image fun j => m - j
  have hinj : Set.InjOn (fun j => m - j) (Finset.Icc 1 m) := by
    intro a ha b hb hab
    have ha_le : a ≤ m := (Finset.mem_Icc.mp ha).2
    have hb_le : b ≤ m := (Finset.mem_Icc.mp hb).2
    exact (tsub_right_inj ha_le hb_le).1 hab
  have hsum_image :
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) =
        ∑ k ∈ s, f k := by
    calc
      (∑ j ∈ Finset.Icc 1 m, varianceWeight β m j) =
          ∑ j ∈ Finset.Icc 1 m, f (m - j) := by
        simp [f, varianceWeight]
      _ = ∑ k ∈ s, f k := by
        simpa [s] using
          (Finset.sum_image (s := Finset.Icc 1 m) (g := fun j => m - j)
            (f := f) hinj).symm
  have hsummable : Summable f :=
    Section52.summable_rpow_three_neg_mul_nat hβ
  rw [hsum_image]
  calc
    (∑ k ∈ s, f k) ≤ ∑' k : ℕ, f k :=
      hsummable.sum_le_tsum s (fun k _hk => Real.rpow_nonneg (by norm_num) _)
    _ = (geometricDiscount β 1)⁻¹ := by
      simpa [f] using Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hβ

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
