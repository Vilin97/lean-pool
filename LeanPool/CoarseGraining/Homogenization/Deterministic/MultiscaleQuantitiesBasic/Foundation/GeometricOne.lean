/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Basic

/-! # Geometric One -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem geometricDiscount_nonneg {s q : ℝ} (hsq : 0 ≤ s * q) :
    0 ≤ geometricDiscount s q := by
  unfold geometricDiscount
  by_cases hzero : s * q = 0
  · simp [hzero]
  · have hsq_pos : 0 < s * q := lt_of_le_of_ne hsq (by simpa [eq_comm] using hzero)
    have hneg : -s * q < 0 := by nlinarith
    have hpow_lt : Real.rpow (3 : ℝ) (-s * q) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
    linarith

theorem geometricDiscount_pos {s q : ℝ} (hsq : 0 < s * q) :
    0 < geometricDiscount s q := by
  unfold geometricDiscount
  have hneg : -s * q < 0 := by nlinarith
  have hpow_lt : Real.rpow (3 : ℝ) (-s * q) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  linarith

theorem geometricWeight_nonneg {s q : ℝ} (n : ℕ) (hsq : 0 ≤ s * q) :
    0 ≤ geometricWeight s q n := by
  unfold geometricWeight
  refine mul_nonneg (geometricDiscount_nonneg hsq) ?_
  exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem geometricWeight_pos {s q : ℝ} (n : ℕ) (hsq : 0 < s * q) :
    0 < geometricWeight s q n := by
  unfold geometricWeight
  refine mul_pos (geometricDiscount_pos hsq) ?_
  exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _

theorem summable_geometricWeight_one {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => geometricWeight s 1 n) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hweight :
      ∀ n : ℕ, geometricWeight s 1 n = geometricDiscount s 1 * r ^ n := by
    intro n
    rw [geometricWeight_one_eq]
    calc
      geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (n : ℝ))
          = geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s)) ^ n := by
              congr 1
              calc
                Real.rpow (3 : ℝ) (-s * (n : ℝ))
                    = Real.rpow (3 : ℝ) ((-s) * (n : ℝ)) := by ring
                _ = Real.rpow (Real.rpow (3 : ℝ) (-s)) (n : ℝ) := by
                      simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s) (n : ℝ))
                _ = (Real.rpow (3 : ℝ) (-s)) ^ n := by
                      exact Real.rpow_natCast (Real.rpow (3 : ℝ) (-s)) n
      _ = geometricDiscount s 1 * r ^ n := by simp [r]
  have hfun :
      (fun n : ℕ => geometricWeight s 1 n) = fun n => geometricDiscount s 1 * r ^ n := by
    funext n
    exact hweight n
  rw [hfun]
  exact (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left (geometricDiscount s 1)

theorem summable_geometricWeight_one_of_lt {H : ℕ → ℝ}
    (hnonneg : ∀ n : ℕ, 0 ≤ H n) {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hsum_t : Summable (fun n : ℕ => geometricWeight t 1 n * H n)) :
    Summable (fun n : ℕ => geometricWeight s 1 n * H n) := by
  let C : ℝ := geometricDiscount s 1 / geometricDiscount t 1
  have hs : 0 < s := lt_trans ht hts
  have hdisc_t_pos : 0 < geometricDiscount t 1 := by
    exact geometricDiscount_pos (by simpa using ht)
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hscaled : Summable (fun n : ℕ => C * (geometricWeight t 1 n * H n)) := hsum_t.mul_left C
  refine Summable.of_nonneg_of_le ?_ ?_ hscaled
  · intro n
    exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) (hnonneg n)
  · intro n
    have hpow :
        Real.rpow (3 : ℝ) (-s * (n : ℝ)) ≤ Real.rpow (3 : ℝ) (-t * (n : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) ?_
      nlinarith
    calc
      geometricWeight s 1 n * H n
          = geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s * (n : ℝ)) * H n) := by
              rw [geometricWeight_one_eq]
              ring
      _ ≤ geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-t * (n : ℝ)) * H n) := by
            refine mul_le_mul_of_nonneg_left ?_ hdisc_s_pos.le
            exact mul_le_mul_of_nonneg_right hpow (hnonneg n)
      _ = C * (geometricWeight t 1 n * H n) := by
            dsimp [C]
            rw [geometricWeight_one_eq]
            field_simp [hdisc_t_pos.ne']
            simp [mul_comm]

theorem tsum_geometricWeight_one_eq_one {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, geometricWeight s 1 n = 1 := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hweight :
      ∀ n : ℕ, geometricWeight s 1 n = geometricDiscount s 1 * r ^ n := by
    intro n
    rw [geometricWeight_one_eq]
    calc
      geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (n : ℝ))
          = geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s)) ^ n := by
              congr 1
              calc
                Real.rpow (3 : ℝ) (-s * (n : ℝ))
                    = Real.rpow (3 : ℝ) ((-s) * (n : ℝ)) := by ring
                _ = Real.rpow (Real.rpow (3 : ℝ) (-s)) (n : ℝ) := by
                      simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s) (n : ℝ))
                _ = (Real.rpow (3 : ℝ) (-s)) ^ n := by
                      exact Real.rpow_natCast (Real.rpow (3 : ℝ) (-s)) n
      _ = geometricDiscount s 1 * r ^ n := by simp [r]
  calc
    ∑' n : ℕ, geometricWeight s 1 n = ∑' n : ℕ, geometricDiscount s 1 * r ^ n := by
      exact tsum_congr hweight
    _ = geometricDiscount s 1 * ∑' n : ℕ, r ^ n := by rw [tsum_mul_left]
    _ = geometricDiscount s 1 * (1 - r)⁻¹ := by
          rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
    _ = (1 - r) * (1 - r)⁻¹ := by
          simp [r, geometricDiscount_one_eq]
    _ = 1 := by
          have hne : 1 - r ≠ 0 := by
            linarith
          simpa using (mul_inv_cancel₀ hne)


end

end Homogenization
