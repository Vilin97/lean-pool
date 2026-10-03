/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarDefs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Generic rational enclosures used by the point checks of `Wt`:
odd Taylor polynomials bracket `arctan` on `[0, ∞)` (monotonicity of the remainder), the shift
`arctan x = π/4 + arctan ((x-1)/(x+1))`, and the Mathlib Taylor remainder bound for `log (1 - u)`.
`Wt_ge` turns four atom bounds into a lower bound for `Wt x`. Written from scratch. -/

public section

open Real

namespace Zeta32.Fstar.PW

/-- `t - t³/3 + t⁵/5 - t⁷/7 ≤ arctan t` for `t ≥ 0`. -/
theorem arctan_ge_S4 {t : ℝ} (ht : 0 ≤ t) : t - t^3/3 + t^5/5 - t^7/7 ≤ arctan t := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => arctan s - (s - s^3/3 + s^5/5 - s^7/7))
      (1 / (1 + s^2) - (1 - s^2 + s^4 - s^6)) s := by
    intro s
    have := (hasDerivAt_arctan s).sub ((((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const
      3)).add
      ((hasDerivAt_pow 5 s).div_const 5)).sub ((hasDerivAt_pow 7 s).div_const 7))
    convert this using 1
    · rfl
    · norm_num
  have hmono : MonotoneOn (fun s => arctan s - (s - s^3/3 + s^5/5 - s^7/7)) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => (hd s).hasDerivWithinAt)
    intro s _
    have h1 : (0:ℝ) < 1 + s^2 := by positivity
    have : 1 / (1 + s^2) - (1 - s^2 + s^4 - s^6) = s^8 / (1 + s^2) := by field_simp; ring
    rw [this]; positivity
  have := hmono Set.self_mem_Ici ht ht
  simp only [arctan_zero] at this
  linarith

/-- `arctan t ≤ t - t³/3 + t⁵/5` for `t ≥ 0`. -/
theorem arctan_le_S3 {t : ℝ} (ht : 0 ≤ t) : arctan t ≤ t - t^3/3 + t^5/5 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => (s - s^3/3 + s^5/5) - arctan s)
      ((1 - s^2 + s^4) - 1 / (1 + s^2)) s := by
    intro s
    have := (((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const 3)).add
      ((hasDerivAt_pow 5 s).div_const 5)).sub (hasDerivAt_arctan s)
    convert this using 1
    · rfl
    · norm_num
  have hmono : MonotoneOn (fun s => (s - s^3/3 + s^5/5) - arctan s) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => (hd s).hasDerivWithinAt)
    intro s _
    have h1 : (0:ℝ) < 1 + s^2 := by positivity
    have : (1 - s^2 + s^4) - 1 / (1 + s^2) = s^6 / (1 + s^2) := by field_simp; ring
    rw [this]; positivity
  have := hmono Set.self_mem_Ici ht ht
  simp only [arctan_zero] at this
  linarith

/-- `arctan x = π/4 + arctan ((x-1)/(x+1))` for `x > -1`. -/
theorem arctan_shift {x : ℝ} (hx : -1 < x) : arctan x = π / 4 + arctan ((x - 1) / (x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith
  have hlt : 1 * ((x - 1) / (x + 1)) < 1 := by
    rw [one_mul, div_lt_one hx1]; linarith
  have h := arctan_add hlt
  rw [arctan_one] at h
  have hn : 1 + (x - 1) / (x + 1) = 2 * x / (x + 1) := by field_simp; ring
  have hd : 1 - 1 * ((x - 1) / (x + 1)) = 2 / (x + 1) := by field_simp; ring
  have he : (1 + (x - 1) / (x + 1)) / (1 - 1 * ((x - 1) / (x + 1))) = x := by
    rw [hn, hd]
    field_simp
  rw [he] at h
  linarith

/-- Lower bound for `arctan x`, `x ≥ 1`. -/
theorem arctan_ge_shift_pos {x : ℝ} (hx : 1 ≤ x) :
    3.141592 / 4 + ((x-1)/(x+1) - ((x-1)/(x+1))^3/3 + ((x-1)/(x+1))^5/5 - ((x-1)/(x+1))^7/7)
      ≤ arctan x := by
  rw [arctan_shift (by linarith)]
  have := arctan_ge_S4 (t := (x-1)/(x+1)) (div_nonneg (by linarith) (by linarith))
  linarith [pi_gt_d6]

/-- Lower bound for `arctan x`, `0 ≤ x ≤ 1`. -/
theorem arctan_ge_shift_neg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    3.141592 / 4 - ((1-x)/(1+x) - ((1-x)/(1+x))^3/3 + ((1-x)/(1+x))^5/5) ≤ arctan x := by
  rw [arctan_shift (by linarith)]
  have hs : (x - 1) / (x + 1) = -((1 - x) / (1 + x)) := by
    rw [neg_div', neg_sub, add_comm]
  rw [hs, arctan_neg]
  have := arctan_le_S3 (t := (1-x)/(1+x)) (div_nonneg (by linarith) (by linarith))
  linarith [pi_gt_d6]

theorem log_one_sub_le {u : ℝ} (h : |u| < 1) (n : ℕ) :
    log (1 - u) ≤ -(∑ i ∈ Finset.range n, u^(i+1)/(i+1)) + |u|^(n+1)/(1 - |u|) := by
  have := (abs_le.mp (abs_log_sub_add_sum_range_le h n)).2
  linarith

theorem log_one_sub_ge {u : ℝ} (h : |u| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, u^(i+1)/(i+1)) - |u|^(n+1)/(1 - |u|) ≤ log (1 - u) := by
  have := (abs_le.mp (abs_log_sub_add_sum_range_le h n)).1
  linarith

/-- Lower bound for `log (1 + t)`, `0 ≤ t < 1`. -/
theorem log_one_add_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, (-t)^(i+1)/(i+1)) - t^(n+1)/(1 - t) ≤ log (1 + t) := by
  have ha : |-t| = t := by rw [abs_neg, abs_of_nonneg h0]
  have := log_one_sub_ge (u := -t) (by rw [ha]; exact h1) n
  rw [ha, sub_neg_eq_add] at this
  exact this

/-- Upper bound for `log y` after scaling by `2^k`. -/
theorem log_le_scaled {y : ℝ} (hy : 0 < y) (k n : ℕ) (hu : |1 - y / 2 ^ k| < 1) :
    log y ≤ k * 0.6931471808 +
      (-(∑ i ∈ Finset.range n, (1 - y/2^k)^(i+1)/(i+1)) + |1 - y/2^k|^(n+1)/(1 - |1 - y/2^k|)) := by
  have h2 : (0:ℝ) < 2^k := by positivity
  have hsplit : log y = k * log 2 + log (1 - (1 - y / 2^k)) := by
    rw [sub_sub_cancel, log_div hy.ne' h2.ne', log_pow]; ring
  rw [hsplit]
  have h1 := log_one_sub_le hu n
  have h3 : (k:ℝ) * log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left log_two_lt_d9.le (Nat.cast_nonneg k)
  linarith

/-- `Wt` in the form without `arctan (1/x)` (the reciprocal identity), for `x > 0`. -/
theorem Wt_eq {x : ℝ} (hx : 0 < x) :
    Wt x = (2/3) * (2 * x * arctan x - log (1 + x^2) + π * x / 4 - x * arctan (x/5) / 2
      + 5 * log (1 + x^2/25) / 4) := by
  have h1 : arctan (1/x) = π/2 - arctan x := by
    rw [one_div, arctan_inv_of_pos hx]
  have h5 : arctan (5/x) = π/2 - arctan (x/5) := by
    rw [show 5/x = (x/5)⁻¹ by field_simp, arctan_inv_of_pos (by positivity)]
  rw [Wt, h1, h5]
  ring

/-- Four atom bounds give a lower bound for `Wt x`. -/
theorem Wt_ge {x A L B M : ℝ} (hx : 0 < x) (hA : A ≤ arctan x) (hL : log (1 + x ^ 2) ≤ L)
    (hB : arctan (x / 5) ≤ B) (hM : M ≤ log (1 + x ^ 2 / 25)) :
    (2/3) * (2 * x * A - L + 3.141592 * x / 4 - x * B / 2 + 5 * M / 4) ≤ Wt x := by
  rw [Wt_eq hx]
  have h1 := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 2 * x)
  have h2 := mul_le_mul_of_nonneg_left hB hx.le
  have h3 : 3.141592 * x ≤ π * x := mul_le_mul_of_nonneg_right pi_gt_d6.le hx.le
  nlinarith

end Zeta32.Fstar.PW
