/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarDefs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Generic tools for the rational point checks of `ρ_{a₋}` and `ℓ(a)`.

* `lser_le_log`: `log z ≥ 2(t + t³/3 + t⁵/5 + t⁷/7)`, `t = (z−1)/(z+1)`, for `z ≥ 1` (partial
sum of the
  nonnegative series `log(1+t) − log(1−t) = Σ 2t^(2k+1)/(2k+1)`, Mathlib
  `hasSum_log_sub_log_of_abs_lt_one`).
* `log_ge`, `log_ge'`, `log_le`: argument reduction by `2^m` with Mathlib's `log_two_gt_d9`,
`log_two_lt_d9`.
* `G_ge`, `G_le`: `Gfun` is increasing in `s = √(a²−x²)` and decreasing in `U = √(c²+a²)`.
* `rho_ge_of`: one point `R ≤ ρ_{a₋}(x)` from rational brackets of the square roots and one log
lower bound.
Written from scratch. -/

public section

open Real
namespace Zeta32.Fstar.B2
noncomputable section

/-- Partial sum `2(t + t³/3 + t⁵/5 + t⁷/7)` of `log((1+t)/(1−t))`. -/
@[expose]
def lser (t : ℝ) : ℝ := 2 * (t + t ^ 3 / 3 + t ^ 5 / 5 + t ^ 7 / 7)

theorem lser_le_log {z : ℝ} (hz : 1 ≤ z) : lser ((z - 1) / (z + 1)) ≤ log z := by
  set t := (z - 1) / (z + 1) with ht
  have hz1 : 0 < z + 1 := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hz1.le
  have ht1 : t < 1 := by rw [ht, div_lt_one hz1]; linarith
  have hs := hasSum_log_sub_log_of_abs_lt_one (x := t) (by rwa [abs_of_nonneg ht0])
  have hsum := sum_le_hasSum (Finset.range 4)
    (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg ht0 _)) hs
  have h1 : 1 + t = 2 * z / (z + 1) := by rw [ht]; field_simp; ring
  have h2 : 1 - t = 2 / (z + 1) := by rw [ht]; field_simp; ring
  have heq : log (1 + t) - log (1 - t) = log z := by
    rw [← log_div (by linarith) (by linarith), h1, h2]
    congr 1
    field_simp
  rw [heq] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  unfold lser
  norm_num at hsum
  linarith

/-- Lower bound `log y ≥ m·log 2 + lser(...)` for `y ≥ 2^m`. -/
theorem log_ge (y : ℝ) (m : ℕ) (h : 2 ^ m ≤ y) :
    m * (6931471803 / 10 ^ 10) + lser ((y / 2 ^ m - 1) / (y / 2 ^ m + 1)) ≤ log y := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hz : 1 ≤ y / 2 ^ m := by rw [le_div_iff₀ h2]; linarith
  have e : log y = m * log 2 + log (y / 2 ^ m) := by
    rw [← log_pow, ← log_mul h2.ne' (by positivity)]
    congr 1
    field_simp
  have hl := lser_le_log hz
  have h2l := log_two_gt_d9
  rw [e]
  have : (m : ℝ) * (6931471803 / 10 ^ 10) ≤ m * log 2 :=
    mul_le_mul_of_nonneg_left (by norm_num at h2l ⊢; linarith) (Nat.cast_nonneg m)
  linarith

/-- Lower bound `log y ≥ −m·log 2 + lser(...)` for `2^m·y ≥ 1`. -/
theorem log_ge' (y : ℝ) (m : ℕ) (h : 1 ≤ 2 ^ m * y) :
    -(m * (6931471808 / 10 ^ 10)) + lser ((2 ^ m * y - 1) / (2 ^ m * y + 1)) ≤ log y := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hy : 0 < y := by
    by_contra hy; push Not at hy
    nlinarith
  have e : log (2 ^ m * y) = m * log 2 + log y := by
    rw [log_mul h2.ne' hy.ne', log_pow]
  have hl := lser_le_log h
  have h2l := log_two_lt_d9
  have : (m : ℝ) * log 2 ≤ m * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left (by norm_num at h2l ⊢; linarith) (Nat.cast_nonneg m)
  linarith

/-- Upper bound `log y ≤ m·log 2 − lser(...)` for `0 < y ≤ 2^m`. -/
theorem log_le (y : ℝ) (m : ℕ) (hy : 0 < y) (h : y ≤ 2 ^ m) :
    log y ≤ m * (6931471808 / 10 ^ 10) - lser ((2 ^ m / y - 1) / (2 ^ m / y + 1)) := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hz : 1 ≤ 2 ^ m / y := by rw [le_div_iff₀ hy]; linarith
  have e : log (2 ^ m / y) = m * log 2 - log y := by
    rw [log_div h2.ne' hy.ne', log_pow]
  have hl := lser_le_log hz
  have h2l := log_two_lt_d9
  have : (m : ℝ) * log 2 ≤ m * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left (by norm_num at h2l ⊢; linarith) (Nat.cast_nonneg m)
  linarith

theorem le_sqrt_of_sq_le {l y : ℝ} (hl : 0 ≤ l) (h : l ^ 2 ≤ y) : l ≤ √y := by
  calc l = √(l ^ 2) := (sqrt_sq hl).symm
    _ ≤ √y := sqrt_le_sqrt h

theorem sqrt_le_of_le_sq {u y : ℝ} (hu : 0 ≤ u) (h : y ≤ u ^ 2) : √y ≤ u := by
  calc √y ≤ √(u ^ 2) := sqrt_le_sqrt h
    _ = u := sqrt_sq hu

/-- `Gfun` from below: smaller `s`, larger `U`. -/
theorem G_ge {a c x sl Uh : ℝ} (hx : 0 < x) (hxa : x ≤ a) (hsl0 : 0 ≤ sl) (hsl : sl ≤ √(a ^ 2 -
  x ^ 2))
    (hU : √(c ^ 2 + a ^ 2) ≤ Uh) : log ((Uh + sl) / (Uh - sl)) ≤ Gfun a c x := by
  have hs0 := sqrt_nonneg (a ^ 2 - x ^ 2)
  have hsU : √(a ^ 2 - x ^ 2) < √(c ^ 2 + a ^ 2) :=
    sqrt_lt_sqrt (by nlinarith) (by nlinarith [sq_nonneg c])
  have hU0 := sqrt_nonneg (c ^ 2 + a ^ 2)
  unfold Gfun
  apply log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hU hsl0, mul_le_mul_of_nonneg_left hsl (hU0.trans hU)]

/-- `Gfun` from above: larger `s`, smaller `U`. -/
theorem G_le {a c x sh Ul : ℝ} (hsh : √(a ^ 2 - x ^ 2) ≤ sh) (hU : Ul ≤ √(c ^ 2 + a ^ 2)) (hshU
  : sh < Ul) :
    Gfun a c x ≤ log ((Ul + sh) / (Ul - sh)) := by
  have hs0 := sqrt_nonneg (a ^ 2 - x ^ 2)
  have hsh0 : 0 ≤ sh := hs0.trans hsh
  unfold Gfun
  apply log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hU hsh0, mul_le_mul_of_nonneg_left hsh (hsh0.trans hshU.le)]

/-- One point of `ρ_{a₋}`: `ρ = (G₀ + 4G₁ − G₅)/(12π)`, each `G` bracketed through rational `s`,
`U`,
the three logs merged into `log P`. -/
theorem rho_ge_of {x sl sh U1 U5 P R : ℝ} (hx : 0 < x) (hxa : x ≤ aMinus)
    (hsl0 : 0 ≤ sl) (hsl : sl ^ 2 ≤ aMinus ^ 2 - x ^ 2) (hsh0 : 0 ≤ sh) (hsh : aMinus ^ 2 - x ^
      2 ≤ sh ^ 2)
    (hU10 : 0 ≤ U1) (hU1 : 1 + aMinus ^ 2 ≤ U1 ^ 2) (hU50 : 0 ≤ U5) (hU5 : U5 ^ 2 ≤ 25 + aMinus ^ 2)
    (hshU5 : sh < U5) (hP0 : 0 < P)
    (hP : P ≤ (aMinus + sl) / (aMinus - sl) * ((U1 + sl) / (U1 - sl)) ^ 4 / ((U5 + sh) / (U5 - sh)))
    (hR0 : 0 ≤ R) (hR : 12 * (31416 / 10000) * R ≤ log P) : R ≤ rhoA aMinus x := by
  have ha : (0 : ℝ) < aMinus := by norm_num [aMinus]
  have hsl' : sl ≤ √(aMinus ^ 2 - x ^ 2) := le_sqrt_of_sq_le hsl0 hsl
  have hsh' : √(aMinus ^ 2 - x ^ 2) ≤ sh := sqrt_le_of_le_sq hsh0 hsh
  have hsa : √(aMinus ^ 2 - x ^ 2) < aMinus := by
    calc √(aMinus ^ 2 - x ^ 2) < √(aMinus ^ 2) := sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      _ = aMinus := sqrt_sq ha.le
  have hU1' : √((1 : ℝ) ^ 2 + aMinus ^ 2) ≤ U1 := sqrt_le_of_le_sq hU10 (by linarith)
  have hU5' : U5 ≤ √((5 : ℝ) ^ 2 + aMinus ^ 2) := le_sqrt_of_sq_le hU50 (by linarith)
  have hU0' : √((0 : ℝ) ^ 2 + aMinus ^ 2) ≤ aMinus := sqrt_le_of_le_sq ha.le (by linarith)
  have hsla : sl < aMinus := lt_of_le_of_lt hsl' hsa
  have hU1a : aMinus ≤ √((1 : ℝ) ^ 2 + aMinus ^ 2) := le_sqrt_of_sq_le ha.le (by linarith)
  have hslU1 : sl < U1 := by linarith
  have g0 := G_ge hx hxa hsl0 hsl' hU0'
  have g1 := G_ge hx hxa hsl0 hsl' hU1'
  have g5 := G_le hsh' hU5' hshU5
  have p0 : 0 < (aMinus + sl) / (aMinus - sl) := div_pos (by linarith) (by linarith)
  have p1 : 0 < (U1 + sl) / (U1 - sl) := div_pos (by linarith) (by linarith)
  have p5 : 0 < (U5 + sh) / (U5 - sh) := div_pos (by linarith) (by linarith)
  have hlog := log_le_log hP0 hP
  rw [log_div (by positivity) p5.ne', log_mul p0.ne' (by positivity), log_pow] at hlog
  unfold rhoA
  rw [le_div_iff₀ (by positivity)]
  have hpi := mul_le_mul_of_nonneg_left pi_lt_d4.le hR0
  norm_num at hlog hpi ⊢
  nlinarith

end
end Zeta32.Fstar.B2
