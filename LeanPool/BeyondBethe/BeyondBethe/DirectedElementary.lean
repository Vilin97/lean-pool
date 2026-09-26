/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Floor

/-! # Directed Elementary -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- The first `N` terms of twice the inverse-hyperbolic-tangent series,
computed exactly over the rationals. -/
def rationalLogSeries (x : ℚ) (N : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range N, x ^ (2 * k + 1) / (2 * k + 1)

/-- A rational upper bound for the omitted tail when `0 ≤ x < 1`. -/
def rationalLogSeriesError (x : ℚ) (N : ℕ) : ℚ :=
  2 * (x ^ (2 * N + 1) / (1 - x ^ 2))

theorem cast_rationalLogSeries (x : ℚ) (N : ℕ) :
    ((rationalLogSeries x N : ℚ) : ℝ) =
      2 * ∑ k ∈ Finset.range N,
        (x : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  simp [rationalLogSeries]

theorem cast_rationalLogSeriesError (x : ℚ) (N : ℕ) :
    ((rationalLogSeriesError x N : ℚ) : ℝ) =
      2 * ((x : ℝ) ^ (2 * N + 1) / (1 - (x : ℝ) ^ 2)) := by
  simp [rationalLogSeriesError]

/-- The range-reduction parameter taking `y ∈ [1,2]` to `x ∈ [0,1/3]`. -/
def rationalLogUnitParameter (y : ℚ) : ℚ := (y - 1) / (y + 1)

theorem rationalLogUnitParameter_nonneg {y : ℚ} (hy : 1 ≤ y) :
    0 ≤ rationalLogUnitParameter y := by
  exact div_nonneg (sub_nonneg.mpr hy) (by linarith)

theorem rationalLogUnitParameter_lt_one {y : ℚ} (hy : 1 ≤ y) :
    rationalLogUnitParameter y < 1 := by
  rw [rationalLogUnitParameter, div_lt_one (by linarith)]
  linarith

theorem rationalLogUnitParameter_le_third {y : ℚ}
    (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
    rationalLogUnitParameter y ≤ 1 / 3 := by
  rw [rationalLogUnitParameter, div_le_iff₀ (by linarith)]
  linarith

theorem rationalLogUnitParameter_ratio {y : ℚ} (hy : 1 ≤ y) :
    (1 + rationalLogUnitParameter y) /
        (1 - rationalLogUnitParameter y) = y := by
  have hden : y + 1 ≠ 0 := by linarith
  rw [rationalLogUnitParameter]
  field_simp [hden]
  ring

/-- Directed lower approximation to `log y` for a rational `y ∈ [1,2]`. -/
def directedLogUnitLower (y : ℚ) (N : ℕ) : ℚ :=
  rationalLogSeries (rationalLogUnitParameter y) N

/-- Directed upper approximation to `log y` for a rational `y ∈ [1,2]`. -/
def directedLogUnitUpper (y : ℚ) (N : ℕ) : ℚ :=
  rationalLogSeries (rationalLogUnitParameter y) N +
    rationalLogSeriesError (rationalLogUnitParameter y) N

theorem directedLogUnitLower_le_log {y : ℚ} (hy : 1 ≤ y) (N : ℕ) :
    ((directedLogUnitLower y N : ℚ) : ℝ) ≤ Real.log (y : ℝ) := by
  let x := rationalLogUnitParameter y
  have hx0q : 0 ≤ x := rationalLogUnitParameter_nonneg hy
  have hx1q : x < 1 := rationalLogUnitParameter_lt_one hy
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx0q
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx1q
  have h := Real.sum_range_le_log_div hx0 hx1 N
  have hratioq := rationalLogUnitParameter_ratio hy
  have hratio : (1 + (x : ℝ)) / (1 - (x : ℝ)) = (y : ℝ) := by
    exact_mod_cast hratioq
  rw [hratio] at h
  rw [directedLogUnitLower, cast_rationalLogSeries]
  dsimp only [x] at h ⊢
  linarith

theorem log_le_directedLogUnitUpper {y : ℚ} (hy : 1 ≤ y) (N : ℕ) :
    Real.log (y : ℝ) ≤ ((directedLogUnitUpper y N : ℚ) : ℝ) := by
  let x := rationalLogUnitParameter y
  have hx0q : 0 ≤ x := rationalLogUnitParameter_nonneg hy
  have hx1q : x < 1 := rationalLogUnitParameter_lt_one hy
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx0q
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx1q
  have h := Real.log_div_le_sum_range_add hx0 hx1 N
  have hratioq := rationalLogUnitParameter_ratio hy
  have hratio : (1 + (x : ℝ)) / (1 - (x : ℝ)) = (y : ℝ) := by
    exact_mod_cast hratioq
  rw [hratio] at h
  rw [directedLogUnitUpper, Rat.cast_add, cast_rationalLogSeries,
    cast_rationalLogSeriesError]
  dsimp only [x] at h ⊢
  linarith

theorem directedLogUnit_width {y : ℚ} (N : ℕ) :
    directedLogUnitUpper y N - directedLogUnitLower y N =
      rationalLogSeriesError (rationalLogUnitParameter y) N := by
  simp [directedLogUnitUpper, directedLogUnitLower]

/-- The dyadic scale obtained by comparing the leading binary positions of a
positive rational's numerator and denominator. -/
def rationalBinaryScale (q : ℚ) : ℚ :=
  (2 : ℚ) ^ Nat.log 2 q.num.natAbs / (2 : ℚ) ^ Nat.log 2 q.den

/-- The residual after dyadic range reduction. -/
def rationalBinaryResidual (q : ℚ) : ℚ := q / rationalBinaryScale q

theorem positive_rational_num_natAbs_ne_zero {q : ℚ} (hq : 0 < q) :
    q.num.natAbs ≠ 0 := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  exact Int.natAbs_ne_zero.mpr hnum.ne'

theorem rationalBinaryResidual_formula {q : ℚ} (hq : 0 < q) :
    rationalBinaryResidual q =
      ((q.num.natAbs : ℚ) * (2 : ℚ) ^ Nat.log 2 q.den) /
        ((q.den : ℚ) * (2 : ℚ) ^ Nat.log 2 q.num.natAbs) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hnumabs : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg hnum.le
  have hden : (q.den : ℚ) ≠ 0 := by positivity
  have hpowNum : (2 : ℚ) ^ Nat.log 2 q.num.natAbs ≠ 0 := by positivity
  have hpowDen : (2 : ℚ) ^ Nat.log 2 q.den ≠ 0 := by positivity
  have hqrep : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
        congr 1
        change (q.num : ℚ) = ((q.num.natAbs : ℤ) : ℚ)
        rw [hnumabs]
  rw [rationalBinaryResidual, rationalBinaryScale]
  nth_rw 1 [hqrep]
  field_simp [hden, hpowNum, hpowDen]

theorem rationalBinaryResidual_gt_half {q : ℚ} (hq : 0 < q) :
    1 / 2 < rationalBinaryResidual q := by
  let a := q.num.natAbs
  let b := q.den
  let A : ℚ := (2 : ℚ) ^ Nat.log 2 a
  let B : ℚ := (2 : ℚ) ^ Nat.log 2 b
  have ha0 : a ≠ 0 := positive_rational_num_natAbs_ne_zero hq
  have hb0 : b ≠ 0 := q.den_nz
  have hA : A ≤ (a : ℚ) := by
    dsimp only [A]
    exact_mod_cast Nat.pow_log_le_self 2 ha0
  have hB : B ≤ (b : ℚ) := by
    dsimp only [B]
    exact_mod_cast Nat.pow_log_le_self 2 hb0
  have haUpper : (a : ℚ) < 2 * A := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
    dsimp only [A]
    exact_mod_cast (by simpa [pow_succ, mul_comm] using this)
  have hbUpper : (b : ℚ) < 2 * B := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
    dsimp only [B]
    exact_mod_cast (by simpa [pow_succ, mul_comm] using this)
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have habpos : 0 < (b : ℚ) * A := mul_pos (by positivity) hApos
  have hprod : (b : ℚ) * A < 2 * ((a : ℚ) * B) := calc
    (b : ℚ) * A < (2 * B) * A :=
      mul_lt_mul_of_pos_right hbUpper hApos
    _ ≤ (2 * B) * a :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hBpos.le)
    _ = 2 * (a * B) := by ring
  rw [rationalBinaryResidual_formula hq]
  change 1 / 2 < (a * B) / (b * A)
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2) habpos]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

theorem rationalBinaryResidual_lt_two {q : ℚ} (hq : 0 < q) :
    rationalBinaryResidual q < 2 := by
  let a := q.num.natAbs
  let b := q.den
  let A : ℚ := (2 : ℚ) ^ Nat.log 2 a
  let B : ℚ := (2 : ℚ) ^ Nat.log 2 b
  have ha0 : a ≠ 0 := positive_rational_num_natAbs_ne_zero hq
  have hb0 : b ≠ 0 := q.den_nz
  have hA : A ≤ (a : ℚ) := by
    dsimp only [A]
    exact_mod_cast Nat.pow_log_le_self 2 ha0
  have hB : B ≤ (b : ℚ) := by
    dsimp only [B]
    exact_mod_cast Nat.pow_log_le_self 2 hb0
  have haUpper : (a : ℚ) < 2 * A := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
    dsimp only [A]
    exact_mod_cast (by simpa [pow_succ, mul_comm] using this)
  have hbUpper : (b : ℚ) < 2 * B := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
    dsimp only [B]
    exact_mod_cast (by simpa [pow_succ, mul_comm] using this)
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have habpos : 0 < (b : ℚ) * A := mul_pos (by positivity) hApos
  have hprod : (a : ℚ) * B < 2 * ((b : ℚ) * A) := calc
    (a : ℚ) * B < (2 * A) * B :=
      mul_lt_mul_of_pos_right haUpper hBpos
    _ ≤ (2 * A) * b :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num) hApos.le)
    _ = 2 * (b * A) := by ring
  rw [rationalBinaryResidual_formula hq]
  change (a * B) / (b * A) < 2
  rw [div_lt_iff₀ habpos]
  simpa using hprod

theorem rationalBinaryResidual_pos {q : ℚ} (hq : 0 < q) :
    0 < rationalBinaryResidual q :=
  (by norm_num : (0 : ℚ) < 1 / 2).trans (rationalBinaryResidual_gt_half hq)

/-- If the residual is below one, inversion moves it into the unit interval;
otherwise it is already there. -/
def rationalLogUnit (q : ℚ) : ℚ :=
  if rationalBinaryResidual q < 1 then
    (rationalBinaryResidual q)⁻¹
  else rationalBinaryResidual q

theorem rationalLogUnit_bounds {q : ℚ} (hq : 0 < q) :
    1 ≤ rationalLogUnit q ∧ rationalLogUnit q < 2 := by
  have hr0 := rationalBinaryResidual_pos hq
  have hrHalf := rationalBinaryResidual_gt_half hq
  have hrTwo := rationalBinaryResidual_lt_two hq
  rw [rationalLogUnit]
  split_ifs with hr
  · constructor
    · exact (one_le_inv₀ hr0).2 hr.le
    · have hinv := (inv_lt_inv₀ hr0 (by norm_num : (0 : ℚ) < 1 / 2)).2 hrHalf
      norm_num at hinv ⊢
      exact hinv
  · exact ⟨le_of_not_gt hr, hrTwo⟩

/-- The signed leading-bit displacement between numerator and denominator. -/
def rationalBinaryExponent (q : ℚ) : ℤ :=
  (Nat.log 2 q.num.natAbs : ℤ) - (Nat.log 2 q.den : ℤ)

theorem rationalBinaryScale_pos (q : ℚ) : 0 < rationalBinaryScale q := by
  unfold rationalBinaryScale
  positivity

theorem log_rationalBinaryScale (q : ℚ) :
    Real.log (rationalBinaryScale q : ℝ) =
      (rationalBinaryExponent q : ℝ) * Real.log 2 := by
  have hnum : ((2 : ℝ) ^ Nat.log 2 q.num.natAbs) ≠ 0 := by positivity
  have hden : ((2 : ℝ) ^ Nat.log 2 q.den) ≠ 0 := by positivity
  rw [rationalBinaryScale, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Real.log_div hnum hden, Real.log_pow, Real.log_pow]
  simp only [rationalBinaryExponent, Int.cast_sub, Int.cast_natCast]
  ring

theorem log_rational_eq_scale_add_residual {q : ℚ} (hq : 0 < q) :
    Real.log (q : ℝ) =
      (rationalBinaryExponent q : ℝ) * Real.log 2 +
        Real.log (rationalBinaryResidual q : ℝ) := by
  have hsQ := rationalBinaryScale_pos q
  have hrQ := rationalBinaryResidual_pos hq
  have hs : 0 < (rationalBinaryScale q : ℝ) := by exact_mod_cast hsQ
  have hr : 0 < (rationalBinaryResidual q : ℝ) := by exact_mod_cast hrQ
  have hqeqQ : q = rationalBinaryScale q * rationalBinaryResidual q := by
    rw [rationalBinaryResidual]
    field_simp [(rationalBinaryScale_pos q).ne']
  have hqeq : (q : ℝ) =
      (rationalBinaryScale q : ℝ) * (rationalBinaryResidual q : ℝ) := by
    exact_mod_cast hqeqQ
  rw [hqeq, Real.log_mul hs.ne' hr.ne', log_rationalBinaryScale]

theorem log_residual_eq_signed_log_unit {q : ℚ} (hq : 0 < q) :
    Real.log (rationalBinaryResidual q : ℝ) =
      if rationalBinaryResidual q < 1 then
        -Real.log (rationalLogUnit q : ℝ)
      else Real.log (rationalLogUnit q : ℝ) := by
  have hrQ := rationalBinaryResidual_pos hq
  have hr : (rationalBinaryResidual q : ℝ) ≠ 0 := by
    exact_mod_cast hrQ.ne'
  rw [rationalLogUnit]
  split_ifs with h
  · simp [Rat.cast_inv, Real.log_inv]
  · rfl

/-- Directed multiplication by an integer: for a negative coefficient the
lower endpoint uses the upper approximation. -/
def directedIntMulLower (k : ℤ) (lo hi : ℚ) : ℚ :=
  if 0 ≤ k then (k : ℚ) * lo else (k : ℚ) * hi

/-- Directed multiplication by an integer: for a negative coefficient the
upper endpoint uses the lower approximation. -/
def directedIntMulUpper (k : ℤ) (lo hi : ℚ) : ℚ :=
  if 0 ≤ k then (k : ℚ) * hi else (k : ℚ) * lo

theorem directedIntMulLower_le {k : ℤ} {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ((directedIntMulLower k lo hi : ℚ) : ℝ) ≤ (k : ℝ) * x := by
  rw [directedIntMulLower]
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hhi (by exact_mod_cast (le_of_not_ge hk))

theorem le_directedIntMulUpper {k : ℤ} {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (k : ℝ) * x ≤ ((directedIntMulUpper k lo hi : ℚ) : ℝ) := by
  rw [directedIntMulUpper]
  split_ifs with hk
  · push_cast
    exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast hk)
  · push_cast
    exact mul_le_mul_of_nonpos_left hlo (by exact_mod_cast (le_of_not_ge hk))

/-- Rational lower bound on `log q` for every positive rational `q`. -/
def directedLogLower (q : ℚ) (N : ℕ) : ℚ :=
  let kPart := directedIntMulLower (rationalBinaryExponent q)
    (directedLogUnitLower 2 N) (directedLogUnitUpper 2 N)
  let y := rationalLogUnit q
  kPart + if rationalBinaryResidual q < 1 then
    -directedLogUnitUpper y N
  else directedLogUnitLower y N

/-- Rational upper bound on `log q` for every positive rational `q`. -/
def directedLogUpper (q : ℚ) (N : ℕ) : ℚ :=
  let kPart := directedIntMulUpper (rationalBinaryExponent q)
    (directedLogUnitLower 2 N) (directedLogUnitUpper 2 N)
  let y := rationalLogUnit q
  kPart + if rationalBinaryResidual q < 1 then
    -directedLogUnitLower y N
  else directedLogUnitUpper y N

theorem directedLogLower_le_log {q : ℚ} (hq : 0 < q) (N : ℕ) :
    ((directedLogLower q N : ℚ) : ℝ) ≤ Real.log (q : ℝ) := by
  have htwoLo := directedLogUnitLower_le_log (y := (2 : ℚ)) (by norm_num) N
  have htwoHi := log_le_directedLogUnitUpper (y := (2 : ℚ)) (by norm_num) N
  have hk := directedIntMulLower_le
    (k := rationalBinaryExponent q) htwoLo htwoHi
  norm_num at hk
  have hyBounds := rationalLogUnit_bounds hq
  have hyLo := directedLogUnitLower_le_log hyBounds.1 N
  have hyHi := log_le_directedLogUnitUpper hyBounds.1 N
  rw [log_rational_eq_scale_add_residual hq,
    log_residual_eq_signed_log_unit hq]
  rw [directedLogLower]
  split_ifs with hr
  · push_cast
    linarith
  · push_cast
    linarith

theorem log_le_directedLogUpper {q : ℚ} (hq : 0 < q) (N : ℕ) :
    Real.log (q : ℝ) ≤ ((directedLogUpper q N : ℚ) : ℝ) := by
  have htwoLo := directedLogUnitLower_le_log (y := (2 : ℚ)) (by norm_num) N
  have htwoHi := log_le_directedLogUnitUpper (y := (2 : ℚ)) (by norm_num) N
  have hk := le_directedIntMulUpper
    (k := rationalBinaryExponent q) htwoLo htwoHi
  norm_num at hk
  have hyBounds := rationalLogUnit_bounds hq
  have hyLo := directedLogUnitLower_le_log hyBounds.1 N
  have hyHi := log_le_directedLogUnitUpper hyBounds.1 N
  rw [log_rational_eq_scale_add_residual hq,
    log_residual_eq_signed_log_unit hq]
  rw [directedLogUpper]
  split_ifs with hr
  · push_cast
    linarith
  · push_cast
    linarith

theorem rationalLogSeriesError_nonneg {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (N : ℕ) : 0 ≤ rationalLogSeriesError x N := by
  rw [rationalLogSeriesError]
  have hpow : x ^ 2 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
  have hden : 0 < 1 - x ^ 2 := by linarith
  positivity

theorem rationalLogSeriesError_le_geometric {x : ℚ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 3) (N : ℕ) :
    rationalLogSeriesError x N ≤
      4 * (1 / 3 : ℚ) ^ (2 * N + 1) := by
  have hx1 : x < 1 := hx.trans_lt (by norm_num)
  have hsq : x ^ 2 ≤ (1 / 3 : ℚ) ^ 2 :=
    pow_le_pow_left₀ hx0 hx 2
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hcoef : 2 / (1 - x ^ 2) ≤ (4 : ℚ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hpow : x ^ (2 * N + 1) ≤
      (1 / 3 : ℚ) ^ (2 * N + 1) :=
    pow_le_pow_left₀ hx0 hx _
  rw [rationalLogSeriesError]
  calc
    2 * (x ^ (2 * N + 1) / (1 - x ^ 2)) =
        x ^ (2 * N + 1) * (2 / (1 - x ^ 2)) := by ring
    _ ≤ (1 / 3 : ℚ) ^ (2 * N + 1) * (2 / (1 - x ^ 2)) :=
      mul_le_mul_of_nonneg_right hpow (div_nonneg (by norm_num) hden.le)
    _ ≤ (1 / 3 : ℚ) ^ (2 * N + 1) * 4 :=
      mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = 4 * (1 / 3 : ℚ) ^ (2 * N + 1) := by ring

theorem four_mul_two_pow_le_three_pow (p : ℕ) :
    4 * 2 ^ p ≤ 3 ^ (2 * p + 3) := by
  induction p with
  | zero => norm_num
  | succ p ih =>
      calc
        4 * 2 ^ (p + 1) = 2 * (4 * 2 ^ p) := by ring
        _ ≤ 2 * 3 ^ (2 * p + 3) := Nat.mul_le_mul_left 2 ih
        _ ≤ 9 * 3 ^ (2 * p + 3) := by gcongr <;> norm_num
        _ = 3 ^ (2 * (p + 1) + 3) := by
          rw [show 2 * (p + 1) + 3 = (2 * p + 3) + 2 by omega,
            pow_add]
          ring

theorem geometric_log_error_le_dyadic (p : ℕ) :
    4 * (1 / 3 : ℚ) ^ (2 * (p + 1) + 1) ≤ (1 / 2 : ℚ) ^ p := by
  have hnat := four_mul_two_pow_le_three_pow p
  have hrat : (4 : ℚ) * (2 : ℚ) ^ p ≤ (3 : ℚ) ^ (2 * p + 3) := by
    exact_mod_cast hnat
  rw [show 2 * (p + 1) + 1 = 2 * p + 3 by omega]
  simp only [one_div, inv_pow]
  rw [mul_inv_le_iff₀ (by positivity : (0 : ℚ) < 3 ^ (2 * p + 3))]
  rw [mul_comm ((2 : ℚ) ^ p)⁻¹]
  rw [le_mul_inv_iff₀ (by positivity : (0 : ℚ) < 2 ^ p)]
  simpa using hrat

theorem directedLogUnit_width_le_dyadic {y : ℚ}
    (hy1 : 1 ≤ y) (hy2 : y ≤ 2) (p : ℕ) :
    directedLogUnitUpper y (p + 1) - directedLogUnitLower y (p + 1) ≤
      (1 / 2 : ℚ) ^ p := by
  rw [directedLogUnit_width]
  exact (rationalLogSeriesError_le_geometric
    (rationalLogUnitParameter_nonneg hy1)
    (rationalLogUnitParameter_le_third hy1 hy2) (p + 1)).trans
      (geometric_log_error_le_dyadic p)

theorem directedIntMul_width (k : ℤ) (lo hi : ℚ) :
    directedIntMulUpper k lo hi - directedIntMulLower k lo hi =
      (k.natAbs : ℚ) * (hi - lo) := by
  cases k with
  | ofNat n => simp [directedIntMulUpper, directedIntMulLower]; ring
  | negSucc n => simp [directedIntMulUpper, directedIntMulLower]; ring

theorem directedLog_width (q : ℚ) (N : ℕ) :
    directedLogUpper q N - directedLogLower q N =
      (rationalBinaryExponent q).natAbs *
          (directedLogUnitUpper 2 N - directedLogUnitLower 2 N) +
        (directedLogUnitUpper (rationalLogUnit q) N -
          directedLogUnitLower (rationalLogUnit q) N) := by
  rw [directedLogUpper, directedLogLower]
  split_ifs <;>
    rw [← directedIntMul_width] <;>
    ring

theorem nat_succ_mul_dyadic_succ_le_one (m : ℕ) :
    (m + 1 : ℚ) * (1 / 2 : ℚ) ^ (m + 1) ≤ 1 := by
  have hn : m + 1 ≤ 2 ^ (m + 1) := (m + 1).lt_two_pow_self.le
  have hq : (m + 1 : ℚ) ≤ (2 : ℚ) ^ (m + 1) := by exact_mod_cast hn
  simp only [one_div, inv_pow]
  rw [mul_inv_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (m + 1))]
  simpa using hq

theorem nat_succ_mul_shifted_dyadic_le (p m : ℕ) :
    (m + 1 : ℚ) * (1 / 2 : ℚ) ^ (p + m + 1) ≤
      (1 / 2 : ℚ) ^ p := by
  rw [show p + m + 1 = p + (m + 1) by omega, pow_add]
  have h := nat_succ_mul_dyadic_succ_le_one m
  calc
    (m + 1 : ℚ) * ((1 / 2 : ℚ) ^ p * (1 / 2 : ℚ) ^ (m + 1)) =
        (1 / 2 : ℚ) ^ p *
          ((m + 1 : ℚ) * (1 / 2 : ℚ) ^ (m + 1)) := by ring
    _ ≤ (1 / 2 : ℚ) ^ p * 1 :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (1 / 2 : ℚ) ^ p := mul_one _

/-- A precision schedule compensating for the signed dyadic exponent.  Its
number of series terms is linear in the requested precision and in the binary
length displacement of the input rational. -/
def directedLogTerms (q : ℚ) (p : ℕ) : ℕ :=
  p + (rationalBinaryExponent q).natAbs + 2

/-- The signed range-reduction exponent is at most twice the canonical input
length.  This makes the series schedule polynomial in ordinary binary input
length rather than in the numerical magnitude of `q`. -/
theorem rationalBinaryExponent_natAbs_le_two_bitLength
    {q : ℚ} (hq : 0 < q) :
    (rationalBinaryExponent q).natAbs ≤ 2 * encodedBitLength ℚ q := by
  have hnum := numerator_natAbs_log_lt_rationalBitLength q
    (positive_rational_num_natAbs_ne_zero hq)
  have hden := denominator_log_lt_rationalBitLength q
  have habs := Int.natAbs_sub_le
    (Nat.log 2 q.num.natAbs : ℤ) (Nat.log 2 q.den : ℤ)
  simp only [Int.natAbs_natCast] at habs
  rw [rationalBinaryExponent]
  omega

theorem directedLogTerms_le_input_precision
    {q : ℚ} (hq : 0 < q) (p : ℕ) :
    directedLogTerms q p ≤ p + 2 * encodedBitLength ℚ q + 2 := by
  have h := rationalBinaryExponent_natAbs_le_two_bitLength hq
  rw [directedLogTerms]
  omega

theorem directedLog_width_le_dyadic {q : ℚ} (hq : 0 < q) (p : ℕ) :
    directedLogUpper q (directedLogTerms q p) -
        directedLogLower q (directedLogTerms q p) ≤
      (1 / 2 : ℚ) ^ p := by
  let m := (rationalBinaryExponent q).natAbs
  let precision := p + m + 1
  have hterms : directedLogTerms q p = precision + 1 := by
    simp [directedLogTerms, precision, m]
  have htwo := directedLogUnit_width_le_dyadic
    (y := (2 : ℚ)) (by norm_num) (by norm_num) precision
  have hy := rationalLogUnit_bounds hq
  have hunit := directedLogUnit_width_le_dyadic
    hy.1 hy.2.le precision
  rw [directedLog_width, hterms]
  change (m : ℚ) *
      (directedLogUnitUpper 2 (precision + 1) -
        directedLogUnitLower 2 (precision + 1)) +
      (directedLogUnitUpper (rationalLogUnit q) (precision + 1) -
        directedLogUnitLower (rationalLogUnit q) (precision + 1)) ≤ _
  calc
    (m : ℚ) *
          (directedLogUnitUpper 2 (precision + 1) -
            directedLogUnitLower 2 (precision + 1)) +
        (directedLogUnitUpper (rationalLogUnit q) (precision + 1) -
          directedLogUnitLower (rationalLogUnit q) (precision + 1)) ≤
        (m : ℚ) * (1 / 2 : ℚ) ^ precision +
          (1 / 2 : ℚ) ^ precision := by
      gcongr
    _ = (m + 1 : ℚ) * (1 / 2 : ℚ) ^ precision := by ring
    _ ≤ (1 / 2 : ℚ) ^ p := by
      simpa only [precision] using nat_succ_mul_shifted_dyadic_le p m

/-- The natural-number ceiling of a nonnegative rational.  Unlike the raw
numerator, its numerical value depends on the magnitude of the rational and
not on the size of a possibly huge denominator. -/
def rationalCeilNat (t : ℚ) : ℕ := Int.toNat ⌈t⌉

theorem le_rationalCeilNat {t : ℚ} (ht : 0 ≤ t) :
    t ≤ rationalCeilNat t := by
  have hceil : t ≤ ((⌈t⌉ : ℤ) : ℚ) := Int.le_ceil t
  have hnonneg : (0 : ℤ) ≤ ⌈t⌉ := Int.ceil_nonneg ht
  rw [← Int.toNat_of_nonneg hnonneg] at hceil
  exact hceil

/-- Number of Bernoulli factors used for a one-sided exponential sandwich.
For nonnegative `t`, this is strictly larger than `2t`.  The former version
used `t.num.natAbs`, which is exponential in the bit length for a bounded
rational with a large denominator; the ceiling is the correct magnitude
parameter. -/
def rationalExpSandwichSteps (t : ℚ) : ℕ := 2 * rationalCeilNat t + 1

/-- A fully rational substitute for evaluating a negative exponential. -/
def rationalExpSandwichFactor (t : ℚ) : ℚ :=
  let M := rationalExpSandwichSteps t
  (1 - t / M) ^ M

theorem nonnegative_rational_le_num_natAbs {t : ℚ} (ht : 0 ≤ t) :
    t ≤ (t.num.natAbs : ℚ) := by
  have hnum : 0 ≤ t.num := Rat.num_nonneg.mpr ht
  have hnumabs : (t.num.natAbs : ℤ) = t.num := Int.natAbs_of_nonneg hnum
  have hden : (1 : ℚ) ≤ t.den := by exact_mod_cast t.den_pos
  calc
    t = (t.num : ℚ) / (t.den : ℚ) := (Rat.num_div_den t).symm
    _ = (t.num.natAbs : ℚ) / (t.den : ℚ) := by
      congr 1
      change (t.num : ℚ) = ((t.num.natAbs : ℤ) : ℚ)
      rw [hnumabs]
    _ ≤ (t.num.natAbs : ℚ) := div_le_self (by positivity) hden

theorem two_mul_lt_rationalExpSandwichSteps {t : ℚ} (ht : 0 ≤ t) :
    2 * t < rationalExpSandwichSteps t := by
  have hle := le_rationalCeilNat ht
  rw [rationalExpSandwichSteps]
  push_cast
  linarith

theorem rationalExpSandwich_argument_bounds {t : ℚ} (ht : 0 ≤ t) :
    0 ≤ t / rationalExpSandwichSteps t ∧
      t / rationalExpSandwichSteps t < 1 / 2 := by
  have hM : (0 : ℚ) < rationalExpSandwichSteps t := by
    have hMN : 0 < rationalExpSandwichSteps t := by
      simp [rationalExpSandwichSteps]
    exact_mod_cast hMN
  constructor
  · exact div_nonneg ht hM.le
  · rw [div_lt_iff₀ hM]
    have := two_mul_lt_rationalExpSandwichSteps ht
    linarith

theorem log_one_sub_between_neg_two_mul_and_neg {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x < 1 / 2) :
    -2 * x ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ -x := by
  have hbase : 0 < 1 - x := by linarith
  have hupper := Real.log_le_sub_one_of_pos hbase
  have hlower0 := Real.one_sub_inv_le_log_of_pos hbase
  have hratio : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hbase]
    nlinarith
  have hid : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hbase.ne']
    ring
  rw [hid] at hlower0
  have hneg : -x / (1 - x) = -(x / (1 - x)) := by ring
  rw [hneg] at hlower0
  constructor <;> linarith

/-- The rational Bernoulli factor lies between the two exponential losses
needed in the final certificate.  Thus the implementation does not need a
separate transcendental exponential evaluator at this step. -/
theorem rationalExpSandwichFactor_bounds {t : ℚ} (ht : 0 ≤ t) :
    Real.exp (-2 * (t : ℝ)) ≤ (rationalExpSandwichFactor t : ℝ) ∧
      (rationalExpSandwichFactor t : ℝ) ≤ Real.exp (-(t : ℝ)) := by
  let M := rationalExpSandwichSteps t
  let x : ℚ := t / M
  have hxQ := rationalExpSandwich_argument_bounds ht
  have hx0Q : 0 ≤ x := by simpa [x, M] using hxQ.1
  have hxhalfQ : x < 1 / 2 := by simpa [x, M] using hxQ.2
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx0Q
  have hxhalf' : (x : ℝ) < (((1 / 2 : ℚ) : ℝ)) := by
    exact_mod_cast hxhalfQ
  have hxhalf : (x : ℝ) < 1 / 2 := by norm_num at hxhalf' ⊢; exact hxhalf'
  have hbase : 0 < (1 : ℝ) - x := by linarith
  have hlog := log_one_sub_between_neg_two_mul_and_neg hx0 hxhalf
  have hMposQ : (0 : ℚ) < M := by
    have hMN : 0 < M := by simp [M, rationalExpSandwichSteps]
    exact_mod_cast hMN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposQ
  have hMxQ : (M : ℚ) * x = t := by
    dsimp only [x]
    field_simp [hMposQ.ne']
  have hMx : (M : ℝ) * (x : ℝ) = (t : ℝ) := by exact_mod_cast hMxQ
  have hlogPow : Real.log (((1 : ℝ) - x) ^ M) =
      (M : ℝ) * Real.log ((1 : ℝ) - x) := Real.log_pow _ _
  have hfactorPos : 0 < ((1 : ℝ) - x) ^ M := pow_pos hbase M
  have hlowerLog : -2 * (t : ℝ) ≤ Real.log (((1 : ℝ) - x) ^ M) := by
    rw [hlogPow]
    have := mul_le_mul_of_nonneg_left hlog.1 hMpos.le
    nlinarith
  have hupperLog : Real.log (((1 : ℝ) - x) ^ M) ≤ -(t : ℝ) := by
    rw [hlogPow]
    have := mul_le_mul_of_nonneg_left hlog.2 hMpos.le
    nlinarith
  have hfactorCast : (rationalExpSandwichFactor t : ℝ) =
      ((1 : ℝ) - x) ^ M := by
    simp [rationalExpSandwichFactor, x, M]
  rw [hfactorCast]
  constructor
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hlowerLog
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hupperLog

/-- A magnitude-sensitive step count for a relative logarithmic loss
`loss`.  Its numerical size is `O(t + t^2/loss)` and is independent of the
denominator used to represent `t`. -/
def rationalExpApproxSteps (t loss : ℚ) : ℕ :=
  2 * rationalCeilNat (t + t ^ 2 / loss) + 1

/-- Directed rational lower approximation to `exp (-t)`. -/
def rationalNegativeExpLower (t loss : ℚ) : ℚ :=
  let M := rationalExpApproxSteps t loss
  (1 - t / M) ^ M

theorem rationalExpApproxSteps_gt_two_mul
    {t loss : ℚ} (ht : 0 ≤ t) (hloss : 0 < loss) :
    2 * t < rationalExpApproxSteps t loss := by
  have hu0 : 0 ≤ t + t ^ 2 / loss := by positivity
  have hceil := le_rationalCeilNat hu0
  have htceil : t ≤ rationalCeilNat (t + t ^ 2 / loss) := by
    have htu : t ≤ t + t ^ 2 / loss :=
      le_add_of_nonneg_right (div_nonneg (sq_nonneg t) hloss.le)
    exact htu.trans hceil
  rw [rationalExpApproxSteps]
  push_cast
  linarith

theorem rationalExpApproxSteps_controls_error
    {t loss : ℚ} (ht : 0 ≤ t) (hloss : 0 < loss) :
    2 * t ^ 2 / rationalExpApproxSteps t loss ≤ loss := by
  let u : ℚ := t + t ^ 2 / loss
  let M : ℚ := rationalExpApproxSteps t loss
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hceil := le_rationalCeilNat hu0
  have hMpos : 0 < M := by
    dsimp only [M, rationalExpApproxSteps]
    positivity
  have hcontrol : 2 * (t ^ 2 / loss) ≤ M := by
    have hsquare : t ^ 2 / loss ≤ u := by
      dsimp only [u]
      linarith
    have htwo : 2 * u ≤ M := by
      dsimp only [M, rationalExpApproxSteps]
      push_cast
      linarith
    linarith
  rw [div_le_iff₀ hMpos]
  have := mul_le_mul_of_nonneg_right hcontrol hloss.le
  field_simp [hloss.ne'] at this ⊢
  nlinarith

theorem log_one_sub_between_neg_add_two_sq_and_neg {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x < 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) ∧
      Real.log (1 - x) ≤ -x := by
  have hbase : 0 < 1 - x := by linarith
  have hupper := Real.log_le_sub_one_of_pos hbase
  have hlower0 := Real.one_sub_inv_le_log_of_pos hbase
  have hratio : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hbase]
    nlinarith
  have hid : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hbase.ne']
    ring
  rw [hid] at hlower0
  have hneg0 := neg_le_neg hratio
  have hneg : -x - 2 * x ^ 2 ≤ -x / (1 - x) := by
    calc
      -x - 2 * x ^ 2 = -(x + 2 * x ^ 2) := by ring
      _ ≤ -(x / (1 - x)) := hneg0
      _ = -x / (1 - x) := by ring
  exact ⟨hneg.trans hlower0, by linarith⟩

/-- The accurate negative-exponential routine has prescribed multiplicative
logarithmic loss. -/
theorem rationalNegativeExpLower_bounds
    {t loss : ℚ} (ht : 0 ≤ t) (hloss : 0 < loss) :
    Real.exp (-(t : ℝ) - (loss : ℝ)) ≤
        (rationalNegativeExpLower t loss : ℝ) ∧
      (rationalNegativeExpLower t loss : ℝ) ≤
        Real.exp (-(t : ℝ)) := by
  let M := rationalExpApproxSteps t loss
  let x : ℚ := t / M
  have hMposQ : (0 : ℚ) < M := by
    dsimp only [M, rationalExpApproxSteps]
    positivity
  have htwo := rationalExpApproxSteps_gt_two_mul ht hloss
  have hx0Q : 0 ≤ x := div_nonneg ht hMposQ.le
  have hxhalfQ : x < 1 / 2 := by
    dsimp only [x]
    rw [div_lt_iff₀ hMposQ]
    linarith
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx0Q
  have hxhalf' : (x : ℝ) < (((1 / 2 : ℚ)) : ℝ) := by
    exact_mod_cast hxhalfQ
  have hxhalf : (x : ℝ) < 1 / 2 := by
    norm_num at hxhalf' ⊢
    exact hxhalf'
  have hbase : 0 < (1 : ℝ) - x := by linarith
  have hlog := log_one_sub_between_neg_add_two_sq_and_neg hx0 hxhalf
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposQ
  have hMxQ : (M : ℚ) * x = t := by
    dsimp only [x]
    field_simp [hMposQ.ne']
  have hMx : (M : ℝ) * (x : ℝ) = (t : ℝ) := by
    exact_mod_cast hMxQ
  have herrQ := rationalExpApproxSteps_controls_error ht hloss
  have herr : 2 * (t : ℝ) ^ 2 / (M : ℝ) ≤ (loss : ℝ) := by
    exact_mod_cast herrQ
  have hMxx : (M : ℝ) * (2 * (x : ℝ) ^ 2) =
      2 * (t : ℝ) ^ 2 / (M : ℝ) := by
    have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
    rw [show (x : ℝ) = (t : ℝ) / (M : ℝ) by
      exact_mod_cast (rfl : x = t / M)]
    field_simp [hMne]
  have hlogPow : Real.log (((1 : ℝ) - x) ^ M) =
      (M : ℝ) * Real.log ((1 : ℝ) - x) := Real.log_pow _ _
  have hfactorPos : 0 < ((1 : ℝ) - x) ^ M := pow_pos hbase M
  have hlowerLog : -(t : ℝ) - (loss : ℝ) ≤
      Real.log (((1 : ℝ) - x) ^ M) := by
    rw [hlogPow]
    have hscaled := mul_le_mul_of_nonneg_left hlog.1 hMpos.le
    nlinarith [hMx, hMxx, herr]
  have hupperLog : Real.log (((1 : ℝ) - x) ^ M) ≤ -(t : ℝ) := by
    rw [hlogPow]
    have hscaled := mul_le_mul_of_nonneg_left hlog.2 hMpos.le
    nlinarith
  have hfactorCast : (rationalNegativeExpLower t loss : ℝ) =
      ((1 : ℝ) - x) ^ M := by
    simp [rationalNegativeExpLower, x, M]
  rw [hfactorCast]
  constructor
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hlowerLog
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hupperLog

/-- Directed rational lower approximation to `exp t` for `t ≥ 0`. -/
def rationalPositiveExpLower (t loss : ℚ) : ℚ :=
  let M := rationalExpApproxSteps t loss
  (1 + t / M) ^ M

theorem log_one_add_between_sub_sq_and_self {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  have hbase : 0 < 1 + x := by linarith
  have hlower0 := Real.one_sub_inv_le_log_of_pos hbase
  have hupper0 := Real.log_le_sub_one_of_pos hbase
  have hid : 1 - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp [hbase.ne']
    ring
  rw [hid] at hlower0
  have hpoly : x - x ^ 2 ≤ x / (1 + x) := by
    rw [le_div_iff₀ hbase]
    nlinarith [sq_nonneg x]
  exact ⟨hpoly.trans hlower0, by linarith⟩

theorem rationalPositiveExpLower_bounds
    {t loss : ℚ} (ht : 0 ≤ t) (hloss : 0 < loss) :
    Real.exp ((t : ℝ) - (loss : ℝ)) ≤
        (rationalPositiveExpLower t loss : ℝ) ∧
      (rationalPositiveExpLower t loss : ℝ) ≤ Real.exp (t : ℝ) := by
  let M := rationalExpApproxSteps t loss
  let x : ℚ := t / M
  have hMposQ : (0 : ℚ) < M := by
    dsimp only [M, rationalExpApproxSteps]
    positivity
  have hx0Q : 0 ≤ x := div_nonneg ht hMposQ.le
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx0Q
  have hbase : 0 < (1 : ℝ) + x := by positivity
  have hlog := log_one_add_between_sub_sq_and_self hx0
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposQ
  have hMxQ : (M : ℚ) * x = t := by
    dsimp only [x]
    field_simp [hMposQ.ne']
  have hMx : (M : ℝ) * (x : ℝ) = (t : ℝ) := by exact_mod_cast hMxQ
  have herrQ := rationalExpApproxSteps_controls_error ht hloss
  have herr : (t : ℝ) ^ 2 / (M : ℝ) ≤ (loss : ℝ) := by
    have hcast : 2 * (t : ℝ) ^ 2 / (M : ℝ) ≤ (loss : ℝ) := by
      exact_mod_cast herrQ
    have hnonneg : 0 ≤ (t : ℝ) ^ 2 / (M : ℝ) := by positivity
    have hid : 2 * (t : ℝ) ^ 2 / (M : ℝ) =
        2 * ((t : ℝ) ^ 2 / (M : ℝ)) := by ring
    rw [hid] at hcast
    linarith
  have hMxx : (M : ℝ) * (x : ℝ) ^ 2 =
      (t : ℝ) ^ 2 / (M : ℝ) := by
    have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
    rw [show (x : ℝ) = (t : ℝ) / (M : ℝ) by
      exact_mod_cast (rfl : x = t / M)]
    field_simp [hMne]
  have hlogPow : Real.log (((1 : ℝ) + x) ^ M) =
      (M : ℝ) * Real.log ((1 : ℝ) + x) := Real.log_pow _ _
  have hfactorPos : 0 < ((1 : ℝ) + x) ^ M := pow_pos hbase M
  have hlowerLog : (t : ℝ) - (loss : ℝ) ≤
      Real.log (((1 : ℝ) + x) ^ M) := by
    rw [hlogPow]
    have hscaled := mul_le_mul_of_nonneg_left hlog.1 hMpos.le
    nlinarith [hMx, hMxx, herr]
  have hupperLog : Real.log (((1 : ℝ) + x) ^ M) ≤ (t : ℝ) := by
    rw [hlogPow]
    have hscaled := mul_le_mul_of_nonneg_left hlog.2 hMpos.le
    nlinarith
  have hfactorCast : (rationalPositiveExpLower t loss : ℝ) =
      ((1 : ℝ) + x) ^ M := by
    simp [rationalPositiveExpLower, x, M]
  rw [hfactorCast]
  constructor
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hlowerLog
  · rw [← Real.exp_log hfactorPos]
    exact Real.exp_le_exp.mpr hupperLog

/-- Directed rational lower exponential at an arbitrary rational argument. -/
def rationalExpLower (s loss : ℚ) : ℚ :=
  if 0 ≤ s then rationalPositiveExpLower s loss
  else rationalNegativeExpLower (-s) loss

theorem rationalExpLower_bounds {s loss : ℚ} (hloss : 0 < loss) :
    Real.exp ((s : ℝ) - (loss : ℝ)) ≤
        (rationalExpLower s loss : ℝ) ∧
      (rationalExpLower s loss : ℝ) ≤ Real.exp (s : ℝ) := by
  rw [rationalExpLower]
  split_ifs with hs
  · exact rationalPositiveExpLower_bounds hs hloss
  · have hneg : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    have h := rationalNegativeExpLower_bounds hneg hloss
    norm_num only [Rat.cast_neg] at h ⊢
    convert h using 1 <;> ring

end BeyondBethe
