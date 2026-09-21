/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums
import LeanPool.RegtsSevenster.RS.Classical.SymFun.BinomialH

/-!
# Super power sums and their generating series

The power-sum sequence of the super vector space `ℂ^{p|q}` is
`superPS p q c = p + (−1)^{c+1} q`: `p` copies of `+1` and `q` copies
of `−1`, the latter weighted by the super sign.  The central result of
this module is the generating-function identity

    `(1 − X)^p · newtonHSeries (superPS p q) = (1 + X)^q`

in `ℂ⟦X⟧`, proved by showing that both sides satisfy the differential
equation `(1 + X) · F′ = q · F` with constant coefficient `1`, whose
coefficient recursion pins the coefficients to `C(q, n)`.  Coefficient
extraction yields binomial evaluations of `newtonH (superPS p q)` in
the pure cases and, for `n > q`, a linear recurrence of order `p` —
the input for hook-vanishing arguments.
-/

namespace RS

open Finset PowerSeries

/-! ### The super power sums -/

/-- The power sums of the super vector space `ℂ^{p|q}`: `p` copies of
`+1` and `q` copies of `−1` with the super sign, so
`superPS p q 1 = p + q`, `superPS p q 2 = p − q`, and so on. -/
noncomputable def superPS (p q : ℕ) : ℕ → ℂ :=
  fun c => (p : ℂ) + (-1) ^ (c + 1) * (q : ℂ)

/-- Super power sums add under direct sums of super vector spaces. -/
theorem superPS_add (p q r s : ℕ) :
    (fun c => superPS p q c + superPS r s c) = superPS (p + r) (q + s) := by
  funext c
  simp only [superPS]
  push_cast
  ring

/-- Super power sums multiply under tensor products of super vector
spaces. -/
theorem superPS_mul (p q r s : ℕ) :
    (fun c => superPS p q c * superPS r s c) =
      superPS (p * r + q * s) (p * s + q * r) := by
  funext c
  have h : (-1 : ℂ) ^ (c + 1) * (-1) ^ (c + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨c + 1, by ring⟩
  simp only [superPS]
  push_cast
  linear_combination ((q : ℂ) * (s : ℂ)) * h

/-! ### Binomial coefficients of `(1 ± X)^k` -/

private theorem coeff_one_add_X_pow (q n : ℕ) :
    coeff n ((1 + X : ℂ⟦X⟧) ^ q) = (q.choose n : ℂ) := by
  have h : ((1 + Polynomial.X : Polynomial ℂ) : ℂ⟦X⟧) = 1 + X := by
    rw [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [← h, ← Polynomial.coe_pow, Polynomial.coeff_coe,
    Polynomial.coeff_one_add_X_pow]

private theorem coeff_one_sub_X_pow (p n : ℕ) :
    coeff n ((1 - X : ℂ⟦X⟧) ^ p) = (-1 : ℂ) ^ n * (p.choose n : ℂ) := by
  have h : rescale (-1 : ℂ) ((1 + X) ^ p) = (1 - X) ^ p := by
    rw [map_pow, map_add, map_one, rescale_neg_one_X]
    ring
  rw [← h, coeff_rescale, coeff_one_add_X_pow]

/-! ### The differential equation of the super series -/

private theorem one_sub_X_mul_geom :
    (1 - X : ℂ⟦X⟧) * PowerSeries.mk (fun _ => (1 : ℂ)) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp
  | succ m => simp [coeff_succ_X_mul]

private theorem one_add_X_mul_alt :
    (1 + X : ℂ⟦X⟧) * PowerSeries.mk (fun n => (-1 : ℂ) ^ n) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp
  | succ m =>
      rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one,
        if_neg (Nat.succ_ne_zero m), pow_succ]
      ring

private theorem powerSumSeries_superPS_eq (p q : ℕ) :
    powerSumSeries (superPS p q) =
      C (p : ℂ) * PowerSeries.mk (fun _ => (1 : ℂ)) +
        C (q : ℂ) * PowerSeries.mk (fun n => (-1 : ℂ) ^ n) := by
  ext n
  simp only [powerSumSeries, superPS, map_add, coeff_C_mul, coeff_mk,
    pow_succ]
  ring

private theorem key_poly_identity (p q : ℕ) :
    (1 - X) * ((1 + X) * powerSumSeries (superPS p q)) =
      C (p : ℂ) * (1 + X) + C (q : ℂ) * (1 - X) := by
  rw [powerSumSeries_superPS_eq]
  linear_combination (C (p : ℂ) * (1 + X)) * one_sub_X_mul_geom +
    (C (q : ℂ) * (1 - X)) * one_add_X_mul_alt

private theorem one_sub_X_mul_derivative_pow (p : ℕ) :
    (1 - X) * d⁄dX ℂ ((1 - X : ℂ⟦X⟧) ^ p) =
      -(C (p : ℂ)) * (1 - X) ^ p := by
  induction p with
  | zero =>
      rw [pow_zero, Derivation.map_one_eq_zero, mul_zero, Nat.cast_zero,
        map_zero, neg_zero, zero_mul]
  | succ m ih =>
      have hD : d⁄dX ℂ (1 - X : ℂ⟦X⟧) = -1 := by
        rw [Derivation.map_sub, derivative_X, Derivation.map_one_eq_zero,
          zero_sub]
      have hC : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD, hC,
        map_add, map_one]
      linear_combination (1 - X) * ih

private theorem superSeries_ode (p q : ℕ) :
    (1 + X) * d⁄dX ℂ ((1 - X) ^ p * newtonHSeries (superPS p q)) =
      C (q : ℂ) * ((1 - X) ^ p * newtonHSeries (superPS p q)) := by
  have hunit : IsUnit (1 - X : ℂ⟦X⟧) :=
    IsUnit.of_mul_eq_one _ one_sub_X_mul_geom
  refine hunit.mul_right_inj.mp ?_
  have hprod : d⁄dX ℂ ((1 - X) ^ p * newtonHSeries (superPS p q)) =
      (1 - X) ^ p *
          (powerSumSeries (superPS p q) * newtonHSeries (superPS p q)) +
        newtonHSeries (superPS p q) * d⁄dX ℂ ((1 - X : ℂ⟦X⟧) ^ p) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, newtonH_derivative]
  rw [hprod]
  linear_combination
    ((1 - X) ^ p * newtonHSeries (superPS p q)) * key_poly_identity p q +
      ((1 + X) * newtonHSeries (superPS p q)) *
        one_sub_X_mul_derivative_pow p

private theorem superSeries_constantCoeff (p q : ℕ) :
    constantCoeff ((1 - X) ^ p * newtonHSeries (superPS p q)) = 1 := by
  rw [map_mul, map_pow, map_sub, map_one, constantCoeff_X, sub_zero,
    one_pow, newtonH_series_constantCoeff, mul_one]

/-- Any power series `F` with `(1 + X) · F′ = q · F` and constant
coefficient `1` has coefficients `C(q, n)`, by the coefficient
recursion `(n + 1) · F_{n+1} = (q − n) · F_n`. -/
private theorem coeff_eq_choose_of_ode {q : ℕ} {F : ℂ⟦X⟧}
    (h0 : constantCoeff F = 1)
    (hode : (1 + X) * d⁄dX ℂ F = C (q : ℂ) * F) :
    ∀ n, coeff n F = (q.choose n : ℂ) := by
  intro n
  induction n with
  | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, h0, Nat.choose_zero_right,
        Nat.cast_one]
  | succ m ih =>
      have h := congrArg (coeff m) hode
      rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at h
      have hX : coeff m (X * d⁄dX ℂ F) = (m : ℂ) * coeff m F := by
        cases m with
        | zero => rw [coeff_zero_X_mul, Nat.cast_zero, zero_mul]
        | succ k =>
            rw [coeff_succ_X_mul, coeff_derivative]
            push_cast
            ring
      rw [hX, ih] at h
      have hrec : ((m : ℂ) + 1) * (q.choose (m + 1) : ℂ) =
          ((q : ℂ) - (m : ℂ)) * (q.choose m : ℂ) := by
        rcases lt_or_ge m q with hlt | hge
        · have hc := congrArg (Nat.cast (R := ℂ))
            (Nat.choose_succ_right_eq q m)
          push_cast [Nat.cast_sub hlt.le] at hc
          linear_combination hc
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
          rcases eq_or_lt_of_le hge with heq | hlt
          · rw [heq, sub_self, zero_mul]
          · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
      apply mul_right_cancel₀ (Nat.cast_add_one_ne_zero m :
        ((m : ℂ) + 1) ≠ 0)
      linear_combination h - hrec

/-! ### The generating-function identity -/

/-- **The super binomial identity.**  The generating series of the
complete homogeneous sequence of the super power sums `superPS p q`
satisfies `(1 − X)^p · H = (1 + X)^q` in `ℂ⟦X⟧`. -/
theorem newtonHSeries_superPS (p q : ℕ) :
    (1 - PowerSeries.X) ^ p * newtonHSeries (superPS p q) =
      (1 + PowerSeries.X) ^ q := by
  ext n
  rw [coeff_eq_choose_of_ode (superSeries_constantCoeff p q)
    (superSeries_ode p q) n, coeff_one_add_X_pow]

/-! ### Binomial evaluations -/

/-- With `p = 0` the complete homogeneous values are the binomial
coefficients of `(1 + X)^q`. -/
theorem newtonH_superPS_zero_p (q n : ℕ) :
    newtonH (superPS 0 q) n = (q.choose n : ℂ) := by
  have h := congrArg (coeff n) (newtonHSeries_superPS 0 q)
  rw [pow_zero, one_mul, coeff_one_add_X_pow] at h
  simpa [newtonHSeries, coeff_mk] using h

/-- With `q = 0` and `p` positive the complete homogeneous values are
the binomial coefficients of `(1 − X)^{−p}`. -/
theorem newtonH_superPS_zero_q (p n : ℕ) (hp : 0 < p) :
    newtonH (superPS p 0) n = ((p - 1 + n).choose n : ℂ) := by
  have hfun : superPS p 0 = fun _ => (p : ℂ) := by
    funext c
    simp [superPS]
  rw [hfun, newtonH_const, show p + n - 1 = p - 1 + n from by omega]

/-! ### The recurrence beyond degree `q` -/

/-- **The order-`p` recurrence beyond degree `q`**, antidiagonal form:
for `n > q` the convolution of the signed binomial row of `(1 − X)^p`
with the complete homogeneous sequence of `superPS p q` vanishes. -/
theorem newtonH_superPS_rec_antidiagonal (p q : ℕ) {n : ℕ}
    (hn : q < n) :
    ∑ ij ∈ Finset.antidiagonal n,
      (-1 : ℂ) ^ ij.1 * (p.choose ij.1 : ℂ) *
        newtonH (superPS p q) ij.2 = 0 := by
  have h := congrArg (coeff n) (newtonHSeries_superPS p q)
  rw [coeff_mul, coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt hn,
    Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_one_sub_X_pow]
  simp only [newtonHSeries, coeff_mk]

end RS
