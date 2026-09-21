/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums

/-!
# Convolution of complete homogeneous sequences

The complete homogeneous sequence of a sum of scalar sequences is the
convolution of the individual sequences: at the level of generating
series, `newtonHSeries (t + t') = newtonHSeries t * newtonHSeries t'`.

The proof follows the house technique: both sides satisfy the
first-order differential equation `F′ = (T + T′) · F` — the left by
the Newton derivative identity applied to the sum, the right by the
Leibniz rule and the identity applied twice — and both have constant
coefficient `1`, so they agree by the coefficient recursion that the
equation pins down.  A reusable uniqueness lemma
`odeUnique_of_constEq` packages the recursion argument.

Coefficient extraction yields the consumer-facing convolution formula
`newtonH_add`, together with its integer-indexed form `newtonHZ_add`
for Jacobi–Trudi consumers.
-/

namespace RS

open Finset PowerSeries

/-! ### Additivity of the power-sum series -/

/-- The shifted power-sum series is additive in the scalar sequence. -/
theorem powerSumSeries_add (t t' : ℕ → ℂ) :
    powerSumSeries (fun c => t c + t' c) =
      powerSumSeries t + powerSumSeries t' := by
  ext n
  simp only [powerSumSeries, coeff_mk, map_add]

/-! ### Uniqueness for the first-order linear ODE -/

/-- **Uniqueness for `F′ = P · F`.**  Two power series satisfying the
same first-order linear differential equation with equal constant
coefficients are equal: the equation determines each coefficient from
the earlier ones by the recursion
`(n + 1) · F_{n+1} = ∑_{i+j=n} P_i · F_j`, and division by the
nonzero scalar `n + 1` closes the strong induction. -/
theorem odeUnique_of_constEq (P F G : ℂ⟦X⟧)
    (hF : d⁄dX ℂ F = P * F) (hG : d⁄dX ℂ G = P * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
        rw [coeff_zero_eq_constantCoeff_apply,
          coeff_zero_eq_constantCoeff_apply, h0]
    | succ m =>
        have hFm := congrArg (coeff m) hF
        have hGm := congrArg (coeff m) hG
        rw [coeff_derivative, coeff_mul] at hFm hGm
        have hsum :
            ∑ ij ∈ Finset.antidiagonal m, coeff ij.1 P * coeff ij.2 F =
              ∑ ij ∈ Finset.antidiagonal m, coeff ij.1 P * coeff ij.2 G := by
          refine Finset.sum_congr rfl fun ij hij => ?_
          have h2 : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
          rw [ih ij.2 (by omega)]
        exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero m)
          (hFm.trans (hsum.trans hGm.symm))

/-! ### The convolution identity -/

/-- **Convolution of Newton generating series.**  The generating
series of the complete homogeneous sequence of a sum of scalar
sequences is the product of the individual generating series. -/
theorem newtonHSeries_add (t t' : ℕ → ℂ) :
    newtonHSeries (fun c => t c + t' c) =
      newtonHSeries t * newtonHSeries t' := by
  apply odeUnique_of_constEq (powerSumSeries t + powerSumSeries t')
  · rw [newtonH_derivative, powerSumSeries_add]
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      newtonH_derivative, newtonH_derivative]
    ring
  · rw [map_mul, newtonH_series_constantCoeff,
      newtonH_series_constantCoeff, newtonH_series_constantCoeff,
      mul_one]

/-- **The convolution formula for complete homogeneous values.**
`h_n (t + t') = ∑_{i+j=n} h_i (t) · h_j (t')`. -/
theorem newtonH_add (t t' : ℕ → ℂ) (n : ℕ) :
    newtonH (fun c => t c + t' c) n =
      ∑ ij ∈ Finset.antidiagonal n, newtonH t ij.1 * newtonH t' ij.2 := by
  have h := congrArg (coeff n) (newtonHSeries_add t t')
  rw [coeff_mul] at h
  simpa only [newtonHSeries, coeff_mk] using h

/-- The convolution formula in the integer-indexed form used by
Jacobi–Trudi consumers: for `0 ≤ m` the value `newtonHZ (t + t') m`
is the antidiagonal convolution over `m.toNat` (in negative degrees
both sides vanish by `newtonHZ_neg`, so the nonnegative case carries
all content). -/
theorem newtonHZ_add (t t' : ℕ → ℂ) (m : ℤ) (hm : 0 ≤ m) :
    newtonHZ (fun c => t c + t' c) m =
      ∑ ij ∈ Finset.antidiagonal m.toNat,
        newtonHZ t ij.1 * newtonHZ t' ij.2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [newtonHZ_natCast, Int.toNat_natCast, newtonH_add]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [newtonHZ_natCast, newtonHZ_natCast]

end RS
