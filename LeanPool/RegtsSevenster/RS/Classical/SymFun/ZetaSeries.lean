/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums

/-!
# Zeta series characterization

The Newton generating series `newtonHSeries t` is the unique power
series with constant term 1 satisfying the trace-zeta differential
equation `H' = S · H`, where `S = powerSumSeries t` is the shifted
power-sum series.  This file establishes the ODE-uniqueness principle
for formal power series over ℂ and applies it to characterize the
Newton series.
-/

namespace RS

open Finset PowerSeries

/-! ### ODE uniqueness for formal power series -/

/-- **ODE uniqueness for formal power series over ℂ.**
If two power series `F` and `G` both have constant term `1` and
satisfy the same first-order linear ODE `F' = S · F`, then `F = G`.

Proof: coefficient induction.  The ODE implies
`(n+1) · coeff (n+1) F = ∑_{i+j=n} coeff i S · coeff j F`;
since all coefficients up to `n` agree by the inductive hypothesis,
the sums for `F` and `G` coincide, and `(n+1) ≠ 0` in `ℂ` allows
cancellation. -/
theorem powerSeries_ode_unique {F G S : PowerSeries ℂ}
    (hF0 : constantCoeff F = 1)
    (hG0 : constantCoeff G = 1)
    (hF : (PowerSeries.derivative (R := ℂ)) F = S * F)
    (hG : (PowerSeries.derivative (R := ℂ)) G = S * G) : F = G := by
  ext n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      rw [coeff_zero_eq_constantCoeff_apply, hF0,
          coeff_zero_eq_constantCoeff_apply, hG0]
    | n + 1 =>
      have hFn : coeff n ((PowerSeries.derivative (R := ℂ)) F) = coeff n (S * F) := congr_arg (coeff n) hF
      have hGn : coeff n ((PowerSeries.derivative (R := ℂ)) G) = coeff n (S * G) := congr_arg (coeff n) hG
      rw [coeff_derivative] at hFn hGn
      rw [coeff_mul] at hFn hGn
      have heq : ∑ p ∈ antidiagonal n, coeff p.1 S * coeff p.2 F =
                 ∑ p ∈ antidiagonal n, coeff p.1 S * coeff p.2 G := by
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        congr 1
        exact ih j (by have := mem_antidiagonal.mp hij; omega)
      have hne : (↑n + 1 : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      exact mul_right_cancel₀ hne (hFn.trans (heq.trans hGn.symm))

/-! ### The Newton ODE -/

/-- The Newton generating series satisfies the trace-zeta ODE:
`d⁄dX (newtonHSeries t) = powerSumSeries t * newtonHSeries t`.
This is a re-export of `newtonH_derivative`. -/
theorem newtonH_series_ode (t : ℕ → ℂ) :
    (PowerSeries.derivative (R := ℂ)) (newtonHSeries t) = powerSumSeries t * newtonHSeries t :=
  newtonH_derivative t

/-! ### The zeta characterization -/

/-- Any power series with constant term 1 satisfying the trace-zeta
differential equation is the Newton series: the trace zeta function
IS the complete homogeneous generating function. -/
theorem eq_newtonH_series_of_ode {t : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF0 : constantCoeff F = 1)
    (hF : (PowerSeries.derivative (R := ℂ)) F = powerSumSeries t * F) :
    F = newtonHSeries t :=
  powerSeries_ode_unique hF0 (newtonH_series_constantCoeff t) hF
    (newtonH_series_ode t)

end RS
