/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.ZetaSeries

/-!
# The trace zeta function in exponential form

`traceZeta t = exp (∑_{m≥1} t m / m · zᵐ)` as a formal power
series, and its identification with the Newton generating series
via the differential characterization — the displayed form of the
trace zeta function.
-/

namespace RS

open PowerSeries

/-- The power-sum logarithm `∑_{m≥1} t m / m · zᵐ`. -/
noncomputable def psLog (t : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => if m = 0 then 0 else t m / m)

/-- The log series has no constant term. -/
theorem constantCoeff_psLog (t : ℕ → ℂ) :
    constantCoeff (psLog t) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, psLog, coeff_mk, if_pos rfl]

/-- Hence it can be substituted into the exponential. -/
theorem hasSubst_psLog (t : ℕ → ℂ) : HasSubst (psLog t) :=
  HasSubst.of_constantCoeff_zero (constantCoeff_psLog t)

/-- The derivative of the power-sum logarithm is the power-sum
series. -/
theorem derivative_psLog (t : ℕ → ℂ) :
    (PowerSeries.derivative (R := ℂ)) (psLog t) = powerSumSeries t := by
  ext n
  rw [coeff_derivative, psLog, coeff_mk, if_neg (by omega)]
  rw [show coeff n (powerSumSeries t) = t (n + 1) from by
    rw [powerSumSeries, coeff_mk]]
  have hne : (((n + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp
  push_cast
  ring

/-- **The trace zeta function** in exponential form. -/
noncomputable def traceZeta (t : ℕ → ℂ) : PowerSeries ℂ :=
  (exp ℂ).subst (psLog t)

/-- **The zeta identification**: the exponential form equals the
Newton generating series. -/
theorem traceZeta_eq_newtonH_series (t : ℕ → ℂ) :
    traceZeta t = newtonHSeries t := by
  apply eq_newtonH_series_of_ode
  · rw [traceZeta, ← coeff_zero_eq_constantCoeff]
    rw [coeff_subst' (hasSubst_psLog t)]
    rw [finsum_eq_single _ 0 (fun d hd => ?_)]
    · rw [pow_zero, coeff_zero_eq_constantCoeff, map_one,
        smul_eq_mul, mul_one]
      exact constantCoeff_exp
    · rw [coeff_zero_eq_constantCoeff, map_pow,
        constantCoeff_psLog, zero_pow hd, smul_zero]
  · rw [traceZeta, derivative_subst (hasSubst_psLog t),
      derivative_exp, derivative_psLog]
    rw [mul_comm]

end RS
