/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaTrace

/-!
# Uniqueness of a normalized formal point-count zeta series

Over the complex numbers, the differential equation

`Z' = Z * A`

together with the constant coefficient of `Z` determines a formal power
series uniquely.  This gives the formal bridge needed after proving Euler's
coefficient identity for an effective-divisor zeta series: that series is the
canonical exponential `formalPointCountZeta`.
-/

namespace BGS.HasseWeil

noncomputable section

/-- Two formal power series with the same constant coefficient and the same
logarithmic-derivative equation are equal. -/
theorem powerSeries_eq_of_constantCoeff_eq_of_derivative_eq_mul
    (F G A : PowerSeries ℂ)
    (hconstant : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G)
    (hF : PowerSeries.derivative ℂ F = F * A)
    (hG : PowerSeries.derivative ℂ G = G * A) :
    F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hconstant
    | succ n =>
      have hFc := congrArg (PowerSeries.coeff n) hF
      have hGc := congrArg (PowerSeries.coeff n) hG
      rw [PowerSeries.coeff_derivative] at hFc hGc
      have hmul : PowerSeries.coeff n (F * A) =
          PowerSeries.coeff n (G * A) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hle : ij.1 ≤ n :=
          Finset.HasAntidiagonal.antidiagonal.fst_le hij
        rw [show PowerSeries.coeff ij.1 F = PowerSeries.coeff ij.1 G by
          exact ih ij.1 (Nat.lt_succ_of_le hle)]
      have hcast : (n : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      apply mul_right_cancel₀ hcast
      calc
        PowerSeries.coeff (n + 1) F * ((n : ℂ) + 1) =
            PowerSeries.coeff n (F * A) := hFc
        _ = PowerSeries.coeff n (G * A) := hmul
        _ = PowerSeries.coeff (n + 1) G * ((n : ℂ) + 1) := hGc.symm

/-- A normalized series satisfying Euler's point-count derivative identity
is the canonical exponential point-count zeta series. -/
theorem eq_formalPointCountZeta_of_normalized_pointCountDerivative
    (Z : PowerSeries ℂ) (pointCount : ℕ → ℕ)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (htrace : HasFormalZetaPointCountDerivative Z pointCount) :
    Z = formalPointCountZeta pointCount := by
  apply powerSeries_eq_of_constantCoeff_eq_of_derivative_eq_mul
      Z (formalPointCountZeta pointCount) (pointCountDerivativeSeries pointCount)
  · rw [hZ0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [formalPointCountZeta,
      PowerSeries.coeff_subst'
        (pointCountLogSeries_hasSubst pointCount)]
    rw [finsum_eq_single _ 0]
    · simp [pointCountLogSeries]
    · intro d hd
      simp [pointCountLogSeries, zero_pow hd]
  · exact htrace
  · exact formalPointCountZeta_hasPointCountDerivative pointCount

end

end BGS.HasseWeil
