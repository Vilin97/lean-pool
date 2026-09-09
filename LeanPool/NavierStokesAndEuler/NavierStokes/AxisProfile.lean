/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Algebraic checks for the natural axis profile

These theorems concern the scaled leading equations and the two explicit
truncations in Proposition 5.1 of the candidate manuscript.  They do not
establish convergence of a formal power series, the nonlinear remainder
estimates, the contraction argument, or the full profile's cone margin.
-/

@[expose] public section


namespace NavierStokes.AxisProfile

noncomputable section

/-- The coefficient of `Y^n` in `(Y ∂YY + m ∂Y) a`, at the formal
coefficient level. -/
def radialOperatorCoeff (m : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((n : ℝ) + m) * a (n + 1)

/-- The regular zero-datum formal inverse used in the scaled equations. -/
def radialInverseCoeff (m : ℕ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => f n / (((n : ℝ) + 1) * ((n : ℝ) + m))

@[simp] theorem radialInverseCoeff_zero (m : ℕ) (f : ℕ → ℝ) :
    radialInverseCoeff m f 0 = 0 := rfl

/-- For positive `m`, the stated shift really inverts the formal radial
operator.  No assertion about convergence is implicit in this theorem. -/
theorem radialOperator_inverse (m : ℕ) (hm : 0 < m) (f : ℕ → ℝ) (n : ℕ) :
    radialOperatorCoeff m (radialInverseCoeff m f) n = f n := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hden : ((n : ℝ) + 1) * ((n : ℝ) + m) ≠ 0 := by positivity
  unfold radialOperatorCoeff
  rw [radialInverseCoeff]
  exact mul_div_cancel₀ (f n) hden

/-- The leading angular series coefficient from Proposition 5.1:
`(-χ/2)^n / (n! (n+1)!)`. -/
def profileCoeff (χ : ℝ) (n : ℕ) : ℝ :=
  (-χ / 2) ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))

@[simp] theorem profileCoeff_zero (χ : ℝ) : profileCoeff χ 0 = 1 := by
  norm_num [profileCoeff]

/-- Exact recurrence for the displayed regular series. -/
theorem profileCoeff_recurrence (χ : ℝ) (n : ℕ) :
    2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * profileCoeff χ (n + 1) =
      -χ * profileCoeff χ n := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  simp only [profileCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp; ring

/-- The formal series solves the leading angular equation coefficient by
coefficient. This does not identify an analytic solution. -/
theorem profileCoeff_scaled_equation (χ : ℝ) (n : ℕ) :
    2 * radialOperatorCoeff 2 (profileCoeff χ) n = -χ * profileCoeff χ n := by
  simpa only [radialOperatorCoeff, Nat.cast_ofNat, mul_assoc] using
    profileCoeff_recurrence χ n

/-- The coefficient transformation for the formal combination `f + Yf'`
is exactly the factorial-square series used for the sign test. -/
theorem weighted_profileCoeff (χ : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * profileCoeff χ n =
      (-χ / 2) ^ n / (n.factorial : ℝ) ^ 2 := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [profileCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp

/-- The cubic lower truncation in the manuscript, with `t = Yχ/2`. -/
def cubicLower (t : ℝ) : ℝ := 1 - t / 2 + t ^ 2 / 12 - t ^ 3 / 144

/-- The quartic upper truncation for `f₀ + s f₀'`, in the variable `t=s/2`. -/
def quarticUpper (t : ℝ) : ℝ :=
  1 - t + t ^ 2 / 4 - t ^ 3 / 36 + t ^ 4 / 576

/-- A rational positivity certificate for the lower truncation on
`t ≤ 2.05`; the natural application also has `t ≥ 0`. -/
theorem cubicLower_gt_quarter (t : ℝ) (ht : t ≤ 41 / 20) :
    1 / 4 < cubicLower t := by
  have hd : 0 ≤ 41 / 20 - t := sub_nonneg.mpr ht
  have h2 : 0 ≤ (41 / 20 - t) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (41 / 20 - t) ^ 3 := pow_nonneg hd _
  have hidentity : cubicLower t =
      cubicLower (41 / 20) +
      (1 / 2 - (41 / 20) / 6 + (41 / 20) ^ 2 / 48) * (41 / 20 - t) +
      (1 / 12 - (41 / 20) / 48) * (41 / 20 - t) ^ 2 +
      (41 / 20 - t) ^ 3 / 144 := by
    unfold cubicLower
    ring
  norm_num [cubicLower] at hidentity
  unfold cubicLower
  nlinarith

/-- A direct rational verification of the numerical strict inequality
used for the initial cone margin. -/
theorem quarticUpper_lt_neg_eighteen_hundredths
    (t : ℝ) (hlo : 99 / 50 ≤ t) (hhi : t ≤ 2) :
    quarticUpper t < -(18 / 100) := by
  have ht : 0 ≤ t := by linarith
  have hsmall : 0 ≤ 1 - t / 2 := by linarith
  have hsmall_le : 1 - t / 2 ≤ 1 / 100 := by linarith
  have hsquare := pow_le_pow_left₀ hsmall hsmall_le 2
  have hcube := pow_le_pow_left₀ (show (0 : ℝ) ≤ 99 / 50 by norm_num) hlo 3
  have hfour := pow_le_pow_left₀ ht hhi 4
  norm_num at hsquare hcube hfour
  unfold quarticUpper
  nlinarith

/-- The first four actual displayed series terms, for a concrete link
between the coefficient calculation and the lower polynomial. -/
theorem first_four_terms_eq_cubic (χ Y : ℝ) :
    profileCoeff χ 0 + profileCoeff χ 1 * Y +
      profileCoeff χ 2 * Y ^ 2 + profileCoeff χ 3 * Y ^ 3 =
      cubicLower (Y * χ / 2) := by
  norm_num [profileCoeff, cubicLower, Nat.factorial_succ]
  ring

/-- The first five terms of the formal `f + Yf'` series give exactly the
quartic sign-test polynomial. -/
theorem first_five_weighted_terms_eq_quartic (χ Y : ℝ) :
    profileCoeff χ 0 + 2 * profileCoeff χ 1 * Y +
      3 * profileCoeff χ 2 * Y ^ 2 + 4 * profileCoeff χ 3 * Y ^ 3 +
      5 * profileCoeff χ 4 * Y ^ 4 = quarticUpper (Y * χ / 2) := by
  norm_num [profileCoeff, quarticUpper, Nat.factorial_succ]
  ring

/-- The leading axial profile displayed in the scaled construction. -/
def leadingAxial (Z L Y : ℝ) : ℝ := -Y * Z / (2 * L)

theorem leadingAxial_zero (Z L : ℝ) : leadingAxial Z L 0 = 0 := by
  simp [leadingAxial]

theorem hasDerivAt_leadingAxial (Z L Y : ℝ) :
    HasDerivAt (leadingAxial Z L) (-Z / (2 * L)) Y := by
  have hfun : leadingAxial Z L = fun x : ℝ => (-Z / (2 * L)) * x := by
    funext x
    unfold leadingAxial
    ring
  rw [hfun]
  simpa only [id_eq, mul_one] using (hasDerivAt_id Y).const_mul (-Z / (2 * L))

/-- The derivative of the linear leading axial solution is constant. -/
theorem hasDerivAt_leadingAxial_derivative (Z L Y : ℝ) :
    HasDerivAt (fun _ : ℝ => -Z / (2 * L)) 0 Y :=
  hasDerivAt_const Y _

/-- The derivative as a function, permitting a second differentiation. -/
theorem deriv_leadingAxial (Z L : ℝ) :
    deriv (leadingAxial Z L) = fun _ : ℝ => -Z / (2 * L) := by
  funext Y
  exact (hasDerivAt_leadingAxial Z L Y).deriv

/-- The linear leading axial profile satisfies the actual scaled ODE. -/
theorem leadingAxial_scaled_equation (Z L Y : ℝ) (hL : L ≠ 0) :
    2 * (Y * deriv (deriv (leadingAxial Z L)) Y + deriv (leadingAxial Z L) Y) =
      -Z / L := by
  rw [deriv_leadingAxial]
  simp only [deriv_const, mul_zero, zero_add]
  field_simp

end

end NavierStokes.AxisProfile
