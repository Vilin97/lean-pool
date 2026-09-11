/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalAxisBridge
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Identification and positivity of the actual natural-axis reference

The reference is the image of the unit datum under the constructed Banach-space
resolvent. Its coefficient recurrence identifies its evaluation with the entire
leading series. Uniform estimates for the actual nonlinear profiles then preserve
positivity and a strict logarithmic-slope margin at one common parameter scale.
-/

section

/-!
# Convergent series for the leading natural axis profile

This module concerns the leading scaled linear equation of Proposition 5.1,
not the nonlinear perturbation or the claimed uniform remainder estimates.
-/

section

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

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.AxisSeries

open scoped BigOperators Topology
open Filter Set

/-- Terms of a family of entire factorial-denominator series. -/
def term (k n : ℕ) (t : ℝ) : ℝ :=
  (-t) ^ n / ((n.factorial : ℝ) * ((n + k).factorial : ℝ))

/-- The generalized leading series; the axis profile uses `k=1`. -/
def bessel (k : ℕ) (t : ℝ) : ℝ := ∑' n : ℕ, term k n t

theorem term_norm_le (k n : ℕ) (t R : ℝ) (hR : 0 ≤ R) (ht : |t| ≤ R) :
    ‖term k n t‖ ≤ R ^ n / (n.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (n + k))
  have hn : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  calc
    ‖term k n t‖ = |t| ^ n /
        ((n.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
      simp [term, Real.norm_eq_abs]
    _ ≤ R ^ n / ((n.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
      gcongr
    _ ≤ R ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_left (pow_nonneg hR _) hn
      nlinarith

/-- Absolute summability, proved by comparison with the exponential series. -/
theorem summable_term (k : ℕ) (t : ℝ) : Summable (fun n : ℕ => term k n t) := by
  exact Summable.of_norm_bounded
    (Real.summable_pow_div_factorial |t|)
    (fun n => term_norm_le k n t |t| (abs_nonneg t) le_rfl)

theorem summable_norm_term (k : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => ‖term k n t‖) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial |t|)
  intro n
  simpa only [norm_norm] using term_norm_le k n t |t| (abs_nonneg t) le_rfl

theorem summable_term_tail (k j : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => term k (n + j) t) :=
  (summable_nat_add_iff j).mpr (summable_term k t)

/-- Differentiating a successor-index term cancels one factorial factor. -/
theorem hasDerivAt_term_succ (k n : ℕ) (t : ℝ) :
    HasDerivAt (term k (n + 1)) (-term (k + 1) n t) t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hk : ((n + (k + 1)).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert! (((hasDerivAt_id t).fun_neg.fun_pow (n + 1)).div_const
    ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial (n + 1 + k) : ℝ))) using 1
  simp only [term, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, id_eq]
  rw [show n + 1 + k = n + (k + 1) by omega]
  field_simp

theorem bessel_eq_constant_add_tail (k : ℕ) (t : ℝ) :
    bessel k t = 1 / (k.factorial : ℝ) + ∑' n : ℕ, term k (n + 1) t := by
  simpa [bessel, term] using (summable_term k t).tsum_eq_zero_add

/-- Differentiation of the convergent infinite series on every real point. -/
theorem hasDerivAt_bessel (k : ℕ) (t : ℝ) :
    HasDerivAt (bessel k) (-bessel (k + 1) t) t := by
  let R : ℝ := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Ioo (-R) R := by
    dsimp [R]
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have htail : HasDerivAt (fun x : ℝ => ∑' n : ℕ, term k (n + 1) x)
      (∑' n : ℕ, -term (k + 1) n t) t := by
    apply hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => R ^ n / (n.factorial : ℝ))
      (g := fun n y => term k (n + 1) y)
      (g' := fun n y => -term (k + 1) n y)
      (t := Ioo (-R) R) (y₀ := t)
      (Real.summable_pow_div_factorial R) isOpen_Ioo isPreconnected_Ioo
    · intro n y _
      exact hasDerivAt_term_succ k n y
    · intro n y hy
      rw [norm_neg]
      exact term_norm_le (k + 1) n y R hR.le
        (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
    · exact ht
    · exact summable_term_tail k 1 t
    · exact ht
  have hfun : bessel k = fun x : ℝ =>
      1 / (k.factorial : ℝ) + ∑' n : ℕ, term k (n + 1) x := by
    funext x
    exact bessel_eq_constant_add_tail k x
  rw [hfun]
  simpa only [tsum_neg, bessel] using htail.const_add (1 / (k.factorial : ℝ))

theorem deriv_bessel (k : ℕ) :
    deriv (bessel k) = fun t : ℝ => -bessel (k + 1) t := by
  funext t
  exact (hasDerivAt_bessel k t).deriv

/-- A termwise contiguous relation, with the constant term removed. -/
theorem term_contiguous (k n : ℕ) (t : ℝ) :
    term k (n + 1) t = ((k : ℝ) + 1) * term (k + 1) (n + 1) t -
      t * term (k + 2) n t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnk : (n : ℝ) + k + 1 ≠ 0 := by positivity
  have hnk' : (n : ℝ) + k + 1 + 1 ≠ 0 := by positivity
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfk : ((n + k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [term, show n + 1 + k = (n + k) + 1 by omega,
    show n + 1 + (k + 1) = (n + k) + 1 + 1 by omega,
    show n + (k + 2) = (n + k) + 1 + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp; ring

theorem factorial_reciprocal (k : ℕ) :
    1 / (k.factorial : ℝ) = ((k : ℝ) + 1) * (1 / ((k + 1).factorial : ℝ)) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The convergent sums satisfy the contiguous relation underlying the ODE. -/
theorem bessel_contiguous (k : ℕ) (t : ℝ) :
    bessel k t = ((k : ℝ) + 1) * bessel (k + 1) t - t * bessel (k + 2) t := by
  have htail : (∑' n : ℕ, term k (n + 1) t) =
      ((k : ℝ) + 1) * (∑' n : ℕ, term (k + 1) (n + 1) t) -
      t * (∑' n : ℕ, term (k + 2) n t) := by
    calc
      _ = ∑' n : ℕ, (((k : ℝ) + 1) * term (k + 1) (n + 1) t -
          t * term (k + 2) n t) := tsum_congr (fun n => term_contiguous k n t)
      _ = _ := by
        rw [((summable_term_tail (k + 1) 1 t).mul_left ((k : ℝ) + 1)).tsum_sub
          ((summable_term (k + 2) t).mul_left t), tsum_mul_left, tsum_mul_left]
  rw [bessel_eq_constant_add_tail k t, bessel_eq_constant_add_tail (k + 1) t,
    htail, factorial_reciprocal k]
  unfold bessel
  ring

theorem second_deriv_bessel (k : ℕ) (t : ℝ) :
    deriv (deriv (bessel k)) t = bessel (k + 2) t := by
  rw [deriv_bessel]
  simpa only [neg_neg, Nat.add_assoc] using (hasDerivAt_bessel (k + 1) t).fun_neg.deriv

/-- An actual differential equation for the infinite function. -/
theorem bessel_ode (k : ℕ) (t : ℝ) :
    t * deriv (deriv (bessel k)) t + ((k : ℝ) + 1) * deriv (bessel k) t +
      bessel k t = 0 := by
  rw [second_deriv_bessel, deriv_bessel, bessel_contiguous k t]
  ring

theorem bessel_zero (k : ℕ) : bessel k 0 = 1 / (k.factorial : ℝ) := by
  rw [bessel_eq_constant_add_tail]
  simp [term]

/-- The leading regular angular profile in the manuscript's scaled radius. -/
def profile (χ Y : ℝ) : ℝ := bessel 1 ((χ / 2) * Y)

theorem profile_eq_tsum (χ Y : ℝ) :
    profile χ Y = ∑' n : ℕ, (-χ * Y / 2) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  unfold profile bessel term
  apply tsum_congr
  intro n
  congr 2
  ring

theorem profile_zero (χ : ℝ) : profile χ 0 = 1 := by
  simp [profile, bessel_zero]

theorem hasDerivAt_profile (χ Y : ℝ) :
    HasDerivAt (profile χ) (-(χ / 2) * bessel 2 ((χ / 2) * Y)) Y := by
  convert! (hasDerivAt_bessel 1 ((χ / 2) * Y)).comp Y
    ((hasDerivAt_id Y).const_mul (χ / 2)) using 1
  simp only [mul_one]
  ring

theorem deriv_profile (χ : ℝ) :
    deriv (profile χ) = fun Y : ℝ => -(χ / 2) * bessel 2 ((χ / 2) * Y) := by
  funext Y
  exact (hasDerivAt_profile χ Y).deriv

theorem second_deriv_profile (χ Y : ℝ) :
    deriv (deriv (profile χ)) Y = (χ / 2) ^ 2 * bessel 3 ((χ / 2) * Y) := by
  rw [deriv_profile]
  have h := ((hasDerivAt_bessel 2 ((χ / 2) * Y)).comp Y
    ((hasDerivAt_id Y).const_mul (χ / 2))).const_mul (-(χ / 2))
  convert! h.deriv using 1
  simp only [mul_one]
  ring

/-- The leading regular equation `2(YΦ''+2Φ') = -χΦ`, for the actual sum. -/
theorem profile_scaled_ode (χ Y : ℝ) :
    2 * (Y * deriv (deriv (profile χ)) Y + 2 * deriv (profile χ) Y) =
      -χ * profile χ Y := by
  rw [second_deriv_profile, deriv_profile]
  unfold profile
  rw [bessel_contiguous 1 ((χ / 2) * Y)]
  norm_num
  ring

/-- The exact successive-term ratio, including its sign. -/
theorem term_succ_ratio (k n : ℕ) (t : ℝ) :
    term k (n + 1) t =
      (-t) / (((n : ℝ) + 1) * ((n : ℝ) + k + 1)) * term k n t := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnk : (n : ℝ) + k + 1 ≠ 0 := by positivity
  have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfk : ((n + k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [term, show n + 1 + k = (n + k) + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem term_sign (k n : ℕ) (t : ℝ) :
    term k n t = (-1 : ℝ) ^ n * term k n (-t) := by
  simp only [term, neg_neg]
  rw [show -t = (-1 : ℝ) * t by ring, mul_pow]
  ring

/-- Once at least the zeroth term is removed, the remaining magnitudes
decrease on `0 ≤ t ≤ 4`, for every nonnegative factorial offset. -/
theorem magnitude_tail_antitone (k j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    Antitone (fun n : ℕ => term k (n + j) (-t)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [show n + 1 + j = (n + j) + 1 by omega, term_succ_ratio]
  simp only [neg_neg]
  have hm : 0 ≤ term k (n + j) (-t) := by
    unfold term
    simp only [neg_neg]
    positivity
  have hd : 0 < (((n + j : ℕ) : ℝ) + 1) * (((n + j : ℕ) : ℝ) + k + 1) := by
    positivity
  apply mul_le_of_le_one_left hm
  apply (div_le_one hd).mpr
  have hnj : (1 : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + j by omega)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hleft : (2 : ℝ) ≤ ((n + j : ℕ) : ℝ) + 1 := by linarith
  have hright : (2 : ℝ) ≤ ((n + j : ℕ) : ℝ) + k + 1 := by linarith
  have hprod := mul_le_mul hleft hright (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 ≤ ((n + j : ℕ) : ℝ) + 1)
  linarith

/-- The cubic tail is an instance of the preceding magnitude estimate. -/
theorem cubic_tail_antitone (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    Antitone (fun n : ℕ => term 1 (n + 4) (-t)) :=
  magnitude_tail_antitone 1 4 (by norm_num) t ht0 (by linarith)

/-- The infinite alternating tail following the cubic has nonnegative sum. -/
theorem cubic_tail_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    0 ≤ ∑' n : ℕ, term 1 (n + 4) t := by
  have hsign : (fun n : ℕ => term 1 (n + 4) t) =
      fun n : ℕ => (-1 : ℝ) ^ n * term 1 (n + 4) (-t) := by
    funext n
    rw [term_sign, pow_add]
    norm_num
  have hs := (summable_term_tail 1 4 t).hasSum
  rw [hsign] at hs
  have hb := Antitone.alternating_series_le_tendsto hs.tendsto_sum_nat
    (cubic_tail_antitone t ht0 ht) 0
  simpa only [hsign, mul_zero, Finset.range_zero, Finset.sum_empty] using hb

theorem cubic_lower_le_bessel (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    AxisProfile.cubicLower t ≤ bessel 1 t := by
  have hpoly : (∑ n ∈ Finset.range 4, term 1 n t) = AxisProfile.cubicLower t := by
    norm_num [Finset.sum_range_succ, term, AxisProfile.cubicLower, Nat.factorial_succ]
    ring
  have hs := (summable_term 1 t).sum_add_tsum_nat_add 4
  rw [hpoly] at hs
  have ht' := cubic_tail_nonneg t ht0 ht
  unfold bessel
  linarith

/-- A uniform positive lower bound for the actual infinite leading series. -/
theorem bessel_one_gt_quarter (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    1 / 4 < bessel 1 t :=
  lt_of_lt_of_le (AxisProfile.cubicLower_gt_quarter t ht)
    (cubic_lower_le_bessel t ht0 ht)

/-- Positivity on the entire axis interval requested in Proposition 5.1,
for the leading profile rather than its nonlinear perturbation. -/
theorem profile_gt_quarter (χ Y : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) : 1 / 4 < profile χ Y := by
  apply bessel_one_gt_quarter
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hχ1) hY0]

theorem profile_pos (χ Y : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) : 0 < profile χ Y := by
  have h := profile_gt_quarter χ Y hχ0 hχ1 hY0 hY1
  linarith

/-- A convergent alternating tail beginning with its positive sign has
nonnegative total, for every offset starting after at least one term. -/
theorem alternating_tail_nonneg (k j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    0 ≤ ∑' n : ℕ, (-1 : ℝ) ^ n * term k (n + j) (-t) := by
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    apply Summable.of_norm_bounded
      ((summable_nat_add_iff j).mpr (summable_norm_term k (-t)))
    intro n
    simp
  have hb := Antitone.alternating_series_le_tendsto hs.hasSum.tendsto_sum_nat
    (magnitude_tail_antitone k j hj t ht0 ht) 0
  simpa using hb

/-- Every odd-length truncation with at least one term is an upper bound
on the actual series on this interval. -/
theorem bessel_le_odd_partial_sum (k j : ℕ) (hj : 1 ≤ j) (hodd : Odd j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    bessel k t ≤ ∑ n ∈ Finset.range j, term k n t := by
  have hsign : ∀ n : ℕ, term k (n + j) t =
      -((-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    intro n
    rw [term_sign, pow_add, hodd.neg_one_pow]
    ring
  have htail : (∑' n : ℕ, term k (n + j) t) =
      -(∑' n : ℕ, (-1 : ℝ) ^ n * term k (n + j) (-t)) := by
    simp_rw [hsign]
    rw [tsum_neg]
  have hs := (summable_term k t).sum_add_tsum_nat_add j
  have hnonneg := alternating_tail_nonneg k j hj t ht0 ht
  rw [htail] at hs
  unfold bessel
  linarith

theorem bessel_one_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    bessel 1 t ≤ 1 := by
  have h := bessel_le_odd_partial_sum 1 1 (by norm_num) (by norm_num) t ht0 ht
  simpa [Finset.sum_range_succ, term] using h

/-- The quartic upper bound controls the actual factorial-square series. -/
theorem bessel_zero_lt_neg_eighteen_hundredths
    (t : ℝ) (ht0 : 99 / 50 ≤ t) (ht1 : t ≤ 2) :
    bessel 0 t < -(18 / 100) := by
  have h := bessel_le_odd_partial_sum 0 5 (by norm_num) ⟨2, by norm_num⟩ t
    (by linarith) (by linarith)
  have hpoly : (∑ n ∈ Finset.range 5, term 0 n t) = AxisProfile.quarticUpper t := by
    norm_num [Finset.sum_range_succ, term, AxisProfile.quarticUpper, Nat.factorial_succ]
    ring
  rw [hpoly] at h
  exact lt_of_le_of_lt h (AxisProfile.quarticUpper_lt_neg_eighteen_hundredths t ht0 ht1)

/-- The derivative combination used in the manuscript's sign test is now
an identity of differentiable infinite functions. -/
theorem bessel_one_add_mul_deriv (t : ℝ) :
    bessel 1 t + t * deriv (bessel 1) t = bessel 0 t := by
  rw [deriv_bessel, bessel_contiguous 0 t]
  norm_num
  ring

theorem bessel_one_log_slope_gt (t : ℝ) (ht0 : 99 / 50 ≤ t) (ht1 : t ≤ 2) :
    236 / 100 < -2 * t * deriv (bessel 1) t / bessel 1 t := by
  have hpos : 0 < bessel 1 t := by
    have h := bessel_one_gt_quarter t (by linarith) (by linarith)
    linarith
  have hupper := bessel_one_le_one t (by linarith) (by linarith)
  have hsign := bessel_zero_lt_neg_eighteen_hundredths t ht0 ht1
  rw [← bessel_one_add_mul_deriv t] at hsign
  apply (lt_div_iff₀ hpos).mpr
  nlinarith

/-- The exact leading profile has the stated `2.36` slope margin at `Y=4`
when `χ≥0.99`. No perturbation estimate is asserted. -/
theorem profile_log_slope_at_four (χ : ℝ) (hχ0 : 99 / 100 ≤ χ) (hχ1 : χ ≤ 1) :
    236 / 100 < -8 * deriv (profile χ) 4 / profile χ 4 := by
  have h := bessel_one_log_slope_gt ((χ / 2) * 4) (by linarith) (by linarith)
  rw [deriv_bessel] at h
  rw [deriv_profile]
  unfold profile
  convert! h using 1
  ring

end NavierStokes.AxisSeries

end

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.AxisReference

open Set AxisCoefficientSpace AxisWeightEstimates NaturalAxisBridge
open scoped BigOperators Topology ContDiff

theorem coefficient_naturalOperator_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) 0 η = 0 := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hz := AxisOperators.jet_regularInverse_zero I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) 0 hη
  dsimp only [AxisOperators.inputJet] at hz
  rw [hz, mul_zero]

theorem coefficient_naturalOperator_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalOperator I hε χ A) (n + 1) η =
      (1 / 2 : ℝ) * (coefficient I (weight ε) χ 0 η *
        coefficient I (weight ε) A n η / radialDivisor 2 n) := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coefficient, Submodule.coe_smul, jet_smul]
  have hs := AxisOperators.jet_regularInverse_succ I hε 2 (by norm_num)
    (AxisOperators.product I hε χ A) n 0 hη
  dsimp only [AxisOperators.inputJet] at hs
  rw [hs]
  change (1 / 2 : ℝ) *
      (coefficient I (weight ε) (AxisOperators.product I hε χ A) n η /
        radialDivisor 2 n) = _
  rw [coefficient_product_constant I hε χ A hχ n hη]
  rfl

/-- The unit datum is preserved at the axis by the actual resolvent. -/
theorem reference_coefficient_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval)
    (he : coefficient I (weight ε) e 0 η = 1) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η = 1 := by
  have heq := congrArg (fun A : AxisSpace I ε => coefficient I (weight ε) A 0 η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) 0 η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) 0 η =
      coefficient I (weight ε) e 0 η at heq
  rw [coefficient_naturalOperator_zero I hε χ _ hη, add_zero, he] at heq
  exact heq

/-- Every higher coefficient is forced by the resolvent equation; the
recurrence is derived from the bounded operators, rather than postulated. -/
theorem reference_coefficient_succ (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η =
      (-coefficient I (weight ε) χ 0 η / 2) *
        coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η /
          radialDivisor 2 n := by
  have heq := congrArg
    (fun A : AxisSpace I ε => coefficient I (weight ε) A (n + 1) η)
    (AxisResolvent.naturalResolvent_equation I hε χ e)
  simp only [coefficient, Submodule.coe_add, jet_add] at heq
  change coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) (n + 1) η +
      coefficient I (weight ε)
        (AxisResolvent.naturalOperator I hε χ
          (AxisResolvent.naturalResolvent I hε χ e)) (n + 1) η =
      coefficient I (weight ε) e (n + 1) η at heq
  rw [coefficient_naturalOperator_succ I hε χ _ hχ n hη,
    he (n + 1) (by omega) η hη] at heq
  linear_combination heq

/-- The constructed resolvent has the factorial coefficients of the
regular Bessel-type reference. -/
theorem reference_coefficient (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (n : ℕ) :
    coefficient I (weight ε) (AxisResolvent.naturalResolvent I hε χ e) n η =
      (-coefficient I (weight ε) χ 0 η / 2) ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  induction n with
  | zero => simpa using reference_coefficient_zero I hε χ e hη he0
  | succ n ih =>
      rw [reference_coefficient_succ I hε χ e hχ he n hη, ih]
      have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        radialDivisor, Nat.cast_ofNat, pow_succ]
      field_simp; ring

/-- Evaluation of the actual coefficient-space reference equals the
entire leading series at every real radius. -/
theorem reference_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ e : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    (he : RadiallyConstant I ε e) {η : ℝ} (hη : η ∈ I.interval)
    (he0 : coefficient I (weight ε) e 0 η = 1) (Y : ℝ) :
    AxisEvaluation.profile I ε (AxisResolvent.naturalResolvent I hε χ e) (Y, η) =
      AxisSeries.profile (coefficient I (weight ε) χ 0 η) Y := by
  rw [AxisEvaluation.profile, AxisSeries.profile_eq_tsum]
  apply tsum_congr
  intro n
  rw [reference_coefficient I hε χ e hχ he hη he0 n]
  rw [← mul_div_assoc, ← mul_pow]
  congr 2
  ring

/-- In particular, the leading pair used by the nonlinear existence theorem
has exactly this angular series. -/
theorem referenceCoefficients_profile_eq_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) =
      AxisSeries.profile (inputValue I ε χ η) Y := by
  exact reference_profile_eq_series I hε χ d.one hd.chi_radial hd.one_radial
    hη (hd.one_value η hη) Y

theorem referenceCoefficients_deriv_Y_eq (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval) (Y : ℝ) :
    deriv (fun y => AxisEvaluation.profile I ε
      (referenceCoefficients I hε χ d).1 (y, η)) Y =
        deriv (AxisSeries.profile (inputValue I ε χ η)) Y := by
  congr 2
  funext y
  exact referenceCoefficients_profile_eq_series I hε χ d hd hη y

/-- The lower bound concerns the reference constructed by the resolvent,
not a separately declared comparison function. -/
theorem referenceCoefficients_gt_quarter (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η Y : ℝ} (hη : η ∈ I.interval)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) :
    1 / 4 < AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (Y, η) := by
  rw [referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_gt_quarter _ Y hχ0 hχ1 hY0 hY1

theorem referenceCoefficients_log_slope_at_four (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) {η : ℝ} (hη : η ∈ I.interval)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    236 / 100 <
      -8 * deriv (fun y => AxisEvaluation.profile I ε
        (referenceCoefficients I hε χ d).1 (y, η)) 4 /
          AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1 (4, η) := by
  rw [referenceCoefficients_deriv_Y_eq I hε χ d hd hη,
    referenceCoefficients_profile_eq_series I hε χ d hd hη]
  exact AxisSeries.profile_log_slope_at_four _ hχ99 hχ1

/-- Quantitative stability of the strict slope margin under simultaneous
value and first-derivative errors of at most `1/1000`. -/
theorem log_slope_stability {v₀ v d₀ d : ℝ}
    (hv₀ : 1 / 4 < v₀) (hvalue : |v - v₀| ≤ 1 / 1000)
    (hderiv : |d - d₀| ≤ 1 / 1000) (hslope : 236 / 100 < -8 * d₀ / v₀) :
    1 / 8 < v ∧ 23 / 10 < -8 * d / v := by
  have hv : 1 / 8 < v := by
    have := (abs_le.mp hvalue).1
    linarith
  refine ⟨hv, ?_⟩
  have hvpos : 0 < v := by linarith
  have hv₀pos : 0 < v₀ := by linarith
  rw [lt_div_iff₀ hvpos]
  rw [lt_div_iff₀ hv₀pos] at hslope
  have he0 := (abs_le.mp hvalue).2
  have he1 := (abs_le.mp hderiv).2
  nlinarith

/-- A single lower bound on the scale makes both evaluation constants
small enough for positivity and logarithmic-slope stability. -/
theorem scaled_error_le {C C₀ C₁ K Λ : ℝ}
    (hCsum : C ≤ C₀ + C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hΛ : 1 + 500 * (C₀ + C₁) * K ≤ Λ) :
    C * (K / (2 * Λ)) ≤ 1 / 1000 := by
  have hsum : 0 ≤ C₀ + C₁ := add_nonneg hC₀ hC₁
  have hΛpos : 0 < Λ := by nlinarith [mul_nonneg hsum hK]
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * Λ)]
  nlinarith [mul_le_mul_of_nonneg_right hCsum hK]

/-- This explicit threshold controls both values and first radial derivatives
on `|Y|≤5`, uniformly over the parameter interval. -/
def stabilityScale (ε K : ℝ) : ℝ :=
  1 + 500 * (AxisEvaluation.jetBound ε 5 0 0 + AxisEvaluation.jetBound ε 5 1 0) * K

theorem stabilityScale_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    0 < stabilityScale ε K := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  unfold stabilityScale
  positivity

theorem value_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |Φ p - Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 0 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_right hC₁) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 0 0 p hY hη).1
  exact le_trans (by simpa only [mixedDerivative, iteratedDeriv_zero] using he) hb

theorem radial_deriv_error_le (I : Window) {ε K Λ : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : stabilityScale ε K ≤ Λ) {Φ u Φ₀ u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u Φ₀ u₀)
    {p : ℝ × ℝ} (hY : |p.1| ≤ 5) (hη : p.2 ∈ Ioo I.left I.right) :
    |partialY Φ p - partialY Φ₀ p| ≤ 1 / 1000 := by
  have hC₀ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hC₁ := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hb : AxisEvaluation.jetBound ε 5 1 0 * (K / (2 * Λ)) ≤ 1 / 1000 :=
    scaled_error_le (le_add_of_nonneg_left hC₀) hC₀ hC₁ hK hΛ
  have he := (herr 5 (by norm_num) (by norm_num) 1 0 p hY hη).1
  exact le_trans
    (by simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one, partialY] using he) hb

/-- Uniform closeness to the actual reference preserves a positive margin
on the full closed radial interval. -/
theorem positive_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {Y η : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10)
    (hη : η ∈ Ioo I.left I.right)
    (hχ0 : 0 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    1 / 8 < Φ (Y, η) := by
  have href := referenceCoefficients_gt_quarter I hε χ d hd
    (show η ∈ I.interval from ⟨hη.1.le, hη.2.le⟩) hχ0 hχ1 hY0 hY1
  have he := value_error_le I hε hK hΛ herr
    (p := (Y, η)) (by simpa only [abs_of_nonneg hY0] using (show Y ≤ 5 by linarith)) hη
  have he' := (abs_le.mp he).1
  linarith

/-- The same scale preserves a strict slope greater than `2.3` wherever
the parameter coefficient is at least `0.99`. -/
theorem log_slope_of_uniformMixedError (I : Window) {ε K Λ : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (hK : 0 ≤ K) (hΛ : stabilityScale ε K ≤ Λ)
    {Φ u u₀ : ℝ × ℝ → ℝ}
    (herr : UniformMixedError I ε (K / (2 * Λ)) Φ u
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1) u₀)
    {η : ℝ} (hη : η ∈ Ioo I.left I.right)
    (hχ99 : 99 / 100 ≤ inputValue I ε χ η) (hχ1 : inputValue I ε χ η ≤ 1) :
    23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hη' : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
  have href := referenceCoefficients_gt_quarter I hε χ d hd hη'
    (by linarith : 0 ≤ inputValue I ε χ η) hχ1
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 41 / 10)
  have hslope := referenceCoefficients_log_slope_at_four I hε χ d hd hη' hχ99 hχ1
  exact (log_slope_stability href
    (value_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    (radial_deriv_error_le I hε hK hΛ herr (p := (4, η)) (by norm_num) hη)
    hslope).2

/-- One sufficiently large scale gives the actual smooth nonlinear
profiles, all mixed-derivative estimates, uniform positivity, and the strict
angular slope bound, simultaneously for the full amplitude norm ball. -/
theorem exists_positive_scaled_profiles (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d)
    (hχ : ∀ η ∈ I.interval, 0 ≤ inputValue I ε χ η ∧ inputValue I ε χ η ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisSpace I ε, ‖a‖ ≤ M → RadiallyConstant I ε a →
      ∃ Φ u B P : ℝ × ℝ → ℝ,
        IsScaledSolution I (parameters I ε χ d) (1 / Λ) (inputValue I ε a) Φ u B P ∧
        UniformMixedError I ε (errorConstant I hε χ d M hM / (2 * Λ))
          Φ u (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
          (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) ∧
        (∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ η ∈ Ioo I.left I.right, 1 / 8 < Φ (Y, η)) ∧
        (∀ η ∈ Ioo I.left I.right, 99 / 100 ≤ inputValue I ε χ η →
          23 / 10 < -8 * partialY Φ (4, η) / Φ (4, η)) := by
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := exists_scaled_profiles I hε χ d hd M hM
  refine ⟨max Λ₀ (stabilityScale ε (errorConstant I hε χ d M hM)),
    hΛ₀.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ a ha harad
  obtain ⟨Φ, u, B, P, hsol, herr⟩ := hexists Λ ((le_max_left _ _).trans hΛ) a ha harad
  have hscale : stabilityScale ε (errorConstant I hε χ d M hM) ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have hK := errorConstant_nonneg I hε χ d M hM
  refine ⟨Φ, u, B, P, hsol, herr, ?_, ?_⟩
  · intro Y hY η hη
    have hχη := hχ η ⟨hη.1.le, hη.2.le⟩
    exact positive_of_uniformMixedError I hε χ d hd hK hscale herr
      hY.1 hY.2 hη hχη.1 hχη.2
  · intro η hη hχ99
    exact log_slope_of_uniformMixedError I hε χ d hd hK hscale herr hη hχ99
      (hχ η ⟨hη.1.le, hη.2.le⟩).2

end NavierStokes.AxisReference

end
