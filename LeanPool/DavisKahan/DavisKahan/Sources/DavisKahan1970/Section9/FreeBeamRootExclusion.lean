/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The free-beam characteristic function has no root below `3π/2`

Davis--Kahan 1970 Section 9 needs the third eigenvalue of the free beam to
exceed `500`.  Everything downstream of that is already proved in this
directory: the eigenvalue is `β⁴` for `β` a positive root of

`characteristic β = cos β · cosh β − 1`,

and `positive_root_fourth_power_gt_five_hundred` turns `4.73 < β` into
`500 < β⁴`.  What is missing is the localization of the first positive root
itself, which is `FirstPositiveRootCertificate` — a structure the repository
never constructs.

This module supplies the part of that localization which needs no decimal
arithmetic: **`cos β · cosh β < 1` for every `β ∈ (0, 3π/2]`**, so the
characteristic function has no root there.  Since `3π/2 ≈ 4.712` and the first
root is `≈ 4.7300407`, what remains after this is only the thin interval
`(3π/2, 4.73]`, where the bound is genuinely numerical: `cos` and `cosh` are
both increasing there, so it comes down to `cos 4.73 · cosh 4.73 < 1`, whose
true value is `≈ 0.9977`.

## The argument

On `(0, π/2]` it is calculus.  Write `f = cos · cosh`.  Then `f 0 = 1`,
`f' = −sin·cosh + cos·sinh` vanishes at `0`, and `f'' = −2 sin·sinh < 0` on
`(0, π/2)`.  So `f'` is strictly decreasing from `0`, hence negative, hence `f`
is strictly decreasing from `1`.

On `[π/2, 3π/2]` there is nothing to do: `cos β ≤ 0` and `cosh β > 0`, so the
product is `≤ 0`.

## Main results

* `TauCeti.DavisKahan1970.Section9.cos_mul_cosh_lt_one_of_le_pi_div_two`
* `TauCeti.DavisKahan1970.Section9.cos_mul_cosh_lt_one_of_le_three_pi_div_two`
-/

open Real

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-! ## The first two derivatives of `cos · cosh` -/

private theorem hasDerivAt_cosMulCosh (b : ℝ) :
    HasDerivAt (fun x => Real.cos x * Real.cosh x)
      (-Real.sin b * Real.cosh b + Real.cos b * Real.sinh b) b :=
  (Real.hasDerivAt_cos b).mul (Real.hasDerivAt_cosh b)

private theorem hasDerivAt_cosMulCosh_deriv (b : ℝ) :
    HasDerivAt (fun x => -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x)
      (-(2 * (Real.sin b * Real.sinh b))) b := by
  have h1 : HasDerivAt (fun x => -Real.sin x * Real.cosh x)
      (-Real.cos b * Real.cosh b + -Real.sin b * Real.sinh b) b :=
    ((Real.hasDerivAt_sin b).neg).mul (Real.hasDerivAt_cosh b)
  have h2 : HasDerivAt (fun x => Real.cos x * Real.sinh x)
      (-Real.sin b * Real.sinh b + Real.cos b * Real.cosh b) b :=
    (Real.hasDerivAt_cos b).mul (Real.hasDerivAt_sinh b)
  have h := h1.add h2
  have heq : (-Real.cos b * Real.cosh b + -Real.sin b * Real.sinh b) +
      (-Real.sin b * Real.sinh b + Real.cos b * Real.cosh b) =
      -(2 * (Real.sin b * Real.sinh b)) := by ring
  rw [heq] at h
  exact h

/-! ## The derivative is negative, hence the function drops below `1` -/

/-- `f' = −sin·cosh + cos·sinh` is negative on `(0, π/2]`: it vanishes at `0`
and its own derivative `−2 sin·sinh` is negative throughout. -/
private theorem cosMulCosh_deriv_neg {b : ℝ} (hb : 0 < b) (hle : b ≤ π / 2) :
    -Real.sin b * Real.cosh b + Real.cos b * Real.sinh b < 0 := by
  have hanti : StrictAntiOn
      (fun x => -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x)
      (Set.Icc 0 (π / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosMulCosh_deriv x).deriv]
    have hs : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos, hx.2])
    have hh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx.1
    nlinarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_refl _, by positivity⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hb.le, hle⟩
  have h := hanti h0 hbmem hb
  simpa using h

/-- **`cos β · cosh β < 1` on `(0, π/2]`.** -/
theorem cos_mul_cosh_lt_one_of_le_pi_div_two {b : ℝ} (hb : 0 < b)
    (hle : b ≤ π / 2) : Real.cos b * Real.cosh b < 1 := by
  have hanti : StrictAntiOn (fun x => Real.cos x * Real.cosh x)
      (Set.Icc 0 (π / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosMulCosh x).deriv]
    exact cosMulCosh_deriv_neg hx.1 hx.2.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_refl _, by positivity⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hb.le, hle⟩
  have h := hanti h0 hbmem hb
  simpa using h

/-- **`cos β · cosh β < 1` on all of `(0, 3π/2]`.**

Past `π/2` the cosine is nonpositive, so the product is nonpositive and there is
nothing to prove; the content is entirely in the first quarter period. -/
theorem cos_mul_cosh_lt_one_of_le_three_pi_div_two {b : ℝ} (hb : 0 < b)
    (hle : b ≤ 3 * π / 2) : Real.cos b * Real.cosh b < 1 := by
  rcases le_or_gt b (π / 2) with h | h
  · exact cos_mul_cosh_lt_one_of_le_pi_div_two hb h
  · have hcos : Real.cos b ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h.le (by linarith)
    have hcosh : 0 < Real.cosh b := Real.cosh_pos b
    nlinarith

/-! ## The thin interval `(3π/2, 4.73]`

Past `3π/2` the cosine turns positive again and the argument above stops
working, but only just: the first root is at `≈ 4.7300407` and `3π/2 ≈ 4.712389`,
so a window of width `0.0177` has to be covered numerically.

Both factors are bounded by their values at the right endpoint — `cos` because
`cos β = sin(β − 3π/2)` and `sin t ≤ t`, `cosh` because it is even and
increasing — so everything reduces to `cos 4.73 · cosh 4.73 < 1`.  The true
value is `≈ 0.99765`, so the margin is about two parts in a thousand and the
bounds below have to be carried to five digits.
-/

/-- `cos x = sin (x − 3π/2)`: the quarter-turn that makes the cosine near
`3π/2` a small sine near `0`. -/
private theorem cos_eq_sin_sub_three_pi_div_two (x : ℝ) :
    Real.cos x = Real.sin (x - 3 * π / 2) := by
  have hc : Real.cos (3 * π / 2) = 0 := by
    have h : (3 * π / 2 : ℝ) = π + π / 2 := by ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have hs : Real.sin (3 * π / 2) = -1 := by
    have h : (3 * π / 2 : ℝ) = π + π / 2 := by ring
    rw [h, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  rw [Real.sin_sub, hs, hc]
  ring

/-- `4.73` overshoots `3π/2` by less than `0.017612`, from `π > 3.141592`. -/
private theorem sub_three_pi_div_two_lt :
    (473 / 100 : ℝ) - 3 * π / 2 < 0.017612 := by
  have := Real.pi_gt_d6
  linarith

/-- `4.73` does overshoot `3π/2`, from `π < 3.141593`. -/
private theorem sub_three_pi_div_two_pos :
    (0 : ℝ) < (473 / 100 : ℝ) - 3 * π / 2 := by
  have := Real.pi_lt_d6
  linarith

/-- **`cosh 4.73 < 56.66`.**

`exp 4.73 = (exp 1)⁴ · exp 0.73`, with `(exp 1)⁴ < 54.5982` from Mathlib's
nine-digit bound on `e` and `exp 0.73 < 2.0751` from six Taylor terms.  The
reciprocal half of the cosine hyperbolic is crushed by `exp 4.73 > 50`. -/
theorem cosh_four_seventy_three_lt : Real.cosh (473 / 100) < 56.66 := by
  rw [Real.cosh_eq]
  have h4 : Real.exp 4 < 54.5982 := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have h3 : (2.7182818286 : ℝ) ^ 4 < 54.5982 := by norm_num
    linarith
  have h073 : Real.exp (73 / 100) < 2.0751 := by
    have hx : |(73 / 100 : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 73 / 100)]; norm_num
    have h := Real.exp_bound hx (n := 6) (by norm_num)
    rw [abs_le] at h
    have hb := h.2
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb
    linarith
  have hup : Real.exp (473 / 100) < 113.297 := by
    have hsplit : Real.exp (473 / 100) = Real.exp 4 * Real.exp (73 / 100) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    calc Real.exp 4 * Real.exp (73 / 100)
        < 54.5982 * Real.exp (73 / 100) :=
          mul_lt_mul_of_pos_right h4 (Real.exp_pos _)
      _ < 54.5982 * 2.0751 := mul_lt_mul_of_pos_left h073 (by norm_num)
      _ < 113.297 := by norm_num
  have hlow : (50 : ℝ) < Real.exp (473 / 100) := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : ((2.7182818283 : ℝ)) ^ 4 < Real.exp 1 ^ 4 :=
      pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
    have h3 : (50 : ℝ) < (2.7182818283 : ℝ) ^ 4 := by norm_num
    have h5 : Real.exp 4 ≤ Real.exp (473 / 100) :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hneg : Real.exp (-(473 / 100 : ℝ)) < 1 / 50 := by
    rw [Real.exp_neg, inv_eq_one_div,
      div_lt_div_iff₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 50)]
    linarith
  linarith

/-- **`cos β < 0.017612` for every `β ≤ 4.73` past `3π/2`.** -/
theorem cos_lt_of_lt_four_seventy_three {b : ℝ} (hlow : 3 * π / 2 < b)
    (hle : b ≤ 473 / 100) : Real.cos b < 0.017612 := by
  rw [cos_eq_sin_sub_three_pi_div_two]
  calc Real.sin (b - 3 * π / 2) ≤ b - 3 * π / 2 := Real.sin_le (by linarith)
    _ ≤ (473 / 100 : ℝ) - 3 * π / 2 := by linarith
    _ < 0.017612 := sub_three_pi_div_two_lt

/-- **`cos β · cosh β < 1` on all of `(0, 4.73]`**, hence the free-beam
characteristic function has no root there.

This is the whole of `FirstPositiveRootCertificate.no_smaller_positive_root`
once `4.73` is known to sit below the first root, and with
`positive_root_fourth_power_gt_five_hundred` it is what turns the paper's
`α₃ > 500` into a theorem. -/
theorem cos_mul_cosh_lt_one_of_le_four_seventy_three {b : ℝ} (hb : 0 < b)
    (hle : b ≤ 473 / 100) : Real.cos b * Real.cosh b < 1 := by
  rcases le_or_gt b (3 * π / 2) with h | h
  · exact cos_mul_cosh_lt_one_of_le_three_pi_div_two hb h
  · have hcos : Real.cos b < 0.017612 := cos_lt_of_lt_four_seventy_three h hle
    have hcosh : Real.cosh b < 56.66 := by
      refine lt_of_le_of_lt ?_ cosh_four_seventy_three_lt
      rw [Real.cosh_le_cosh, abs_of_pos hb, abs_of_pos (by norm_num)]
      exact hle
    rcases le_or_gt (Real.cos b) 0 with hc | hc
    · nlinarith [Real.cosh_pos b]
    · calc Real.cos b * Real.cosh b < 0.017612 * Real.cosh b :=
            mul_lt_mul_of_pos_right hcos (Real.cosh_pos b)
        _ < 0.017612 * 56.66 := mul_lt_mul_of_pos_left hcosh (by norm_num)
        _ < 1 := by norm_num

end Section9
end DavisKahan1970
end TauCeti
