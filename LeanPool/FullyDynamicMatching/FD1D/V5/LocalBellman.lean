/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.LocalInvariants

/-!
# The local quadratic Bellman inequality

This module follows the normalization and three active-cap cases in the
appendix of `manuscript-v5/optimal_dynamic_matching.tex`.
-/

namespace FD1D.V5.LocalBellman

noncomputable section

open LocalPolicy

namespace Normalized

/-- Squared imbalance parameter used in the normalized Bellman calculation. -/
def lambda (ρ : ℝ) : ℝ := ρ ^ 2
/-- Scale times one minus the squared imbalance. -/
def A (s ρ : ℝ) : ℝ := s * (1 - lambda ρ)
/-- Shifted scale appearing in the normalized potential ratios. -/
def g (s r : ℝ) : ℝ := s + r
/-- Positive denominator factor in the normalized feedback identities. -/
def d (s ρ : ℝ) : ℝ := s * (A s ρ + 2) + 1

/-- Normalized rate of the plus child for the selected correction. -/
def hPlus (s ρ z : ℝ) : ℝ :=
  (s + z) / (s * (1 + ρ))

/-- Normalized rate of the minus child for the selected correction. -/
def hMinus (s ρ z : ℝ) : ℝ :=
  (s - z) / (s * (1 - ρ))

/-- Half the difference between the residual parameter and the correction. -/
def tPlus (r z : ℝ) : ℝ := (r - z) / 2
/-- Half the sum of the residual parameter and the correction. -/
def tMinus (r z : ℝ) : ℝ := (r + z) / 2

/-- Normalized parent potential ratio. -/
def ZParent (s r : ℝ) : ℝ :=
  g s r / (s + 1 / 2)

/-- Normalized potential ratio for the plus child. -/
def ZPlus (s r ρ : ℝ) : ℝ :=
  g s r / (s * (1 + ρ) + 1)

/-- Normalized potential ratio for the minus child. -/
def ZMinus (s r ρ : ℝ) : ℝ :=
  g s r / (s * (1 - ρ) + 1)

/-- Average child Bellman contribution minus the parent contribution. -/
def residual (s r ρ z : ℝ) : ℝ :=
  ((tPlus r z * ZPlus s r ρ +
        bellman (hPlus s ρ z) (tPlus r z) (ZPlus s r ρ)) +
      (tMinus r z * ZMinus s r ρ +
        bellman (hMinus s ρ z) (tMinus r z) (ZMinus s r ρ))) / 2 -
    bellman 1 r (ZParent s r)

/-- Change of the mean squared normalized child rate relative to one. -/
def rateIncrement (s ρ z : ℝ) : ℝ :=
  (hPlus s ρ z ^ 2 + hMinus s ρ z ^ 2) / 2 - 1

/-- Feedback correction in the normalized local policy. -/
def feedback (s ρ : ℝ) : ℝ :=
  8 * s * ρ / A s ρ

/-- Correction corresponding to uniform deletion rates. -/
def uniform (s ρ : ℝ) : ℝ :=
  s * ρ

/-- Largest correction permitted by the normalized floor constraint. -/
def floorCap (s r ρ : ℝ) : ℝ :=
  (s - s * (1 - ρ) * r) / (s * (1 - ρ) + 1)

/-- Rescaled gap between the scale and the chosen floor parameter. -/
def J (s ρ k : ℝ) : ℝ :=
  (s - k) / A s ρ

/-- Auxiliary expression controlling the normalized Bellman residual. -/
def bracket (s r ρ k : ℝ) : ℝ :=
  s * k - J s ρ k * (s + 1 / 2) -
    (1 / 2 - r) * s ^ 2 / (s + 1 / 2)

theorem lambda_nonneg (ρ : ℝ) :
    0 ≤ lambda ρ := by
  exact sq_nonneg ρ

theorem lambda_lt_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    lambda ρ < 1 := by
  unfold lambda
  nlinarith [sq_nonneg ρ]

theorem A_pos {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < A s ρ := by
  unfold A
  exact mul_pos hs (sub_pos.mpr (lambda_lt_one hρ0 hρ1))

theorem g_pos {s r : ℝ} (hr : -s < r) :
    0 < g s r := by
  unfold g
  linarith

theorem d_pos {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < d s ρ := by
  have hA := (A_pos hs hρ0 hρ1).le
  unfold d
  positivity

theorem residual_eq_common
    {s r ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (ρ * k) =
      r ^ 2 / 8 - lambda ρ * k ^ 2 / 24 +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) +
        lambda ρ * g s r / d s ρ * bracket s r ρ k := by
  have hs0 : s ≠ 0 := hs.ne'
  have hA : A s ρ ≠ 0 := (A_pos hs hρ0 hρ1).ne'
  have hd : d s ρ ≠ 0 := (d_pos hs hρ0 hρ1).ne'
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  have hρp : 1 + ρ ≠ 0 := by
    have := lambda_lt_one hρ0 hρ1
    nlinarith [sq_nonneg ρ]
  have hρm : 1 - ρ ≠ 0 := by linarith
  have hp : s * (1 + ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 + ρ) + 1 := by positivity
    exact this.ne'
  have hm : s * (1 - ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 - ρ) + 1 := by positivity
    exact this.ne'
  unfold residual tPlus tMinus hPlus hMinus
    ZPlus ZMinus ZParent bellman bracket J
  field_simp [hs0, hA, hd, hsHalf, hρp, hρm, hp, hm]
  unfold d A lambda g
  ring

theorem rateIncrement_eq_common
    {s ρ k : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (ρ * k) =
      2 * lambda ρ * J s ρ k +
        (1 + lambda ρ) * lambda ρ * J s ρ k ^ 2 := by
  have hs0 : s ≠ 0 := hs.ne'
  have hA : A s ρ ≠ 0 := (A_pos hs hρ0 hρ1).ne'
  have hρp : 1 + ρ ≠ 0 := by
    have := lambda_lt_one hρ0 hρ1
    nlinarith [sq_nonneg ρ]
  have hρm : 1 - ρ ≠ 0 := by linarith
  unfold rateIncrement hPlus hMinus J
  field_simp [hs0, hA, hρp, hρm]
  unfold A lambda
  ring

theorem uniform_hPlus {s ρ : ℝ}
    (hs : 0 < s) (hρ1 : ρ ≠ -1) :
    hPlus s ρ (uniform s ρ) = 1 := by
  unfold hPlus uniform
  have hsum : 1 + ρ ≠ 0 := by
    intro h
    exact hρ1 (by linarith)
  field_simp [hs.ne', hsum]

theorem uniform_hMinus {s ρ : ℝ}
    (hs : 0 < s) (hρ1 : ρ ≠ 1) :
    hMinus s ρ (uniform s ρ) = 1 := by
  unfold hMinus uniform
  have hsub : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  field_simp [hs.ne', hsub]

theorem uniform_rateIncrement {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (uniform s ρ) = 0 := by
  rw [rateIncrement, uniform_hPlus hs (by linarith),
    uniform_hMinus hs (by linarith)]
  norm_num

theorem uniform_residual_eq
    {s r ρ : ℝ}
    (hs : 0 < s)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (uniform s ρ) =
      r ^ 2 / 8 - (uniform s ρ) ^ 2 / 24 +
        g s r ^ 2 * (uniform s ρ) ^ 2 /
          (d s ρ * (s + 1 / 2)) +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  have hp : s * (1 + ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 + ρ) + 1 := by positivity
    exact this.ne'
  have hm : s * (1 - ρ) + 1 ≠ 0 := by
    have : 0 < s * (1 - ρ) + 1 := by
      have := lambda_lt_one hρ0 hρ1
      nlinarith [sq_nonneg ρ]
    exact this.ne'
  have hd : d s ρ ≠ 0 := (d_pos hs hρ0 hρ1).ne'
  unfold residual tPlus tMinus ZPlus ZMinus ZParent
  rw [uniform_hPlus hs (by linarith), uniform_hMinus hs (by linarith)]
  unfold bellman uniform g
  field_simp [hs0, hsHalf, hp, hm, hd]
  unfold d A lambda
  ring

private theorem denominator_ratio_identity
    {s ρ : ℝ} (hs : s ≠ 0) :
    d s ρ * (s + 1 / 2) / s ^ 2 =
      A s ρ + 2 + A s ρ / (2 * s) + 2 / s +
        1 / (2 * s ^ 2) := by
  unfold d
  field_simp
  ring

private theorem uniform_denominator_le
    {s ρ : ℝ}
    (hs : 1 / 2 ≤ s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hactive : A s ρ ≤ 8) :
    d s ρ * (s + 1 / 2) ≤ 13 * s ^ 2 := by
  have hspos : 0 < s := by linarith
  have hA0 : 0 ≤ A s ρ := (A_pos hspos hρ0 hρ1).le
  have hAleS : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have hid := denominator_ratio_identity (ρ := ρ) hspos.ne'
  by_cases hs1 : s ≤ 1
  · have hA : A s ρ ≤ 1 := hAleS.trans hs1
    have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
      linarith
    have h2div : 2 / s ≤ 4 := by
      apply (div_le_iff₀ hspos).2
      nlinarith
    have hlast : 1 / (2 * s ^ 2) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hratio :
        d s ρ * (s + 1 / 2) / s ^ 2 ≤ 19 / 2 := by
      rw [hid]
      linarith
    have hsSq : 0 < s ^ 2 := sq_pos_of_pos hspos
    have := (div_le_iff₀ hsSq).1 hratio
    nlinarith
  · have hsone : 1 ≤ s := le_of_not_ge hs1
    by_cases hs8 : s ≤ 8
    · have hA : A s ρ ≤ 8 := hactive
      have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
        linarith
      have h2div : 2 / s ≤ 2 := by
        apply (div_le_iff₀ hspos).2
        nlinarith
      have hlast : 1 / (2 * s ^ 2) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
        nlinarith [sq_nonneg (s - 1)]
      have hratio :
          d s ρ * (s + 1 / 2) / s ^ 2 ≤ 13 := by
        rw [hid]
        linarith
      exact (div_le_iff₀ (sq_pos_of_pos hspos)).1 hratio
    · have hsEight : 8 ≤ s := le_of_not_ge hs8
      have hA : A s ρ ≤ 8 := hactive
      have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
        nlinarith [hAleS]
      have h2div : 2 / s ≤ 1 / 4 := by
        apply (div_le_iff₀ hspos).2
        nlinarith
      have hlast : 1 / (2 * s ^ 2) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
        nlinarith [sq_nonneg (s - 1)]
      have hratio :
          d s ρ * (s + 1 / 2) / s ^ 2 ≤ 13 := by
        rw [hid]
        linarith
      exact (div_le_iff₀ (sq_pos_of_pos hspos)).1 hratio

private theorem weighted_square_bound
    {s r lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * s ^ 2 / 21 ≤ r ^ 2 / 8 + lam * (s + r) ^ 2 / 13 := by
  let C : ℝ := 168 * lam + 273
  have hC : 0 < C := by dsimp [C]; nlinarith
  have hrem : 0 ≤ 69888 * lam * (1 - lam) * s ^ 2 := by positivity
  have hid :
      4 * C *
          (168 * lam * r ^ 2 + 336 * lam * r * s +
            64 * lam * s ^ 2 + 273 * r ^ 2) =
        (2 * C * r + 336 * lam * s) ^ 2 +
          69888 * lam * (1 - lam) * s ^ 2 := by
    dsimp [C]
    ring
  have hpoly :
      0 ≤ 168 * lam * r ^ 2 + 336 * lam * r * s +
        64 * lam * s ^ 2 + 273 * r ^ 2 := by
    nlinarith [sq_nonneg (2 * C * r + 336 * lam * s)]
  nlinarith

theorem uniform_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hactive : A s ρ ≤ 8) :
    residual s r ρ (uniform s ρ) ≥
      (rateIncrement s ρ (uniform s ρ) + uniform s ρ ^ 2) / 1000 := by
  have hg : 0 < g s r := g_pos hr0
  have hlam0 : 0 ≤ lambda ρ := lambda_nonneg ρ
  have hlam1 : lambda ρ ≤ 1 := (lambda_lt_one hρ0 hρ1).le
  have hzsq : uniform s ρ ^ 2 = lambda ρ * s ^ 2 := by
    unfold uniform lambda
    ring
  rw [uniform_rateIncrement hs hρ0 hρ1, zero_add]
  rw [uniform_residual_eq hs hρ0 hρ1]
  by_cases hsHalf : 1 / 2 ≤ s
  · have hden := uniform_denominator_le hsHalf hρ0 hρ1 hactive
    have hdpos : 0 < d s ρ * (s + 1 / 2) := by
      exact mul_pos (d_pos hs hρ0 hρ1) (by linarith)
    have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
    have hsquare :
        lambda ρ * g s r ^ 2 / 13 ≤
          g s r ^ 2 * uniform s ρ ^ 2 /
            (d s ρ * (s + 1 / 2)) := by
      rw [hzsq]
      have hnum : 0 ≤ lambda ρ * g s r ^ 2 := by positivity
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hdpos).2
      nlinarith
    have hcauchy :=
      weighted_square_bound (s := s) (r := r) hlam0 hlam1
    have hlast :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) := by
      have hhalf : 0 ≤ 1 / 2 - r := by linarith
      have hsone : 0 ≤ s + 1 := by linarith
      have hden : 0 < 2 * d s ρ * (s + 1 / 2) :=
        mul_pos (mul_pos (by norm_num) (d_pos hs hρ0 hρ1)) (by linarith)
      exact div_nonneg
        (mul_nonneg (mul_nonneg hg.le hhalf) hsone) hden.le
    simp only [g] at hsquare hlast ⊢
    nlinarith
  · have hsUpper : s ≤ 1 / 2 := le_of_not_ge hsHalf
    have hAleS : A s ρ ≤ s := by
      unfold A lambda
      nlinarith [sq_nonneg ρ]
    have hdUpper : d s ρ ≤ (s + 1) ^ 2 := by
      unfold d
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hAleS)]
    have hcoef :
        1 / 3 ≤ (s + 1) / (2 * d s ρ * (s + 1 / 2)) := by
      have hdpos := d_pos hs hρ0 hρ1
      have hden : 0 < 2 * d s ρ * (s + 1 / 2) := by positivity
      apply (le_div_iff₀ hden).2
      have hbound :
          2 * (s + 1) ^ 2 * (s + 1 / 2) ≤ 3 * (s + 1) := by
        have hfac : 0 ≤ s + 1 := by positivity
        nlinarith [mul_nonneg hfac
          (mul_nonneg (sub_nonneg.mpr hs.le) (by linarith : 0 ≤ 1 - s))]
      nlinarith [mul_le_mul_of_nonneg_right hdUpper
        (by linarith : 0 ≤ 2 * (s + 1 / 2))]
    have hlast :
        g s r * (1 / 2 - r) / 3 ≤
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * d s ρ * (s + 1 / 2)) := by
      have hfactor : 0 ≤ g s r * (1 / 2 - r) := by positivity
      calc
        g s r * (1 / 2 - r) / 3 =
            (g s r * (1 / 2 - r)) * (1 / 3) := by ring
        _ ≤ (g s r * (1 / 2 - r)) *
              ((s + 1) / (2 * d s ρ * (s + 1 / 2))) :=
          mul_le_mul_of_nonneg_left hcoef hfactor
        _ = g s r * (1 / 2 - r) * (s + 1) /
              (2 * d s ρ * (s + 1 / 2)) := by ring
    have hzle : uniform s ρ ^ 2 ≤ s ^ 2 := by
      rw [hzsq]
      nlinarith [mul_le_mul_of_nonneg_right hlam1 (sq_nonneg s)]
    have hcore :
        s ^ 2 / 12 ≤ r ^ 2 / 8 - s ^ 2 / 24 +
          (s + r) * (1 / 2 - r) / 3 := by
      have hleft : 0 ≤ r + s := by linarith
      have hright : 0 ≤ 4 - 5 * r - 3 * s := by linarith
      nlinarith [mul_nonneg hleft hright]
    have hsquare :
        0 ≤ g s r ^ 2 * uniform s ρ ^ 2 /
          (d s ρ * (s + 1 / 2)) := by
      have hden : 0 < d s ρ * (s + 1 / 2) :=
        mul_pos (d_pos hs hρ0 hρ1) (by linarith)
      exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le
    simp only [g] at hlast hsquare ⊢
    nlinarith

private theorem feedback_bracket_bound
    {s r ρ : ℝ}
    (hs : 0 < s) (hr : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA8 : 8 ≤ A s ρ) :
    r * s + 13 * s ^ 2 / (2 * A s ρ) ≤
      bracket s r ρ (8 * s / A s ρ) := by
  have hApos := A_pos hs hρ0 hρ1
  have hAle : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have hsHalf : 0 < s + 1 / 2 := by linarith
  have hratio : s ^ 2 / (s + 1 / 2) ≤ s := by
    apply (div_le_iff₀ hsHalf).2
    nlinarith
  have hslack : 0 ≤ 1 / 2 - r := by linarith
  have hdiscard :
      -(1 / 2 - r) * s ^ 2 / (s + 1 / 2) ≥
        -(1 / 2 - r) * s := by
    have hmul := mul_le_mul_of_nonneg_left hratio hslack
    calc
      -(1 / 2 - r) * s = -((1 / 2 - r) * s) := by ring
      _ ≤ -((1 / 2 - r) * (s ^ 2 / (s + 1 / 2))) :=
        neg_le_neg hmul
      _ = -(1 / 2 - r) * s ^ 2 / (s + 1 / 2) := by ring
  have hfirst :
      r * s + 7 * s ^ 2 / A s ρ + 8 * s ^ 2 / A s ρ ^ 2 -
          s / 2 - s / (2 * A s ρ) ≤
        bracket s r ρ (8 * s / A s ρ) := by
    unfold bracket J
    calc
      r * s + 7 * s ^ 2 / A s ρ + 8 * s ^ 2 / A s ρ ^ 2 -
          s / 2 - s / (2 * A s ρ)
          ≤ s * (8 * s / A s ρ) -
              ((s - 8 * s / A s ρ) / A s ρ) * (s + 1 / 2) -
              (1 / 2 - r) * s := by
                have hfour : 0 ≤ 4 * s / A s ρ ^ 2 := by positivity
                have hid :
                    s * (8 * s / A s ρ) -
                        ((s - 8 * s / A s ρ) / A s ρ) *
                          (s + 1 / 2) -
                        (1 / 2 - r) * s =
                      r * s + 7 * s ^ 2 / A s ρ +
                        8 * s ^ 2 / A s ρ ^ 2 - s / 2 -
                        s / (2 * A s ρ) +
                        4 * s / A s ρ ^ 2 := by
                  field_simp [hApos.ne']
                  ring
                rw [hid]
                linarith
      _ ≤ s * (8 * s / A s ρ) -
              ((s - 8 * s / A s ρ) / A s ρ) * (s + 1 / 2) -
              (1 / 2 - r) * s ^ 2 / (s + 1 / 2) := by
                convert add_le_add_left hdiscard
                  (s * (8 * s / A s ρ) -
                    ((s - 8 * s / A s ρ) / A s ρ) *
                      (s + 1 / 2)) using 1 <;> ring
  have hone :
      s / 2 ≤ s ^ 2 / (2 * A s ρ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * A s ρ)).2
    nlinarith
  have htwo :
      s / (2 * A s ρ) ≤ 8 * s ^ 2 / A s ρ ^ 2 := by
    have hleft : 0 ≤ s / (2 * A s ρ) := by positivity
    have hfac : 1 ≤ 16 * s / A s ρ := by
      apply (le_div_iff₀ hApos).2
      nlinarith
    calc
      s / (2 * A s ρ) =
          (s / (2 * A s ρ)) * 1 := by ring
      _ ≤ (s / (2 * A s ρ)) * (16 * s / A s ρ) :=
        mul_le_mul_of_nonneg_left hfac hleft
      _ = 8 * s ^ 2 / A s ρ ^ 2 := by ring
  have hcombine :=
    add_le_add hone htwo
  have hbudget :
      r * s + 13 * s ^ 2 / (2 * A s ρ) +
          (s / 2 + s / (2 * A s ρ)) ≤
        r * s + 7 * s ^ 2 / A s ρ +
          8 * s ^ 2 / A s ρ ^ 2 := by
    calc
      r * s + 13 * s ^ 2 / (2 * A s ρ) +
          (s / 2 + s / (2 * A s ρ))
          = (s / 2 + s / (2 * A s ρ)) +
              (r * s + 13 * s ^ 2 / (2 * A s ρ)) := by ring
      _ ≤ (s ^ 2 / (2 * A s ρ) +
              8 * s ^ 2 / A s ρ ^ 2) +
            (r * s + 13 * s ^ 2 / (2 * A s ρ)) :=
        add_le_add_left hcombine _
      _ = r * s + 7 * s ^ 2 / A s ρ +
            8 * s ^ 2 / A s ρ ^ 2 := by ring
  calc
    r * s + 13 * s ^ 2 / (2 * A s ρ)
        ≤ r * s + 7 * s ^ 2 / A s ρ +
            8 * s ^ 2 / A s ρ ^ 2 - s / 2 -
              s / (2 * A s ρ) := by
          linarith
    _ ≤ bracket s r ρ (8 * s / A s ρ) := hfirst

private theorem feedback_delta_bounds
    {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA8 : 8 ≤ A s ρ) :
    let α := 1 / A s ρ
    let δ := d s ρ / (s * A s ρ)
    0 ≤ α ∧ α ≤ 1 / 8 ∧
      1 + 2 * α ≤ δ ∧ δ ≤ (1 + α) ^ 2 := by
  dsimp
  have hApos := A_pos hs hρ0 hρ1
  have hAle : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have halpha0 : 0 ≤ 1 / A s ρ := by positivity
  have halpha8 : 1 / A s ρ ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) hA8
  have hsA : 0 < s * A s ρ := mul_pos hs hApos
  have hdelta :
      d s ρ / (s * A s ρ) =
        1 + 2 / A s ρ + 1 / (s * A s ρ) := by
    unfold d
    field_simp [hs.ne', hApos.ne']
  rw [hdelta]
  refine ⟨halpha0, halpha8, ?_, ?_⟩
  · have : 0 ≤ 1 / (s * A s ρ) := by positivity
    calc
      1 + 2 * (1 / A s ρ) = 1 + 2 / A s ρ := by ring
      _ ≤ 1 + 2 / A s ρ + 1 / (s * A s ρ) :=
        le_add_of_nonneg_right this
  · have hone : 1 / s ≤ 1 / A s ρ :=
      one_div_le_one_div_of_le hApos hAle
    have hmul :
        1 / (s * A s ρ) ≤ 1 / A s ρ ^ 2 := by
      calc
        1 / (s * A s ρ) = (1 / s) * (1 / A s ρ) := by
          field_simp
        _ ≤ (1 / A s ρ) * (1 / A s ρ) :=
          mul_le_mul_of_nonneg_right hone halpha0
        _ = 1 / A s ρ ^ 2 := by ring
    calc
      1 + 2 / A s ρ + 1 / (s * A s ρ)
          ≤ 1 + 2 / A s ρ + 1 / A s ρ ^ 2 := by
            linarith
      _ = (1 + 1 / A s ρ) ^ 2 := by ring

private theorem feedback_fraction_bound
    {α δ lam : ℝ}
    (hα0 : 0 ≤ α) (hα8 : α ≤ 1 / 8)
    (hδ : 1 + 2 * α ≤ δ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α)) ≤
      19 / 8 := by
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  have hδplus : 0 < δ + 8 * lam * α := by positivity
  have hlamDiff : 0 ≤ (1 - lam) * (1 + 2 * α) := by positivity
  have hsecond :
      lam * (1 + 10 * α) ≤ δ + 8 * lam * α := by
    nlinarith
  have hcross :
      lam * ((1 + 2 * α) * (1 + 10 * α)) ≤
        δ * (δ + 8 * lam * α) := by
    calc
      lam * ((1 + 2 * α) * (1 + 10 * α)) =
          (1 + 2 * α) * (lam * (1 + 10 * α)) := by ring
      _ ≤ δ * (δ + 8 * lam * α) :=
        mul_le_mul hδ hsecond (by positivity) hδpos.le
  have hcoarse :
      2 * (1 + (13 / 2) * α) ^ 2 /
          ((1 + 2 * α) * (1 + 10 * α)) ≤
        19 / 8 := by
    have hden0 : 0 < (1 + 2 * α) * (1 + 10 * α) := by positivity
    apply (div_le_iff₀ hden0).2
    have hpoly : 0 ≤ 3 / 8 + 5 / 2 * α - 37 * α ^ 2 := by
      have haux : 37 * α ^ 2 ≤ 37 / 8 * α := by
        nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hα8)]
      nlinarith
    nlinarith
  calc
    2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α))
        ≤ 2 * (1 + (13 / 2) * α) ^ 2 /
          ((1 + 2 * α) * (1 + 10 * α)) := by
        apply (div_le_div_iff₀
          (mul_pos hδpos hδplus) (by positivity)).2
        have hfactor : 0 ≤ 2 * (1 + (13 / 2) * α) ^ 2 := by positivity
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hcross hfactor
    _ ≤ 19 / 8 := hcoarse

private theorem feedback_quadratic_bound
    {u α δ lam : ℝ}
    (hα0 : 0 ≤ α) (hα8 : α ≤ 1 / 8)
    (hδLower : 1 + 2 * α ≤ δ)
    (hδUpper : δ ≤ (1 + α) ^ 2)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam / 12 ≤
      u ^ 2 / 8 +
        lam / δ * (1 + α * u) * (u + 13 / 2) -
        8 / 3 * lam := by
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδLower
  have hlead : 0 < δ + 8 * lam * α := by positivity
  have hfrac :=
    feedback_fraction_bound hα0 hα8 hδLower hlam0 hlam1
  have hdelta81 : δ ≤ 81 / 64 := by
    calc
      δ ≤ (1 + α) ^ 2 := hδUpper
      _ ≤ (1 + (1 / 8 : ℝ)) ^ 2 := by gcongr
      _ = 81 / 64 := by norm_num
  have hC : 41 / 8 ≤ (13 / 2 : ℝ) / δ := by
    apply (le_div_iff₀ hδpos).2
    nlinarith
  have hsquare :
      0 ≤
        (δ + 8 * lam * α) *
          (u + 4 * lam * (1 + (13 / 2) * α) /
            (δ + 8 * lam * α)) ^ 2 / (8 * δ) := by
    positivity
  have hid :
      u ^ 2 / 8 +
          lam / δ * (1 + α * u) * (u + 13 / 2) -
          8 / 3 * lam =
        (δ + 8 * lam * α) *
            (u + 4 * lam * (1 + (13 / 2) * α) /
              (δ + 8 * lam * α)) ^ 2 / (8 * δ) +
          lam * ((13 / 2 : ℝ) / δ - 8 / 3 -
            2 * lam * (1 + (13 / 2) * α) ^ 2 /
              (δ * (δ + 8 * lam * α))) := by
    field_simp [hδpos.ne', hlead.ne']
    ring
  rw [hid]
  have hbracket :
      1 / 12 ≤ (13 / 2 : ℝ) / δ - 8 / 3 -
        2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α)) := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hbracket hlam0
  nlinarith
private theorem feedback_normalization
    {s r ρ : ℝ} (hs : 0 < s) (hρnonneg : 0 ≤ ρ) (hρ1 : ρ < 1) :
      (s / A s ρ) ^ 2 *
          ((r / (s / A s ρ)) ^ 2 / 8 +
            lambda ρ / (d s ρ / (s * A s ρ)) * (1 + (1 / A s ρ) * (r / (s / A s ρ))) * ((r / (s /
              A s ρ)) + 13 / 2) -
            8 / 3 * lambda ρ) =
        r ^ 2 / 8 - lambda ρ * (8 * s / A s ρ) ^ 2 / 24 +
          lambda ρ * g s r / d s ρ *
            (r * s + 13 * s ^ 2 / (2 * A s ρ)) := by
  have hApos := A_pos hs hρnonneg hρ1
  have hdpos := d_pos hs hρnonneg hρ1
  field_simp [hs.ne', hApos.ne', hdpos.ne']
  unfold g
  ring

private theorem feedback_rate_bound
    {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hA8 : 8 ≤ A s ρ) :
    rateIncrement s ρ (feedback s ρ) ≤ 4 * lambda ρ * (s / A s ρ) ^ 2 := by
  have hρnonneg := hρ0.le
  have hlam0 : 0 ≤ lambda ρ := lambda_nonneg ρ
  have hlam1 : lambda ρ ≤ 1 := (lambda_lt_one hρnonneg hρ1).le
  have hApos := A_pos hs hρnonneg hρ1
  let ω : ℝ := s / A s ρ
  have hωpos : 0 < ω := div_pos hs hApos
  have hωone : 1 ≤ ω := by
    have hAle : A s ρ ≤ s := by
      unfold A lambda
      nlinarith [sq_nonneg ρ]
    exact (le_div_iff₀ hApos).2 (by simpa using hAle)
  have hfeedback : feedback s ρ = ρ * (8 * s / A s ρ) := by
    unfold feedback
    ring
  have hJ :
      J s ρ (8 * s / A s ρ) =
        ω * (1 - 8 / A s ρ) := by
    dsimp [ω]
    unfold J
    field_simp [hApos.ne']
  have hJ0 : 0 ≤ J s ρ (8 * s / A s ρ) := by
    rw [hJ]
    have hfrac : 8 / A s ρ ≤ 1 :=
      (div_le_one hApos).2 hA8
    exact mul_nonneg hωpos.le (sub_nonneg.mpr hfrac)
  have hJω : J s ρ (8 * s / A s ρ) ≤ ω := by
    rw [hJ]
    have : 0 ≤ 8 / A s ρ := by positivity
    nlinarith
  have hrateCommon :=
    rateIncrement_eq_common
      (s := s) (ρ := ρ) (k := 8 * s / A s ρ)
      hs hρnonneg hρ1
  rw [hfeedback, hrateCommon]
  have hlinear :
      2 * lambda ρ * J s ρ (8 * s / A s ρ) ≤
        2 * lambda ρ * ω ^ 2 := by
    have hJone :
        J s ρ (8 * s / A s ρ) ≤ ω ^ 2 :=
      hJω.trans (by nlinarith [hωone])
    exact mul_le_mul_of_nonneg_left hJone (by positivity)
  have hquadJ :
      (1 + lambda ρ) * lambda ρ *
          J s ρ (8 * s / A s ρ) ^ 2 ≤
        2 * lambda ρ * ω ^ 2 := by
    have hJsq :
        J s ρ (8 * s / A s ρ) ^ 2 ≤ ω ^ 2 :=
      (sq_le_sq₀ hJ0 hωpos.le).2 hJω
    have honeLambda : 1 + lambda ρ ≤ 2 := by linarith
    calc
      (1 + lambda ρ) * lambda ρ *
            J s ρ (8 * s / A s ρ) ^ 2
          ≤ 2 * lambda ρ *
            J s ρ (8 * s / A s ρ) ^ 2 := by
              gcongr
      _ ≤ 2 * lambda ρ * ω ^ 2 := by
        exact mul_le_mul_of_nonneg_left hJsq (by positivity)
  exact (add_le_add hlinear hquadJ).trans_eq (by ring)

theorem feedback_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactive : feedback s ρ ≤ uniform s ρ) :
    residual s r ρ (feedback s ρ) ≥
      (rateIncrement s ρ (feedback s ρ) + feedback s ρ ^ 2) / 1000 := by
  have hρnonneg : 0 ≤ ρ := hρ0.le
  have hlam0 : 0 ≤ lambda ρ := lambda_nonneg ρ
  have hlam1 : lambda ρ ≤ 1 := (lambda_lt_one hρnonneg hρ1).le
  have hApos := A_pos hs hρnonneg hρ1
  have hA8 : 8 ≤ A s ρ := by
    unfold feedback uniform at hactive
    have hsρ : 0 < s * ρ := mul_pos hs hρ0
    have hmul := (div_le_iff₀ hApos).1 hactive
    nlinarith
  let ω : ℝ := s / A s ρ
  let α : ℝ := 1 / A s ρ
  let u : ℝ := r / ω
  let δ : ℝ := d s ρ / (s * A s ρ)
  have hωpos : 0 < ω := div_pos hs hApos
  have hωone : 1 ≤ ω := by
    have hAle : A s ρ ≤ s := by
      unfold A lambda
      nlinarith [sq_nonneg ρ]
    exact (le_div_iff₀ hApos).2 (by simpa using hAle)
  obtain ⟨hα0, hα8, hδLower, hδUpper⟩ :=
    feedback_delta_bounds hs hρnonneg hρ1 hA8
  have hquad :=
    feedback_quadratic_bound
      (u := u) hα0 hα8 hδLower hδUpper hlam0 hlam1
  have hg : 0 < g s r := g_pos hr0
  have hthird :
      0 ≤ g s r * (1 / 2 - r) * (s + 1) /
        (2 * d s ρ * (s + 1 / 2)) := by
    have hdpos := d_pos hs hρnonneg hρ1
    positivity
  have hbracket :=
    feedback_bracket_bound hs hr1 hρnonneg hρ1 hA8
  have hcommon :=
    residual_eq_common
      (s := s) (r := r) (ρ := ρ) (k := 8 * s / A s ρ)
      hs hρnonneg hρ1
  have hfeedback :
      feedback s ρ = ρ * (8 * s / A s ρ) := by
    unfold feedback
    ring
  have hnormalize :
      ω ^ 2 *
          (u ^ 2 / 8 +
            lambda ρ / δ * (1 + α * u) * (u + 13 / 2) -
            8 / 3 * lambda ρ) =
        r ^ 2 / 8 - lambda ρ * (8 * s / A s ρ) ^ 2 / 24 +
          lambda ρ * g s r / d s ρ *
            (r * s + 13 * s ^ 2 / (2 * A s ρ)) := by
    exact feedback_normalization hs hρnonneg hρ1
  have hres :
      lambda ρ * ω ^ 2 / 12 ≤
        residual s r ρ (feedback s ρ) := by
    rw [hfeedback, hcommon]
    have hquadScaled :=
      mul_le_mul_of_nonneg_left hquad (sq_nonneg ω)
    rw [hnormalize] at hquadScaled
    have hlast :
        lambda ρ * g s r / d s ρ *
              (r * s + 13 * s ^ 2 / (2 * A s ρ)) ≤
          lambda ρ * g s r / d s ρ *
              bracket s r ρ (8 * s / A s ρ) := by
      have hcoef :
          0 ≤ lambda ρ * g s r / d s ρ :=
        div_nonneg (mul_nonneg hlam0 hg.le)
          (d_pos hs hρnonneg hρ1).le
      exact mul_le_mul_of_nonneg_left hbracket hcoef
    nlinarith
  have hfeedbackSq :
      feedback s ρ ^ 2 = 64 * lambda ρ * ω ^ 2 := by
    dsimp [ω]
    unfold feedback lambda
    ring
  have hrate := feedback_rate_bound hs hρ0 hρ1 hA8
  have htarget :
      (rateIncrement s ρ (feedback s ρ) + feedback s ρ ^ 2) / 1000 ≤
        lambda ρ * ω ^ 2 / 12 := by
    rw [hfeedbackSq]
    have henergyNonneg : 0 ≤ lambda ρ * ω ^ 2 := by positivity
    nlinarith
  exact htarget.trans hres

/-- Auxiliary floor coordinate obtained from the normalized child scales. -/
def floorEll (u v K : ℝ) : ℝ :=
  1 - u * (K - 1) / (2 * v)

/-- Weight of the correction term in the floor residual estimate. -/
def floorW (u v K : ℝ) : ℝ :=
  (K + 1) * (u + 1) / (2 * (v + 1))

/-- Relative difference of the shifted normalized child scales. -/
def floorEta (u v : ℝ) : ℝ :=
  (v + 1 - u) / (v + 1 + u)

/-- Residual bound expressed in the floor coordinates. -/
def floorR (K e u v : ℝ) : ℝ :=
  (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 - 2 * K * e - 6 * e) / 96 +
    floorW u v K / 2 *
      (e * floorEta u v - (K - 1 + floorEll u v K) / 2)

/-- Rational lower-bound expression used in the floor-case estimate. -/
def floorJ (K e : ℝ) : ℝ :=
  5 * K ^ 2 - 3 + 2 * e ^ 2 - (2 * K + 6) * e +
    24 * (K + 1) * e * (K + e) / (K * (16 + K + e))

private theorem floorJ_bound_large
    {K e : ℝ} (hK : 1 ≤ K) (heK : K ≤ e) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have he0 : 0 ≤ e := hKpos.le.trans heK
  have hK8 : 0 < K + 8 := by linarith
  have hden : 0 < K * (16 + K + e) := by positivity
  have hgap : 0 ≤ (e - K) * (K + 1) := by positivity
  have hfrac :
      24 * (K + 1) / (K + 8) ≤
        24 * (K + 1) * (K + e) /
          (K * (16 + K + e)) := by
    apply (div_le_div_iff₀ hK8 hden).2
    nlinarith
  have hcoefBase :
      2 * K + 6 - 24 * (K + 1) / (K + 8) ≤ 8 * K / 3 := by
    rw [← mul_le_mul_iff_of_pos_right hK8]
    field_simp [hK8.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ K + 36)]
  have hcoef :
      2 * K + 6 -
          24 * (K + 1) * (K + e) /
            (K * (16 + K + e)) ≤
        8 * K / 3 := by
    linarith
  have hlinear :=
    mul_le_mul_of_nonneg_right hcoef he0
  have hlinearLower :
      -(8 * K * e / 3) ≤
        -(2 * K + 6) * e +
          24 * (K + 1) * e * (K + e) /
            (K * (16 + K + e)) := by
    have hneg := neg_le_neg hlinear
    calc
      -(8 * K * e / 3) = -(8 * K / 3 * e) := by ring
      _ ≤ -((2 * K + 6 -
          24 * (K + 1) * (K + e) /
            (K * (16 + K + e))) * e) := hneg
      _ = -(2 * K + 6) * e +
          24 * (K + 1) * e * (K + e) /
            (K * (16 + K + e)) := by ring
  have hbase : 2 * K ^ 2 ≤ 5 * K ^ 2 - 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ K + 1)]
  have hfirst :
      2 * K ^ 2 + 2 * e ^ 2 - 8 * K * e / 3 ≤
        floorJ K e := by
    unfold floorJ
    linarith
  have hsquare : 0 ≤ (K - e) ^ 2 := sq_nonneg _
  exact (by
    calc
      (K ^ 2 + e ^ 2) / 4
          ≤ 2 * K ^ 2 + 2 * e ^ 2 - 8 * K * e / 3 := by
            nlinarith
      _ ≤ floorJ K e := hfirst)
private theorem floorJ_bound_small
    {K e : ℝ} (hK : 1 ≤ K) (he0 : 0 ≤ e) (heK : e ≤ K) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let ξ : ℝ := e / K
  let c : ℝ := 1 + ξ
  have hξ0 : 0 ≤ ξ := div_nonneg he0 hKpos.le
  have hξ1 : ξ ≤ 1 := (div_le_one hKpos).2 heK
  have hc1 : 1 ≤ c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c]; linarith
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc1
  have hdenSmall : 0 < 16 + c := by linarith
  have hdenLarge : 0 < 16 + K * c := by positivity
  have hratio :
      2 / (16 + c) ≤ (K + 1) / (16 + K * c) := by
    apply (div_le_div_iff₀ hdenSmall hdenLarge).2
    have hprod :
        0 ≤ (K - 1) * (16 - c) :=
      mul_nonneg (sub_nonneg.mpr hK) (by linarith)
    nlinarith
  let B : ℝ := 6 - 48 * c / (16 + c)
  have hB : 2 / 3 ≤ B := by
    dsimp [B]
    rw [← mul_le_mul_iff_of_pos_right hdenSmall]
    field_simp [hdenSmall.ne']
    nlinarith
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2 / 3).trans hB
  have hscaledRatio :
      48 * c / (16 + c) ≤
        24 * (K + 1) * c / (16 + K * c) := by
    calc
      48 * c / (16 + c) =
          (24 * c) * (2 / (16 + c)) := by ring
      _ ≤ (24 * c) * ((K + 1) / (16 + K * c)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 24 * (K + 1) * c / (16 + K * c) := by ring
  have hbracket :
      6 - 24 * (K + 1) * c / (16 + K * c) ≤ B := by
    dsimp [B]
    linarith
  have hξdiv : ξ / K ≤ ξ := by
    have honeDiv : 1 / K ≤ 1 := (div_le_one hKpos).2 hK
    calc
      ξ / K = ξ * (1 / K) := by ring
      _ ≤ ξ * 1 := mul_le_mul_of_nonneg_left honeDiv hξ0
      _ = ξ := by ring
  have hInvSq : 1 / K ^ 2 ≤ 1 := by
    have hKSq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
    exact (div_le_one (sq_pos_of_pos hKpos)).2 hKSq
  have hidentity :
      floorJ K e / K ^ 2 =
        5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
          ξ / K *
            (6 - 24 * (K + 1) * c / (16 + K * c)) := by
    dsimp [ξ, c]
    unfold floorJ
    field_simp [hKpos.ne', hdenLarge.ne']
    ring
  have hratioLower :
      2 + 2 * ξ ^ 2 - 8 * ξ +
          48 * ξ * (1 + ξ) / (17 + ξ) ≤
        floorJ K e / K ^ 2 := by
    rw [hidentity]
    have hmulBracket :=
      mul_le_mul_of_nonneg_left hbracket
        (div_nonneg hξ0 hKpos.le)
    have hmulB :=
      mul_le_mul_of_nonneg_right hξdiv hB0
    have hthree : 3 / K ^ 2 ≤ 3 := by
      calc
        3 / K ^ 2 = 3 * (1 / K ^ 2) := by ring
        _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left hInvSq (by norm_num)
        _ = 3 := by ring
    calc
      2 + 2 * ξ ^ 2 - 8 * ξ +
            48 * ξ * (1 + ξ) / (17 + ξ) =
          2 + 2 * ξ ^ 2 - 2 * ξ - ξ * B := by
            dsimp [B, c]
            ring
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 - ξ * B := by
        linarith
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
            ξ / K * B := by
        linarith
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
            ξ / K *
              (6 - 24 * (K + 1) * c / (16 + K * c)) := by
        linarith
  let j : ℝ :=
    2 + 2 * ξ ^ 2 - 8 * ξ +
      48 * ξ * (1 + ξ) / (17 + ξ)
  have hdenXi : 0 < 17 + ξ := by linarith
  have hpoly :
      0 ≤ 7 * ξ ^ 3 + 29 * (3 * ξ - 2) ^ 2 +
        18 * ξ ^ 2 + 3 * ξ + 3 := by positivity
  have hj :
      (1 + ξ ^ 2) / 4 ≤ j := by
    have hid :
        4 * (17 + ξ) * (j - (1 + ξ ^ 2) / 4) =
          7 * ξ ^ 3 + 29 * (3 * ξ - 2) ^ 2 +
            18 * ξ ^ 2 + 3 * ξ + 3 := by
      dsimp [j]
      field_simp [hdenXi.ne']
      ring
    have hnonneg :
        0 ≤ 4 * (17 + ξ) * (j - (1 + ξ ^ 2) / 4) := by
      rw [hid]
      exact hpoly
    have hfac : 0 < 4 * (17 + ξ) := by positivity
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hfac).mp hnonneg)
  have hnormalized :
      (1 + ξ ^ 2) / 4 ≤ floorJ K e / K ^ 2 :=
    hj.trans (by simpa [j] using hratioLower)
  have hKSqpos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized hKSqpos.le
  have hleft :
      K ^ 2 * ((1 + ξ ^ 2) / 4) =
        (K ^ 2 + e ^ 2) / 4 := by
    dsimp [ξ]
    field_simp [hKpos.ne']
  have hright :
      K ^ 2 * (floorJ K e / K ^ 2) = floorJ K e := by
    field_simp [hKpos.ne']
  rwa [hleft, hright] at hscaled

theorem floorJ_bound
    {K e : ℝ} (hK : 1 ≤ K) (he0 : 0 ≤ e) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  by_cases heK : K ≤ e
  · exact floorJ_bound_large hK heK
  · exact floorJ_bound_small hK he0 (le_of_not_ge heK)

private theorem floorR_lower
    {K e u v : ℝ}
    (hK : 1 ≤ K) (he0 : 0 ≤ e)
    (hEll1 : floorEll u v K ≤ 1)
    (hW0 : 0 ≤ floorW u v K)
    (hWUpper : floorW u v K ≤ (K + 1) / (2 * K))
    (hEta : (K + e) / (16 + K + e) ≤ floorEta u v) :
    (K ^ 2 + e ^ 2) / 384 ≤ floorR K e u v := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hQpos : 0 < 16 + K + e := by linarith
  by_cases hcase : K / 2 ≤ e * floorEta u v
  · have hinner :
        0 ≤ e * floorEta u v -
          (K - 1 + floorEll u v K) / 2 := by
      have : K - 1 + floorEll u v K ≤ K := by linarith
      linarith
    have hsecond :
        0 ≤ floorW u v K / 2 *
          (e * floorEta u v -
            (K - 1 + floorEll u v K) / 2) := by
      positivity
    have hfirst :
        (4 * K ^ 2 + 6 * K + e ^ 2) / 96 ≤
          (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 -
            2 * K * e - 6 * e) / 96 := by
      nlinarith [sq_nonneg (K + 3 - e)]
    unfold floorR
    nlinarith [sq_nonneg K, sq_nonneg e]
  · have hcase' :
        e * floorEta u v - K / 2 < 0 := by linarith
    have hinner :
        e * floorEta u v - K / 2 ≤
          e * floorEta u v -
            (K - 1 + floorEll u v K) / 2 := by
      linarith
    have hfirstProduct :
        floorW u v K / 2 *
              (e * floorEta u v - K / 2) ≤
          floorW u v K / 2 *
              (e * floorEta u v -
                (K - 1 + floorEll u v K) / 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    have hupperNonneg : 0 ≤ (K + 1) / (4 * K) := by positivity
    have hWdiv :
        floorW u v K / 2 ≤ (K + 1) / (4 * K) := by
      calc
        floorW u v K / 2 ≤ ((K + 1) / (2 * K)) / 2 :=
          div_le_div_of_nonneg_right hWUpper (by norm_num)
        _ = (K + 1) / (4 * K) := by ring
    have hsecondProduct :
        (K + 1) / (4 * K) *
              (e * floorEta u v - K / 2) ≤
          floorW u v K / 2 *
              (e * floorEta u v - K / 2) := by
      exact mul_le_mul_of_nonpos_right hWdiv hcase'.le
    have hEtaMul :
        e * ((K + e) / (16 + K + e)) ≤
          e * floorEta u v :=
      mul_le_mul_of_nonneg_left hEta he0
    have hthirdProduct :
        (K + 1) / (4 * K) *
              (e * ((K + e) / (16 + K + e)) - K / 2) ≤
          (K + 1) / (4 * K) *
              (e * floorEta u v - K / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hupperNonneg
    have hJidentity :
        (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 -
              2 * K * e - 6 * e) / 96 +
            (K + 1) / (4 * K) *
              (e * ((K + e) / (16 + K + e)) - K / 2) =
          floorJ K e / 96 := by
      unfold floorJ
      field_simp [hKpos.ne', hQpos.ne']
      ring
    have hRge :
        floorJ K e / 96 ≤ floorR K e u v := by
      unfold floorR
      rw [← hJidentity]
      linarith
    have hJ := floorJ_bound hK he0
    calc
      (K ^ 2 + e ^ 2) / 384 ≤ floorJ K e / 96 := by
        linarith
      _ ≤ floorR K e u v := hRge

private theorem floor_rate_bound
    {K e u v : ℝ}
    (hK : 1 ≤ K)
    (hEll0 : 0 ≤ floorEll u v K)
    (hEll1 : floorEll u v K ≤ 1) :
    (floorEll u v K ^ 2 + ((K + 1) / 2) ^ 2) / 2 - 1 +
        ((K + e) / 2) ^ 2 ≤
      K ^ 2 + e ^ 2 := by
  have hEllSq : floorEll u v K ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - floorEll u v K)]
  have hKSq : ((K + 1) / 2) ^ 2 ≤ K ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ 3 * K + 1)]
  have hsumSq :
      ((K + e) / 2) ^ 2 ≤ (K ^ 2 + e ^ 2) / 2 := by
    nlinarith [sq_nonneg (K - e)]
  nlinarith [sq_nonneg e]

private theorem floor_coordinate_bounds
    {K e u v : ℝ}
    (hK : 1 ≤ K) (he0 : 0 ≤ e) (hu : 0 < u)
    (hrel : v = K * (u + 1) + e)
    (hfeedback : (K + e) * u * v ≤ 4 * (v ^ 2 - u ^ 2)) :
    0 < floorEll u v K ∧ floorEll u v K ≤ 1 ∧
      0 < floorW u v K ∧ floorW u v K ≤ (K + 1) / (2 * K) ∧
      (K + e) / (16 + K + e) ≤ floorEta u v := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hv : 0 < v := by rw [hrel]; positivity
  have huv : u ≤ v := by
    rw [hrel]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hu.le]
  have hKminus : 0 ≤ K - 1 := sub_nonneg.mpr hK
  have hEll1 : floorEll u v K ≤ 1 := by
    unfold floorEll
    have : 0 ≤ u * (K - 1) / (2 * v) := by positivity
    linarith
  have hEll0 : 0 < floorEll u v K := by
    have hnum : u * (K - 1) < 2 * v := by
      rw [hrel]
      nlinarith [mul_pos hKpos hu]
    unfold floorEll
    apply sub_pos.mpr
    exact (div_lt_one (by positivity : 0 < 2 * v)).2 hnum
  have hW0 : 0 < floorW u v K := by
    unfold floorW
    positivity
  have hWUpper : floorW u v K ≤ (K + 1) / (2 * K) := by
    have hden : 0 < 2 * (v + 1) := by positivity
    have hdenK : 0 < 2 * K := by positivity
    unfold floorW
    apply (div_le_div_iff₀ hden hdenK).2
    rw [hrel]
    nlinarith [mul_nonneg (by linarith : 0 ≤ K + 1)
      (by linarith : 0 ≤ e + 1)]
  have hdiff : 0 ≤ v - u := sub_nonneg.mpr huv
  have hQ : 0 < K + e := by linarith
  have hQden : 0 < 16 + K + e := by linarith
  have hvu : 0 < v + u := by positivity
  have hetaDen : 0 < v + 1 + u := by positivity
  have hfactor :
      4 * (v ^ 2 - u ^ 2) ≤ 8 * (v - u) * v := by
    nlinarith [sq_nonneg (v - u)]
  have hcancel :
      (K + e) * u ≤ 8 * (v - u) := by
    have hmul :
        (K + e) * u * v ≤ 8 * (v - u) * v :=
      hfeedback.trans hfactor
    exact (mul_le_mul_iff_of_pos_right hv).mp (by
      convert hmul using 1)
  have hc :
      (K + e) / (16 + K + e) ≤ (v - u) / (v + u) := by
    apply (div_le_div_iff₀ hQden hvu).2
    nlinarith
  have heta :
      (v - u) / (v + u) ≤ floorEta u v := by
    unfold floorEta
    apply (div_le_div_iff₀ hvu hetaDen).2
    nlinarith
  exact ⟨hEll0, hEll1, hW0, hWUpper, hc.trans heta⟩

/-- Minus-child scale in the floor coordinate system. -/
def floorU (s ρ : ℝ) : ℝ :=
  s * (1 - ρ)

/-- Plus-child scale in the floor coordinate system. -/
def floorV (s ρ : ℝ) : ℝ :=
  s * (1 + ρ)

/-- Twice the gap of the residual parameter from `1 / 2`. -/
def floorE (r : ℝ) : ℝ :=
  1 - 2 * r

/-- Floor parameter expressed through the two normalized child scales. -/
def floorK (s r ρ : ℝ) : ℝ :=
  (floorV s ρ - floorE r) / (floorU s ρ + 1)

private theorem floorU_pos
    {s ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    0 < floorU s ρ := by
  unfold floorU
  positivity

private theorem floorV_pos
    {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) :
    0 < floorV s ρ := by
  unfold floorV
  positivity

private theorem floor_relation
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    floorV s ρ =
      floorK s r ρ * (floorU s ρ + 1) + floorE r := by
  have hu := floorU_pos hs hρ1
  unfold floorK
  field_simp [(by positivity : 0 < floorU s ρ + 1).ne']
  ring

private theorem floorCap_eq_coordinates
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    floorCap s r ρ = (floorK s r ρ + floorE r) / 2 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring

private theorem floor_hMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    hMinus s ρ (floorCap s r ρ) =
      (floorK s r ρ + 1) / 2 := by
  have hu := floorU_pos hs hρ1
  have hrho : 1 - ρ ≠ 0 := by linarith
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold hMinus floorCap floorK floorE floorU floorV
  field_simp [hs.ne', hrho, hden.ne']
  ring

private theorem floor_hPlus_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    hPlus s ρ (floorCap s r ρ) =
      floorEll (floorU s ρ) (floorV s ρ) (floorK s r ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hrhop : 1 + ρ ≠ 0 := by linarith
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold hPlus floorCap floorEll floorK floorE floorU floorV
  field_simp [hs.ne', hrhop, hden.ne', hv.ne']
  ring

private theorem floor_ZMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    ZMinus s r ρ = (floorK s r ρ + 1) / 2 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold ZMinus g floorK floorE floorU floorV
  field_simp [hden.ne']
  ring

private theorem floor_ZPlus_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ZPlus s r ρ =
      floorW (floorU s ρ) (floorV s ρ) (floorK s r ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hdenU : 0 < s * (1 - ρ) + 1 := by positivity
  have hdenV : 0 < s * (1 + ρ) + 1 := by positivity
  unfold ZPlus g floorW floorK floorE floorU floorV
  field_simp [hdenU.ne', hdenV.ne']
  ring

private theorem floor_tPlus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    tPlus r (floorCap s r ρ) =
      -(2 * floorE r + floorK s r ρ - 1) / 4 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold tPlus floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring

private theorem floor_tMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    tMinus r (floorCap s r ρ) =
      (floorK s r ρ + 1) / 4 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold tMinus floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring

private theorem floor_ZParent_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    ZParent s r =
      (floorK s r ρ + 1) * (floorU s ρ + 1) /
        (floorU s ρ + floorV s ρ + 1) := by
  have hu := floorU_pos hs hρ1
  have hdenParent : 0 < s + 1 / 2 := by linarith
  have hdenTwo : 0 < 2 * s + 1 := by linarith
  have hrel := floor_relation (r := r) hs hρ1
  have hkterm :
      floorK s r ρ * (floorU s ρ + 1) =
        floorV s ρ - floorE r := by linarith
  have hsum :
      floorU s ρ + floorV s ρ = 2 * s := by
    unfold floorU floorV
    ring
  have hnum :
      (floorK s r ρ + 1) * (floorU s ρ + 1) =
        2 * (s + r) := by
    rw [show (floorK s r ρ + 1) * (floorU s ρ + 1) =
      floorK s r ρ * (floorU s ρ + 1) +
        floorU s ρ + 1 by ring, hkterm]
    unfold floorE floorU floorV
    ring
  unfold ZParent g
  rw [hnum, hsum]
  field_simp [hdenParent.ne', hdenTwo.ne']
private theorem floor_residual_algebra
    {K e u v r : ℝ}
    (hu : 0 < u) (hv : 0 < v)
    (hrel : v = K * (u + 1) + e)
    (hr : r = (1 - e) / 2) :
    ((-(2 * e + K - 1) / 4 * floorW u v K +
          bellman (floorEll u v K) (-(2 * e + K - 1) / 4)
            (floorW u v K)) +
        ((K + 1) / 4 * ((K + 1) / 2) +
          bellman ((K + 1) / 2) ((K + 1) / 4) ((K + 1) / 2))) / 2 -
      bellman 1 r
        ((K + 1) * (u + 1) / (u + v + 1)) =
      floorR K e u v := by
  subst r
  subst v
  unfold floorR bellman floorEta floorW floorEll
  field_simp [hu.ne', hv.ne']
  ring
private theorem floor_residual_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (floorCap s r ρ) =
      floorR (floorK s r ρ) (floorE r) (floorU s ρ) (floorV s ρ) := by
  rw [residual, floor_hPlus_eq hs hρ0 hρ1,
    floor_hMinus_eq hs hρ1, floor_tPlus_eq hs hρ1,
    floor_tMinus_eq hs hρ1, floor_ZPlus_eq hs hρ0 hρ1,
    floor_ZMinus_eq hs hρ1, floor_ZParent_eq hs hρ1]
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hrel := floor_relation (r := r) hs hρ1
  have hr : r = (1 - floorE r) / 2 := by
    unfold floorE
    ring
  exact floor_residual_algebra hu hv hrel hr

private theorem floor_rateIncrement_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (floorCap s r ρ) =
      (floorEll (floorU s ρ) (floorV s ρ) (floorK s r ρ) ^ 2 +
        ((floorK s r ρ + 1) / 2) ^ 2) / 2 - 1 := by
  rw [rateIncrement, floor_hPlus_eq hs hρ0 hρ1,
    floor_hMinus_eq hs hρ1]

private theorem feedback_eq_floor_coordinates
    {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    feedback s ρ =
      2 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) /
        (floorU s ρ * floorV s ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0.le
  have hA := A_pos hs hρ0.le hρ1
  have hsq : 0 < 1 - ρ ^ 2 := sub_pos.mpr (lambda_lt_one hρ0.le hρ1)
  have hrhom : 1 - ρ ≠ 0 := by linarith
  have hrhop : 1 + ρ ≠ 0 := by linarith
  unfold feedback A lambda floorU floorV
  field_simp [hs.ne', hsq.ne', hrhom, hrhop]
  ring

private theorem uniform_eq_floor_coordinates
    (s ρ : ℝ) :
    uniform s ρ = (floorV s ρ - floorU s ρ) / 2 := by
  unfold uniform floorU floorV
  ring
theorem floor_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactiveU : floorCap s r ρ ≤ uniform s ρ)
    (hactiveF : floorCap s r ρ ≤ feedback s ρ) :
    residual s r ρ (floorCap s r ρ) ≥
      (rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2) /
        1000 := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0.le
  have he0 : 0 ≤ floorE r := by
    unfold floorE
    linarith
  have hrel := floor_relation (r := r) hs hρ1
  have hactiveU' :
      (floorK s r ρ + floorE r) / 2 ≤
        (floorV s ρ - floorU s ρ) / 2 := by
    rw [← floorCap_eq_coordinates hs hρ1,
      ← uniform_eq_floor_coordinates]
    exact hactiveU
  have hprod :
      0 ≤ (floorK s r ρ - 1) * floorU s ρ := by
    nlinarith
  have hK : 1 ≤ floorK s r ρ := by
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hprod hu)
  have hactiveF' :
      (floorK s r ρ + floorE r) / 2 ≤
        2 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) /
          (floorU s ρ * floorV s ρ) := by
    rw [← floorCap_eq_coordinates hs hρ1,
      ← feedback_eq_floor_coordinates hs hρ0 hρ1]
    exact hactiveF
  have hfeedback :
      (floorK s r ρ + floorE r) * floorU s ρ * floorV s ρ ≤
        4 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) := by
    have huv : 0 < floorU s ρ * floorV s ρ := mul_pos hu hv
    have hmul := (le_div_iff₀ huv).1 hactiveF'
    nlinarith
  obtain ⟨hEll0, hEll1, hW0, hWUpper, hEta⟩ :=
    floor_coordinate_bounds hK he0 hu hrel hfeedback
  have hResidual :=
    floorR_lower hK he0 hEll1 hW0.le hWUpper hEta
  have hRate :=
    floor_rate_bound (e := floorE r) hK hEll0.le hEll1
  have hResidual' :
      (floorK s r ρ ^ 2 + floorE r ^ 2) / 384 ≤
        residual s r ρ (floorCap s r ρ) := by
    rw [floor_residual_eq hs hρ0.le hρ1]
    exact hResidual
  have hRate' :
      rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2 ≤
        floorK s r ρ ^ 2 + floorE r ^ 2 := by
    rw [floor_rateIncrement_eq hs hρ0.le hρ1,
      floorCap_eq_coordinates hs hρ1]
    exact hRate
  have henergy :
      0 ≤ floorK s r ρ ^ 2 + floorE r ^ 2 := by positivity
  calc
    (rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2) /
          1000
        ≤ (floorK s r ρ ^ 2 + floorE r ^ 2) / 1000 := by
          exact div_le_div_of_nonneg_right hRate' (by norm_num)
    _ ≤ (floorK s r ρ ^ 2 + floorE r ^ 2) / 384 := by
          nlinarith
    _ ≤ residual s r ρ (floorCap s r ρ) := hResidual'

theorem equal_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2) :
    residual s r 0 0 ≥
      (rateIncrement s 0 0 + 0 ^ 2) / 1000 := by
  have hcommon :=
    residual_eq_common
      (s := s) (r := r) (ρ := 0) (k := 0)
      hs (by norm_num) (by norm_num)
  have hcommon' :
      residual s r 0 0 =
        r ^ 2 / 8 +
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * d s 0 * (s + 1 / 2)) := by
    simpa [lambda] using hcommon
  have hres :
      0 ≤ residual s r 0 0 := by
    rw [hcommon']
    have hg : 0 < g s r := g_pos hr0
    have hd : 0 < d s 0 := d_pos hs (by norm_num) (by norm_num)
    have hterm :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s 0 * (s + 1 / 2)) := by
      positivity
    exact add_nonneg (by positivity) hterm
  have hrate : rateIncrement s 0 0 = 0 := by
    unfold rateIncrement hPlus hMinus
    field_simp [hs.ne']
    ring
  simpa [hrate] using hres

theorem threeCap_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    let z := min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ))
    residual s r ρ z ≥ (rateIncrement s ρ z + z ^ 2) / 1000 := by
  dsimp
  by_cases hρ : ρ = 0
  · subst ρ
    have hfloor : 0 ≤ floorCap s r 0 := by
      unfold floorCap
      have hden : 0 < s + 1 := by positivity
      norm_num
      exact div_nonneg (by nlinarith) hden.le
    have hchoice :
        min (feedback s 0) (min (uniform s 0) (floorCap s r 0)) = 0 := by
      simp [feedback, uniform, hfloor]
    rw [hchoice]
    exact equal_case hs hr0 hr1
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρ)
  have hApos := A_pos hs hρ0 hρ1
  by_cases hFU : feedback s ρ ≤ uniform s ρ
  · by_cases hFH : feedback s ρ ≤ floorCap s r ρ
    · have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            feedback s ρ :=
        min_eq_left (le_min hFU hFH)
      rw [hchoice]
      exact feedback_case hs hr0 hr1 hρpos hρ1 hFU
    · have hHF : floorCap s r ρ ≤ feedback s ρ := le_of_not_ge hFH
      have hHU : floorCap s r ρ ≤ uniform s ρ := hHF.trans hFU
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            floorCap s r ρ := by
        rw [min_eq_right hHU, min_eq_right hHF]
      rw [hchoice]
      exact floor_case hs hr1 hρpos hρ1 hHU hHF
  · have hUF : uniform s ρ ≤ feedback s ρ := le_of_not_ge hFU
    by_cases hUH : uniform s ρ ≤ floorCap s r ρ
    · have hA8 : A s ρ ≤ 8 := by
        unfold uniform feedback at hUF
        have hsρ : 0 < s * ρ := mul_pos hs hρpos
        have hmul := (le_div_iff₀ hApos).1 hUF
        nlinarith
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            uniform s ρ := by
        rw [min_eq_left hUH, min_eq_right hUF]
      rw [hchoice]
      exact uniform_case hs hr0 hr1 hρ0 hρ1 hA8
    · have hHU : floorCap s r ρ ≤ uniform s ρ := le_of_not_ge hUH
      have hHF : floorCap s r ρ ≤ feedback s ρ := hHU.trans hUF
      have hchoice :
          min (feedback s ρ) (min (uniform s ρ) (floorCap s r ρ)) =
            floorCap s r ρ := by
        rw [min_eq_right hHU, min_eq_right hHF]
      rw [hchoice]
      exact floor_case hs hr1 hρpos hρ1 hHU hHF

/-! ## Empty-child boundary -/

/--
The normalized residual when the larger child is occupied and the smaller
child is empty. The occupied child has normalized rate one; `emptyRate` is
the auxiliary rate assigned to the empty child.
-/
def emptyResidual (s r emptyRate : ℝ) : ℝ :=
  let total := g s r
  let occupiedDrift := (r - s) / 2
  let occupiedZ := total / (2 * s + 1)
  let emptyDrift := total / 2
  ((occupiedDrift * occupiedZ +
        bellman 1 occupiedDrift occupiedZ) +
      (emptyDrift * total +
        bellman emptyRate emptyDrift total)) / 2 -
    bellman 1 r (total / (s + 1 / 2))

/-- Normalized child-rate energy at a one-empty-child boundary. -/
def emptyRateIncrement (emptyRate : ℝ) : ℝ :=
  (1 + emptyRate ^ 2) / 2 - 1

private theorem emptyResidual_uniform_eq
    {s r : ℝ} (hs : 0 < s) :
    emptyResidual s r 1 =
      r ^ 2 / 8 - s ^ 2 / 24 +
        g s r ^ 2 * s ^ 2 /
          ((2 * s + 1) * (s + 1 / 2)) +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * (2 * s + 1) * (s + 1 / 2)) := by
  have htwo : 2 * s + 1 ≠ 0 := by linarith
  have hhalf : s + 1 / 2 ≠ 0 := by linarith
  unfold emptyResidual bellman
  dsimp only
  field_simp [htwo, hhalf]
  unfold g
  ring

private theorem empty_uniform_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2) :
    emptyResidual s r 1 ≥
      (emptyRateIncrement 1 + s ^ 2) / 1000 := by
  have hg : 0 < g s r := g_pos hr0
  rw [emptyResidual_uniform_eq hs]
  have hrate : emptyRateIncrement 1 = 0 := by
    norm_num [emptyRateIncrement]
  rw [hrate, zero_add]
  by_cases hsHalf : 1 / 2 ≤ s
  · have hden :
        (2 * s + 1) * (s + 1 / 2) ≤ 13 * s ^ 2 := by
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hdenpos : 0 < (2 * s + 1) * (s + 1 / 2) := by
      positivity
    have hsquare :
        g s r ^ 2 / 13 ≤
          g s r ^ 2 * s ^ 2 /
            ((2 * s + 1) * (s + 1 / 2)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hdenpos).2
      have hmul :=
        mul_le_mul_of_nonneg_left hden (sq_nonneg (g s r))
      nlinarith
    have hcauchy :=
      weighted_square_bound
        (s := s) (r := r) (lam := 1) (by norm_num) (by norm_num)
    have hlast :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * (2 * s + 1) * (s + 1 / 2)) := by
      positivity
    simp only [g, one_mul] at hcauchy hsquare hlast ⊢
    nlinarith
  · have hsUpper : s ≤ 1 / 2 := le_of_not_ge hsHalf
    have hdUpper : 2 * s + 1 ≤ (s + 1) ^ 2 := by
      nlinarith [sq_nonneg s]
    have hcoef :
        1 / 3 ≤
          (s + 1) / (2 * (2 * s + 1) * (s + 1 / 2)) := by
      have hdenpos :
          0 < 2 * (2 * s + 1) * (s + 1 / 2) := by
        positivity
      apply (le_div_iff₀ hdenpos).2
      have hbound :
          2 * (s + 1) ^ 2 * (s + 1 / 2) ≤ 3 * (s + 1) := by
        have hfac : 0 ≤ s + 1 := by positivity
        nlinarith [mul_nonneg hfac
          (mul_nonneg (sub_nonneg.mpr hs.le)
            (by linarith : 0 ≤ 1 - s))]
      have hmul :=
        mul_le_mul_of_nonneg_right hdUpper
          (by linarith : 0 ≤ 2 * (s + 1 / 2))
      nlinarith
    have hlast :
        g s r * (1 / 2 - r) / 3 ≤
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * (2 * s + 1) * (s + 1 / 2)) := by
      have hfactor : 0 ≤ g s r * (1 / 2 - r) := by positivity
      calc
        g s r * (1 / 2 - r) / 3 =
            (g s r * (1 / 2 - r)) * (1 / 3) := by ring
        _ ≤ (g s r * (1 / 2 - r)) *
              ((s + 1) /
                (2 * (2 * s + 1) * (s + 1 / 2))) :=
          mul_le_mul_of_nonneg_left hcoef hfactor
        _ = g s r * (1 / 2 - r) * (s + 1) /
              (2 * (2 * s + 1) * (s + 1 / 2)) := by ring
    have hcore :
        s ^ 2 / 12 ≤ r ^ 2 / 8 - s ^ 2 / 24 +
          (s + r) * (1 / 2 - r) / 3 := by
      have hleft : 0 ≤ r + s := by linarith
      have hright : 0 ≤ 4 - 5 * r - 3 * s := by linarith
      nlinarith [mul_nonneg hleft hright]
    have hsquare :
        0 ≤ g s r ^ 2 * s ^ 2 /
          ((2 * s + 1) * (s + 1 / 2)) := by
      positivity
    simp only [g] at hlast hsquare ⊢
    nlinarith

private theorem empty_floor_residual_eq
    {s r : ℝ} (hs : 0 < s) :
    emptyResidual s r (g s r) =
      floorR (2 * g s r - 1) (1 - 2 * r) 0 (2 * s) := by
  have hsTwo : 2 * s ≠ 0 := by linarith
  have hsOne : 2 * s + 1 ≠ 0 := by linarith
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  unfold emptyResidual floorR floorW floorEta floorEll bellman
  dsimp only
  field_simp [hsTwo, hsOne, hsHalf]
  unfold g
  ring

private theorem empty_floor_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hg1 : 1 ≤ g s r) :
    emptyResidual s r (g s r) ≥
      (emptyRateIncrement (g s r) + s ^ 2) / 1000 := by
  let K : ℝ := 2 * g s r - 1
  let e : ℝ := 1 - 2 * r
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have he0 : 0 ≤ e := by
    dsimp [e]
    linarith
  have hsum : K + e = 2 * s := by
    dsimp [K, e]
    unfold g
    ring
  have hEll : floorEll 0 (2 * s) K = 1 := by
    unfold floorEll
    field_simp
    ring
  have hW0 : 0 ≤ floorW 0 (2 * s) K := by
    unfold floorW
    positivity
  have hWUpper :
      floorW 0 (2 * s) K ≤ (K + 1) / (2 * K) := by
    have hdenS : 0 < 2 * (2 * s + 1) := by positivity
    have hdenK : 0 < 2 * K := by positivity
    unfold floorW
    norm_num only [zero_add]
    apply (div_le_div_iff₀ hdenS hdenK).2
    have hKUpper : K ≤ 2 * s + 1 := by
      dsimp [K]
      unfold g
      linarith
    nlinarith
  have hEta :
      (K + e) / (16 + K + e) ≤ floorEta 0 (2 * s) := by
    have hetaEq : floorEta 0 (2 * s) = 1 := by
      unfold floorEta
      field_simp
      ring
    have hdenEq : 16 + K + e = 16 + 2 * s := by
      linarith
    rw [hsum, hdenEq, hetaEq]
    have hden : 0 < 16 + 2 * s := by positivity
    exact (div_le_one hden).2 (by linarith)
  have hResidual :=
    floorR_lower hK he0
      (by rw [hEll]) hW0 hWUpper hEta
  have hResidual' :
      (K ^ 2 + e ^ 2) / 384 ≤
        emptyResidual s r (g s r) := by
    rw [empty_floor_residual_eq hs]
    simpa [K, e] using hResidual
  have hRate :=
    floor_rate_bound (e := e) (u := 0) (v := 2 * s) hK
      (by rw [hEll]; norm_num) (by rw [hEll])
  have hG : (K + 1) / 2 = g s r := by
    dsimp [K]
    ring
  have hS : (K + e) / 2 = s := by
    rw [hsum]
    ring
  have hRate' :
      emptyRateIncrement (g s r) + s ^ 2 ≤ K ^ 2 + e ^ 2 := by
    simpa [emptyRateIncrement, hEll, hG, hS] using hRate
  have henergy : 0 ≤ K ^ 2 + e ^ 2 := by positivity
  calc
    (emptyRateIncrement (g s r) + s ^ 2) / 1000
        ≤ (K ^ 2 + e ^ 2) / 1000 := by
          exact div_le_div_of_nonneg_right hRate' (by norm_num)
    _ ≤ (K ^ 2 + e ^ 2) / 384 := by
          nlinarith
    _ ≤ emptyResidual s r (g s r) := hResidual'

end Normalized

/-! ## Concrete local policy -/

/-- The left side of the manuscript's local Bellman inequality. -/
def localResidual (a p h : ℝ) (x y : ℕ) : ℝ :=
  ((discrepancyLeft a p h x y * regularizedMassLeft a p x +
        bellman (rateLeft a p h x y) (discrepancyLeft a p h x y)
          (regularizedMassLeft a p x )) +
      (discrepancyRight a p h x y * regularizedMassRight a p y +
        bellman (rateRight a p h x y) (discrepancyRight a p h x y)
          (regularizedMassRight a p y))) / 2 -
    bellman h (discrepancy a p h x y) (regularizedMass a p x y)

/-- The rate increment plus squared deletion bias in the local inequality. -/
def localEnergy (a p h : ℝ) (x y : ℕ) : ℝ :=
  (rateLeft a p h x y ^ 2 + rateRight a p h x y ^ 2) / 2 -
    h ^ 2 + bias a p h x y ^ 2 / a ^ 2

private theorem discrepancy_swap (a p h : ℝ) (x y : ℕ) :
    discrepancy a p h y x = discrepancy a p h x y := by
  unfold discrepancy
  rw [parentMass_swap]

private theorem regularizedMass_swap (a p : ℝ) (x y : ℕ) :
    regularizedMass a p y x = regularizedMass a p x y := by
  simp [regularizedMass, inventory, add_comm]

private theorem discrepancyLeft_swap (a p h : ℝ) (x y : ℕ) :
    discrepancyLeft a p h y x = discrepancyRight a p h x y := by
  unfold discrepancyLeft discrepancyRight
  rw [massLeft_swap]

private theorem discrepancyRight_swap (a p h : ℝ) (x y : ℕ) :
    discrepancyRight a p h y x = discrepancyLeft a p h x y := by
  unfold discrepancyLeft discrepancyRight
  rw [massRight_swap]

private theorem regularizedMassLeft_swap (a p : ℝ) (y : ℕ) :
    regularizedMassLeft a p y = regularizedMassRight a p y := by
  rfl

private theorem regularizedMassRight_swap (a p : ℝ) (x : ℕ) :
    regularizedMassRight a p x = regularizedMassLeft a p x := by
  rfl

private theorem localResidual_swap (a p h : ℝ) (x y : ℕ) :
    localResidual a p h y x = localResidual a p h x y := by
  unfold localResidual
  rw [discrepancyLeft_swap a p h x y,
    discrepancyRight_swap a p h x y,
    regularizedMassLeft_swap a p y,
    regularizedMassRight_swap a p x,
    rateLeft_swap a p h x y, rateRight_swap a p h x y,
    discrepancy_swap a p h x y, regularizedMass_swap a p x y]
  ring

private theorem localEnergy_swap (a p h : ℝ) (x y : ℕ) :
    localEnergy a p h y x = localEnergy a p h x y := by
  unfold localEnergy
  rw [rateLeft_swap a p h x y, rateRight_swap a p h x y,
    bias_swap a p h x y]
  ring

private theorem bellman_scale (c u t Z : ℝ) :
    bellman (c * u) (c * t) (c * Z) = c ^ 2 * bellman u t Z := by
  unfold bellman
  ring

private theorem discrepancy_scale
    {a p h : ℝ} {x y : ℕ} (hh : 0 < h) :
    discrepancy a p h x y =
      h * (discrepancy a p h x y / h) := by
  field_simp [hh.ne']

private theorem discrepancyLeft_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    discrepancyLeft a p h x y =
      h * Normalized.tPlus
        (discrepancy a p h x y / h)
        (bias a p h x y / (a * h)) := by
  rw [LocalPolicy.discrepancyLeft_eq]
  unfold Normalized.tPlus
  field_simp [ha.ne', hh.ne']

private theorem discrepancyRight_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    discrepancyRight a p h x y =
      h * Normalized.tMinus
        (discrepancy a p h x y / h)
        (bias a p h x y / (a * h)) := by
  rw [LocalPolicy.discrepancyRight_eq]
  unfold Normalized.tMinus
  field_simp [ha.ne', hh.ne']

private theorem rateLeft_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    rateLeft a p h x y =
      h * Normalized.hPlus
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y)
        (bias a p h x y / (a * h)) := by
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hsum : x + y ≠ 0 := by omega
  have hN : 0 < inventory x y := inventory_pos hsum
  unfold rateLeft
  rw [ite_eq_right hsum, ite_eq_right hx.ne']
  unfold massLeft parentMass Normalized.hPlus inventory
  field_simp [ha.ne', hh.ne', hxr.ne', hN.ne']
  ring

private theorem rateRight_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    rateRight a p h x y =
      h * Normalized.hMinus
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y)
        (bias a p h x y / (a * h)) := by
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hsum : x + y ≠ 0 := by omega
  have hN : 0 < inventory x y := inventory_pos hsum
  unfold rateRight
  rw [ite_eq_right hsum, ite_eq_right hy.ne']
  unfold massRight parentMass Normalized.hMinus inventory
  field_simp [ha.ne', hh.ne', hyr.ne', hN.ne']
  ring

private theorem regularizedMassLeft_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    regularizedMassLeft a p x =
      h * Normalized.ZPlus
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hNnonneg := inventory_nonneg x y
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hNden : 0 < inventory x y + a / 2 := by linarith
  have hxden : 0 < (x : ℝ) + a / 2 := by positivity
  unfold regularizedMassLeft Normalized.ZPlus Normalized.g
    discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hxden.ne']
  ring_nf
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hxden.ne']


private theorem regularizedMassRight_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    regularizedMassRight a p y =
      h * Normalized.ZMinus
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hNnonneg := inventory_nonneg x y
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hNden : 0 < inventory x y + a / 2 := by linarith
  have hyden : 0 < (y : ℝ) + a / 2 := by positivity
  unfold regularizedMassRight Normalized.ZMinus Normalized.g
    discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hyden.ne']
  ring_nf
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hyden.ne']


private theorem regularizedMass_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) :
    regularizedMass a p x y =
      h * Normalized.ZParent
        (inventory x y / a)
        (discrepancy a p h x y / h) := by
  have hNnonneg := inventory_nonneg x y
  have hden : 0 < inventory x y + a / 2 := by linarith
  unfold regularizedMass Normalized.ZParent Normalized.g
    discrepancy parentMass
  field_simp [ha.ne', hh.ne', hden.ne']
  ring

private theorem parentBellman_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    bellman h (discrepancy a p h x y) (regularizedMass a p x y) =
      h ^ 2 * bellman 1
        (discrepancy a p h x y / h)
        (Normalized.ZParent
          (inventory x y / a)
          (discrepancy a p h x y / h)) := by
  rw [regularizedMass_normalization ha hh]
  conv_lhs =>
    congr
    · rw [show h = h * 1 by ring]
    · rw [discrepancy_scale hh]
  exact bellman_scale h 1
    (discrepancy a p h x y / h)
    (Normalized.ZParent
      (inventory x y / a)
      (discrepancy a p h x y / h))

private theorem positive_residual_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    localResidual a p h x y =
      h ^ 2 *
        Normalized.residual
          (inventory x y / a)
          (discrepancy a p h x y / h)
          (((x : ℝ) - y) / inventory x y)
          (bias a p h x y / (a * h)) := by
  unfold localResidual Normalized.residual
  rw [rateLeft_normalization ha hh hx hy,
    rateRight_normalization ha hh hx hy,
    discrepancyLeft_normalization ha hh,
    discrepancyRight_normalization ha hh,
    regularizedMassLeft_normalization ha hh hx hy,
    regularizedMassRight_normalization ha hh hx hy,
    parentBellman_normalization ha hh]
  simp only [bellman_scale]
  ring

private theorem positive_energy_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    localEnergy a p h x y =
      h ^ 2 *
        (Normalized.rateIncrement
            (inventory x y / a)
            (((x : ℝ) - y) / inventory x y)
            (bias a p h x y / (a * h)) +
          (bias a p h x y / (a * h)) ^ 2) := by
  unfold localEnergy Normalized.rateIncrement
  rw [rateLeft_normalization ha hh hx hy,
    rateRight_normalization ha hh hx hy]
  field_simp [ha.ne', hh.ne']

private theorem feedbackCandidate_normalization
    {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    feedbackCandidate a h x y / (a * h) =
      Normalized.feedback
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y) := by
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 < inventory x y := inventory_pos (by omega)
  unfold feedbackCandidate parentMass Normalized.feedback Normalized.A
    Normalized.lambda inventory
  field_simp [ha.ne', hh.ne', hxr.ne', hyr.ne', hN.ne']
  ring_nf
  field_simp [ha.ne', hh.ne', hxr.ne', hyr.ne', hN.ne']
  ring

private theorem uniformCandidate_normalization
    {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    uniformCandidate h x y / (a * h) =
      Normalized.uniform
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y) := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  unfold uniformCandidate parentMass Normalized.uniform inventory
  field_simp [ha.ne', hh.ne', hN.ne']


private theorem floorCandidate_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    floorCandidate a p h x y / (a * h) =
      Normalized.floorCap
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hden : 0 < 2 * (y : ℝ) + a := by positivity
  unfold floorCandidate discrepancy parentMass Normalized.floorCap inventory
  field_simp [ha.ne', hh.ne', hyr.ne', hN.ne', hden.ne']
  ring_nf
  field_simp [ha.ne', hh.ne', hyr.ne', hN.ne', hden.ne']
  ring

private theorem ordered_positive_case
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x) (hx : 0 < x) (hy : 0 < y)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  let s : ℝ := inventory x y / a
  let r : ℝ := discrepancy a p h x y / h
  let ρ : ℝ := ((x : ℝ) - y) / inventory x y
  let z : ℝ := bias a p h x y / (a * h)
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hr0 : -s < r := by
    dsimp [s, r]
    unfold discrepancy parentMass
    field_simp [ha.ne', hh.ne']
    nlinarith
  have hr1 : r ≤ 1 / 2 := by
    dsimp [r]
    exact (div_le_iff₀ hh).2 (by nlinarith)
  have hρ0 : 0 ≤ ρ := by
    dsimp [ρ]
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hxy)
    · exact hN.le
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply (div_lt_one hN).2
    have hyR : 0 < (y : ℝ) := by exact_mod_cast hy
    unfold inventory
    linarith
  have hResidual :
      localResidual a p h x y =
        h ^ 2 * Normalized.residual s r ρ z := by
    simpa [s, r, ρ, z] using
      positive_residual_normalization ha hh hx hy
  have hEnergy :
      localEnergy a p h x y =
        h ^ 2 * (Normalized.rateIncrement s ρ z + z ^ 2) := by
    simpa [s, ρ, z] using positive_energy_normalization ha hh hx hy
  have hnormalized :
      Normalized.residual s r ρ z ≥
        (Normalized.rateIncrement s ρ z + z ^ 2) / 1000 := by
    by_cases heq : x = y
    · subst x
      have hb : bias a p h y y = 0 := by
        simp [bias, orderedBias]
      have hρ : ρ = 0 := by
        simp [ρ, inventory]
      have hz : z = 0 := by
        simp [z, hb]
      rw [hρ, hz]
      exact Normalized.equal_case hs hr0 hr1
    · have hlt : y < x := lt_of_le_of_ne hxy (Ne.symm heq)
      have hb :
          bias a p h x y =
            min (feedbackCandidate a h x y)
              (min (uniformCandidate h x y)
                (floorCandidate a p h x y)) := by
        unfold bias
        rw [ite_eq_left hxy]
        unfold orderedBias
        rw [ite_eq_right heq, ite_eq_right (by omega : x + y ≠ 0),
          ite_eq_right hy.ne']
      have hah : 0 ≤ a * h := (mul_pos ha hh).le
      have hzChoice :
          z =
            min (Normalized.feedback s ρ)
              (min (Normalized.uniform s ρ)
                (Normalized.floorCap s r ρ)) := by
        dsimp [z]
        rw [hb, ← min_div_div_right hah,
          ← min_div_div_right hah]
        rw [feedbackCandidate_normalization ha hh hx hy,
          uniformCandidate_normalization ha hh hx hy,
          floorCandidate_normalization ha hh hx hy]
      rw [hzChoice]
      exact Normalized.threeCap_case hs hr0 hr1 hρ0 hρ1
  rw [hResidual, hEnergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized (sq_nonneg h)
  calc
    h ^ 2 * (Normalized.rateIncrement s ρ z + z ^ 2) / 1000 =
        h ^ 2 *
          ((Normalized.rateIncrement s ρ z + z ^ 2) / 1000) := by ring
    _ ≤ h ^ 2 * Normalized.residual s r ρ z := hscaled

private theorem ordered_empty_residual_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) :
    localResidual a p h x 0 =
      h ^ 2 *
        Normalized.emptyResidual
          ((x : ℝ) / a)
          (discrepancy a p h x 0 / h)
          (rateRight a p h x 0 / h) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : x + 0 ≠ 0 := by omega
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hb : bias a p h x 0 = parentMass h x 0 := by
    simp [bias, orderedBias, hx0]
  have hRL : rateLeft a p h x 0 = h := by
    unfold rateLeft
    rw [ite_eq_right hsum, ite_eq_right hx0]
    unfold massLeft
    rw [hb]
    simp [parentMass, inventory, hx0]
  have hRR : rateRight a p h x 0 = max h (p / a) := by
    unfold rateRight
    rw [ite_eq_right hsum, ite_eq_left rfl]
  unfold localResidual Normalized.emptyResidual
  dsimp only
  rw [hRL, hRR]
  unfold discrepancyLeft discrepancyRight regularizedMassLeft
    regularizedMassRight regularizedMass discrepancy massLeft massRight
    Normalized.g bellman
  rw [hb]
  unfold parentMass inventory
  field_simp [ha.ne', hh.ne', hxr.ne']
  ring_nf


private theorem ordered_empty_energy_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) :
    localEnergy a p h x 0 =
      h ^ 2 *
        (Normalized.emptyRateIncrement
            (rateRight a p h x 0 / h) +
          ((x : ℝ) / a) ^ 2) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : x + 0 ≠ 0 := by omega
  have hb : bias a p h x 0 = parentMass h x 0 := by
    simp [bias, orderedBias, hx0]
  have hRL : rateLeft a p h x 0 = h := by
    unfold rateLeft
    rw [ite_eq_right hsum, ite_eq_right hx0]
    unfold massLeft
    rw [hb]
    simp [parentMass, inventory, hx0]
  unfold localEnergy Normalized.emptyRateIncrement
  rw [hRL]
  rw [hb]
  unfold parentMass inventory
  field_simp [ha.ne', hh.ne']
  ring

private theorem empty_total_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) :
    Normalized.g ((x : ℝ) / a)
        (discrepancy a p h x 0 / h) =
      p / (a * h) := by
  unfold Normalized.g discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne']
  ring

private theorem ordered_one_empty_case
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h) (hx : 0 < x)
    (ht : discrepancy a p h x 0 ≤ h / 2) :
    localResidual a p h x 0 ≥ localEnergy a p h x 0 / 1000 := by
  let s : ℝ := (x : ℝ) / a
  let r : ℝ := discrepancy a p h x 0 / h
  let emptyRate : ℝ := rateRight a p h x 0 / h
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hr0 : -s < r := by
    dsimp [s, r]
    unfold discrepancy parentMass inventory
    field_simp [ha.ne', hh.ne']
    norm_num at *
    nlinarith
  have hr1 : r ≤ 1 / 2 := by
    dsimp [r]
    exact (div_le_iff₀ hh).2 (by nlinarith)
  have hResidual :
      localResidual a p h x 0 =
        h ^ 2 * Normalized.emptyResidual s r emptyRate := by
    simpa [s, r, emptyRate] using
      ordered_empty_residual_normalization ha hh hx
  have hEnergy :
      localEnergy a p h x 0 =
        h ^ 2 *
          (Normalized.emptyRateIncrement emptyRate + s ^ 2) := by
    simpa [s, emptyRate] using
      ordered_empty_energy_normalization ha hh hx
  have hnormalized :
      Normalized.emptyResidual s r emptyRate ≥
        (Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000 := by
    by_cases hsmall : p / a ≤ h
    · have hRate : emptyRate = 1 := by
        dsimp [emptyRate]
        unfold rateRight
        rw [ite_eq_right (by omega : x + 0 ≠ 0), ite_eq_left rfl,
          max_eq_left hsmall]
        field_simp [hh.ne']
      rw [hRate]
      exact Normalized.empty_uniform_case hs hr0 hr1
    · have hlarge : h ≤ p / a := le_of_not_ge hsmall
      have hRate :
          emptyRate = Normalized.g s r := by
        dsimp [emptyRate]
        unfold rateRight
        rw [ite_eq_right (by omega : x + 0 ≠ 0), ite_eq_left rfl,
          max_eq_right hlarge]
        rw [empty_total_normalization ha hh]
        ring
      have hg1 : 1 ≤ Normalized.g s r := by
        rw [← hRate]
        dsimp [emptyRate]
        unfold rateRight
        rw [ite_eq_right (by omega : x + 0 ≠ 0), ite_eq_left rfl,
          max_eq_right hlarge]
        apply (le_div_iff₀ hh).2
        simpa using hlarge
      rw [hRate]
      exact Normalized.empty_floor_case hs hr0 hr1 hg1
  rw [hResidual, hEnergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized (sq_nonneg h)
  calc
    h ^ 2 * (Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000 =
        h ^ 2 *
          ((Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000) := by
            ring
    _ ≤ h ^ 2 * Normalized.emptyResidual s r emptyRate := hscaled

private theorem empty_parent_residual_eq
    {a p h : ℝ} (ha : 0 < a) :
    localResidual a p h 0 0 =
      h * (p / a) / 2 - 7 * (p / a) ^ 2 / 8 := by
  unfold localResidual discrepancyLeft discrepancyRight
    regularizedMassLeft regularizedMassRight regularizedMass
    discrepancy massLeft massRight rateLeft rateRight bias orderedBias
    parentMass inventory bellman
  simp only [Nat.cast_zero, zero_add, add_zero, le_refl, ite_eq_left,
    ]
  field_simp [ha.ne']
  ring

private theorem empty_parent_energy_eq (a p h : ℝ) :
    localEnergy a p h 0 0 = 0 := by
  unfold localEnergy rateLeft rateRight bias orderedBias parentMass inventory
  norm_num

private theorem empty_parent_case
    {a p h : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (ht : discrepancy a p h 0 0 ≤ h / 2) :
    localResidual a p h 0 0 ≥ localEnergy a p h 0 0 / 1000 := by
  have ht' : p / a ≤ h / 2 := by
    simpa [discrepancy, parentMass, inventory] using ht
  have ht0 : 0 ≤ p / a := by positivity
  have hproduct :
      0 ≤ (p / a) * (h / 2 - p / a) := by positivity
  rw [empty_parent_residual_eq ha, empty_parent_energy_eq]
  norm_num
  nlinarith [sq_nonneg (p / a)]

private theorem ordered_case
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  by_cases hy : y = 0
  · subst y
    by_cases hx : x = 0
    · subst x
      exact empty_parent_case ha hp ht
    · exact ordered_one_empty_case ha hp hh (Nat.pos_of_ne_zero hx) ht
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    exact ordered_positive_case ha hp hh hxy hxpos hypos ht

/--
The concrete local Bellman inequality from Lemma `lem:local` of the v5
manuscript, including positive, one-empty, and empty-parent nodes.
-/
theorem local_bellman_inequality
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  by_cases hxy : y ≤ x
  · exact ordered_case ha hp hh hxy ht
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    have htSwap : discrepancy a p h y x ≤ h / 2 := by
      rwa [discrepancy_swap]
    have hs := ordered_case ha hp hh hyx htSwap
    rwa [localResidual_swap, localEnergy_swap] at hs

end

end FD1D.V5.LocalBellman
