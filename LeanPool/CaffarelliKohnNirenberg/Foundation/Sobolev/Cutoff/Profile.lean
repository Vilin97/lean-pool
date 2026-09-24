/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A quantitative smooth transition profile

This file records the one-dimensional profile used by the ball and space-time
cutoff constructions.

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The namespace and imports are independent.

## Main definitions

* `CKN.smoothTransitionProfile`: the canonical smooth transition from `0` to
  `1`.
* `CKN.smoothTransitionProfile.derivBound`: its explicit first-derivative
  bound.

## Main results

* `smoothTransitionProfile.abs_deriv_le_eight`: the first derivative is
  bounded by `8`.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace CKN

/-- The canonical smooth transition from `0` to `1`. -/
def smoothTransitionProfile : ℝ → ℝ :=
  Real.smoothTransition

namespace smoothTransitionProfile

/-- The canonical transition profile is smooth to every order. -/
theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff

/-- The canonical transition profile vanishes to the left of `0`. -/
theorem zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    smoothTransitionProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

/-- The canonical transition profile equals `1` to the right of `1`. -/
theorem one_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothTransitionProfile t = 1 :=
  Real.smoothTransition.one_of_one_le ht

/-- The canonical transition profile is nonnegative. -/
theorem nonneg (t : ℝ) :
    0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t

/-- The canonical transition profile is at most `1`. -/
theorem le_one (t : ℝ) :
    smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t

/-- The explicit first-derivative constant for the canonical transition. -/
def derivBound : ℝ :=
  8

@[simp]
theorem derivBound_eq_eight :
    derivBound = 8 :=
  rfl

private theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue
      (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h :=
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (1 : ℝ[X]) x
  simp only [Polynomial.derivative_one, sub_zero, mul_one,
    Polynomial.eval_one, one_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  exact h

private theorem mul_exp_neg_le (s : ℝ) :
    s * Real.exp (-s) ≤ Real.exp (-1) := by
  have hle : s ≤ Real.exp (s - 1) := by
    have h := Real.add_one_le_exp (s - 1)
    linarith only [h]
  calc
    s * Real.exp (-s) ≤
        Real.exp (s - 1) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf

private theorem expNegInvGlue_deriv_le (x : ℝ) :
    x⁻¹ ^ 2 * expNegInvGlue x ≤
      4 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
    positivity
  · have hgx :
        expNegInvGlue x = Real.exp (-x⁻¹) := by
      simp only [expNegInvGlue, ite_eq_right (not_le.mpr hx)]
    rw [hgx]
    let t := x⁻¹
    have ht0 : 0 < t := inv_pos.mpr hx
    let a := (t / 2) * Real.exp (-(t / 2))
    have ha0 : 0 ≤ a := by
      positivity
    have hale : a ≤ Real.exp (-1) :=
      mul_exp_neg_le (t / 2)
    have hsq :
        a * a ≤ Real.exp (-1) * Real.exp (-1) :=
      mul_self_le_mul_self ha0 hale
    have e2 :
        Real.exp (-(t / 2)) * Real.exp (-(t / 2)) =
          Real.exp (-t) := by
      rw [← Real.exp_add]
      ring_nf
    have haa :
        a * a = (t ^ 2 * Real.exp (-t)) / 4 := by
      rw [show a = (t / 2) * Real.exp (-(t / 2)) from rfl,
        mul_mul_mul_comm, e2]
      ring
    have hee :
        Real.exp (-1) * Real.exp (-1) =
          Real.exp (-2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hee, haa] at hsq
    linarith only [hsq]

private theorem expNegInvGlue_ge_of_half_le {y : ℝ}
    (hy : 1 / 2 ≤ y) :
    Real.exp (-2) ≤ expNegInvGlue y := by
  have hy0 : (0 : ℝ) < y := by
    linarith only [hy]
  have hgy :
      expNegInvGlue y = Real.exp (-y⁻¹) := by
    simp only [expNegInvGlue, ite_eq_right (not_le.mpr hy0)]
  rw [hgy]
  apply Real.exp_le_exp.mpr
  have hmul : y⁻¹ * y = 1 :=
    inv_mul_cancel₀ hy0.ne'
  have hinv : y⁻¹ ≤ 2 := by
    nlinarith only [
      mul_nonneg (inv_pos.mpr hy0).le
        (show (0 : ℝ) ≤ y - 1 / 2 by linarith only [hy]),
      hmul]
  linarith only [hinv]

private theorem smoothTransition_denom_ge (x : ℝ) :
    Real.exp (-2) ≤
      expNegInvGlue x + expNegInvGlue (1 - x) := by
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · have ha := expNegInvGlue_ge_of_half_le hx
    have hb := expNegInvGlue.nonneg (1 - x)
    linarith only [ha, hb]
  · have hx' : (1 / 2 : ℝ) ≤ 1 - x := by
      linarith only [hx]
    have hb := expNegInvGlue_ge_of_half_le hx'
    have ha := expNegInvGlue.nonneg x
    linarith only [hb, ha]

private theorem real_smoothTransition_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition
      ((x⁻¹ ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x) +
          expNegInvGlue x *
            ((1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x))) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have ha := expNegInvGlue_hasDerivAt x
  have hb :=
    (expNegInvGlue_hasDerivAt (1 - x)).comp x
      ((hasDerivAt_id x).const_sub 1)
  have hD := ha.add hb
  have hDne :
      expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hq := ha.div hD hDne
  simp only [Pi.add_apply, Function.comp_apply] at hq
  convert hq using 1
  congr 1
  ring

private theorem real_smoothTransition_abs_deriv_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ 8 := by
  rw [(real_smoothTransition_hasDerivAt x).deriv]
  let a := expNegInvGlue x
  let b := expNegInvGlue (1 - x)
  let P := x⁻¹ ^ 2 * expNegInvGlue x
  let Q := (1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x)
  have ha0 : 0 ≤ a := expNegInvGlue.nonneg x
  have hb0 : 0 ≤ b := expNegInvGlue.nonneg (1 - x)
  have hP0 : 0 ≤ P := by
    dsimp [P]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hPle : P ≤ 4 * Real.exp (-2) :=
    expNegInvGlue_deriv_le x
  have hQle : Q ≤ 4 * Real.exp (-2) :=
    expNegInvGlue_deriv_le (1 - x)
  have hab : Real.exp (-2) ≤ a + b :=
    smoothTransition_denom_ge x
  have hab0 : 0 < a + b :=
    lt_of_lt_of_le (Real.exp_pos _) hab
  have hden : 0 < (a + b) ^ 2 := by
    positivity
  have hval0 :
      0 ≤ (P * b + a * Q) / (a + b) ^ 2 := by
    positivity
  rw [abs_of_nonneg hval0, div_le_iff₀ hden]
  have step1 :
      P * b + a * Q ≤ (P + Q) * (a + b) := by
    nlinarith only [mul_nonneg hP0 ha0, mul_nonneg hQ0 hb0]
  have step2 :
      (P + Q) * (a + b) ≤
        8 * Real.exp (-2) * (a + b) := by
    nlinarith only [hab0, hPle, hQle]
  have step3 :
      8 * Real.exp (-2) * (a + b) ≤
        8 * (a + b) ^ 2 := by
    nlinarith only [hab, hab0]
  linarith only [step1, step2, step3]

/-- The absolute value of the first derivative is bounded by `8`. -/
theorem abs_deriv_le_eight (t : ℝ) :
    |deriv smoothTransitionProfile t| ≤ 8 := by
  simpa only [smoothTransitionProfile] using
    real_smoothTransition_abs_deriv_le t

end smoothTransitionProfile

end CKN
