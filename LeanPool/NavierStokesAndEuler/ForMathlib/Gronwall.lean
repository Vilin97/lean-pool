/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Scalar Gronwall estimates with interior derivatives

These estimates require continuity on a closed interval and derivatives only in its interior.
The time origin and initial value are arbitrary. The unperturbed estimates allow any real
growth coefficient; the perturbed estimates bound a nonnegative constant forcing error.
No positivity assumption on the function itself is needed except to deduce that it vanishes.

The separation of the scalar argument follows Code4me2's `NavierStokes/GronwallInterior.lean`
[refactor](https://github.com/Code4me2/NavierStokesAndEuler/tree/26e896edbd).
The estimates here retain arbitrary initial times and values.
-/

public section

open Set

namespace Gronwall

/-- The integrating factor turns `f' ≤ K * f` into a nonincreasing function.
There is no sign restriction on `K` or `f`. -/
theorem antitoneOn_exp_neg_mul_of_deriv_le {a b K : ℝ} {f f' : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t) :
    AntitoneOn (fun t => Real.exp (-K * t) * f t) (Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont)
      (f' := fun t => Real.exp (-K * t) * (f' t - K * f t))
  · intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hd := (((hasDerivAt_id t).const_mul (-K)).exp.mul (hderiv t ht'))
    convert! hd.hasDerivWithinAt using 1
    dsimp
    ring
  · intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hbound t (by simpa only [interior_Icc] using ht)))

/-- A scalar differential inequality with only interior derivatives gives the usual
exponential bound from the initial value, even when `K` or `f a` is negative. -/
theorem le_exp_mul_of_deriv_le {a b K : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t) :
    ∀ t ∈ Icc a b, f t ≤ f a * Real.exp (K * (t - a)) := by
  intro t ht
  have hle := antitoneOn_exp_neg_mul_of_deriv_le hcont hderiv hbound
    ⟨le_rfl, hab⟩ ht ht.1
  have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (K * t)).le
  have hcancel : Real.exp (K * t) * Real.exp (-K * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hshift : Real.exp (K * t) * Real.exp (-K * a) =
      Real.exp (K * (t - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [← mul_assoc, hcancel, one_mul, hshift] at hmul
  simpa only [mul_comm (Real.exp (K * (t - a))) (f a)] using hmul

/-- A nonnegative function that initially vanishes and satisfies `f' ≤ K * f`
in the interior vanishes on the entire closed interval. -/
theorem eq_zero_of_deriv_le {a b K : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b)) (hinitial : f a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t) :
    ∀ t ∈ Icc a b, f t = 0 := by
  intro t ht
  apply le_antisymm _ (hnonneg t ht)
  simpa only [hinitial, zero_mul] using le_exp_mul_of_deriv_le hab hcont hderiv hbound t ht

/-- With nonnegative growth and forcing bounds, the weighted value increases by at most
`ε * (t - a)`. The initial value and the function may have either sign. -/
theorem exp_neg_mul_le_add_of_deriv_le_add {a b K ε : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t + ε) :
    ∀ t ∈ Icc a b, Real.exp (-K * (t - a)) * f t ≤ f a + ε * (t - a) := by
  let g : ℝ → ℝ := fun t => Real.exp (-K * (t - a)) * f t - ε * (t - a)
  let g' : ℝ → ℝ := fun t => Real.exp (-K * (t - a)) * (f' t - K * f t) - ε
  have hgcont : ContinuousOn g (Icc a b) :=
    ((Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).continuousOn.mul hcont).sub
        (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
  have hgderiv (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt g (g' t) t := by
    have hd := (hasDerivAt_id t).sub_const a
    convert! (((hd.const_mul (-K)).exp.mul (hderiv t ht)).sub
      (hd.const_mul ε)) using 1
    dsimp [g, g']
    ring
  have hg : AntitoneOn g (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have hexp : Real.exp (-K * (t - a)) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) (sub_nonneg.mpr ht'.1.le))
      have hfirst := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr (hbound t ht'))
        (Real.exp_pos (-K * (t - a))).le
      have hsecond := mul_le_mul_of_nonneg_right hexp hε
      dsimp only [g']
      linarith
  intro t ht
  have hle := hg ⟨le_rfl, hab⟩ ht ht.1
  simpa only [g, sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero,
    sub_le_iff_le_add] using hle

/-- An interior differential inequality `f' ≤ K * f + ε` yields an exponential
bound with arbitrary initial time and initial value. -/
theorem le_exp_mul_add_of_deriv_le_add {a b K ε : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t + ε) :
    ∀ t ∈ Icc a b, f t ≤ (f a + ε * (t - a)) * Real.exp (K * (t - a)) := by
  intro t ht
  have hweighted := exp_neg_mul_le_add_of_deriv_le_add hab hK hε hcont hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos (K * (t - a))).le
  have hcancel : Real.exp (-K * (t - a)) * Real.exp (K * (t - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [mul_right_comm _ (f t), hcancel, one_mul] using hmul

/-- A nonpositive initial value gives a bound valid uniformly on the closed interval.
Only `K` and `ε` must be nonnegative; the function need not be. -/
theorem le_uniform_exp_mul_of_deriv_le_add {a b K ε : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hcont : ContinuousOn f (Icc a b))
    (hinitial : f a ≤ 0) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t + ε) :
    ∀ t ∈ Icc a b, f t ≤ ε * (b - a) * Real.exp (K * (b - a)) := by
  intro t ht
  calc
    f t ≤ (f a + ε * (t - a)) * Real.exp (K * (t - a)) :=
      le_exp_mul_add_of_deriv_le_add hab hK hε hcont hderiv hbound t ht
    _ ≤ ε * (t - a) * Real.exp (K * (t - a)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ ε * (b - a) * Real.exp (K * (b - a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hε)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hK))
        (Real.exp_pos _).le (mul_nonneg hε (sub_nonneg.mpr hab))

end Gronwall
