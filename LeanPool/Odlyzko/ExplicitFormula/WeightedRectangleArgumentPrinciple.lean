/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral
public import LeanPool.Odlyzko.ExplicitFormula.WeightedDiskArgumentPrinciple

/-!
# Weighted Rectangle Argument Principle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace NumberField.Odlyzko

theorem rectangleIntegral_fill_weightedLogDerivFiniteRemainder_eq_zero
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ}
    {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ f z)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z)
    (hzero : ∀ z ∈ Icc a b ×ℂ Icc u v, f z = 0 → z ∈ S)
    (horder : ∀ p ∈ S,
      meromorphicOrderAt f p = (order p : WithTop ℤ)) :
    rectangleIntegral
      (fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S)
      (a + u * I) (b + v * I) = 0 := by
  let F :=
    fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S
  have hF : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ F z := by
    intro z hz
    exact analyticAt_fill_weightedLogDerivFiniteRemainder
      (hf z hz) (hh z hz) (hzero z hz) horder
  have hcg :=
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      F (a + u * I) (b + v * I) ∅ countable_empty
      (by
        intro z hz
        exact (hF z (by
          simp_all))
          |>.continuousAt.continuousWithinAt)
      (by
        intro z hz
        apply (hF z ?_).differentiableAt
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
          sub_self, add_zero, add_im, ofReal_im, mul_im, I_im,
          mul_one, zero_add, min_eq_left hab, max_eq_right hab,
          min_eq_left huv, max_eq_right huv, Set.mem_sdiff,
          mem_reProdIm, mem_Ioo] at hz
        exact ⟨⟨hz.1.1.1.le, hz.1.1.2.le⟩,
          ⟨hz.1.2.1.le, hz.1.2.2.le⟩⟩)
  simpa [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral] using hcg

theorem rectangleIntegral_weightedLogDerivFiniteRemainder_eq_zero
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ}
    {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v)
    (hS : ∀ p ∈ S,
      a < p.re ∧ p.re < b ∧ u < p.im ∧ p.im < v)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ f z)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z)
    (hzero : ∀ z ∈ Icc a b ×ℂ Icc u v, f z = 0 → z ∈ S)
    (horder : ∀ p ∈ S,
      meromorphicOrderAt f p = (order p : WithTop ℤ)) :
    rectangleIntegral (weightedLogDerivFiniteRemainder f h S order)
      (a + u * I) (b + v * I) = 0 := by
  rw [← rectangleIntegral_fill_weightedLogDerivFiniteRemainder_eq_zero
    hab huv hf hh hzero horder]
  unfold rectangleIntegral horizontalIntegral verticalSegmentIntegral
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
    sub_self, add_zero, add_im, ofReal_im, mul_im, I_im,
    mul_one, zero_add]
  have hbot :
      (∫ x in a..b, weightedLogDerivFiniteRemainder f h S order (x + u * I)) =
        ∫ x in a..b,
          fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S
            (x + u * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    symm
    apply fillFinitePunctures_apply_of_notMem
    intro hxS
    have hx := hS (x + u * I) hxS
    simpa using hx.2.2.1.ne'
  have htop :
      (∫ x in a..b, weightedLogDerivFiniteRemainder f h S order (x + v * I)) =
        ∫ x in a..b,
          fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S
            (x + v * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    symm
    apply fillFinitePunctures_apply_of_notMem
    intro hxS
    have hx := hS (x + v * I) hxS
    simpa using hx.2.2.2.ne
  have hright :
      (∫ y in u..v, weightedLogDerivFiniteRemainder f h S order (b + y * I)) =
        ∫ y in u..v,
          fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S
            (b + y * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    symm
    apply fillFinitePunctures_apply_of_notMem
    intro hyS
    have hy := hS (b + y * I) hyS
    simpa using hy.2.1.ne
  have hleft :
      (∫ y in u..v, weightedLogDerivFiniteRemainder f h S order (a + y * I)) =
        ∫ y in u..v,
          fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S
            (a + y * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    symm
    apply fillFinitePunctures_apply_of_notMem
    intro hyS
    have hy := hS (a + y * I) hyS
    simpa using hy.1.ne'
  simp_all

theorem rectangleIntegral_mul_logDeriv_eq_two_pi_I_mul_sum
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ}
    {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v)
    (hS : ∀ p ∈ S,
      a < p.re ∧ p.re < b ∧ u < p.im ∧ p.im < v)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ f z)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z)
    (hzero : ∀ z ∈ Icc a b ×ℂ Icc u v, f z = 0 → z ∈ S)
    (horder : ∀ p ∈ S,
      meromorphicOrderAt f p = (order p : WithTop ℤ)) :
    rectangleIntegral (fun z ↦ h z * logDeriv f z)
        (a + u * I) (b + v * I) =
      (2 * Real.pi * I) * ∑ p ∈ S, h p * (order p : ℂ) := by
  let integrand : ℂ → ℂ := fun z ↦ h z * logDeriv f z
  let principal : ℂ → ℂ :=
    fun z ↦ ∑ p ∈ S, (h p * (order p : ℂ)) / (z - p)
  have hboundary_ne :
      ∀ z ∈ Icc a b ×ℂ Icc u v,
        (z.re = a ∨ z.re = b ∨ z.im = u ∨ z.im = v) →
        f z ≠ 0 := by grind
  have hintegrand_border :
      RectangleBorderIntegrable integrand (a + u * I) (b + v * I) := by
    simp only [RectangleBorderIntegrable, add_re, ofReal_re, mul_re,
      I_re, mul_zero, sub_self, add_zero, add_im, ofReal_im,
      mul_im, I_im, mul_one, zero_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have hz : x + u * I ∈ Icc a b ×ℂ Icc u v := by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all
      have hc := ((hh _ hz).mul ((hf _ hz).deriv.div (hf _ hz)
        (hboundary_ne _ hz (Or.inr (Or.inr (Or.inl (by simp)))))))
        |>.continuousAt
      have hpath : Continuous (fun x : ℝ ↦ (x : ℂ) + u * I) :=
        Complex.continuous_ofReal.add (continuous_const.mul continuous_const)
      simpa [Function.comp_def, integrand, logDeriv_apply] using
        hc.comp_continuousWithinAt
          (f := fun x : ℝ ↦ (x : ℂ) + u * I)
          hpath.continuousAt.continuousWithinAt
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have hz : x + v * I ∈ Icc a b ×ℂ Icc u v := by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all
      have hc := ((hh _ hz).mul ((hf _ hz).deriv.div (hf _ hz)
        (hboundary_ne _ hz (Or.inr (Or.inr (Or.inr (by simp)))))))
        |>.continuousAt
      have hpath : Continuous (fun x : ℝ ↦ (x : ℂ) + v * I) :=
        Complex.continuous_ofReal.add (continuous_const.mul continuous_const)
      simpa [Function.comp_def, integrand, logDeriv_apply] using
        hc.comp_continuousWithinAt
          (f := fun x : ℝ ↦ (x : ℂ) + v * I)
          hpath.continuousAt.continuousWithinAt
    · apply ContinuousOn.intervalIntegrable
      intro y hy
      have hz : b + y * I ∈ Icc a b ×ℂ Icc u v := by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all
      have hc := ((hh _ hz).mul ((hf _ hz).deriv.div (hf _ hz)
        (hboundary_ne _ hz (Or.inr (Or.inl (by simp))))))
        |>.continuousAt
      have hpath : Continuous (fun y : ℝ ↦ (b : ℂ) + y * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      simpa [Function.comp_def, integrand, logDeriv_apply] using
        hc.comp_continuousWithinAt
          (f := fun y : ℝ ↦ (b : ℂ) + y * I)
          hpath.continuousAt.continuousWithinAt
    · apply ContinuousOn.intervalIntegrable
      intro y hy
      have hz : a + y * I ∈ Icc a b ×ℂ Icc u v := by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all
      have hc := ((hh _ hz).mul ((hf _ hz).deriv.div (hf _ hz)
        (hboundary_ne _ hz (Or.inl (by simp)))))
        |>.continuousAt
      have hpath : Continuous (fun y : ℝ ↦ (a : ℂ) + y * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      simpa [Function.comp_def, integrand, logDeriv_apply] using
        hc.comp_continuousWithinAt
          (f := fun y : ℝ ↦ (a : ℂ) + y * I)
          hpath.continuousAt.continuousWithinAt
  have hprincipal_term :
      ∀ p ∈ S, RectangleBorderIntegrable
        (fun z ↦ (h p * (order p : ℂ)) / (z - p))
        (a + u * I) (b + v * I) := by
    intro p hp
    have hi := hS p hp
    simp only [RectangleBorderIntegrable, add_re, ofReal_re, mul_re,
      I_re, mul_zero, sub_self, add_zero, add_im, ofReal_im,
      mul_im, I_im, mul_one, zero_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      apply ContinuousOn.intervalIntegrable
      intro t _
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
    · intro heq
      have := congrArg im heq
      simp at this
      linarith
    · intro heq
      have := congrArg im heq
      simp at this
      linarith
    · intro heq
      have := congrArg re heq
      simp at this
      linarith
    · intro heq
      have := congrArg re heq
      simp at this
      linarith
  have hprincipal_border :
      RectangleBorderIntegrable principal (a + u * I) (b + v * I) := by
    exact rectangleBorderIntegrable_fun_sum hprincipal_term
  have hrem :=
    rectangleIntegral_weightedLogDerivFiniteRemainder_eq_zero
      hab huv hS hf hh hzero horder
  have hsub := hintegrand_border.sub hprincipal_border
  change rectangleIntegral
      (fun z ↦ integrand z - principal z)
      (a + u * I) (b + v * I) =
        rectangleIntegral integrand (a + u * I) (b + v * I) -
          rectangleIntegral principal (a + u * I) (b + v * I) at hsub
  rw [show weightedLogDerivFiniteRemainder f h S order =
      fun z ↦ integrand z - principal z by rfl, hsub] at hrem
  have hprincipal :
      rectangleIntegral principal (a + u * I) (b + v * I) =
        ∑ p ∈ S, (2 * Real.pi * I) * (h p * (order p : ℂ)) := by
    rw [show principal =
        fun z ↦ ∑ p ∈ S, (h p * (order p : ℂ)) / (z - p) by grind,
      rectangleIntegral_fun_sum hprincipal_term]
    apply Finset.sum_congr rfl
    intro p hp
    simpa only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      sub_self, add_zero, add_im, ofReal_im, mul_im, I_im,
      mul_one, zero_add] using
      rectangleIntegral_principal
        (z := a + u * I) (w := b + v * I) (p := p)
        (c := h p * (order p : ℂ))
        (by simpa using (hS p hp).1)
        (by simpa using (hS p hp).2.1)
        (by simpa using (hS p hp).2.2.1)
        (by simpa using (hS p hp).2.2.2)
  rw [hprincipal] at hrem
  change rectangleIntegral integrand (a + u * I) (b + v * I) =
    (2 * Real.pi * I) * ∑ p ∈ S, h p * (order p : ℂ)
  calc
    rectangleIntegral integrand (a + u * I) (b + v * I) =
        ∑ p ∈ S, (2 * Real.pi * I) * (h p * (order p : ℂ)) :=
      sub_eq_zero.mp hrem
    _ = _ := by rw [Finset.mul_sum]

end NumberField.Odlyzko
