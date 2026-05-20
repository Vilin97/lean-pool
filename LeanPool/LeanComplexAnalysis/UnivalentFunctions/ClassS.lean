/-
Copyright (c) 2026 seb488, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: seb488, Aristotle
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.LinearCombination'

/-!
# Univalent Function Classes: classS and classSigma

We define the class S of normalized univalent functions on the unit disc and the class Σ of
univalent functions on the exterior of the closed unit disk with the expansion
`g(z) = z + b₀ + b₁/z + ...` at infinity. We then prove:

- For any function `f` in `S`, its square root transform `g(z) = sqrt(f(z^2))`
  is also in `S`; `square_root_transform_in_S`. This involves proving the existence of an analytic
  square root of `f(z)/z` and verifying the properties of the transformed function.

- If `f` is in `classS`, then `g(z) = 1/f(1/z)` is in `classSigma`; `inv_f_inv_in_Sigma`.
-/

namespace LeanPool.LeanComplexAnalysis

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Complex
open Metric

noncomputable section

/-! ## Definitions -/

/--
The class S consists of normalized analytic univalent functions on the unit disc.
-/
def classS : Set (ℂ → ℂ) :=
    {f | AnalyticOn ℂ f (ball 0 1) ∧ Set.InjOn f (ball 0 1) ∧ f 0 = 0 ∧ deriv f 0 = 1}

/--
The class Sigma of analytic and injective functions on the complement of the closed
unit disc with the expansion `g(z) = z + b0 + b1/z + ...`
-/
def classSigma : Set (ℂ → ℂ) := {g | AnalyticOn ℂ g {z | 1 < ‖z‖} ∧  Set.InjOn g {z | 1 < ‖z‖} ∧
    ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧ ∀ z, 1 < ‖z‖ → g z = z + h (1 / z)}

/-! ## Theorems -/

/--
If `f` is analytic on the unit disc, then `dslope f 0` (= `f(z)/z` for `z≠0`, `f'(z)` for `z=0`)
is also analytic on the unit disc.
-/
lemma analyticOn_dslope_of_analyticOn (f : ℂ → ℂ) :
    AnalyticOn ℂ f (ball 0 1) → AnalyticOn ℂ (dslope f 0) (ball 0 1) := by
  revert f
  intros f hf
  have h.diff : DifferentiableOn ℂ f (ball 0 1) := by
    exact hf.differentiableOn
  apply_rules [DifferentiableOn.analyticOn, h.diff]
  · have h.diff_dslope : DifferentiableOn ℂ (fun z =>
      if z = 0 then deriv f 0 else (f z - f 0) / z) (ball 0 1) := by
      have h.diff_zero : HasDerivAt (fun z =>
        if z = 0 then deriv f 0 else (f z - f 0) / z) (deriv (deriv f) 0 / 2) 0 := by
        have h_diff_zero : Filter.Tendsto (fun z =>
          (f z - f 0 - deriv f 0 * z) / z^2) (nhdsWithin 0 {0}ᶜ) (
            nhds (deriv (deriv f) 0 / 2)) := by
          have h_diff_zero : HasDerivAt (fun z => deriv f z) (deriv (deriv f) 0) 0 := by
            have h_diff_zero : AnalyticOn ℂ (deriv f) (ball 0 1) := by
              apply_rules [DifferentiableOn.analyticOn, h.diff.deriv]
              · exact isOpen_ball
              · exact isOpen_ball
            exact h_diff_zero.differentiableOn.differentiableAt (
              ball_mem_nhds _ zero_lt_one) |> DifferentiableAt.hasDerivAt
          have h_diff_zero : Filter.Tendsto (fun z =>
            (∫ t in (0 : ℝ)..1, (deriv f (t * z) - deriv f 0)) / z) (
              nhdsWithin 0 {0}ᶜ) (nhds (deriv (deriv f) 0 / 2)) := by
            have h_diff_zero : Filter.Tendsto (fun z =>
              (∫ t in (0 : ℝ)..1, (deriv f (t * z) - deriv f 0) / z)) (
                nhdsWithin 0 {0}ᶜ) (nhds (deriv (deriv f) 0 / 2)) := by
              have h_diff_zero : Filter.Tendsto (fun z =>
                ∫ t in (0 : ℝ)..1, (deriv f (t * z) - deriv f 0) / z) (
                  nhdsWithin 0 {0}ᶜ) (nhds (∫ t in (0 : ℝ)..1, deriv (deriv f) 0 * t)) := by
                refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
                  ?_ ?_ ?_ ?_ ?_
                focus use fun x => ‖deriv (deriv f) 0‖ * x + 1
                · filter_upwards [self_mem_nhdsWithin] with n hn
                  refine Measurable.aestronglyMeasurable ?_
                  fun_prop
                · rw [eventually_nhdsWithin_iff]
                  rw [Metric.eventually_nhds_iff]
                  have := h_diff_zero.tendsto_slope_zero
                  have := Metric.tendsto_nhdsWithin_nhds.mp this
                  obtain ⟨δ, hδ, H⟩ := this 1 zero_lt_one; use δ, hδ; intro y hy hy'
                  filter_upwards [] with x hx; by_cases hx' : x = 0 <;>
                    simp_all only [div_eq_inv_mul,
                      Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_zero, zero_mul, sub_self,
                      norm_zero, Set.uIoc_of_le (zero_le_one' ℝ), Set.mem_Ioc,
                      dist_eq_norm, sub_zero, norm_mul, smul_eq_mul, zero_add,
                      mul_zero]
                  have := H (show (x : ℂ) * y ≠ 0 from mul_ne_zero (
                    ofReal_ne_zero.mpr hx') hy') (
                      by simpa [abs_of_nonneg hx.1.le] using by nlinarith [norm_nonneg y])
                  simp_all only [mul_assoc, mul_comm, mul_inv_rev, norm_inv]
                  have := norm_sub_le (y⁻¹ * ((x : ℂ) ⁻¹ * (deriv f (y * x) - deriv f 0)) -
                    deriv (deriv f) 0) (-deriv (deriv f) 0); simp_all  [mul_left_comm]
                  rw [abs_of_nonneg hx.1.le] at this
                  nlinarith [inv_mul_cancel_left₀ hx' (‖y‖⁻¹ * ‖deriv f (y * x) -
                    deriv f 0‖), inv_mul_cancel₀ hx', inv_mul_cancel₀ (show ‖y‖ ≠ 0 by aesop)]
                · exact Continuous.intervalIntegrable (by continuity) _ _
                · refine Filter.Eventually.of_forall fun x hx => ?_
                  have h_diff_zero : HasDerivAt (fun z =>
                    deriv f (x * z)) (deriv (deriv f) 0 * x) 0 := by
                    convert HasDerivAt.comp 0 (show HasDerivAt (fun z => deriv f z) (
                      deriv (deriv f) 0) (x * 0) by simpa using h_diff_zero) (
                        HasDerivAt.const_mul (x : ℂ) (hasDerivAt_id 0)) using 1; norm_num
                  simpa [div_eq_inv_mul] using h_diff_zero.tendsto_slope_zero
              have h_aux : (deriv (deriv f) 0 / 2 : ℂ) =
                  ∫ (t : ℝ) in 0..1, deriv (deriv f) 0 * (↑t : ℂ) := by
                rw [show ∫ (t : ℝ) in 0..1, deriv (deriv f) 0 * (↑t : ℂ) =
                      deriv (deriv f) 0 * ∫ (t : ℝ) in 0..1, (↑t : ℂ) from
                    intervalIntegral.integral_const_mul _ _]
                rw [show ∫ (t : ℝ) in 0..1, (↑t : ℂ) = (1 / 2 : ℂ) from ?_]
                · ring
                · trans ((∫ (t : ℝ) in 0..1, t : ℝ) : ℂ)
                  · exact intervalIntegral.integral_ofReal
                  · simp [integral_id]
              rw [h_aux]
              exact h_diff_zero
            refine h_diff_zero.congr fun z => ?_
            exact intervalIntegral.integral_div z (fun t => deriv f (↑t * z) - deriv f 0)
          have h_diff_zero : ∀ z ∈ ball 0 1, z ≠ 0 →
            (∫ t in (0 : ℝ)..1, deriv f (t * z) - deriv f 0) = (f z - f 0 - deriv f 0 * z) / z := by
            intros z hz hz_ne_zero
            have h_ftc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∫ t in a..b, deriv f (t * z) * z =
              f (b * z) - f (a * z) := by
              intros a b _ _ _; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
              · intro x hx; convert HasDerivAt.comp x (h.diff.hasDerivAt <| ?_) (
                  HasDerivAt.mul (hasDerivAt_id _ |> HasDerivAt.ofReal_comp) <|
                    hasDerivAt_const _ _) using 1 <;> ring_nf
                · simp  [mul_comm]
                · exact IsOpen.mem_nhds (isOpen_ball) (by simpa [abs_of_nonneg (
                    show 0 ≤ x by cases Set.mem_uIcc.mp hx <;> linarith)] using lt_of_le_of_lt (
                      mul_le_of_le_one_left (norm_nonneg _) (show |x| ≤ 1 by
                        cases Set.mem_uIcc.mp hx <;> exact abs_le.mpr ⟨by linarith, by linarith⟩)) (
                          by simpa using hz))
              · apply_rules [ContinuousOn.intervalIntegrable]
                have h_cont : ContinuousOn (deriv f) (ball 0 1) := by
                  have h_cont : AnalyticOn ℂ (deriv f) (ball 0 1) := by
                    apply_rules [DifferentiableOn.analyticOn, hf.differentiableOn]
                    · apply_rules [DifferentiableOn.deriv, hf.differentiableOn]
                      exact isOpen_ball
                    · exact isOpen_ball
                  exact h_cont.continuousOn
                exact ContinuousOn.mul (h_cont.comp (Continuous.continuousOn
                  (by continuity)) fun x hx =>
                    by exact mem_ball_zero_iff.mpr <|
                      by simpa [abs_of_nonneg (show 0 ≤ x by cases Set.mem_uIcc.mp hx <;> linarith)]
                      using lt_of_le_of_lt (
                      mul_le_of_le_one_left (norm_nonneg _) <| show (|x| : ℝ) ≤ 1 by
                      cases Set.mem_uIcc.mp hx <;> exact abs_le.mpr ⟨by linarith, by linarith⟩) <|
                        by simpa using hz) continuousOn_const
            have := h_ftc 0 1; simp only [mem_ball, dist_zero_right, ne_eq, ofReal_zero,
              zero_mul, ofReal_one, one_mul, zero_le_one, le_refl, forall_const] at *
            rw [intervalIntegral.integral_sub] <;> norm_num [h_ftc]
            · field_simp
              have := h_ftc 0 1; norm_num at this
              rw [show ∫ (t : ℝ) in 0..1, deriv f ((↑t : ℂ) * z) * z =
                    (∫ (t : ℝ) in 0..1, deriv f ((↑t : ℂ) * z)) * z from
                  intervalIntegral.integral_mul_const _ _] at this
              linear_combination' this
            · apply_rules [ContinuousOn.intervalIntegrable]
              have h_cont : ContinuousOn (deriv f) (ball 0 1) := by
                have h_cont : AnalyticOn ℂ (deriv f) (ball 0 1) := by
                  apply_rules [DifferentiableOn.analyticOn, h.diff]
                  · apply_rules [DifferentiableOn.deriv, h.diff]
                    exact isOpen_ball
                  · exact isOpen_ball
                exact h_cont.continuousOn
              apply h_cont.comp (Continuous.continuousOn (by continuity))
              intro x hx
              apply mem_ball_zero_iff.mpr
              have hx_nonneg : 0 ≤ x := by
                norm_num at hx
                linarith
              simp [abs_of_nonneg hx_nonneg]
              nlinarith [abs_le.mp (abs_re_le_norm z),
           abs_le.mp (abs_im_le_norm z),
           Set.mem_Icc.mp (by simpa using hx)]
          refine Filter.Tendsto.congr' (f₁ := fun z ↦
            (∫ (t : ℝ) in 0..1, deriv f (↑t * z) - deriv f 0) / z) ?_ ?_
          focus filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
            ball_mem_nhds _ zero_lt_one)] with z hz₁ hz₂ using by rw [h_diff_zero z hz₂ hz₁]; ring
          assumption
        rw [hasDerivAt_iff_tendsto_slope_zero]
        refine h_diff_zero.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        by_cases h : z = 0 <;> simp_all  [div_eq_mul_inv, sq, mul_assoc, mul_comm]
        grind
      intro z hz
      by_cases h : z = 0 <;> simp_all only [DifferentiableWithinAt, mem_ball, dist_zero_right]
      · exact ⟨_, h.diff_zero.hasFDerivAt.hasFDerivWithinAt⟩
      · exact ⟨_, DifferentiableAt.hasFDerivAt (
          by exact DifferentiableAt.congr_of_eventuallyEq (
            DifferentiableAt.div (h.diff.differentiableAt (
              isOpen_ball.mem_nhds <| by simpa) |> DifferentiableAt.sub <|
                differentiableAt_const _) differentiableAt_id h) <|
                  Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds h) fun x hx =>
                    if_neg hx) |> HasFDerivAt.hasFDerivWithinAt⟩
    convert h.diff_dslope using 1
    ext; simp  [dslope] ; ring_nf
    simp  [Function.update, slope_def_field]; ring_nf
  · exact isOpen_ball

/--
For any function `f` in `classS`, the difference slope of `f` at `0` is
non-zero everywhere on the unit disc.
-/
lemma dslope_ne_zero_of_in_S (f : ℂ → ℂ) (hf : f ∈ classS) :
    ∀ z ∈ ball 0 1, dslope f 0 z ≠ 0 := by
  intro z hz
  by_cases h : z = 0
  · rw [h, dslope_same]
    exact hf.2.2.2 ▸ one_ne_zero
  · rw [dslope_of_ne _ h]
    rw [slope_def_field]
    simp only [hf.2.2.1, sub_zero]
    apply div_ne_zero
    · have h_inj := hf.2.1
      have h0 : 0 ∈ ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
      have h_neq : f z ≠ f 0 := by
        apply fun a => mt a h
        intro h_eq
        exact h_inj hz h0 h_eq
      rwa [hf.2.2.1] at h_neq
    · exact h

/--
The primitive of a function `f` on the unit ball,
defined as the integral along the segment from 0 to `z`.
-/
def primitiveOnBall (f : ℂ → ℂ) (z : ℂ) : ℂ := z * ∫ t in (0 : ℝ)..1, f ((t : ℂ) * z)

/--
The derivative of the integral of `f(t*w)` with respect to `w` at `z` is the integral of
`f'(t*z)*t`.
-/
lemma hasDerivAt_integral_of_analytic_mul (f : ℂ → ℂ) (hf : AnalyticOn ℂ f (ball 0 1))
    (z : ℂ) (hz : z ∈ ball 0 1) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, f (t * w)) (∫ t in (0 : ℝ)..1,
    deriv f (t * z) * t) z := by
  have h_f_deriv : AnalyticOn ℂ (deriv f) (ball 0 1) := by
              apply_rules [DifferentiableOn.analyticOn, hf.differentiableOn]
              · apply_rules [DifferentiableOn.deriv, hf.differentiableOn]
                exact isOpen_ball
              · exact isOpen_ball
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h_dominated_convergence : Filter.Tendsto (fun t : ℂ => ∫ u in (0 : ℝ)..1, (
    f ((u : ℂ) * (z + t)) - f ((u : ℂ) * z)) / t) (nhdsWithin 0 {0}ᶜ) (
      nhds (∫ u in (0 : ℝ)..1, deriv f ((u : ℂ) * z) * (u : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
    focus use fun x => 2 * (SupSet.sSup (Set.image (fun w => ‖deriv f w‖) (
      Metric.closedBall 0 (‖z‖ + (1 - ‖z‖) / 2)))) * |x|
    · norm_num at *
      rw [eventually_nhdsWithin_iff]
      rw [Metric.eventually_nhds_iff]
      refine ⟨1 - ‖z‖, by linarith, fun y hy hy' =>
        ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc⟩
      apply ContinuousOn.div_const
      refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.comp hf.continuousOn ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · intro u hu
          simp_all only [mem_ball, dist_zero_right, Complex.norm_mul, norm_real,
            Real.norm_eq_abs, Set.mem_Ioc]
          exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨
            by linarith, by linarith⟩)) (by linarith [norm_add_le z y])
      · exact ContinuousOn.comp hf.continuousOn (
          Continuous.continuousOn (by continuity)) fun u hu =>
            by exact mem_ball_zero_iff.mpr (
              by simpa [abs_of_nonneg hu.1.le] using by nlinarith [hu.1, hu.2, norm_nonneg z])
    · rw [eventually_nhdsWithin_iff]
      rw [Metric.eventually_nhds_iff]
      refine ⟨(1 - ‖z‖) / 2, half_pos (sub_pos.mpr <| by simpa using hz), fun y hy hy' =>
        Filter.Eventually.of_forall fun x hx => ?_⟩
      have h_mean_value : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv f (x * z + t * (x * y))‖ ≤
        SupSet.sSup (Set.image (fun w => ‖deriv f w‖) (
          Metric.closedBall 0 (‖z‖ + (1 - ‖z‖) / 2))) := by
        intro t ht
        have h_mean_value : (x * z + t * (x * y)) ∈ Metric.closedBall 0 (‖z‖ + (1 - ‖z‖) / 2) := by
          rw [Set.uIoc_of_le (zero_le_one' ℝ), Set.mem_Ioc] at hx
          simp_all only [Metric.mem_closedBall, dist_zero_right, Set.mem_Icc]
          refine le_trans (norm_add_le _ _) ?_
          norm_num [abs_of_nonneg hx.1.le, abs_of_nonneg ht.1]
          nlinarith [mul_le_mul_of_nonneg_left hx.2 (norm_nonneg z),
            mul_le_mul_of_nonneg_left ht.2 (norm_nonneg y), norm_nonneg z, norm_nonneg y]
        refine le_csSup ?_ ?_
        · have h_cont : ContinuousOn (deriv f) (Metric.closedBall 0 (‖z‖ + (1 - ‖z‖) / 2)) := by
            exact h_f_deriv.continuousOn.mono (Metric.closedBall_subset_ball <|
             by linarith [show ‖z‖ < 1 from by simpa using hz])
          exact IsCompact.bddAbove (isCompact_closedBall _ _ |>
            IsCompact.image_of_continuousOn <| h_cont.norm)
        · aesop
      have h_ftc : f (x * (z + y)) - f (x * z) =
        ∫ t in (0 : ℝ)..1, deriv f (x * z + t * (x * y)) * (x * y) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
        rotate_right
        focus use fun t => f (x * z + t * (x * y))
        · norm_num [mul_add]
        · intro t ht
          convert HasDerivAt.comp t (hf.differentiableOn.differentiableAt (
            isOpen_ball.mem_nhds <| ?_) |> DifferentiableAt.hasDerivAt) (
              HasDerivAt.add (hasDerivAt_const _ _) <|
                HasDerivAt.mul (hasDerivAt_id _ |> HasDerivAt.ofReal_comp) <|
                  hasDerivAt_const _ _) using 1 <;> norm_num
          norm_num at *
          refine lt_of_le_of_lt (norm_add_le _ _) ?_
          norm_num [abs_of_nonneg hx.1.le, abs_of_nonneg ht.1]
          nlinarith [mul_le_mul_of_nonneg_left ht.2 hx.1.le,
            mul_le_mul_of_nonneg_left ht.1 hx.1.le, norm_nonneg z, norm_nonneg y]
        · apply_rules [ContinuousOn.intervalIntegrable]
          refine ContinuousOn.mul ?_ continuousOn_const
          refine ContinuousOn.comp (show ContinuousOn (deriv f) (ball 0 1) from ?_) ?_ ?_
          · exact h_f_deriv.continuousOn
          · exact Continuous.continuousOn (by continuity)
          · intro t ht
            rw [Set.uIoc_of_le (zero_le_one' ℝ), Set.mem_Ioc] at hx
            rw [Set.uIcc_of_le (zero_le_one' ℝ), Set.mem_Icc] at ht
            simp_all only [mem_ball, dist_zero_right, Set.mem_Icc]
            refine lt_of_le_of_lt (norm_add_le _ _) ?_
            norm_num [abs_of_nonneg hx.1.le, abs_of_nonneg ht.1]
            nlinarith [mul_le_mul_of_nonneg_left ht.2 hx.1.le,
              mul_le_mul_of_nonneg_left hx.2 (norm_nonneg z),
                mul_le_mul_of_nonneg_left hx.2 (norm_nonneg y)]
      rw [h_ftc, intervalIntegral.integral_of_le zero_le_one]
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hy')]
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
      refine le_trans (MeasureTheory.integral_mono_of_nonneg (g := fun t =>
        sSup ((fun w => ‖deriv f w‖) '' closedBall 0 (‖z‖ + (1 - ‖z‖) / 2)) *
          |x| * ‖y‖) ?_ ?_ ?_) ?_
      · exact Filter.Eventually.of_forall fun t => norm_nonneg _
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht using by
          simpa [mul_assoc, abs_mul] using
            mul_le_mul_of_nonneg_right (h_mean_value t <|
              Set.Ioc_subset_Icc_self ht) (by positivity)
      · norm_num
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left
            (by apply_rules [Real.sSup_nonneg]; rintro _ ⟨w, hw, rfl⟩; exact norm_nonneg _)
              (by norm_num)) (by positivity)) (by positivity)
    · exact Continuous.intervalIntegrable (by continuity) _ _
    · refine Filter.Eventually.of_forall fun x hx => ?_
      have h_deriv : HasDerivAt (fun w => f (x * w)) (deriv f (x * z) * x) z := by
        convert HasDerivAt.comp z (hf.differentiableOn.differentiableAt (
          IsOpen.mem_nhds isOpen_ball <| ?_) |> DifferentiableAt.hasDerivAt) (
            HasDerivAt.const_mul (x : ℂ) (hasDerivAt_id z)) using 1; focus aesop
        simp_all
        nlinarith [abs_of_pos hx.1]
      simpa [div_eq_inv_mul] using h_deriv.tendsto_slope_zero
  refine h_dominated_convergence.congr' ?_
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul, mem_ball_zero_iff] at hz ⊢
  rw [Metric.eventually_nhds_iff]
  refine ⟨(1 - ‖z‖) / 2, half_pos (sub_pos.mpr hz), ?_⟩
  refine fun y hy hy' => ?_
  rw [show ∫ (u : ℝ) in 0..1, (f ((↑u : ℂ) * (z + y)) - f ((↑u : ℂ) * z)) / y =
        (∫ (u : ℝ) in 0..1, (f ((↑u : ℂ) * (z + y)) - f ((↑u : ℂ) * z))) / y from
      intervalIntegral.integral_div _ _,
      intervalIntegral.integral_sub]
  · ring
  · apply_rules [ContinuousOn.intervalIntegrable]
    refine ContinuousOn.comp hf.continuousOn ?_ ?_
    · exact Continuous.continuousOn (by continuity)
    · norm_num [Set.MapsTo]
      intro x hx₁ hx₂; rw [abs_of_nonneg hx₁] ; exact lt_of_le_of_lt (
        mul_le_of_le_one_left (norm_nonneg _) hx₂) (
          by linarith [norm_add_le z y, show ‖y‖ < (1 - ‖z‖) / 2 by simpa using hy])
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact ContinuousOn.comp (hf.continuousOn) (
      Continuous.continuousOn (by continuity)) fun x hx => by exact mem_ball_zero_iff.mpr (
        by simpa [abs_of_nonneg (show 0 ≤ x by aesop)] using
          by nlinarith [norm_nonneg z, abs_le.mp (abs_re_le_norm z), abs_le.mp (abs_im_le_norm z),
            Set.mem_Icc.mp (by simpa using hx)])

/--
The derivative of the primitive of `f` on the unit ball at `z` is `f(z)`.
-/
lemma hasDerivAt_primitiveOnBall (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (ball 0 1)) (z : ℂ) (hz : z ∈ ball 0 1) :
    HasDerivAt (primitiveOnBall f) (f z) z := by
  have h_deriv : HasDerivAt (fun w => w * ∫ t in (0 : ℝ)..1, f (t * w)) (1 * (
    ∫ t in (0 : ℝ)..1, f (t * z)) + z * (∫ t in (0 : ℝ)..1, deriv f (t * z) * t)) z := by
    convert HasDerivAt.mul (hasDerivAt_id z) (hasDerivAt_integral_of_analytic_mul f hf z hz) using 1
  have h_ftc : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t * f (t * z)) (
    f (t * z) + t * z * deriv f (t * z)) t := by
    intro t ht
    convert HasDerivAt.mul (HasDerivAt.ofReal_comp (hasDerivAt_id t)) (
      HasDerivAt.comp t (hf.differentiableOn.differentiableAt (
        IsOpen.mem_nhds isOpen_ball <| ?_) |> DifferentiableAt.hasDerivAt) <|
          HasDerivAt.mul (hasDerivAt_id t |> HasDerivAt.ofReal_comp) <|
            hasDerivAt_const _ _) using 1 <;> norm_num ; focus ring
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)) (by simpa using hz)
  have h_ftc_integral : ∫ t in (0 : ℝ)..1, (f (t * z) + t * z * deriv f (t * z)) =
    1 * f (1 * z) - 0 * f (0 * z) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    rotate_right
    focus use fun t => t * f (t * z)
    · norm_num
    · aesop
    · apply_rules [ContinuousOn.intervalIntegrable]
      refine ContinuousOn.add ?_ ?_
      · refine hf.continuousOn.comp ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · exact fun t ht =>
            by simpa [abs_of_nonneg (show 0 ≤ t by
              norm_num at ht; linarith)] using lt_of_le_of_lt (mul_le_of_le_one_left (by
                positivity) (show |t| ≤ 1 by norm_num at ht; exact abs_le.mpr ⟨by
                  linarith, by linarith⟩)) (by simpa using hz)
      · refine ContinuousOn.mul ?_ ?_
        · exact Continuous.continuousOn (by continuity)
        · have h_cont_deriv : ContinuousOn (deriv f) (ball 0 1) := by
            have h_cont_deriv : AnalyticOn ℂ (deriv f) (ball 0 1) := by
              apply_rules [DifferentiableOn.analyticOn, hf.differentiableOn]
              · apply_rules [DifferentiableOn.deriv, hf.differentiableOn]
                exact isOpen_ball
              · exact isOpen_ball
            exact h_cont_deriv.continuousOn
          exact h_cont_deriv.comp (Continuous.continuousOn <| by continuity) fun x hx =>
            by exact mem_ball_zero_iff.mpr <|
              by simpa [abs_of_nonneg (show 0 ≤ x by
                norm_num at hx; linarith)] using lt_of_le_of_lt (
                  mul_le_of_le_one_left (norm_nonneg _) <| show (|x| : ℝ) ≤ 1 by
                  norm_num at hx; exact abs_le.mpr ⟨by linarith, by linarith⟩) <| by simpa using hz
  rw [intervalIntegral.integral_add] at h_ftc_integral <;> norm_num at *
  · convert h_deriv using 1
    exact h_ftc_integral.symm.trans (
      by rw [show z * ∫ t in (0 : ℝ)..1, deriv f (↑t * z) * ↑t =
              ∫ t in (0 : ℝ)..1, z * (deriv f (↑t * z) * ↑t) from
              (intervalIntegral.integral_const_mul z _).symm]; congr; ext; ring)
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact hf.continuousOn.comp (Continuous.continuousOn <| by continuity) fun x hx =>
      by exact mem_ball_zero_iff.mpr <|
        by simpa [abs_of_nonneg (show 0 ≤ x by aesop)] using
          by nlinarith [abs_le.mp (abs_re_le_norm z),
            abs_le.mp (abs_im_le_norm z), Set.mem_Icc.mp <|
              by simpa using hx]
  · apply_rules [ContinuousOn.intervalIntegrable]
    refine ContinuousOn.mul (Continuous.continuousOn (by continuity)) ?_
    have h_cont_deriv : ContinuousOn (fun t : ℂ => deriv f t) (ball 0 1) := by
      have h_cont_deriv : AnalyticOn ℂ (deriv f) (ball 0 1) := by
        apply_rules [DifferentiableOn.analyticOn, hf.differentiableOn]
        · apply_rules [DifferentiableOn.deriv, hf.differentiableOn]
          exact isOpen_ball
        · exact isOpen_ball
      exact h_cont_deriv.continuousOn
    exact h_cont_deriv.comp (Continuous.continuousOn (by continuity)) fun x hx =>
      by simpa [abs_of_nonneg (show 0 ≤ x by norm_num at hx; linarith)] using
        by nlinarith [norm_nonneg z, Set.mem_Icc.mp (by simpa using hx)]

/--
The primitive of an analytic function on the unit ball is analytic on the unit ball.
-/
lemma analyticOn_primitiveOnBall (f : ℂ → ℂ) (hf : AnalyticOn ℂ f (ball 0 1)) :
    AnalyticOn ℂ (primitiveOnBall f) (ball 0 1) := by
  apply DifferentiableOn.analyticOn
  · intro z hz
    exact (hasDerivAt_primitiveOnBall f hf z hz).differentiableAt.differentiableWithinAt
  · exact isOpen_ball

/--
If `f` is a non-vanishing analytic function on the unit ball, then there exists an analytic
function `g` on the unit ball such that `exp(g(z)) = f(z)`.
-/
lemma exists_log_of_analytic_nonzero_on_ball (f : ℂ → ℂ)
    (hf_anal : AnalyticOn ℂ f (ball 0 1)) (hf_ne_zero : ∀ z ∈ ball 0 1, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (ball 0 1) ∧ ∀ z ∈ ball 0 1, exp (g z) = f z := by
  set L : ℂ → ℂ := fun z => deriv f z / f z
  have hL_anal : AnalyticOn ℂ L (ball 0 1) := by
    apply_rules [AnalyticOn.div, hf_anal]
    apply_rules [DifferentiableOn.analyticOn, hf_anal.differentiableOn]
    · apply_rules [DifferentiableOn.deriv, hf_anal.differentiableOn]
      exact isOpen_ball
    · exact isOpen_ball
  set g0 : ℂ → ℂ := primitiveOnBall L
  have hg0_anal : AnalyticOn ℂ g0 (ball 0 1) := by
    exact analyticOn_primitiveOnBall L hL_anal
  have hg0_deriv : ∀ z ∈ ball 0 1, deriv g0 z = L z := by
    exact fun z hz => HasDerivAt.deriv (hasDerivAt_primitiveOnBall L hL_anal z hz)
  set H : ℂ → ℂ := fun z => f z * exp (-g0 z)
  have hH_deriv_zero : ∀ z ∈ ball 0 1, deriv H z = 0 := by
    intro z hz
    have hH_deriv_step : deriv H z = deriv f z * exp (-g0 z) + f z * (-deriv g0 z) *
      exp (-g0 z) := by
      convert HasDerivAt.deriv (HasDerivAt.mul (hf_anal.differentiableOn.differentiableAt (
        isOpen_ball.mem_nhds hz) |>
          DifferentiableAt.hasDerivAt) (HasDerivAt.comp z (hasDerivAt_exp _) (
            HasDerivAt.neg (hg0_anal.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz) |>
              DifferentiableAt.hasDerivAt)))) using 1; ring!
    grind
  have hH_const : ∀ z ∈ ball 0 1, H z = H 0 := by
    intro z hz
    have hH_const : ∀ z ∈ ball 0 1, deriv H z = 0 := by
      assumption
    have hH_const : ∀ z ∈ ball 0 1, H z = H 0 := by
      have h_diff : DifferentiableOn ℂ H (ball 0 1) := by
        exact DifferentiableOn.mul (hf_anal.differentiableOn) (
          differentiable_exp.comp_differentiableOn (hg0_anal.differentiableOn.neg))
      intro z hz
      have h_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • z ∈ ball 0 1 := by
        simp_all only [Set.mem_Icc, real_smul, mem_ball, dist_zero_right, Complex.norm_mul,
          norm_real, Real.norm_eq_abs, and_imp]
        exact fun t ht₁ ht₂ => by rw [abs_of_nonneg ht₁]; nlinarith [norm_nonneg z]
      have h_int : ∫ t in (0 : ℝ)..1, deriv H (t • z) * z = H z - H 0 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
        rotate_right
        focus use fun t => H (t • z)
        · norm_num
        · intro t ht; have := h_diff.hasDerivAt (
            IsOpen.mem_nhds isOpen_ball <| h_path t <| by simpa using ht)
          simp only [real_smul, mul_comm (↑t : ℂ) z] at this
          simp only [real_smul]
          convert this.comp t (HasDerivAt.const_mul z (hasDerivAt_id t |>
            HasDerivAt.ofReal_comp)) using 1
          · norm_num [mul_assoc, mul_comm, mul_left_comm, Function.comp_def]
          · push_cast; ring
        · exact (ContinuousOn.intervalIntegrable (by rw [continuousOn_congr fun t ht =>
            by rw [hH_const _ (h_path t <| by simpa using ht)]]; exact continuousOn_const)) ..
      have h_zero : ∫ t in (0 : ℝ)..1, deriv H (t • z) * z = 0 := by
        rw [intervalIntegral.integral_congr fun t ht =>
          by rw [hH_const _ (h_path t <| by simpa using ht)]]; norm_num
      have h_eq : H z = H 0 := by
        linear_combination' h_int.symm.trans h_zero
      exact h_eq
    exact hH_const z hz
  have hf_eq : ∀ z ∈ ball 0 1, f z = H 0 * exp (g0 z) := by
    intro z hz; rw [← hH_const z hz, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, H 0 = exp c := by
    exact ⟨log (H 0), by rw [exp_log (mul_ne_zero (hf_ne_zero 0 (by norm_num)) (exp_ne_zero _))]⟩
  refine ⟨fun z => c + g0 z, ?_, ?_⟩ <;> norm_num [hc] at *
  · exact AnalyticOn.add analyticOn_const hg0_anal
  · exact fun z hz => by rw [hf_eq z hz, exp_add]

/--
For any function `f` in `classS`, there exists an analytic function `h` on the unit disc such that
`h(z)^2 = f(z)/z` for non-zero `z`, and `h(0) = 1`.
-/
lemma exists_sqrt_f_div_z (f : ℂ → ℂ) (hf : f ∈ classS) :
    ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧ h 0 = 1 ∧
    ∀ z ∈ ball 0 1, z ≠ 0 → h z ^ 2 = f z / z := by
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, AnalyticOn ℂ g (ball 0 1) ∧
    ∀ z ∈ ball 0 1, exp (g z) = dslope f 0 z := by
    apply exists_log_of_analytic_nonzero_on_ball
    · exact analyticOn_dslope_of_analyticOn f hf.1
    · exact fun z a ↦ dslope_ne_zero_of_in_S f hf z a
  obtain ⟨n, hn⟩ : ∃ n : ℤ, g 0 = 2 * Real.pi * I * n := by
    have := hg.2 0; norm_num [hf.2.2] at this; rw [exp_eq_one_iff] at this
    obtain ⟨n, hn⟩ := this; exact ⟨n, by linear_combination' hn⟩
  refine ⟨fun z => exp ((g z - 2 * Real.pi * I * n) / 2), ?_, ?_, ?_⟩
  · exact DifferentiableOn.analyticOn (by exact DifferentiableOn.cexp (DifferentiableOn.div_const (
      hg.1.differentiableOn.sub_const _) _)) (isOpen_ball)
  · norm_num [hn]
  · intro z hz hz'; rw [← exp_nat_mul] ; ring_nf
    have h_exp := hg.2 z hz
    simp only [dslope, Function.update_of_ne hz', slope_def_field, hf.2.2.1,
      sub_zero] at h_exp
    rw [exp_sub, h_exp,
      show ((↑π * I * ↑n * 2 : ℂ)) = I * (Real.pi * (n * 2)) from by ring,
      show cexp (I * (Real.pi * (n * 2))) = 1 from by
        rw [exp_eq_one_iff]; use n; ring]
    field_simp

/--
The class S consists of normalized analytic univalent functions on the unit disc.
The square root transform of `f`, defined by `g(z) = sqrt(f(z^2))`, is also in S.
-/
theorem square_root_transform_in_S (f : ℂ → ℂ) (hf : f ∈ classS) :
    ∃ g ∈ classS, ∀ z ∈ ball 0 1, g z ^ 2 = f (z ^ 2) := by
  unfold classS at *
  obtain ⟨h, h_analytic, h_eq⟩ : ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧ h 0 = 1 ∧
    ∀ z ∈ ball 0 1, z ≠ 0 → h z ^ 2 = f z / z := by
    exact exists_sqrt_f_div_z f hf
  use fun z => z * h (z^2)
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply_rules [AnalyticOn.mul, AnalyticOn.pow, analyticOn_id, analyticOn_const]
      exact h_analytic.comp (by apply_rules [AnalyticOn.pow, analyticOn_id]) fun x hx =>
        by simpa using hx.out.trans_le (by norm_num)
    · intro z hz w hw h_eq'
      have h_inj : z^2 = w^2 := by
        have h_inj : f (z^2) = f (w^2) := by
          have h_f_eq : z^2 * h (z^2)^2 = w^2 * h (w^2)^2 := by
            linear_combination' h_eq' * (z * h (z ^ 2) + w * h (w ^ 2))
          by_cases hz' : z ^ 2 = 0 <;> by_cases hw' : w ^ 2 = 0 <;> simp_all [mul_div_cancel₀]
        exact hf.2.1 (by simpa using hz) (by simpa using hw) h_inj
      by_cases hzw : z = w <;> simp_all [sq_eq_sq_iff_eq_or_eq_neg]
      have := h_eq.2 (w ^ 2) (by simpa using pow_lt_one₀ (norm_nonneg _) hw two_ne_zero)
      simp_all [div_eq_mul_inv]
      by_cases hw : w = 0 <;> simp_all [Set.InjOn]
      have := hf.2.1 (
        show ‖w ^ 2‖ < 1
          from by simpa [hw] using pow_lt_one₀ (norm_nonneg _) ‹‖w‖ < 1› two_ne_zero) (
            show ‖0‖ < 1 from by norm_num); simp_all  [sq]
    · norm_num
    · convert HasDerivAt.deriv (HasDerivAt.mul (hasDerivAt_id 0) (HasDerivAt.comp 0 (
        h_analytic.differentiableOn.differentiableAt (isOpen_ball.mem_nhds <| by norm_num) |>
          DifferentiableAt.hasDerivAt) (hasDerivAt_pow 2 0))) using 1; norm_num [h_eq]
  · intro z hz; by_cases hz' : z = 0
    · subst hz'
      simp [hf.2.2.1, h_eq.1]
    · have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball, dist_zero_right, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) (by simpa using hz) (by norm_num)
      rw [show (z * h (z ^ 2)) ^ 2 = z ^ 2 * h (z ^ 2) ^ 2 from by ring,
        h_eq.2 (z ^ 2) hz2 (pow_ne_zero 2 hz')]
      rw [mul_div_cancel₀ _ (pow_ne_zero 2 hz')]

/--
If `f` is in `classS`, then `1/f(z) - 1/z` extends to an analytic function on the unit disk.
-/
lemma inv_f_sub_inv_id_analytic (f : ℂ → ℂ) (hf : f ∈ classS) :
    ∃ h, AnalyticOn ℂ h (ball 0 1) ∧ ∀ z ∈ ball 0 1, z ≠ 0 → h z = 1 / f z - 1 / z := by
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ℂ → ℂ, AnalyticOn ℂ h₁ (ball 0 1) ∧
    ∀ z ∈ ball 0 1, z ≠ 0 → h₁ z = 1 / (f z / z) - 1 := by
    obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ℂ → ℂ, AnalyticOn ℂ h₁ (ball 0 1) ∧
      ∀ z ∈ ball 0 1, z ≠ 0 → h₁ z = f z / z := by
      have h_f_div_z : AnalyticOn ℂ (fun z => dslope f 0 z) (ball 0 1) := by
        apply_rules [analyticOn_dslope_of_analyticOn, hf.1]
      refine ⟨fun z => dslope f 0 z, h_f_div_z, fun z hz hz' => ?_⟩;
      simp [dslope, hz']
      simp [slope_def_field, hf.2.2.1]
    use fun z => 1 / h₁ z - 1
    refine ⟨?_, ?_⟩
    · apply_rules [AnalyticOn.sub, AnalyticOn.div, analyticOn_const]
      · exact hh₁.1
      · intro z hz; by_cases h : z = 0 <;>
          simp_all only [div_eq_inv_mul, ne_eq, mem_ball, dist_zero_right]
        · have h_lim : Filter.Tendsto (fun z => h₁ z) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
            have h_lim : Filter.Tendsto (fun z => z⁻¹ * f z) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
              have h_lim : HasDerivAt f 1 0 := by
                convert hf.2.2.2 ▸ hasDerivAt_deriv_iff.mpr _ using 1
                exact hf.1.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)
              simpa [div_eq_inv_mul, hf.2.2.1] using h_lim.tendsto_slope_zero
            refine h_lim.congr' ?_
            filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
              ball_mem_nhds _ zero_lt_one)] with
              z hz₁ hz₂ using by rw [hh₁.2 z (by simpa using hz₂) hz₁]
          exact fun h => absurd (tendsto_nhds_unique h_lim (hh₁.1.continuousOn.continuousAt (
            ball_mem_nhds _ zero_lt_one) |> fun h => h.mono_left inf_le_left)) (by aesop)
        · intro H
          have hinj := hf.2.1
          have hh1_z : h₁ z = z⁻¹ * f z := hh₁.2 z (by simpa using hz) h
          rw [H] at hh1_z
          have hf_z : f z = 0 := by
            have : z⁻¹ * f z = 0 := hh1_z.symm
            have hz_inv : z⁻¹ ≠ 0 := inv_ne_zero h
            exact (mul_eq_zero.mp this).resolve_left hz_inv
          simp only [Set.InjOn, mem_ball, dist_zero_right] at hinj
          exact absurd (@hinj z (by simpa using hz) 0 (by norm_num)
            (by simp [hf_z, hf.2.2.1])) h
    · aesop
  have h_h : ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧ ∀ z ∈ ball 0 1, z ≠ 0 → h z = h₁ z / z := by
    have h_h : ∃ h : ℂ → ℂ, AnalyticOn ℂ h (ball 0 1) ∧ ∀ z ∈ ball 0 1, h z * z = h₁ z := by
      have h_h : ∀ z ∈ ball 0 1, h₁ z = (dslope (fun z => h₁ z) 0 z) * z := by
        intro z hz; by_cases hz' : z = 0
        all_goals first
          | (rw [hz']; simp only [dslope, Function.update_self, mul_zero])
          | simp only [dslope, Function.update_of_ne hz']
        · have h_lim : Filter.Tendsto (fun z => h₁ z) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
            have h_lim : Filter.Tendsto (fun z =>
              (f z / z)⁻¹ - 1) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
              have h_lim : Filter.Tendsto (fun z =>
                f z / z) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
                have h_lim : HasDerivAt f 1 0 := by
                   exact hf.2.2.2 ▸ hasDerivAt_deriv_iff.mpr (
                      show DifferentiableAt ℂ f 0 from by exact (
                        hf.1.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)))
                simpa [div_eq_inv_mul, hf.2.2.1] using h_lim.tendsto_slope_zero
              simpa using Filter.Tendsto.sub_const (h_lim.inv₀ <| by norm_num) 1
            refine h_lim.congr' ?_
            filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
              ball_mem_nhds _ zero_lt_one)] with
              z hz hz' using by aesop
          exact tendsto_nhds_unique (hh₁.1.continuousOn.continuousAt (
            ball_mem_nhds _ zero_lt_one) |> fun h =>
            h.mono_left inf_le_left) h_lim
        · have h_h : h₁ 0 = 0 := by
            have h_h2 : Filter.Tendsto (fun z => (f z / z)⁻¹ - 1) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
                have h_h3 : Filter.Tendsto (fun z => f z / z) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
                  have h_h4 : HasDerivAt f 1 0 := by
                    exact hf.2.2.2 ▸ hasDerivAt_deriv_iff.mpr (
                      show DifferentiableAt ℂ f 0 from by exact (
                        hf.1.differentiableOn.differentiableAt (ball_mem_nhds _ zero_lt_one)))
                  simpa [div_eq_inv_mul, hf.2.2.1] using h_h4.tendsto_slope_zero
                simpa using Filter.Tendsto.sub_const (h_h3.inv₀ <| by norm_num) 1
            have h_h : Filter.Tendsto (fun z => h₁ z) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
              refine h_h2.congr' ?_
              filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (
                ball_mem_nhds _ zero_lt_one)] with
                z hz hz' using by aesop
            exact tendsto_nhds_unique (hh₁.1.continuousOn.continuousAt (
              ball_mem_nhds _ zero_lt_one) |> fun h => h.mono_left inf_le_left) h_h
          simp  [slope_def_field, h_h, hz']
      use fun z => dslope (fun z => h₁ z) 0 z
      exact ⟨analyticOn_dslope_of_analyticOn _ hh₁.1, fun z hz => h_h z hz ▸ rfl⟩
    exact ⟨h_h.choose, h_h.choose_spec.1, fun z hz hz' =>
      by rw [← h_h.choose_spec.2 z hz, mul_div_cancel_right₀ _ hz']⟩
  obtain ⟨h, hh⟩ := h_h
  use h
  refine ⟨hh.1, ?_⟩
  intro z hz hz'
  rw [hh.2 z hz hz', hh₁.2 z hz hz']
  field_simp

/--
The function `1/f(1/z)` is analytic on the exterior of the unit disk.
-/
lemma inv_f_inv_analyticOn (f : ℂ → ℂ) (hf : f ∈ classS) :
    AnalyticOn ℂ (fun z => 1 / f (1 / z)) {z | 1 < ‖z‖} := by
  apply_rules [AnalyticOn.div, analyticOn_const, AnalyticOn.inv]
  · refine (AnalyticOn.comp hf.1 ?_ ?_)
    · apply AnalyticOn.div
      · exact analyticOn_const
      · exact analyticOn_id
      · intro x hx h; rw [h] at hx; norm_num at hx
    · exact fun x hx => by simpa [abs_of_pos] using inv_lt_one_of_one_lt₀ hx
  · intro z hz
    have h_f_ne_zero : ∀ w ∈ ball 0 1, w ≠ 0 → f w ≠ 0 := by
      intro w hw hw_ne_zero
      have h_f_ne_zero : f w ≠ f 0 := by
        exact fun h => hw_ne_zero <| hf.2.1 (by aesop) (by aesop) h
      have := hf.2.2.1; aesop
    exact h_f_ne_zero _ (by simpa using inv_lt_one_of_one_lt₀ hz) (one_div_ne_zero <|
      by rintro rfl; norm_num at hz)

/--
The function `1/f(1/z)` is injective on the exterior of the unit disk.
-/
lemma inv_f_inv_injOn (f : ℂ → ℂ) (hf : f ∈ classS) :
    Set.InjOn (fun z => 1 / f (1 / z)) {z | 1 < ‖z‖} := by
  have h_f_inj : Set.InjOn f {z : ℂ | ‖z‖ < 1} := by
    exact fun x hx y hy hxy => hf.2.1 (by simpa using hx) (by simpa using hy) hxy
  intro z hz w hw h_eq
  have := h_f_inj (show ‖1 / z‖ < 1 by simpa [abs_inv] using inv_lt_one_of_one_lt₀ hz) (
    show ‖1 / w‖ < 1 by simpa [abs_inv] using inv_lt_one_of_one_lt₀ hw); aesop

/--
If `f` is in `classS`, then `g(z) = 1/f(1/z)` is in `classSigma`.
-/
theorem inv_f_inv_in_Sigma (f : ℂ → ℂ) (hf : f ∈ classS) :
    (fun z => 1 / f (1 / z)) ∈ classSigma := by
  refine ⟨?_, ?_, ?_⟩
  · exact inv_f_inv_analyticOn f hf
  · exact inv_f_inv_injOn f hf
  · obtain ⟨h, hh⟩ := inv_f_sub_inv_id_analytic f hf
    refine ⟨h, hh.1, fun z hz => ?_⟩
    rw [hh.2] <;> norm_num
    · exact inv_lt_one_of_one_lt₀ hz
    · rintro rfl; norm_num at hz

end

end LeanPool.LeanComplexAnalysis
