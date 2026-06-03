/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Tactic.Common
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# FTC for Log-Derivative Integrals

Fundamental theorem of calculus for integrals of f'/f along curves,
generalizing the specific computations used in winding number calculations.

## Main results

* `intervalIntegrable_logDeriv_of_slitPlane` - ∫ f'/f is interval integrable when f stays in
  slitPlane
* `integral_logDeriv_eq_log_sub` - ∫ f'/f = log f(b) - log f(a) when f stays in slitPlane
* `ftc_log_on_segment` - combined integrability + FTC for a single C¹ function in slitPlane
* `ftc_log_neg_on_segment` - combined integrability + FTC when -f stays in slitPlane
* `ftc_log_piece` - combined integrability + FTC when f and g agree a.e. (generalizes
  Common.lean version)
-/

open Set MeasureTheory Complex
open scoped Interval

namespace LogDerivFTC

private noncomputable instance : ContinuousSMul ℝ ℂ :=
  ⟨(show (fun p : ℝ × ℂ => p.1 • p.2) = (fun p => (p.1 : ℂ) * p.2) from
    funext fun p => by simp [Complex.real_smul]) ▸
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩

/-!
### Basic integrability and FTC for C¹ curves staying in the slit plane
-/

/-- If f : ℝ → ℂ is C¹ on [a,b] with f(t) ∈ slitPlane for all t ∈ [a,b],
then the log-derivative t ↦ deriv f t / f t is interval integrable on [a,b]. -/
theorem intervalIntegrable_logDeriv_of_slitPlane {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 :=
    fun t ht => Complex.slitPlane_ne_zero (hf_slit t ht)
  have hdiv_cont : ContinuousOn (fun t => deriv f t / f t) (Icc a b) :=
    hf_deriv_cont.div hf_cont hf_ne
  exact (hdiv_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable

/-- Fundamental theorem of calculus for log-derivative integrals:
If f : ℝ → ℂ is differentiable on (a,b) with derivative continuous on [a,b],
and f(t) ∈ slitPlane for all t ∈ [a,b], then
∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a). -/
theorem integral_logDeriv_eq_log_sub {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 :=
    fun t ht => Complex.slitPlane_ne_zero (hf_slit t ht)
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b :=
    intervalIntegrable_logDeriv_of_slitPlane hab hf_cont hf_deriv_cont hf_slit
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (ContinuousOn.clog hf_cont hf_slit)
    (fun t ht => (hf_diff t ht).hasDerivAt.clog_real (hf_slit t (Ioo_subset_Icc_self ht)))
    hint

/-!
### Combined integrability + FTC for a.e.-equal pairs of curves

This is the general version of `ftc_log_piece` from `ValenceFormula.WindingWeights.Common`,
allowing g to differ from f on a null set (e.g. finitely many points).
-/

/-- Combined integrability and FTC for log-derivative integrals.

Given a "reference" function h (C¹ with values in slitPlane) and a function g
that agrees with h on (a,b) up to a null set (with matching endpoint values),
both ∫ g'/g and ∫ h'/h are interval integrable and equal Complex.log(g b) - Complex.log(g a).

This generalizes the `ftc_log_piece` lemma in `ValenceFormula.WindingWeights.Common`
to the setting where h serves as the smooth comparison function. -/
theorem ftc_log_piece {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_ne : ∀ t ∈ Icc a b, h t ≠ 0 :=
    fun t ht => Complex.slitPlane_ne_zero (hh_slit t ht)
  have hh_div_cont : ContinuousOn (fun t => deriv h t / h t) (Icc a b) :=
    hh_deriv_cont.div hh_cont hh_ne
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    (hh_div_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  -- The set {b} has measure zero, so g and h agree a.e. on Ι a b
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton b)
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  have hint_g : IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
    constructor
    · exact MeasureTheory.Integrable.congr
        (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
    · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
      exact MeasureTheory.integrableOn_empty
  have h_ftc := integral_logDeriv_eq_log_sub hab hh_cont hh_diff hh_deriv_cont hh_slit
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (h b) - Complex.log (h a) := h_ftc
      _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]⟩

/-- Combined integrability and FTC for a single C¹ function staying in slitPlane.

Returns both `IntervalIntegrable (f'/f)` and `∫ f'/f = log(f(b)) - log(f(a))`.
This is the direct-function version of `ftc_log_piece` (no g/h a.e.-equal pair needed). -/
theorem ftc_log_on_segment {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 :=
    fun t ht => Complex.slitPlane_ne_zero (hf_slit t ht)
  have hF_cont : ContinuousOn (fun t => Complex.log (f t)) (Icc a b) :=
    hf_cont.clog (fun t ht => hf_slit t ht)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t => Complex.log (f t))
      (deriv f x / f x) x :=
    fun x hx => (hf_diff x hx).hasDerivAt.clog_real (hf_slit x (Ioo_subset_Icc_self hx))
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf_deriv_cont.div hf_cont hf_ne
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hint⟩

/-- Combined integrability and FTC when `-f` stays in slitPlane.

Returns both `IntervalIntegrable (f'/f)` and `∫ f'/f = log(-f(b)) - log(-f(a))`.
This is the negation variant of `ftc_log_on_segment`. -/
theorem ftc_log_neg_on_segment {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, -(f t) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t =
      Complex.log (-(f b)) - Complex.log (-(f a)) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 := fun t ht =>
    neg_ne_zero.mp (Complex.slitPlane_ne_zero (hf_slit t ht))
  have hF_cont : ContinuousOn (fun t => Complex.log (-(f t))) (Icc a b) :=
    hf_cont.neg.clog (fun t ht => hf_slit t ht)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t => Complex.log (-(f t)))
      (deriv f x / f x) x := by
    intro x hx
    have hslit := hf_slit x (Ioo_subset_Icc_self hx)
    have h_log := (hf_diff x hx).hasDerivAt.neg.clog_real hslit
    convert h_log using 1
    exact (neg_div_neg_eq (deriv f x) (f x)).symm
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf_deriv_cont.div hf_cont hf_ne
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hint⟩

/-- FTC for log-derivative when the negated function stays in slitPlane:
∫ f'/f = log(-f(b)) - log(-f(a)) when -f ∈ slitPlane on [a,b]. -/
theorem integral_logDeriv_eq_neg_log_sub {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_neg_slit : ∀ t ∈ Icc a b, -f t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv f t / f t = Complex.log (-f b) - Complex.log (-f a) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 := fun t ht =>
    neg_ne_zero.mp (Complex.slitPlane_ne_zero (hf_neg_slit t ht))
  have hF_cont : ContinuousOn (fun t => Complex.log (-(f t))) (Icc a b) :=
    hf_cont.neg.clog (fun t ht => hf_neg_slit t ht)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t => Complex.log (-(f t)))
      (deriv f x / f x) x := by
    intro x hx
    have hslit := hf_neg_slit x (Ioo_subset_Icc_self hx)
    have h_log := (hf_diff x hx).hasDerivAt.neg.clog_real hslit
    convert h_log using 1
    exact (neg_div_neg_eq (deriv f x) (f x)).symm
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf_deriv_cont.div hf_cont (fun x hx => hf_ne x hx)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hint

end LogDerivFTC
