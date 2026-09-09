/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The actual mean-zero periodic angular primitive

This is an explicit Bochner integral, valid also for a Hilbert-valued angle
curve such as a time-L² pressure coefficient. Periodicity is proved from the
zero integral of the forcing; subtracting the actual mean fixes the constant.
-/

@[expose] public section


noncomputable section

namespace EulerAngleMeanZeroPrimitive

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The raw angular primitive, anchored at angle zero. -/
def rawPrimitive (f : ℝ → E) (θ : ℝ) : E := ∫ s in 0..θ, f s

/-- The actual angular primitive with its mean over one period removed. -/
def primitive (P : ℝ) (f : ℝ → E) (θ : ℝ) : E :=
  rawPrimitive f θ - P⁻¹ • (∫ s in 0..P, rawPrimitive f s)

/-- The explicit integral has the actual derivative prescribed by the forcing. -/
theorem rawPrimitive_hasDerivAt (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    HasDerivAt (rawPrimitive f) (f θ) θ :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- The raw angular primitive is continuous. -/
theorem rawPrimitive_continuous (f : ℝ → E) (hf : Continuous f) : Continuous (rawPrimitive f) :=
  (show Differentiable ℝ (rawPrimitive f) from
    fun θ => (rawPrimitive_hasDerivAt f hf θ).differentiableAt).continuous

/-- Removing the mean does not change the actual angular derivative. -/
theorem primitive_hasDerivAt (P : ℝ) (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    HasDerivAt (primitive P f) (f θ) θ :=
  (rawPrimitive_hasDerivAt f hf θ).sub_const _

/-- The normalized angular primitive is continuous. -/
theorem primitive_continuous (P : ℝ) (f : ℝ → E) (hf : Continuous f) :
    Continuous (primitive P f) :=
  (rawPrimitive_continuous f hf).sub continuous_const

omit [CompleteSpace E] in
/-- Zero angular mean of the forcing makes the raw integral periodic. -/
theorem rawPrimitive_periodic (P : ℝ) (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f P) (hmean : ∫ θ in 0..P, f θ = 0) :
    Function.Periodic (rawPrimitive f) P := by
  intro θ
  unfold rawPrimitive
  rw [hper.intervalIntegral_add_eq_add 0 θ (fun a b => hf.intervalIntegrable a b),
    zero_add, hmean, add_zero]

omit [CompleteSpace E] in
/-- The normalized angular primitive is genuinely periodic. -/
theorem primitive_periodic (P : ℝ) (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f P) (hmean : ∫ θ in 0..P, f θ = 0) :
    Function.Periodic (primitive P f) P := by
  intro θ
  simp only [primitive, rawPrimitive_periodic P f hf hper hmean θ]

/-- The normalization gives exactly zero integral over one angular period. -/
theorem primitive_mean_zero (P : ℝ) (hP : P ≠ 0) (f : ℝ → E) (hf : Continuous f) :
    (∫ θ in 0..P, primitive P f θ) = 0 := by
  unfold primitive
  rw [intervalIntegral.integral_sub ((rawPrimitive_continuous f hf).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, smul_smul,
    mul_inv_cancel₀ hP, one_smul, sub_self]

/-- The zero-mean angular primitive is unique among genuine differentiable primitives. -/
theorem primitive_unique (P : ℝ) (hP : P ≠ 0) (f : ℝ → E) (hf : Continuous f)
    (g : ℝ → E) (hg : ∀ θ, HasDerivAt g (f θ) θ)
    (hmean : ∫ θ in 0..P, g θ = 0) : g = primitive P f := by
  let d := fun θ => g θ - primitive P f θ
  have hd : ∀ θ, HasDerivAt d 0 θ := by
    intro θ
    change HasDerivAt (g - primitive P f) 0 θ
    simpa only [sub_self] using (hg θ).sub (primitive_hasDerivAt P f hf θ)
  have hconst : ∀ θ, d θ = d 0 :=
    fun θ => is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
      (fun x => (hd x).deriv) θ 0
  have hdmean : (∫ θ in 0..P, d θ) = 0 := by
    change (∫ θ in 0..P, g θ - primitive P f θ) = 0
    rw [intervalIntegral.integral_sub
      ((show Continuous g from (show Differentiable ℝ g from fun x => (hg
          x).differentiableAt).continuous).intervalIntegrable _ _)
      ((primitive_continuous P f hf).intervalIntegrable _ _), hmean,
      primitive_mean_zero P hP f hf, sub_self]
  have hz : d 0 = 0 := by
    have hi : (∫ θ in 0..P, d θ) = P • d 0 := by
      simp only [hconst, intervalIntegral.integral_const, sub_zero]
    rw [hi] at hdmean
    exact (smul_eq_zero.mp hdmean).resolve_left hP
  funext θ
  exact sub_eq_zero.mp ((hconst θ).trans hz)

end EulerAngleMeanZeroPrimitive
