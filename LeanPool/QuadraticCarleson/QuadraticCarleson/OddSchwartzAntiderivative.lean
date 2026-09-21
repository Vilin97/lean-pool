/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Antiderivatives of zero-integral Schwartz functions

If a Schwartz function has integral zero, its primitive obtained by
integration from negative infinity is again Schwartz. The zeroth-derivative
decay bounds follow by using the nearer tail on each half-line and bounding
its weighted norm by a weighted `L¹` moment of the original function.
All higher derivative bounds are inherited from the original function.

Odd Schwartz functions have integral zero, and therefore have Schwartz
antiderivatives.
-/

open MeasureTheory Set Filter
open scoped SchwartzMap Topology ContDiff

namespace QuadraticCarleson

/-- The primitive normalized to vanish at negative infinity. -/
noncomputable def schwartzPrimitiveFunction (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∫ t in Iic x, f t

theorem schwartzPrimitiveFunction_eq_intervalIntegral (f : 𝓢(ℝ, ℂ)) :
    schwartzPrimitiveFunction f =
      fun x ↦ (∫ t in (0 : ℝ)..x, f t) + ∫ t in Iic (0 : ℝ), f t := by
  funext x
  exact sub_eq_iff_eq_add.mp
    (intervalIntegral.integral_Iic_sub_Iic f.integrable.integrableOn
      f.integrable.integrableOn)

theorem hasDerivAt_schwartzPrimitiveFunction (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (schwartzPrimitiveFunction f) (f x) x := by
  rw [schwartzPrimitiveFunction_eq_intervalIntegral]
  exact (f.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.add_const _

theorem deriv_schwartzPrimitiveFunction (f : 𝓢(ℝ, ℂ)) :
    deriv (schwartzPrimitiveFunction f) = f :=
  funext (fun x ↦ (hasDerivAt_schwartzPrimitiveFunction f x).deriv)

theorem contDiff_schwartzPrimitiveFunction (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (schwartzPrimitiveFunction f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x ↦ (hasDerivAt_schwartzPrimitiveFunction f x).differentiableAt, ?_⟩
  rw [deriv_schwartzPrimitiveFunction]
  exact f.smooth'

/-- A tail supported where `‖t‖ ≥ ‖x‖` is bounded by a Schwartz moment. -/
theorem norm_pow_mul_norm_schwartz_setIntegral_le (f : 𝓢(ℝ, ℂ)) (k : ℕ)
    (x : ℝ) (s : Set ℝ) (hs : ∀ t ∈ s, ‖x‖ ≤ ‖t‖) :
    ‖x‖ ^ k * ‖∫ t in s, f t‖ ≤ ∫ t : ℝ, ‖t‖ ^ k * ‖f t‖ := by
  calc
    ‖x‖ ^ k * ‖∫ t in s, f t‖ ≤ ‖x‖ ^ k * ∫ t in s, ‖f t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ t in s, ‖x‖ ^ k * ‖f t‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ t in s, ‖t‖ ^ k * ‖f t‖ := by
      apply setIntegral_mono_of_nonneg (fun _ _ ↦ by positivity)
        (fun t ht ↦ ?_) (f.integrable_pow_mul volume k).integrableOn
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hs t ht) k) (norm_nonneg _)
    _ ≤ ∫ t : ℝ, ‖t‖ ^ k * ‖f t‖ :=
      setIntegral_le_integral (f.integrable_pow_mul volume k)
        (Eventually.of_forall fun _ ↦ by positivity)

theorem schwartzPrimitiveFunction_eq_neg_tail (f : 𝓢(ℝ, ℂ))
    (hf : (∫ t : ℝ, f t) = 0) (x : ℝ) :
    schwartzPrimitiveFunction f x = -(∫ t in Ioi x, f t) := by
  have h := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := x)
    f.integrable.integrableOn f.integrable.integrableOn
  rw [hf] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Every polynomially weighted value of the primitive is controlled by
the corresponding weighted `L¹` moment of the original Schwartz function. -/
theorem norm_pow_mul_schwartzPrimitiveFunction_le (f : 𝓢(ℝ, ℂ))
    (hf : (∫ t : ℝ, f t) = 0) (k : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖schwartzPrimitiveFunction f x‖ ≤
      ∫ t : ℝ, ‖t‖ ^ k * ‖f t‖ := by
  rcases le_or_gt x 0 with hx | hx
  · apply norm_pow_mul_norm_schwartz_setIntegral_le f k x (Iic x)
    intro t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hx,
      abs_of_nonpos (ht.trans hx)]
    exact neg_le_neg ht
  · rw [schwartzPrimitiveFunction_eq_neg_tail f hf, norm_neg]
    apply norm_pow_mul_norm_schwartz_setIntegral_le f k x (Ioi x)
    intro t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx.le,
      abs_of_nonneg (hx.trans ht).le]
    exact ht.le

/-- The primitive of a zero-integral Schwartz function, bundled with all
its smoothness and rapid-decay bounds. -/
noncomputable def schwartzPrimitive (f : 𝓢(ℝ, ℂ)) (hf : (∫ t : ℝ, f t) = 0) :
    𝓢(ℝ, ℂ) where
  toFun := schwartzPrimitiveFunction f
  smooth' := contDiff_schwartzPrimitiveFunction f
  decay' k n := by
    cases n with
    | zero =>
      refine ⟨∫ t : ℝ, ‖t‖ ^ k * ‖f t‖, fun x ↦ ?_⟩
      simpa only [norm_iteratedFDeriv_zero] using
        norm_pow_mul_schwartzPrimitiveFunction_le f hf k x
    | succ n =>
      obtain ⟨C, _, hC⟩ := f.decay k n
      refine ⟨C, fun x ↦ ?_⟩
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
        deriv_schwartzPrimitiveFunction] using hC x

@[simp]
theorem schwartzPrimitive_apply (f : 𝓢(ℝ, ℂ)) (hf : (∫ t : ℝ, f t) = 0) (x : ℝ) :
    schwartzPrimitive f hf x = ∫ t in Iic x, f t := rfl

theorem derivCLM_schwartzPrimitive (f : 𝓢(ℝ, ℂ)) (hf : (∫ t : ℝ, f t) = 0) :
    SchwartzMap.derivCLM ℂ ℂ (schwartzPrimitive f hf) = f := by
  ext x
  change deriv (schwartzPrimitiveFunction f) x = f x
  rw [deriv_schwartzPrimitiveFunction]

/-- An explicit bound for every seminorm involving no derivatives. -/
theorem seminorm_zero_schwartzPrimitive_le (f : 𝓢(ℝ, ℂ))
    (hf : (∫ t : ℝ, f t) = 0) (k : ℕ) :
    SchwartzMap.seminorm ℂ k 0 (schwartzPrimitive f hf) ≤
      ∫ t : ℝ, ‖t‖ ^ k * ‖f t‖ := by
  apply SchwartzMap.seminorm_le_bound
  · exact integral_nonneg (fun _ ↦ by positivity)
  · intro x
    rw [norm_iteratedFDeriv_zero]
    change ‖x‖ ^ k * ‖schwartzPrimitiveFunction f x‖ ≤ _
    exact norm_pow_mul_schwartzPrimitiveFunction_le f hf k x

/-- Every higher-derivative seminorm is controlled by the corresponding
seminorm of the original Schwartz function. -/
theorem seminorm_succ_schwartzPrimitive_le (f : 𝓢(ℝ, ℂ))
    (hf : (∫ t : ℝ, f t) = 0) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k (n + 1) (schwartzPrimitive f hf) ≤
      SchwartzMap.seminorm ℂ k n f := by
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (schwartzPrimitiveFunction f) x‖ ≤ _
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
    deriv_schwartzPrimitiveFunction] using f.le_seminorm ℂ k n x

theorem exists_schwartz_antiderivative_of_integral_eq_zero (f : 𝓢(ℝ, ℂ))
    (hf : (∫ t : ℝ, f t) = 0) :
    ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.derivCLM ℂ ℂ g = f :=
  ⟨schwartzPrimitive f hf, derivCLM_schwartzPrimitive f hf⟩

theorem integral_schwartz_odd_eq_zero (f : 𝓢(ℝ, ℂ))
    (hf : Function.Odd (f : ℝ → ℂ)) : (∫ t : ℝ, f t) = 0 := by
  apply self_eq_neg.mp
  calc
    (∫ t : ℝ, f t) = ∫ t : ℝ, f (-t) := (integral_neg_eq_self f volume).symm
    _ = -(∫ t : ℝ, f t) := by
      have heq : (fun t : ℝ ↦ f (-t)) = fun t ↦ -f t := funext hf
      rw [heq, integral_neg]

/-- Every odd complex Schwartz function on the real line has a complex
Schwartz antiderivative. -/
theorem exists_schwartz_antiderivative_of_odd (f : 𝓢(ℝ, ℂ))
    (hf : Function.Odd (f : ℝ → ℂ)) :
    ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.derivCLM ℂ ℂ g = f :=
  exists_schwartz_antiderivative_of_integral_eq_zero f (integral_schwartz_odd_eq_zero f hf)

end QuadraticCarleson
