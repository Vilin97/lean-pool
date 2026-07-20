/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Group.NatPowAssoc
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

/-! # Csqrt -/


@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction


/-- The principal complex square root `a ↦ exp ((1 / 2) * log a)`. -/
noncomputable def csqrt : ℂ → ℂ := (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a)))

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have : (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_lt z.2).symm)
  rw [this, deriv_comp]
  · simp only [one_div, Complex.deriv_exp, deriv_const_mul_field', neg_mul,
    smul_eq_mul]
    rw [Complex.exp_neg]
    field_simp
    have hsq : cexp (Complex.log (z : ℂ) / 2) ^ 2 = cexp (Complex.log (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]; grind
    simpa [hsq, (Complex.hasDerivAt_log hzz).deriv, Complex.exp_log <| ne_zero z]
      using Complex.mul_inv_cancel <| ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z :=
  (Complex.differentiableAt_log (mem_slitPlane_iff.mpr (Or.inr (ne_of_lt z.2).symm))).const_mul
    _ |>.cexp


lemma csqrt_I : (csqrt (Complex.I)) ^ 24 = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1, 1]
    rw [← mul_assoc, show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log I_ne_zero]
  have : Complex.I ^ 12 = (.I ^ 4) ^ 3 := by rw [← npow_mul]
  simp [this, Complex.I_pow_four]

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1, 1]
    rw [← mul_assoc, show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]
