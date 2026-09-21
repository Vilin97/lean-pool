/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.UnitCircle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# The cyclotomic defect in the opening

This module isolates the characteristic-zero algebra used after compatible finite-field
eigenvalues have been lifted to roots of unity.  The difficult number-field reduction interface
is not assumed here: given three complex unit-circle lifts, we define the symmetric defect,
prove its uniform archimedean bound, and prove that it cannot vanish unless all three traces do.
-/

namespace BGS.Markoff

/-- The trace associated to a nonzero eigenvalue and its reciprocal. -/
def cyclotomicTrace {K : Type*} [Field K] (z : K) : K :=
  z + z⁻¹

/-- The symmetric Markoff defect of three lifted eigenvalues. -/
def cyclotomicDefect {K : Type*} [Field K] (z₁ z₂ z₃ : K) : K :=
  cyclotomicTrace z₁ ^ 2 + cyclotomicTrace z₂ ^ 2 + cyclotomicTrace z₃ ^ 2 -
    cyclotomicTrace z₁ * cyclotomicTrace z₂ * cyclotomicTrace z₃

/-- On the complex unit circle, reciprocal-eigenvalue trace is twice the real part. -/
theorem cyclotomicTrace_eq_two_mul_re {z : ℂ} (hz : ‖z‖ = 1) :
    cyclotomicTrace z = (2 * z.re : ℝ) := by
  rw [cyclotomicTrace, Complex.inv_eq_conj hz]
  apply Complex.ext
  · simp
    ring
  · simp

/-- A unit-circle trace has complex norm at most two. -/
theorem norm_cyclotomicTrace_le_two {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cyclotomicTrace z‖ ≤ 2 := by
  rw [cyclotomicTrace]
  calc
    ‖z + z⁻¹‖ ≤ ‖z‖ + ‖z⁻¹‖ := norm_add_le _ _
    _ = 2 := by simp [hz]; norm_num

/-- Every complex embedding of the symmetric cyclotomic defect has absolute value at most
`20`, provided the three eigenvalues lie on the unit circle. -/
theorem norm_cyclotomicDefect_le_twenty
    {z₁ z₂ z₃ : ℂ} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1) :
    ‖cyclotomicDefect z₁ z₂ z₃‖ ≤ 20 := by
  let t₁ := cyclotomicTrace z₁
  let t₂ := cyclotomicTrace z₂
  let t₃ := cyclotomicTrace z₃
  have ht₁ : ‖t₁‖ ≤ 2 := norm_cyclotomicTrace_le_two hz₁
  have ht₂ : ‖t₂‖ ≤ 2 := norm_cyclotomicTrace_le_two hz₂
  have ht₃ : ‖t₃‖ ≤ 2 := norm_cyclotomicTrace_le_two hz₃
  have ht₁sq : ‖t₁ ^ 2‖ ≤ 4 := by rw [norm_pow]; nlinarith [norm_nonneg t₁]
  have ht₂sq : ‖t₂ ^ 2‖ ≤ 4 := by rw [norm_pow]; nlinarith [norm_nonneg t₂]
  have ht₃sq : ‖t₃ ^ 2‖ ≤ 4 := by rw [norm_pow]; nlinarith [norm_nonneg t₃]
  have htprod : ‖t₁ * t₂ * t₃‖ ≤ 8 := by
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg t₁, norm_nonneg t₂, norm_nonneg t₃,
      mul_nonneg (norm_nonneg t₁) (norm_nonneg t₂)]
  change ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ ≤ 20
  have hsum : ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ ≤
      ‖t₁ ^ 2‖ + ‖t₂ ^ 2‖ + ‖t₃ ^ 2‖ := by
    calc
      ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ ≤ ‖t₁ ^ 2 + t₂ ^ 2‖ + ‖t₃ ^ 2‖ :=
        norm_add_le _ _
      _ ≤ (‖t₁ ^ 2‖ + ‖t₂ ^ 2‖) + ‖t₃ ^ 2‖ := by
        linarith [norm_add_le (t₁ ^ 2) (t₂ ^ 2)]
  calc
    ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 - t₁ * t₂ * t₃‖ ≤
        ‖t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2‖ + ‖t₁ * t₂ * t₃‖ := norm_sub_le _ _
    _ ≤ (‖t₁ ^ 2‖ + ‖t₂ ^ 2‖ + ‖t₃ ^ 2‖) + ‖t₁ * t₂ * t₃‖ := by
      linarith
    _ ≤ 20 := by linarith

/-- Three unit-circle lifts with vanishing cyclotomic defect have zero trace in every
coordinate. -/
theorem cyclotomicTrace_eq_zero_of_defect_eq_zero
    {z₁ z₂ z₃ : ℂ} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1)
    (hdefect : cyclotomicDefect z₁ z₂ z₃ = 0) :
    cyclotomicTrace z₁ = 0 ∧ cyclotomicTrace z₂ = 0 ∧ cyclotomicTrace z₃ = 0 := by
  let a : ℝ := 2 * z₁.re
  let b : ℝ := 2 * z₂.re
  let c : ℝ := 2 * z₃.re
  have ht₁ : cyclotomicTrace z₁ = (a : ℂ) := cyclotomicTrace_eq_two_mul_re hz₁
  have ht₂ : cyclotomicTrace z₂ = (b : ℂ) := cyclotomicTrace_eq_two_mul_re hz₂
  have ht₃ : cyclotomicTrace z₃ = (c : ℂ) := cyclotomicTrace_eq_two_mul_re hz₃
  have hreal : a ^ 2 + b ^ 2 + c ^ 2 - a * b * c = 0 := by
    rw [cyclotomicDefect, ht₁, ht₂, ht₃] at hdefect
    exact_mod_cast hdefect
  let x : NormalizedPoint ℝ := ⟨a, b, c⟩
  have hx : IsNormalizedMarkoff x := hreal
  have haBound : a ∈ Set.Icc (-2 : ℝ) 2 := by
    dsimp [a]
    have hre := Complex.abs_re_le_norm z₁
    rw [hz₁] at hre
    obtain ⟨hreLower, hreUpper⟩ := abs_le.mp hre
    constructor <;> nlinarith
  have hxOrigin := real_normalizedMarkoff_eq_origin_of_firstCoordinate_mem_Icc x hx haBound
  have ha : a = 0 := congrArg NormalizedPoint.u1 hxOrigin
  have hb : b = 0 := congrArg NormalizedPoint.u2 hxOrigin
  have hc : c = 0 := congrArg NormalizedPoint.u3 hxOrigin
  exact ⟨ht₁.trans (by simp [ha]), ht₂.trans (by simp [hb]), ht₃.trans (by simp [hc])⟩

/-- Unless all three reciprocal-eigenvalue traces vanish, the cyclotomic defect is nonzero. -/
theorem cyclotomicDefect_ne_zero_of_some_trace_ne_zero
    {z₁ z₂ z₃ : ℂ} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hz₃ : ‖z₃‖ = 1)
    (htrace : cyclotomicTrace z₁ ≠ 0 ∨ cyclotomicTrace z₂ ≠ 0 ∨
      cyclotomicTrace z₃ ≠ 0) :
    cyclotomicDefect z₁ z₂ z₃ ≠ 0 := by
  intro hzero
  obtain ⟨h₁, h₂, h₃⟩ := cyclotomicTrace_eq_zero_of_defect_eq_zero hz₁ hz₂ hz₃ hzero
  rcases htrace with htrace | htrace | htrace
  · exact htrace h₁
  · exact htrace h₂
  · exact htrace h₃

end BGS.Markoff
