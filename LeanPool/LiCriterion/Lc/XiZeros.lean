/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
  Zeros of the Xi Function

  This file proves AXIOM 1 from LiCriterion.lean:
  The zeros of ξ(s) are exactly the nontrivial zeros of ζ(s).

  Definition (from LiCriterion.lean line 1304):
    ξ(s) = (1/2) * s * (s-1) * Λ₀(s) + (1/2)

  where Λ₀ = completedRiemannZeta₀ is the entire completed zeta function.

  Key identity (proven below):
    ξ(s) = (1/2) * s * (s-1) * Λ(s)

  where Λ = completedRiemannZeta = π^(-s/2) Γ(s/2) ζ(s).

  Reference: Mathlib.NumberTheory.LSeries.RiemannZeta
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! ## Key Identity: ξ(s) = (1/2) s(s-1) Λ(s)

We prove that our definition of ξ using Λ₀ is equivalent to the standard
definition using Λ = completedRiemannZeta.

The relationship is:
  Λ₀(s) = Λ(s) + 1/s + 1/(1-s)

Substituting:
  ξ(s) = (1/2) s(s-1) Λ₀(s) + 1/2
       = (1/2) s(s-1) [Λ(s) + 1/s + 1/(1-s)] + 1/2
       = (1/2) s(s-1) Λ(s) + (1/2)(s-1) - (1/2)s + 1/2
       = (1/2) s(s-1) Λ(s) + 0
       = (1/2) s(s-1) Λ(s)
-/

open Complex
open scoped BigOperators

namespace XiZeros

/-- Nontrivial zeros of ζ: zeros in the critical strip 0 < Re(s) < 1 -/
def NontrivialZero : Type :=
  {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Definition of ξ (matching LiCriterion.lean) -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

/-- ξ(s) equals (1/2) s(s-1) Λ(s) when s ≠ 0 and s ≠ 1.

This is the standard form of the xi function. -/
lemma xi_eq_half_s_sm1_Lambda {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold riemannXi
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hs1)
  -- Use the Mathlib equation: Λ = Λ₀ - 1/s - 1/(1-s)
  have h := completedRiemannZeta_eq s
  -- h : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)
  -- So: completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s)
  rw [h]
  field_simp
  ring

/-- ξ has no zeros at s=0 or s=1 -/
lemma xi_ne_zero_at_trivial_points :
    riemannXi 0 ≠ 0 ∧ riemannXi 1 ≠ 0 := by
  constructor
  · -- ξ(0) = (1/2) * 0 * (-1) * Λ₀(0) + (1/2) = (1/2) ≠ 0
    unfold riemannXi
    norm_num
  · -- ξ(1) = (1/2) * 1 * 0 * Λ₀(1) + (1/2) = (1/2) ≠ 0
    unfold riemannXi
    norm_num

/-! ## Zeros of ξ in the Critical Strip

In the critical strip 0 < Re(s) < 1:
- s ≠ 0 and s ≠ 1, so s(s-1) ≠ 0
- ξ(s) = (1/2) s(s-1) Λ(s), so ξ(s) = 0 ⟺ Λ(s) = 0

And Λ(s) = π^(-s/2) Γ(s/2) ζ(s) where:
- π^(-s/2) ≠ 0 always (exponential)
- Γ(s/2) ≠ 0 for Re(s/2) > 0, i.e., Re(s) > 0 (Γ has no zeros, only poles at ≤ 0)

Therefore: ξ(s) = 0 ⟺ ζ(s) = 0 in the critical strip.
-/

/-- In the critical strip, ζ(s) = 0 implies Λ(s) = 0. -/
lemma zeta_zero_implies_Lambda_zero {s : ℂ} (hs_re_pos : 0 < s.re) (_hs_re_lt : s.re < 1)
    (hzeta : riemannZeta s = 0) : completedRiemannZeta s = 0 := by
  -- Λ(s) = π^(-s/2) Γ(s/2) ζ(s) = ... * 0 = 0
  -- Use riemannZeta s = completedRiemannZeta s / Gammaℝ s
  -- Since riemannZeta s = 0 and Gammaℝ s ≠ 0 (for Re(s) > 0), we get completedRiemannZeta s = 0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs_re_pos
    simp at hs_re_pos
  rw [riemannZeta_def_of_ne_zero hs0] at hzeta
  exact div_eq_zero_iff.mp hzeta |>.resolve_right (Gammaℝ_ne_zero_of_re_pos hs_re_pos)

/-- In the critical strip, Λ(s) = 0 implies ζ(s) = 0. -/
lemma Lambda_zero_implies_zeta_zero {s : ℂ} (_hs_re_pos : 0 < s.re) (_hs_re_lt : s.re < 1)
    (hs0 : s ≠ 0) (_hs1 : s ≠ 1)
    (hLambda : completedRiemannZeta s = 0) : riemannZeta s = 0 := by
  -- ζ(s) = Λ(s) / Γℝ(s), so if Λ(s) = 0 then ζ(s) = 0
  rw [riemannZeta_def_of_ne_zero hs0, hLambda, zero_div]

/-- If a product is zero and the first factor is nonzero, then the second factor is zero. -/
lemma mul_eq_zero_of_ne_zero_left {a b : ℂ} (ha : a ≠ 0) (hab : a * b = 0) : b = 0 := by
  cases mul_eq_zero.mp hab with
  | inl h => exact absurd h ha
  | inr h => exact h

/-- AXIOM 1: Zeros of ξ are exactly nontrivial zeros of ζ -/
theorem xi_zeros_are_nontrivial_zeros :
    ∀ s : ℂ, riemannXi s = 0 ↔ ∃ ρ : NontrivialZero, s = ρ.val := by
  intro s
  constructor
  · -- Forward: ξ(s) = 0 → s is a nontrivial zero
    intro h_xi
    -- First, s must be in the critical strip
    -- If s = 0 or s = 1, then ξ(s) = 1/2 ≠ 0
    have hs0 : s ≠ 0 := by
      intro heq
      rw [heq] at h_xi
      exact xi_ne_zero_at_trivial_points.1 h_xi
    have hs1 : s ≠ 1 := by
      intro heq
      rw [heq] at h_xi
      exact xi_ne_zero_at_trivial_points.2 h_xi
    -- Use ξ(s) = (1/2) s(s-1) Λ(s)
    rw [xi_eq_half_s_sm1_Lambda hs0 hs1] at h_xi
    -- Since s ≠ 0, s ≠ 1, and (1/2) ≠ 0, we have Λ(s) = 0
    have h_Lambda : completedRiemannZeta s = 0 := by
      have h_half : (1 / 2 : ℂ) ≠ 0 := by norm_num
      have h_s : s ≠ 0 := hs0
      have h_sm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have h_prod : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero h_half h_s) h_sm1
      exact mul_eq_zero_of_ne_zero_left h_prod h_xi
    -- Prove s is in critical strip using nonvanishing results and functional equation
    have hs_re_lt : s.re < 1 := by
      by_contra h
      push Not at h
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h
      have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one h)
      rw [riemannZeta_def_of_ne_zero hs0, div_ne_zero_iff] at hz
      exact hz.1 h_Lambda
    have hs_re_pos : 0 < s.re := by
      by_contra h
      push Not at h
      have h1ms_re : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
      have h1ms_ne_zero : 1 - s ≠ 0 := by
        intro heq
        exact hs1 (sub_eq_zero.mp heq).symm
      have hz : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1ms_re
      have hL1ms : completedRiemannZeta (1 - s) = 0 := by
        rw [completedRiemannZeta_one_sub s]
        exact h_Lambda
      have hG : (1 - s).Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < (1 - s).re)
      rw [riemannZeta_def_of_ne_zero h1ms_ne_zero, div_ne_zero_iff] at hz
      exact hz.1 hL1ms
    have hzeta : riemannZeta s = 0 :=
      Lambda_zero_implies_zeta_zero hs_re_pos hs_re_lt hs0 hs1 h_Lambda
    exact ⟨⟨s, hzeta, hs_re_pos, hs_re_lt⟩, rfl⟩
  · -- Backward: s is a nontrivial zero → ξ(s) = 0
    intro ⟨ρ, hρ⟩
    obtain ⟨hρ_zero, hρ_re_pos, hρ_re_lt⟩ := ρ.property
    -- ρ is in critical strip, so ρ ≠ 0 and ρ ≠ 1
    have hs0 : ρ.val ≠ 0 := by
      intro heq
      rw [heq] at hρ_re_pos
      simp at hρ_re_pos
    have hs1 : ρ.val ≠ 1 := by
      intro heq
      rw [heq] at hρ_re_lt
      simp at hρ_re_lt
    rw [hρ]
    -- ξ(ρ) = (1/2) ρ(ρ-1) Λ(ρ)
    rw [xi_eq_half_s_sm1_Lambda hs0 hs1]
    -- Since ζ(ρ) = 0, we have Λ(ρ) = 0 (in the critical strip)
    have h_Lambda : completedRiemannZeta ρ.val = 0 :=
      zeta_zero_implies_Lambda_zero hρ_re_pos hρ_re_lt hρ_zero
    rw [h_Lambda]
    ring

end XiZeros
