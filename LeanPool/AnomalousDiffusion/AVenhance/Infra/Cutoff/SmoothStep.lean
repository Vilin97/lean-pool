/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support

/-! Reusable one-dimensional smooth step and plateau cutoffs. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

open Filter

/-- The standard smooth transition from zero to one. -/
abbrev step : ℝ → ℝ := Real.smoothTransition

theorem step_contDiff : ContDiff ℝ (⊤ : ℕ∞) step := by
  exact Real.smoothTransition.contDiff

theorem step_nonneg (x : ℝ) : 0 ≤ step x :=
  Real.smoothTransition.nonneg x

theorem step_le_one (x : ℝ) : step x ≤ 1 :=
  Real.smoothTransition.le_one x

theorem step_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : step x = 0 :=
  Real.smoothTransition.zero_of_nonpos hx

theorem step_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : step x = 1 :=
  Real.smoothTransition.one_of_one_le hx

/-- The reflected transition complements the original transition. -/
theorem step_one_sub (x : ℝ) : step (1 - x) = 1 - step x := by
  change expNegInvGlue (1 - x) /
      (expNegInvGlue (1 - x) + expNegInvGlue (1 - (1 - x))) =
    1 - expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))
  rw [sub_sub_cancel]
  have hd : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  calc
    expNegInvGlue (1 - x) /
        (expNegInvGlue (1 - x) + expNegInvGlue x) =
        1 - expNegInvGlue x /
          (expNegInvGlue (1 - x) + expNegInvGlue x) := by
            field_simp [show expNegInvGlue (1 - x) + expNegInvGlue x ≠ 0 by
              simpa [add_comm] using hd]
            ring
    _ = 1 - expNegInvGlue x /
        (expNegInvGlue x + expNegInvGlue (1 - x)) := by rw [add_comm]

/-- A smooth cutoff equal to one on `[left,right]`, with transition width `margin` on
both sides, and zero outside `[left-margin,right+margin]`. -/
def plateau (left right margin x : ℝ) : ℝ :=
  step ((x - (left - margin)) / margin) *
    step (((right + margin) - x) / margin)

/-- Smooth compactly supported functions have a uniform bound for every finite collection
of scalar iterated derivatives. -/
theorem exists_iteratedDeriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ x : ℝ,
      |iteratedDeriv j f x| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hcompact.exists_bound_iteratedFDeriv hf N
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro j hj x
  have h := hC j hj x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  have h' : ‖iteratedDeriv j f x‖ ≤ max 1 C := h.trans (le_max_right _ _)
  simpa only [Real.norm_eq_abs] using h'

theorem SmoothStep.step_deriv_compact : HasCompactSupport (deriv step) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  have hne : deriv step x ≠ 0 := by simpa [Function.mem_support] using hx
  constructor
  · by_contra hleft
    have hlocal : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] step := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge hleft)] with y hy
      symm
      exact step_zero_of_nonpos hy.le
    have hd := hlocal.deriv_eq
    have : deriv step x = 0 := by simpa using hd.symm
    exact hne this
  · by_contra hright
    have hlocal : (fun _ : ℝ => (1 : ℝ)) =ᶠ[nhds x] step := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hright)] with y hy
      symm
      exact step_one_of_one_le (le_of_lt hy)
    have hd := hlocal.deriv_eq
    have : deriv step x = 0 := by simpa using hd.symm
    exact hne this

theorem SmoothStep.step_deriv_contDiff : ContDiff ℝ (⊤ : ℕ∞) (deriv step) := by
  exact (contDiff_infty_iff_deriv.mp step_contDiff).2

/-- The smooth step has a finite uniform bound for every finite collection of iterated
derivatives. Derivatives of positive order have compact support because the step is constant
outside the unit transition interval. -/
theorem step_iteratedDeriv_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ x : ℝ,
      |iteratedDeriv j step x| ≤ C := by
  obtain ⟨C, hC1, hC⟩ := exists_iteratedDeriv_bound SmoothStep.step_deriv_contDiff
    SmoothStep.step_deriv_compact N
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j
    rw [iteratedDeriv_zero]
    rw [abs_of_nonneg (step_nonneg x)]
    exact (step_le_one x).trans (le_max_left _ _)
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hderiv : iteratedDeriv j step x = iteratedDeriv (j - 1) (deriv step) x := by
      calc
        iteratedDeriv j step x = iteratedDeriv ((j - 1) + 1) step x := by
          congr 2
          omega
        _ = iteratedDeriv (j - 1) (deriv step) x := by rw [iteratedDeriv_succ']
    rw [hderiv]
    exact (hC (j - 1) (by omega) x).trans (le_max_right _ _)

end AVenhance.Infra.Cutoff
