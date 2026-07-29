/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedGaussKernelIntegral

/-!
# Gauss Digamma Vertical Sqrt Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Real Set

namespace NumberField.Odlyzko

theorem norm_gaussDigammaIntegrand_vertical_le_four_div
    {σ t x : ℝ} (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤ 4 / x := by
  have hden : x / 2 ≤ 1 - Real.exp (-x) :=
    half_mul_le_one_sub_exp_neg hx.le hx1
  have hnum :
      Real.exp (-x) + Real.exp (-σ * x) ≤ 2 := by
    have hsecond : Real.exp (-σ * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        simp_all)
    linarith
  calc
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
        (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)) :=
      norm_gaussDigammaIntegrand_vertical_le σ t hx
    _ ≤ 2 / (x / 2) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 / x := by grind

theorem norm_gaussDigammaIntegrand_vertical_le_sqrt
    {σ t x : ℝ} (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      4 * Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x) := by
  let N : ℝ := ‖(σ : ℂ) + t * I - 1‖
  have hN : 0 ≤ N := norm_nonneg _
  by_cases hsmall : N * x ≤ 1
  · have hlocal :
        ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤ 4 * N := by
      apply norm_gaussDigammaIntegrand_le_local
        (s := (σ : ℂ) + t * I) hx hx1
      grind
    have hNsqrt : N ≤ Real.sqrt (N / x) := by
      rw [Real.le_sqrt hN (div_nonneg hN hx.le)]
      apply (le_div_iff₀ hx).mpr
      nlinarith
    grind
  · have hlarge : 1 ≤ N * x := le_of_not_ge hsmall
    have hinvSqrt : 1 / x ≤ Real.sqrt (N / x) := by
      rw [Real.le_sqrt (by positivity) (div_nonneg hN hx.le)]
      rw [div_pow]
      rw [div_le_div_iff₀ (sq_pos_of_pos hx) hx]
      nlinarith
    change
      ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
        4 * Real.sqrt (N / x)
    exact
      (norm_gaussDigammaIntegrand_vertical_le_four_div hσ hx hx1).trans
        (by
          grind)

end NumberField.Odlyzko
