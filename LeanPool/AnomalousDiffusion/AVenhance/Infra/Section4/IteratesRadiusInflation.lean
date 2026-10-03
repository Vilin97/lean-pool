/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Iterates Radius Inflation

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A small zeroth jet and an analytic positive-jet profile can use one common
small profile by enlarging the radius parameter by the inverse smallness. -/
theorem iterate_positive_radius_inflation (n : ℕ) (hn : 1 ≤ n)
    {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    r ^ n ≤ ρ * (r / ρ) ^ n := by
  have hrad : r ≤ r / ρ := (le_div_iff₀ hρ).mpr
    (mul_le_of_le_one_right hr hρ1)
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrad (n - 1)) hr
  have hn' : n = (n - 1) + 1 := by omega
  calc
    _ = r ^ (n - 1) * r := by
      conv_lhs => rw [hn', pow_succ]
    _ ≤ (r / ρ) ^ (n - 1) * r := hp
    _ = _ := by
      conv_rhs => rw [hn', pow_succ]
      field_simp

/-- Positive analytic jets inherit a common small prefactor after inflation. -/
theorem iterate_positive_profile_radius_inflation (n : ℕ) (hn : 1 ≤ n)
    {B r ρ f : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hf : |f| ≤ B * (n.factorial : ℝ) * r ^ n) :
    |f| ≤ (B * ρ) * (n.factorial : ℝ) * (r / ρ) ^ n := by
  have ht := mul_le_mul_of_nonneg_left (iterate_positive_radius_inflation n hn hr hρ hρ1)
    (by positivity : 0 ≤ B * (n.factorial : ℝ))
  exact hf.trans (by convert ht using 1; ring)

end AVenhance.Infra.Section4
