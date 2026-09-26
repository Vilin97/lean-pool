/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Kappa Cap Arithmetic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

noncomputable section

namespace CKN.Core.Step4

private lemma inv_add_const_nondec {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hle : τ₁ ≤ τ₂) :
    (1 / τ₁ + 8 / 25)⁻¹ ≤ (1 / τ₂ + 8 / 25)⁻¹ := by
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ hle
  have hdiv : 1 / τ₂ ≤ 1 / τ₁ := one_div_le_one_div_of_le hτ₁ hle
  have hpos : 0 < 1 / τ₂ + 8 / 25 := by positivity
  have hsum : 1 / τ₂ + 8 / 25 ≤ 1 / τ₁ + 8 / 25 := by linarith only [hdiv]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hsum

/-- For `q > 5/2` the cap `min q (25/11)` is the base value `25/11`. -/
theorem min_q_twentyFive_div_eleven {q : ℝ} (hq : 5 / 2 < q) : min q (25 / 11 : ℝ) = 25 / 11 := by
  have h : (25 / 11 : ℝ) ≤ q := by
    have h' : (25 / 11 : ℝ) ≤ 5 / 2 := by norm_num
    linarith only [h', hq]
  exact min_eq_right h

/-- For `q > 5/2` the cap `min (25/11) q` is the base value `25/11`. -/
theorem min_twentyFive_div_eleven_q {q : ℝ} (hq : 5 / 2 < q) : min (25 / 11 : ℝ) q = 25 / 11 := by
  rw [min_comm]
  exact min_q_twentyFive_div_eleven hq



/-- At the base velocity `τ = 25/3` the capped exponent `min (25/11) q` is at most
`min κ(τ) q` for any `τ ≥ 25/3`. -/
theorem min_kappa_base_le {q τ : ℝ} (hτ : 25 / 3 ≤ τ) :
    min (25 / 11 : ℝ) q ≤ min ((1 / τ + 8 / 25)⁻¹) q := by
  have hpos : 0 < (25 / 3 : ℝ) := by norm_num
  have hkappa : (1 / (25 / 3 : ℝ) + 8 / 25)⁻¹ ≤ (1 / τ + 8 / 25)⁻¹ := inv_add_const_nondec hpos hτ
  have hbase : (1 / (25 / 3 : ℝ) + 8 / 25)⁻¹ = (25 / 11 : ℝ) := by norm_num
  rw [hbase] at hkappa
  exact min_le_min hkappa (le_refl q)

/-- The capped exponent is positive when both `τ` and `q` are positive. -/
theorem min_kappa_pos {q τ : ℝ} (hτ : 0 < τ) (hq : 0 < q) : 0 < min ((1 / τ + 8 / 25)⁻¹) q := by
  have hkappa : 0 < (1 / τ + 8 / 25)⁻¹ := by
    have hsum : 0 < 1 / τ + 8 / 25 := by positivity
    exact inv_pos.mpr hsum
  exact lt_min hkappa hq

end CKN.Core.Step4
