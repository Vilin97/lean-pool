/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
### The archimedean Hilbert symbol over `ℝ`

Over the reals the Hilbert symbol `(a,b)_ℝ` is `-1` exactly when both `a` and `b`
are negative, and `1` otherwise (for nonzero arguments). Geometrically, the conic
`z² - a x² - b y² = 0` has a nonzero real point precisely when at least one of
`a, b` is positive: a positive `a` gives `(√a, 1, 0)`, a positive `b` gives
`(√b, 0, 1)`, while two negative coefficients force `z² ≤ 0`, hence `z = x = y = 0`.
-/

public section

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable

-- Theorem: over `ℝ`, for nonzero `a` and `b`, `hilbertSym a b = 1` iff `0 < a ∨ 0 < b`,
-- and `hilbertSym a b = -1` otherwise.
theorem hilbertSym_real_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1 := by
  have hne : ¬ (a = 0 ∨ b = 0) := by tauto
  have key : (∃ z x y : ℝ, (z, x, y) ≠ (0, 0, 0) ∧
      z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) ↔ 0 < a ∨ 0 < b := by
    constructor
    · rintro ⟨z, x, y, hne0, heq⟩
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      have ha_neg : a < 0 := lt_of_le_of_ne hcon.1 ha
      have hb_neg : b < 0 := lt_of_le_of_ne hcon.2 hb
      have hax : a * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_neg.le (sq_nonneg x)
      have hby : b * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb_neg.le (sq_nonneg y)
      have hz2 : z ^ 2 = 0 := by nlinarith [sq_nonneg z]
      have hx2 : x ^ 2 = 0 := by
        have hax0 : a * x ^ 2 = 0 := by nlinarith [hax, hby]
        exact (mul_eq_zero.mp hax0).resolve_left ha
      have hy2 : y ^ 2 = 0 := by
        have hby0 : b * y ^ 2 = 0 := by nlinarith [hax, hby]
        exact (mul_eq_zero.mp hby0).resolve_left hb
      have hz : z = 0 := sq_eq_zero_iff.mp hz2
      have hx : x = 0 := sq_eq_zero_iff.mp hx2
      have hy : y = 0 := sq_eq_zero_iff.mp hy2
      exact hne0 (by simp [hz, hx, hy])
    · rintro (ha' | hb')
      · exact ⟨Real.sqrt a, 1, 0, by simp, by simp [Real.sq_sqrt ha'.le]⟩
      · exact ⟨Real.sqrt b, 0, 1, by simp, by simp [Real.sq_sqrt hb'.le]⟩
  unfold hilbertSym
  rw [ite_eq_right hne]
  by_cases h : 0 < a ∨ 0 < b
  · rw [ite_eq_left (key.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hs => h (key.mp hs)), ite_eq_right h]

-- Theorem: the real Hilbert symbol is multiplicative in its first argument.
theorem hilbertSym_real_mul_left (a a' b : ℝ) :
    hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b := by
  by_cases hb : b = 0
  · simp [hb, hilbertSym_zero_right]
  by_cases ha : a = 0
  · simp [ha, hilbertSym_zero_left]
  by_cases ha' : a' = 0
  · simp [ha', hilbertSym_zero_left]
  rw [hilbertSym_real_eq (mul_ne_zero ha ha') hb,
    hilbertSym_real_eq ha hb, hilbertSym_real_eq ha' hb]
  by_cases hbpos : 0 < b
  · rw [ite_eq_left (Or.inr hbpos), ite_eq_left (Or.inr hbpos), ite_eq_left (Or.inr hbpos)]
    norm_num
  · by_cases hpa : 0 < a
    · by_cases hpa' : 0 < a'
      · rw [ite_eq_left (Or.inl (mul_pos hpa hpa')), ite_eq_left (Or.inl hpa),
          ite_eq_left (Or.inl hpa')]
        norm_num
      · have ha'_neg : a' < 0 := lt_of_le_of_ne (le_of_not_gt hpa') ha'
        have hneg : ¬ (0 < a * a' ∨ 0 < b) := by
          rw [not_or]
          exact ⟨not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hpa ha'_neg)), hbpos⟩
        rw [ite_eq_right hneg, ite_eq_left (Or.inl hpa), ite_eq_right (by tauto)]
        norm_num
    · have ha_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
      by_cases hpa' : 0 < a'
      · have hneg : ¬ (0 < a * a' ∨ 0 < b) := by
          rw [not_or]
          exact ⟨not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos ha_neg hpa')), hbpos⟩
        rw [ite_eq_right hneg, ite_eq_right (by tauto), ite_eq_left (Or.inl hpa')]
        norm_num
      · have ha'_neg : a' < 0 := lt_of_le_of_ne (le_of_not_gt hpa') ha'
        rw [ite_eq_left (Or.inl (mul_pos_of_neg_of_neg ha_neg ha'_neg)),
          ite_eq_right (by tauto), ite_eq_right (by tauto)]
        norm_num

/-- The real numbers carry a bilinear Hilbert symbol. -/
instance : HasBilinHilbertSym ℝ :=
  ⟨fun {a a' b} => hilbertSym_real_mul_left a a' b⟩

end HasseMinkowski
