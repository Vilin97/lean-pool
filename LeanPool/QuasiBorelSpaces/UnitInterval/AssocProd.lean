/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Topology.UnitInterval

/-!
# LeanPool.QuasiBorelSpaces.UnitInterval.AssocProd

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.UnitInterval.AssocProd`.
-/


open scoped unitInterval

namespace unitInterval

/-- Helper function for `choose_assoc` -/
@[simps]
noncomputable def assocProd (p q : I) : I where
  val := (σ p * q) / σ (p * q)
  property := by
    have ⟨_, _⟩ := p.property
    have ⟨_, _⟩ := q.property
    simp only [unitInterval.coe_symm_eq, Set.Icc.coe_mul, Set.mem_Icc]
    by_cases h : (p : ℝ) < 1 ∨ (q : ℝ) < 1
    · rw [le_div_iff₀, div_le_iff₀]
      · constructor <;> nlinarith
      · cases h <;> nlinarith
      · cases h <;> nlinarith
    · simp only [not_or, not_lt] at h
      have h₁ : (p : ℝ) = 1 := le_antisymm p.property.2 h.1
      have h₂ : (q : ℝ) = 1 := le_antisymm q.property.2 h.2
      simp only [h₁, h₂, sub_self, mul_one, div_zero, le_refl, zero_le_one, and_self]

@[inherit_doc]
scoped infixr:80 " ⍟ " => assocProd

@[simp]
lemma mul_assocProd
    (p q : I)
    : σ (p * q) * (p ⍟ q) = σ p * q := by
  ext : 1
  wlog hp : (p : ℝ) < 1
  · have : (p : ℝ) = 1 := le_antisymm p.property.2 (by grind)
    simp only [
      Set.Icc.coe_mul, coe_symm_eq, this, one_mul,
      assocProd_coe, sub_self, zero_mul, zero_div, mul_zero]
  wlog hq : (q : ℝ) > 0
  · simp only [gt_iff_lt, coe_pos, not_lt, le_zero_iff] at hq
    simp only [
      hq, mul_zero, symm_zero, one_mul, assocProd_coe, coe_symm_eq,
      Set.Icc.coe_zero, Set.Icc.coe_one, div_one]
  simp only [Set.Icc.coe_mul, coe_symm_eq, assocProd_coe, mul_div]
  rw [div_eq_iff]
  · ring_nf
  · suffices p * (q : ℝ) < 1 by grind
    apply lt_of_lt_of_le
    · change p * q < 1 * (q : ℝ)
      simp only [one_mul, mul_lt_iff_lt_one_left, hq, hp]
    · simp only [one_mul, q.property.2]

@[simp]
lemma mul_symm_assocProd
    (p q : I)
    : σ (p * q) * σ (p ⍟ q) = σ q := by
  ext : 1
  wlog hp : (p : ℝ) < 1
  · have : (p : ℝ) = 1 := le_antisymm p.property.2 (by grind)
    simp only [
      Set.Icc.coe_mul, coe_symm_eq, this, one_mul, assocProd_coe,
      sub_self, zero_mul, zero_div, sub_zero, mul_one]
  wlog hq : (q : ℝ) > 0
  · simp only [gt_iff_lt, coe_pos, not_lt, le_zero_iff] at hq
    simp only [
      hq, mul_zero, symm_zero, one_mul, coe_symm_eq, assocProd_coe,
      Set.Icc.coe_zero, Set.Icc.coe_one, div_one, sub_zero]
  have hpq : 1 - p * (q : ℝ) > 0 := by
    suffices p * (q : ℝ) < 1 by grind
    apply lt_of_lt_of_le
    · change p * q < 1 * (q : ℝ)
      simp only [one_mul, mul_lt_iff_lt_one_left, hq, hp]
    · simp only [one_mul, q.property.2]
  have hpq' : 1 - p * (q : ℝ) ≠ 0 := by grind
  simp only [
    Set.Icc.coe_mul, coe_symm_eq, assocProd_coe,
    mul_sub, mul_one, mul_div]
  rw [← mul_right_cancel_iff_of_pos hpq]
  simp only [
    sub_mul, one_mul, isUnit_iff_ne_zero, ne_eq,
    hpq', not_false_eq_true, IsUnit.div_mul_cancel]
  ring_nf

@[simp]
lemma mul_symm_assocProd'
    (p q : I) (hpq : p < 1 ∨ q < 1)
    : p * σ (p ⍟ q) = q ⍟ p := by
  ext : 1
  wlog hq : (q : ℝ) > 0
  · simp only [gt_iff_lt, coe_pos, not_lt, le_zero_iff] at hq
    simp only [
      hq, Set.Icc.coe_mul, coe_symm_eq, assocProd_coe, Set.Icc.coe_zero, mul_zero,
      symm_zero, Set.Icc.coe_one, div_one, sub_zero, mul_one, one_mul, zero_mul]
  wlog hp : (p : ℝ) > 0
  · simp only [gt_iff_lt, coe_pos, not_lt, le_zero_iff] at hp
    simp only [
      hp, zero_mul, Set.Icc.coe_zero, assocProd_coe,
      coe_symm_eq, mul_zero, symm_zero, Set.Icc.coe_one, div_one]
  have hpq : 1 - q * (p : ℝ) ≠ 0 := by
    suffices q * (p : ℝ) < 1 by grind
    cases hpq with
    | inl hpq =>
      apply lt_of_lt_of_le
      · change q * p < q * (1 : ℝ)
        simp only [hq, mul_lt_mul_iff_right₀, coe_lt_one, hpq]
      · simp only [mul_one, q.property.2]
    | inr hpq =>
      apply lt_of_lt_of_le
      · change q * p < 1 * (p : ℝ)
        simp only [hp, mul_lt_mul_iff_left₀, coe_lt_one, hpq]
      · simp only [one_mul, p.property.2]
  simp only [Set.Icc.coe_mul, coe_symm_eq, assocProd_coe, mul_sub, mul_comm (p : ℝ) q]
  rw [eq_div_iff, sub_mul]
  · simp only [mul_one, mul_assoc]
    rw [div_mul_cancel₀]
    · ring_nf
    · exact hpq
  · exact hpq

end unitInterval
