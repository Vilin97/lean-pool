/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Algebra.TrigSigns
import LeanPool.Erdos132WeiE2.Algebra.BezoutGenerated
import LeanPool.Erdos132WeiE2.Algebra.TanExpressions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Algebraic exclusions for the E2 diameter-heptagon pattern

This module converts the possible distance collisions to tangent-coordinate polynomials and
applies the generated Bézout certificates.
-/

namespace LeanPool.Erdos132WeiE2.Algebra

/-- The tangent-coordinate numerator of the E2 closure curve. -/
def closurePolynomial (x y : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 2 - 12 * x + y ^ 2 + 1

/-- The tangent-coordinate numerator forced by the distance collision `RA = Q`. -/
def pRQ (x y : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + x ^ 4 + 16 * x ^ 3 * y + 2 * x ^ 2 * y ^ 2 -
    30 * x ^ 2 - 16 * x * y + y ^ 2 + 1

/-- The tangent-coordinate numerator forced by the distance collision `RA = eC`. -/
def pRC (x y : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + 2 * x ^ 4 * y + x ^ 4 + 2 * x ^ 3 * y ^ 2 - 2 * x ^ 3 +
    2 * x ^ 2 * y ^ 2 - 30 * x ^ 2 + 2 * x * y ^ 2 - 2 * x + y ^ 2 - 2 * y + 1

/-- The tangent-coordinate numerator forced by the distance collision `RB = eC`. -/
def pBC (x y : ℝ) : ℝ :=
  x ^ 4 * y ^ 4 + 2 * x ^ 4 * y ^ 3 - 6 * x ^ 4 * y ^ 2 + 2 * x ^ 4 * y +
    x ^ 4 + 2 * x ^ 3 * y ^ 4 - 32 * x ^ 3 * y - 2 * x ^ 3 +
    2 * x ^ 2 * y ^ 4 + 20 * x ^ 2 * y ^ 2 - 30 * x ^ 2 +
    2 * x * y ^ 4 + 32 * x * y - 2 * x + y ^ 4 - 2 * y ^ 3 - 6 * y ^ 2 -
    2 * y + 1

/-- The tangent-coordinate numerator forced by the distance collision `RB = eA`. -/
def pBA (x y : ℝ) : ℝ :=
  (x - y) * (x * y + 1) * (x ^ 2 * y + x * y ^ 2 + 3 * x - y)

/-- Certified unit ideal for the collision `(RA, RB) = (Q, eC)`. -/
lemma exclude_ra_q_rb_ec (x y : ℝ)
    (hF : x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 2 - 12 * x + y ^ 2 + 1 = 0)
    (hRQ : pRQ x y = 0) (hBC : pBC x y = 0) : False := by
  have hRQ' : x ^ 4 * y ^ 2 + x ^ 4 + 16 * x ^ 3 * y + 2 * x ^ 2 * y ^ 2 -
      30 * x ^ 2 - 16 * x * y + y ^ 2 + 1 = 0 := by
    simpa only [pRQ] using hRQ
  have hBC' : x ^ 4 * y ^ 4 + 2 * x ^ 4 * y ^ 3 - 6 * x ^ 4 * y ^ 2 +
      2 * x ^ 4 * y + x ^ 4 + 2 * x ^ 3 * y ^ 4 - 32 * x ^ 3 * y - 2 * x ^ 3 +
      2 * x ^ 2 * y ^ 4 + 20 * x ^ 2 * y ^ 2 - 30 * x ^ 2 + 2 * x * y ^ 4 +
      32 * x * y - 2 * x + y ^ 4 - 2 * y ^ 3 - 6 * y ^ 2 - 2 * y + 1 = 0 := by
    simpa only [pBC] using hBC
  have hid := case1_bezout_identity x y
  rw [hF, hRQ', hBC'] at hid
  norm_num at hid

/-- Certified unit ideal for the collision `(RA, RB) = (Q, eA)`. -/
lemma exclude_ra_q_rb_ea (x y : ℝ)
    (hF : x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 2 - 12 * x + y ^ 2 + 1 = 0)
    (hRQ : pRQ x y = 0) (hBA : pBA x y = 0) : False := by
  have hRQ' : x ^ 4 * y ^ 2 + x ^ 4 + 16 * x ^ 3 * y + 2 * x ^ 2 * y ^ 2 -
      30 * x ^ 2 - 16 * x * y + y ^ 2 + 1 = 0 := by
    simpa only [pRQ] using hRQ
  have hBA' : (x - y) * (x * y + 1) *
      (x ^ 2 * y + x * y ^ 2 + 3 * x - y) = 0 := by
    simpa only [pBA] using hBA
  have hid := case2_bezout_identity x y
  rw [hF, hRQ', hBA'] at hid
  norm_num at hid

/-- Certified unit ideal for the collision `(RA, RB) = (eC, eA)`. -/
lemma exclude_ra_ec_rb_ea (x y : ℝ)
    (hF : x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 2 - 12 * x + y ^ 2 + 1 = 0)
    (hRC : pRC x y = 0) (hBA : pBA x y = 0) : False := by
  have hRC' : x ^ 4 * y ^ 2 + 2 * x ^ 4 * y + x ^ 4 + 2 * x ^ 3 * y ^ 2 -
      2 * x ^ 3 + 2 * x ^ 2 * y ^ 2 - 30 * x ^ 2 + 2 * x * y ^ 2 - 2 * x +
      y ^ 2 - 2 * y + 1 = 0 := by
    simpa only [pRC] using hRC
  have hBA' : (x - y) * (x * y + 1) *
      (x ^ 2 * y + x * y ^ 2 + 3 * x - y) = 0 := by
    simpa only [pBA] using hBA
  have hid := case3_bezout_identity x y
  rw [hF, hRC', hBA'] at hid
  norm_num at hid

lemma tan_dictionary (A B x y : ℝ)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2)) :
    Real.sin (A / 2) = 2 * x / (1 + x ^ 2) ∧
      Real.cos (A / 2) = (1 - x ^ 2) / (1 + x ^ 2) ∧
      Real.sin (A + B) = 2 * y / (1 + y ^ 2) ∧
      Real.cos (A + B) = (1 - y ^ 2) / (1 + y ^ 2) := by
  have hcosA : Real.cos (A / 2) ≠ -1 := by
    have hpos : 0 < Real.cos (A / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    linarith
  have hcosS : Real.cos (A + B) ≠ -1 := by
    have hpos : 0 < Real.cos ((A + B) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    have hdouble : Real.cos (A + B) ≠ -1 := by
      intro heq
      have hsquare := Real.cos_sq_add_sin_sq ((A + B) / 2)
      have hdoubleCos := Real.cos_two_mul_eq_one_sub ((A + B) / 2)
      rw [show 2 * ((A + B) / 2) = A + B by ring, heq] at hdoubleCos
      nlinarith
    exact hdouble
  constructor
  · rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq]
    rw [show A / 2 / 2 = A / 4 by ring, ← hx]
  constructor
  · rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (A / 2) hcosA]
    rw [show A / 2 / 2 = A / 4 by ring, ← hx]
  constructor
  · rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, ← hy]
  · rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (A + B) hcosS, ← hy]

lemma closure_implies_polynomial (A B x y : ℝ)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2))
    (hclosure : 2 * Real.sin (A / 2) * (1 + 2 * Real.cos (A + B)) = 1) :
    closurePolynomial x y = 0 := by
  obtain ⟨hsinA, _, _, hcosS⟩ := tan_dictionary A B x y hA hApi hS hSpi hx hy
  have hdx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hdy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  rw [hsinA, hcosS] at hclosure
  field_simp [hdx, hdy] at hclosure
  dsimp only [closurePolynomial]
  linear_combination -hclosure

lemma ra_eq_q_implies_pRQ (A B x y RA Q : ℝ)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2))
    (hRA : RA ^ 2 = 4 - 4 * Real.cos A - 2 * Real.cos B +
      4 * Real.cos (A + B) - 2 * Real.cos (2 * A + B))
    (hQ : Q ^ 2 = 3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B))
    (heq : RA = Q) : pRQ x y = 0 := by
  obtain ⟨hsinHalf, hcosHalf, hsinS, hcosS⟩ :=
    tan_dictionary A B x y hA hApi hS hSpi hx hy
  have hdx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hdy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  subst RA
  rw [cos_B_as_S_sub_A A B] at hRA hQ
  rw [cos_twoA_add_B_as_S_add_A A B] at hRA
  rw [cos_A_as_half A, sin_A_as_half A,
    hsinHalf, hcosHalf, hsinS, hcosS] at hRA hQ
  field_simp [hdx, hdy] at hRA hQ
  dsimp only [pRQ]
  linear_combination hRA - hQ

lemma ra_eq_ec_implies_pRC (A B C x y RA eC : ℝ)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2))
    (hRA : RA ^ 2 = 4 - 4 * Real.cos A - 2 * Real.cos B +
      4 * Real.cos (A + B) - 2 * Real.cos (2 * A + B))
    (heC : eC = 2 * Real.sin (C / 2)) (heq : RA = eC) : pRC x y = 0 := by
  obtain ⟨hsinHalf, hcosHalf, hsinS, hcosS⟩ :=
    tan_dictionary A B x y hA hApi hS hSpi hx hy
  have hdx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hdy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  have heCsq : eC ^ 2 = 2 - 2 * Real.cos C := by
    rw [heC, two_sin_half_sq]
  subst RA
  rw [heCsq, cos_C_as_sin_halfA_add_S A B C hsum, Real.sin_add,
    cos_B_as_S_sub_A A B, cos_twoA_add_B_as_S_add_A A B,
    cos_A_as_half A, sin_A_as_half A,
    hsinHalf, hcosHalf, hsinS, hcosS] at hRA
  field_simp [hdx, hdy] at hRA
  dsimp only [pRC]
  linear_combination hRA / 2

lemma rb_eq_ec_implies_pBC (A B C x y RB eC : ℝ)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2))
    (hRB : RB ^ 2 = 4 - 2 * Real.cos A - 4 * Real.cos B +
      4 * Real.cos (A + B) - 2 * Real.cos (A + 2 * B))
    (heC : eC = 2 * Real.sin (C / 2)) (heq : RB = eC) : pBC x y = 0 := by
  obtain ⟨hsinHalf, hcosHalf, hsinS, hcosS⟩ :=
    tan_dictionary A B x y hA hApi hS hSpi hx hy
  have hdx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hdy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  have heCsq : eC ^ 2 = 2 - 2 * Real.cos C := by
    rw [heC, two_sin_half_sq]
  subst RB
  rw [heCsq, cos_C_as_sin_halfA_add_S A B C hsum, Real.sin_add,
    cos_B_as_S_sub_A A B, cos_A_add_twoB_as_twoS_sub_A A B,
    cos_A_as_half A, sin_A_as_half A,
    hsinHalf, hcosHalf, hsinS, hcosS] at hRB
  field_simp [hdx, hdy] at hRB
  dsimp only [pBC]
  linear_combination hRB / 2

lemma rb_eq_ea_implies_pBA (A B x y RB eA : ℝ)
    (hA : 0 < A) (hApi : A < Real.pi)
    (hS : 0 < A + B) (hSpi : A + B < Real.pi)
    (hx : x = Real.tan (A / 4)) (hy : y = Real.tan ((A + B) / 2))
    (hRB : RB ^ 2 = 4 - 2 * Real.cos A - 4 * Real.cos B +
      4 * Real.cos (A + B) - 2 * Real.cos (A + 2 * B))
    (heA : eA = 2 * Real.sin (A / 2)) (heq : RB = eA) : pBA x y = 0 := by
  obtain ⟨hsinHalf, hcosHalf, hsinS, hcosS⟩ :=
    tan_dictionary A B x y hA hApi hS hSpi hx hy
  have hdx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hdy : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
  subst RB
  rw [heA, cos_B_as_S_sub_A A B, cos_A_add_twoB_as_twoS_sub_A A B,
    cos_A_as_half A, sin_A_as_half A,
    hsinHalf, hcosHalf, hsinS, hcosS] at hRB
  field_simp [hdx, hdy] at hRB
  dsimp only [pBA]
  linear_combination -hRB / 16

end LeanPool.Erdos132WeiE2.Algebra
