/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic

/-!
# Square classes for the incidence auxiliary curve

This file proves the polynomial and rational-function-field algebra behind geometric integrality
of the off-diagonal incidence curve.  The remaining coordinate-ring normal-form argument is
stated separately in `BGS.Markoff.Incidence`.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- A nonunit squarefree element of a UFD does not become a square in its fraction field. -/
lemma not_isSquare_algebraMap_of_squarefree_not_isUnit
    {R Q : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field Q] [Algebra R Q] [IsFractionRing R Q]
    {f : R} (hsq : Squarefree f) (hf : ¬ IsUnit f) :
    ¬ IsSquare (algebraMap R Q f) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, b, hab, hrepr⟩ := IsFractionRing.exists_reduced_fraction R x
  have hbQ : algebraMap R Q (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hmap :
      algebraMap R Q (f * (b : R) ^ 2) = algebraMap R Q (a ^ 2) := by
    simp only [map_mul, map_pow]
    rw [hx, ← hrepr, IsFractionRing.mk'_eq_div]
    field_simp [hbQ]
  have heq : f * (b : R) ^ 2 = a ^ 2 :=
    FaithfulSMul.algebraMap_injective R Q hmap
  have hfa2 : f ∣ a ^ 2 := ⟨(b : R) ^ 2, heq.symm⟩
  have hfa : f ∣ a := (hsq.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hfa2
  obtain ⟨c, hac⟩ := hfa
  have heq2 : (b : R) ^ 2 = f * c ^ 2 := by
    apply mul_left_cancel₀ hsq.ne_zero
    calc
      f * (b : R) ^ 2 = a ^ 2 := heq
      _ = (f * c) ^ 2 := by rw [hac]
      _ = f * (f * c ^ 2) := by ring
  have hfb2 : f ∣ (b : R) ^ 2 := ⟨c ^ 2, heq2⟩
  have hfb : f ∣ (b : R) :=
    (hsq.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hfb2
  exact hf (hab ⟨c, hac⟩ hfb)

/-- The twofold-cover polynomial whose square root is the auxiliary `lambda` coordinate. -/
def incidenceBranchPolynomial (a : K) : K[X] :=
  C (9 * a ^ 2 - 4) * X ^ 2 - C (4 * a ^ 2)

lemma incidenceBranchPolynomial_natDegree {a : K} (hA : 9 * a ^ 2 - 4 ≠ 0) :
    (incidenceBranchPolynomial a).natDegree = 2 := by
  rw [incidenceBranchPolynomial, natDegree_sub_C,
    natDegree_C_mul_X_pow 2 (9 * a ^ 2 - 4) hA]

lemma incidenceBranchPolynomial_not_isUnit {a : K} (hA : 9 * a ^ 2 - 4 ≠ 0) :
    ¬ IsUnit (incidenceBranchPolynomial a) :=
  not_isUnit_of_natDegree_pos _ <| by
    rw [incidenceBranchPolynomial_natDegree hA]
    norm_num

/-- The branch polynomials for two parameters have an explicit constant Bezout combination. -/
lemma incidenceBranchPolynomial_linearCombination (a b : K) :
    C (9 * b ^ 2 - 4) * incidenceBranchPolynomial a -
        C (9 * a ^ 2 - 4) * incidenceBranchPolynomial b =
      C (16 * (a ^ 2 - b ^ 2)) := by
  simp only [incidenceBranchPolynomial]
  ring_nf
  rw [← C_mul, ← C_neg, ← C_mul, ← C_add]
  congr 1
  ring

/-- Away from characteristic two, distinct parameter squares give coprime branch polynomials. -/
lemma incidenceBranchPolynomial_isCoprime
    (h2 : (2 : K) ≠ 0) {a b : K} (hab : a ^ 2 ≠ b ^ 2) :
    IsCoprime (incidenceBranchPolynomial a) (incidenceBranchPolynomial b) := by
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  have hc : (16 * (a ^ 2 - b ^ 2) : K) ≠ 0 :=
    mul_ne_zero h16 (sub_ne_zero.mpr hab)
  let c : K := 16 * (a ^ 2 - b ^ 2)
  refine ⟨C c⁻¹ * C (9 * b ^ 2 - 4), -(C c⁻¹ * C (9 * a ^ 2 - 4)), ?_⟩
  calc
    (C c⁻¹ * C (9 * b ^ 2 - 4)) * incidenceBranchPolynomial a +
        -(C c⁻¹ * C (9 * a ^ 2 - 4)) * incidenceBranchPolynomial b =
      C c⁻¹ *
        (C (9 * b ^ 2 - 4) * incidenceBranchPolynomial a -
          C (9 * a ^ 2 - 4) * incidenceBranchPolynomial b) := by ring
    _ = C c⁻¹ * C c := by rw [incidenceBranchPolynomial_linearCombination]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, map_one]

/-- Each branch polynomial is separable under exactly the nondegeneracy hypotheses used in the
incidence graph. -/
lemma incidenceBranchPolynomial_separable
    (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (hA : 9 * a ^ 2 - 4 ≠ 0) :
    (incidenceBranchPolynomial a).Separable := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have hquot : (4 * a ^ 2 / (9 * a ^ 2 - 4) : K) ≠ 0 :=
    div_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 ha)) hA
  have hsep :
      (X ^ 2 - C (4 * a ^ 2 / (9 * a ^ 2 - 4)) : K[X]).Separable :=
    separable_X_pow_sub_C _ h2 hquot
  have hunit : IsUnit (C (9 * a ^ 2 - 4) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hA)
  have heq :
      incidenceBranchPolynomial a =
        C (9 * a ^ 2 - 4) *
          (X ^ 2 - C (4 * a ^ 2 / (9 * a ^ 2 - 4))) := by
    simp only [incidenceBranchPolynomial, mul_sub]
    rw [← C_mul]
    rw [mul_div_cancel₀ (4 * a ^ 2) hA]
  rw [heq]
  exact hsep.unit_mul hunit

/-- The product has no repeated irreducible factor.  This is the polynomial shadow of the
independence of the two quadratic square classes. -/
lemma incidenceBranchPolynomial_product_squarefree
    (h2 : (2 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    Squarefree (incidenceBranchPolynomial a * incidenceBranchPolynomial b) := by
  exact ((incidenceBranchPolynomial_separable h2 ha hA).mul
    (incidenceBranchPolynomial_separable h2 hb hB)
    (incidenceBranchPolynomial_isCoprime h2 hab)).squarefree

/-- The three nonzero elements of the span of the two branch square classes are nonsquares in the
rational function field.  Equivalently, the two classes are linearly independent over `ZMod 2`. -/
lemma incidenceBranchSquareClasses_independent_ratFunc
    (h2 : (2 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) (incidenceBranchPolynomial a)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K) (incidenceBranchPolynomial b)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K)
        (incidenceBranchPolynomial a * incidenceBranchPolynomial b)) := by
  have hsqA := (incidenceBranchPolynomial_separable h2 ha hA).squarefree
  have hsqB := (incidenceBranchPolynomial_separable h2 hb hB).squarefree
  have hsqAB := incidenceBranchPolynomial_product_squarefree h2 ha hb hA hB hab
  refine ⟨not_isSquare_algebraMap_of_squarefree_not_isUnit hsqA
      (incidenceBranchPolynomial_not_isUnit hA),
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqB
      (incidenceBranchPolynomial_not_isUnit hB), ?_⟩
  apply not_isSquare_algebraMap_of_squarefree_not_isUnit hsqAB
  intro hunit
  exact incidenceBranchPolynomial_not_isUnit hA (IsUnit.mul_iff.mp hunit).1

/-- Equality of the squared branch locations forces equality of the parameter squares. -/
lemma incidenceBranchLocation_injective
    (h2 : (2 : K) ≠ 0) {a b : K}
    (h : a ^ 2 * (9 * b ^ 2 - 4) = b ^ 2 * (9 * a ^ 2 - 4)) :
    a ^ 2 = b ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  apply (mul_left_cancel₀ h4)
  calc
    4 * a ^ 2 = -(a ^ 2 * (9 * b ^ 2 - 4) - 9 * a ^ 2 * b ^ 2) := by ring
    _ = -(b ^ 2 * (9 * a ^ 2 - 4) - 9 * a ^ 2 * b ^ 2) := by rw [h]
    _ = 4 * b ^ 2 := by ring

end

end BGS.Markoff
