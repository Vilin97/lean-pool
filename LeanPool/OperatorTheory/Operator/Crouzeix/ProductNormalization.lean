/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.PolynomialSupNormZero

/-!
# Normalize the Crouzeix product estimate

On an infinite compact control set, a positive-degree polynomial has positive
sup norm.  Exact degree-two homogeneity therefore reduces the remaining
Crouzeix--Palencia product estimate to polynomials of unit sup norm.

## Main declaration

* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized` --
  transfers the unit-sup-norm product estimate to every positive-degree
  polynomial.
-/

@[expose] public section

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- On an infinite compact set, it suffices to prove the sharp product bound
for positive-degree polynomials of unit sup norm. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hp : 0 < p.natDegree)
    (hnormalized : ∀ q : Polynomial ℂ, 0 < q.natDegree →
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  let m := polynomialSupNorm p K
  have hm0 : m ≠ 0 := by
    intro hm
    have hpzero : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p hK hKinf hm
    subst p
    simp only [Polynomial.natDegree_zero, lt_self_iff_false] at hp
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg p K) (Ne.symm hm0)
  let q : Polynomial ℂ := ((m : ℂ)⁻¹) • p
  have hscalar : ((m : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0)
  have hqdegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_smul p hscalar]
    exact hp
  have hqnorm : polynomialSupNorm q K = 1 := by
    dsimp only [q]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hqbound := hnormalized q hqdegree hqnorm
  have hpq : (m : ℂ) • q = p := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm0), one_smul]
  calc
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ =
        m ^ 2 * ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ := by
      rw [← hpq, norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    _ ≤ m ^ 2 * 1 := mul_le_mul_of_nonneg_left hqbound (sq_nonneg m)
    _ = polynomialSupNorm p K ^ 2 := by simp only [m, mul_one]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
