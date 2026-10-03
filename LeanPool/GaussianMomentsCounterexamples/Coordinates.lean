/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Explicit polynomials and normalized complex Gaussian coordinates. -/

public section

noncomputable section
namespace GaussianMomentsCounterexamples
open MvPolynomial

/-- Natural complex coordinates are ordered `W, Z, T`. -/
@[expose] def naturalP3 : MvPolynomial (Fin 3) ℂ :=
  (1 + X 1) * (X 0 - C (1 / 2) * (2 + X 1) * X 2 ^ 2)
/-- Natural complex coordinates are ordered `W₁, Z₁, W₂, Z₂`. -/
@[expose] def naturalP4 : MvPolynomial (Fin 4) ℂ :=
  (1 + X 3) * (X 0 * (1 - X 1) + X 2)

theorem naturalP3_expansion : naturalP3 =
    X 0 + X 0 * X 1 - X 2 ^ 2 - C (3 / 2) * X 1 * X 2 ^ 2 -
      C (1 / 2) * X 1 ^ 2 * X 2 ^ 2 := by
  unfold naturalP3
  have h : (C (3 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) = 3 * C (1 / 2) := by
    rw [← map_ofNat C, ← map_mul]
    norm_num
  have h₂ : (2 : MvPolynomial (Fin 3) ℂ) * C (1 / 2) = 1 := by
    rw [← map_ofNat C, ← map_mul]
    norm_num
  rw [h]
  linear_combination -(X 2 ^ 2) * h₂

theorem naturalP4_expansion : naturalP4 =
    X 0 - X 0 * X 1 + X 2 + X 0 * X 3 - X 0 * X 1 * X 3 + X 2 * X 3 := by
  unfold naturalP4
  ring

/-- Exponent vector for a monomial in three natural coordinates. -/
def exp3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem exp3_inj (a b c d e f : ℕ) :
    exp3 a b c = exp3 d e f ↔ a = d ∧ b = e ∧ c = f := by
  simp [exp3, Finsupp.ext_iff, Fin.forall_fin_succ]

theorem naturalP3_monomials : naturalP3 =
    monomial (exp3 1 0 0) 1 + monomial (exp3 1 1 0) 1 +
    monomial (exp3 0 0 2) (-1) + monomial (exp3 0 1 2) (-(3/2)) +
    monomial (exp3 0 2 2) (-(1/2)) := by
  rw [naturalP3_expansion]
  simp only [exp3, Finsupp.single_zero, add_zero, zero_add, X,
    monomial_mul_monomial, monomial_pow, C_mul_monomial, map_neg, Finsupp.smul_single,
      smul_eq_mul]
  simp only [mul_one, one_pow, sub_eq_add_neg]

theorem naturalP3_support : naturalP3.support =
    {exp3 1 0 0, exp3 1 1 0, exp3 0 0 2, exp3 0 1 2, exp3 0 2 2} := by
  classical
  rw [naturalP3_monomials]
  ext d
  by_cases h₁ : d = exp3 1 0 0
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp3_inj]
  by_cases h₂ : d = exp3 1 1 0
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp3_inj]
  by_cases h₃ : d = exp3 0 0 2
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp3_inj]
  by_cases h₄ : d = exp3 0 1 2
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp3_inj]
  by_cases h₅ : d = exp3 0 2 2
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp3_inj]
  simp [mem_support_iff, coeff_monomial, h₁, h₂, h₃, h₄, h₅,
    Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄, Ne.symm h₅]

theorem naturalP3_support_card : naturalP3.support.card = 5 := by
  rw [naturalP3_support]
  simp [exp3_inj]

theorem naturalP3_totalDegree : naturalP3.totalDegree = 4 := by
  rw [totalDegree, naturalP3_support]
  norm_num [exp3, Finsupp.sum_add_index, Finsupp.sum_single_index]

/-- Exponent vector for a monomial in four natural coordinates. -/
def exp4 (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c + Finsupp.single 3 d

@[simp] theorem exp4_inj (a b c d e f g h : ℕ) :
    exp4 a b c d = exp4 e f g h ↔ a = e ∧ b = f ∧ c = g ∧ d = h := by
  simp [exp4, Finsupp.ext_iff, Fin.forall_fin_succ]

theorem naturalP4_monomials : naturalP4 =
    monomial (exp4 1 0 0 0) 1 + monomial (exp4 1 1 0 0) (-1) +
    monomial (exp4 0 0 1 0) 1 + monomial (exp4 1 0 0 1) 1 +
    monomial (exp4 1 1 0 1) (-1) + monomial (exp4 0 0 1 1) 1 := by
  rw [naturalP4_expansion]
  simp [exp4, X, monomial_mul_monomial, sub_eq_add_neg]

theorem naturalP4_support : naturalP4.support =
    {exp4 1 0 0 0, exp4 1 1 0 0, exp4 0 0 1 0, exp4 1 0 0 1, exp4 1 1 0 1, exp4 0 0 1 1} := by
  classical
  rw [naturalP4_monomials]
  ext d
  by_cases h0 : d = exp4 1 0 0 0
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  by_cases h1 : d = exp4 1 1 0 0
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  by_cases h2 : d = exp4 0 0 1 0
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  by_cases h3 : d = exp4 1 0 0 1
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  by_cases h4 : d = exp4 1 1 0 1
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  by_cases h5 : d = exp4 0 0 1 1
  · subst d; norm_num [mem_support_iff, map_add, coeff_monomial, exp4_inj]
  simp [mem_support_iff, coeff_monomial, h0, h1, h2, h3, h4, h5,
    Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]

theorem naturalP4_support_card : naturalP4.support.card = 6 := by
  rw [naturalP4_support]
  simp [exp4_inj]

theorem naturalP4_totalDegree : naturalP4.totalDegree = 3 := by
  rw [totalDegree, naturalP4_support]
  norm_num [exp4, Finsupp.sum_add_index, Finsupp.sum_single_index]

theorem naturalP3_ne_zero : naturalP3 ≠ 0 := by
  intro h
  have := naturalP3_support_card
  simp [h] at this

theorem naturalP4_ne_zero : naturalP4 ≠ 0 := by
  intro h
  have := naturalP4_support_card
  simp [h] at this

/-- The normalization used in the manuscript. -/
@[expose] def normalization : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma normalization_sq : normalization ^ 2 = 1 / 2 := by
  unfold normalization
  rw [inv_pow, ← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

/-- The normalized complex coordinate (Xᵢ + iXⱼ)/√2. -/
@[expose] def normalizedZ {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) ℂ :=
  C normalization * (X i + C Complex.I * X j)

/-- The conjugate normalized coordinate (Xᵢ - iXⱼ)/√2. -/
@[expose] def normalizedW {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) ℂ :=
  C normalization * (X i - C Complex.I * X j)

lemma recoverX {n : ℕ} (i j : Fin n) :
    C normalization * (normalizedW i j + normalizedZ i j) = X i := by
  unfold normalizedW normalizedZ
  ring_nf
  simp only [← map_pow, normalization_sq]
  have h : (C (1 / 2 : ℂ) : MvPolynomial (Fin n) ℂ) * 2 = 1 := by
    rw [← map_ofNat C, ← map_mul]; norm_num
  linear_combination (X i) * h

lemma recoverY {n : ℕ} (i j : Fin n) :
    C (Complex.I * normalization) * (normalizedW i j - normalizedZ i j) = X j := by
  unfold normalizedW normalizedZ
  rw [map_mul]
  ring_nf
  simp only [← map_pow, normalization_sq, Complex.I_sq, map_neg, map_one]
  have h : (C (1 / 2 : ℂ) : MvPolynomial (Fin n) ℂ) * 2 = 1 := by
    rw [← map_ofNat C, ← map_mul]; norm_num
  linear_combination (X j) * h

lemma recombineW {n : ℕ} (a b : MvPolynomial (Fin n) ℂ) :
    C normalization * (C normalization * (a + b) -
      C Complex.I * (C (Complex.I * normalization) * (a - b))) = a := by
  rw [map_mul]
  ring_nf
  simp only [← map_pow, normalization_sq, Complex.I_sq, map_neg, map_one]
  have h : (C (1 / 2 : ℂ) : MvPolynomial (Fin n) ℂ) * 2 = 1 := by
    rw [← map_ofNat C, ← map_mul]; norm_num
  linear_combination a * h

lemma recombineZ {n : ℕ} (a b : MvPolynomial (Fin n) ℂ) :
    C normalization * (C normalization * (a + b) +
      C Complex.I * (C (Complex.I * normalization) * (a - b))) = b := by
  rw [map_mul]
  ring_nf
  simp only [← map_pow, normalization_sq, Complex.I_sq, map_neg, map_one]
  have h : (C (1 / 2 : ℂ) : MvPolynomial (Fin n) ℂ) * 2 = 1 := by
    rw [← map_ofNat C, ← map_mul]; norm_num
  linear_combination b * h

/-- Substitution from natural complex coordinates into the real-coordinate polynomial ring. -/
@[expose] def normalizedSub3 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![normalizedW 0 1, normalizedZ 0 1, X 2]

/-- Substitute two normalized conjugate pairs into four real coordinates. -/
@[expose] def normalizedSub4 : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![normalizedW 0 1, normalizedZ 0 1, normalizedW 2 3, normalizedZ 2 3]

/-- Recover three original coordinates from the natural complex coordinates. -/
@[expose] def inverseSub3 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![C normalization * (X 0 + X 1),
    C (Complex.I * normalization) * (X 0 - X 1), X 2]

/-- Recover four original coordinates from two natural conjugate pairs. -/
@[expose] def inverseSub4 : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![C normalization * (X 0 + X 1),
    C (Complex.I * normalization) * (X 0 - X 1),
    C normalization * (X 2 + X 3),
    C (Complex.I * normalization) * (X 2 - X 3)]

/-- The explicit three-variable counterexample, on the original real coordinates. -/
@[expose] def P3 : MvPolynomial (Fin 3) ℂ := normalizedSub3 naturalP3

/-- The linear multiplier witnessing nonvanishing mixed moments in three dimensions. -/
@[expose] def Q3 : MvPolynomial (Fin 3) ℂ := normalizedZ 0 1

/-- The explicit four-variable counterexample, on the original real coordinates. -/
@[expose] def P4 : MvPolynomial (Fin 4) ℂ := normalizedSub4 naturalP4

/-- The linear multiplier witnessing nonvanishing mixed moments in four dimensions. -/
@[expose] def Q4 : MvPolynomial (Fin 4) ℂ := normalizedZ 2 3

end GaussianMomentsCounterexamples
