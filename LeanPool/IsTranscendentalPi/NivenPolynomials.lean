/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import LeanPool.IsTranscendentalPi.CalculusOnPoly

/-!
# Niven polynomials

The auxiliary polynomials `Fₚ = Xᵖ⁻¹ Tᵖ` and basic facts about their degree, used
to build the integer that drives the contradiction in Niven's proof.
-/

open Polynomial
open Complex

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- `Fₚ = Xᵖ⁻¹ Tᵖ`. -/
def Fp {R : Type*} [Semiring R] (T : R[X]) (p : ℕ) : R[X] := X^(p - 1) * T^p

/-- If `T ≠ 0`, then `deg(Fₚ) = (p - 1) + p deg(T)`. -/
lemma natDegree_Fp {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    (T : R[X]) (p : ℕ) (hT : T ≠ 0) :
    (Fp T p).natDegree = (p - 1) + p * T.natDegree := by
  rw [Fp, (monic_X_pow (p - 1)).natDegree_mul' (pow_ne_zero p hT), natDegree_X_pow, natDegree_pow]

/-- If `T ≠ 0`, then `deg(Fₚ⁽ⁱ⁾) ≤ (p - 1) + p deg(T) - i`. -/
lemma natDegree_iterate_derivative_Fp_le {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    (T : R[X]) (p i : ℕ) (hT : T ≠ 0) :
    ((derivative^[i]) (Fp T p)).natDegree ≤ (p - 1) + p * T.natDegree - i := by
  apply le_trans (natDegree_iterate_derivative (Fp T p) i)
  rw [natDegree_Fp T p hT]

/-- The `(p - 1)`-th coefficient of `Fₚ` is `T(0)ᵖ`. -/
lemma coeff_Fp_pred {R : Type*} [CommSemiring R] (T : R[X]) (p : ℕ) :
    (Fp T p).coeff (p - 1) = (T.coeff 0) ^ p := by
  simp [Fp, coeff_X_pow_mul', coeff_zero_eq_eval_zero]

/-- `Fₚ⁽ᵖ⁻¹⁾(0) = (p - 1)! * T(0)ᵖ`. -/
lemma coeff_zero_iterate_derivative_Fp_pred {R : Type*} [CommSemiring R] (T : R[X]) (p : ℕ) :
    ((derivative^[p - 1]) (Fp T p)).coeff 0 = (p - 1).factorial * (T.coeff 0) ^ p := by
  simp [coeff_iterate_derivative, Nat.descFactorial_self, coeff_Fp_pred T p]

/-- `P(0)` is the constant coefficient of `P`. -/
lemma aeval_zero_eq_cast_coeff_zero
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (P : R[X]) :
    aeval (0 : A) P = algebraMap R A (P.coeff 0) := by
  exact (coeff_zero_eq_aeval_zero' (A := A) P).symm

/-- If `T ≠ 0`, then `multₐ(Tᵖ) = p * multₐ(T)`. -/
lemma rootMultiplicity_npow (T : ℤ[X]) (a : ℂ) (p : ℕ) (hT : T ≠ 0) :
    rootMultiplicity a ((T.map (algebraMap ℤ ℂ))^p)
      = p * rootMultiplicity a (T.map (algebraMap ℤ ℂ)) := by
  have hmap : (T.map (algebraMap ℤ ℂ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (f := algebraMap ℤ ℂ)
      (hf := Int.cast_injective (α := ℂ))).2 hT
  have hpow : ((T.map (algebraMap ℤ ℂ))^p) ≠ 0 := pow_ne_zero _ hmap
  rw [rootMultiplicity_eq_multiplicity, if_neg hpow, rootMultiplicity_eq_multiplicity, if_neg hmap]
  exact (finiteMultiplicity_X_sub_C a hmap).multiplicity_pow (prime_X_sub_C a)

/-- If `T ≠ 0`, then `multₐ(Fₚ) = p - 1 + p * multₐ(T)` if `a = 0` and `p * multₐ(T)` otherwise. -/
lemma rootMultiplicity_Fp (T : ℤ[X]) (p : ℕ) (a : ℂ) (hT : T ≠ 0) :
    rootMultiplicity a ((Fp T p).map (algebraMap ℤ ℂ))
      = (if a = 0 then (p - 1) else 0) + p * rootMultiplicity a (T.map (algebraMap ℤ ℂ)) := by
  have hmap : (T.map (algebraMap ℤ ℂ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (f := algebraMap ℤ ℂ) (hf := Int.cast_injective (α := ℂ))).2 hT
  have hFp : (X^(p - 1) * (T.map (algebraMap ℤ ℂ))^p : ℂ[X]) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ X_ne_zero
    · exact pow_ne_zero _ hmap
  by_cases hzero : a = 0
  · subst hzero
    have hXpow : rootMultiplicity (0 : ℂ) (X^(p - 1) : ℂ[X]) = p - 1 := by
      simpa using (rootMultiplicity_X_sub_C_pow (a := (0 : ℂ)) (n := p - 1))
    rw [Fp, Polynomial.map_mul, Polynomial.map_pow]
    simp only [Polynomial.map_X, Polynomial.map_pow]
    rw [rootMultiplicity_mul (p := (X^(p - 1) : ℂ[X])) (q := (T.map (algebraMap ℤ ℂ))^p)
      (x := (0 : ℂ)) hFp, hXpow, rootMultiplicity_npow T (0 : ℂ) p hT]
    simp
  · have hXpow : rootMultiplicity a (X^(p - 1) : ℂ[X]) = 0 := by
      apply rootMultiplicity_eq_zero
      simpa [IsRoot, eval_X_pow] using (pow_ne_zero (p - 1) hzero)
    rw [if_neg hzero, Fp, Polynomial.map_mul, Polynomial.map_pow]
    simp only [Polynomial.map_X, Polynomial.map_pow]
    rw [rootMultiplicity_mul (p := (X^(p - 1) : ℂ[X])) (q := (T.map (algebraMap ℤ ℂ))^p)
      (x := a) hFp, hXpow, rootMultiplicity_npow T a p hT]

/-- `Sₚ,ᵢ` is defined so that `Fₚ⁽ⁱ⁾ = i! • Sₚ,ᵢ`. -/
def Sp {R : Type*} [Semiring R] (T : R[X]) (p i : ℕ) : R[X] :=
  ∑ j ∈ (derivative^[i] (Fp T p)).support, C (((j + i).choose i) • (Fp T p).coeff (j + i)) * X^j

/-- We define `Gₚ(T) = ∑ᵢ₌ₚᵈ (i! / p!) • Sₚ,ᵢ(T)`, where `d = deg(Fₚ)`. -/
def Gp {R : Type*} [Semiring R] (T : R[X]) (p : ℕ) : R[X] :=
  ∑ i ∈ Finset.Icc p (Fp T p).natDegree, (i.factorial / p.factorial) • (Sp T p i)

/-- `F_{p,d} = ∑ᵢ₌ₚᵈ Fₚ⁽ⁱ⁾`, with `d = deg(Fₚ)`. -/
def Fpd (T : ℤ[X]) (p : ℕ) : ℤ[X] := sumDeriv (Fp T p)

/-- The proof that `Fₚ⁽ⁱ⁾ = i! • Sₚ,ᵢ`. -/
lemma iterate_derivative_Fp_eq_factorial_Sp
    {R : Type*} [Semiring R] (T : R[X]) (p i : ℕ) :
    derivative^[i] (Fp T p) = i.factorial • Sp T p i := by
  simpa [Sp] using
    (iterate_derivative_eq_factorial_smul_sum (p := Fp T p) (k := i))

/-- If `multₐ(T) ≥ m`, then `F_{p,d}(a)` is expressed in terms of `Fₚ⁽ⁱ⁾(a)`. -/
lemma aeval_Fpd (T : ℤ[X]) (p m : ℕ) (a : ℂ) (hT : T ≠ 0)
    (hmT : m ≤ rootMultiplicity a (T.map (algebraMap ℤ ℂ))) :
    aeval a (Fpd T p)
      =
      ∑ i ∈ Finset.Icc  ((if a = 0 then (p - 1) else 0) + p * m)
                        (Fp T p).natDegree,
        aeval a ((derivative^[i]) (Fp T p)) := by
  have hmFp :
      (if a = 0 then p - 1 else 0) + p * m ≤
        rootMultiplicity a ((Fp T p).map (algebraMap ℤ ℂ)) := by
    rw [rootMultiplicity_Fp T p a hT]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left p hmT) (if a = 0 then p - 1 else 0)
  simpa [Fpd] using
    (aeval_sumDeriv_eq_sum_Icc
      (T := Fp T p)
      (a := a)
      (m := (if a = 0 then p - 1 else 0) + p * m)
      (hm := by simpa using hmFp))

/-- The definition of `∑ᵢ₌ₚᵈ Fₚ⁽ⁱ⁾` with `d = deg(Fₚ)`. -/
def sumStartpDerivFp {R : Type*} [Semiring R] (T : R[X]) (p : ℕ) : R[X]
  := ∑ i ∈ Finset.Icc p (Fp T p).natDegree, derivative^[i] (Fp T p)

/-- If `a` is a root of `T`, then `T ≠ 0`. -/
lemma TwithRootNotZero (T : ℤ[X]) (a : ℂ)
  (hroot : a ∈ T.aroots ℂ) : T ≠ 0 := by exact (Polynomial.mem_aroots.1 hroot).1

/-- If `a ≠ 0` and `a` is a root of `T`, then `F_{p,d} = ∑ᵢ₌ₚᵈ Fₚ⁽ⁱ⁾(a)`. -/
lemma aeval_Fpd_at_nonzero (T : ℤ[X]) (p : ℕ) (a : ℂ) (ha : a ≠ 0)
    (hroot : a ∈ T.aroots ℂ) : aeval a (Fpd T p) = aeval a (sumStartpDerivFp T p) := by
  have hroot' : 1 ≤ rootMultiplicity a (T.map (algebraMap ℤ ℂ)) := by
    rcases Polynomial.mem_aroots'.1 hroot with ⟨hT0, hroot0⟩
    exact Nat.succ_le_of_lt <|
      (Polynomial.rootMultiplicity_pos hT0).2
        (by simpa [Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq] using hroot0)
  simpa [ha, sumStartpDerivFp] using
    (aeval_Fpd T p 1 a (TwithRootNotZero T a hroot) hroot')

/-- If `0 < p` and `T ≠ 0`, then `F_{p,d}(0) = (p - 1)! T(0)ᵖ + ∑ᵢ₌ₚᵈ Fₚ⁽ⁱ⁾(0)`. -/
lemma aeval_Fpd_at_zero (T : ℤ[X]) (p : ℕ) (hp : 0 < p) (hT : T ≠ 0) :
    aeval (0 : ℂ) (Fpd T p)
      = (p - 1).factorial * (aeval (0 : ℂ) T) ^ p + aeval (0 : ℂ) (sumStartpDerivFp T p) := by
  rw [aeval_Fpd T p 0 (0 : ℂ) hT
      (Nat.zero_le (rootMultiplicity (0 : ℂ) (T.map (algebraMap ℤ ℂ))))]
  simp only [↓reduceIte, mul_zero, add_zero]
  have hdeg : p - 1 ≤ (Fp T p).natDegree := by
    rw [natDegree_Fp T p hT]
    exact Nat.le_add_right (p - 1) (p * T.natDegree)
  have hfirst :
      aeval (0 : ℂ) ((derivative^[p - 1]) (Fp T p))
        = (p - 1).factorial * (aeval (0 : ℂ) T) ^ p := by
    simpa [aeval_zero_eq_cast_coeff_zero, map_mul, map_pow] using
      congrArg (algebraMap ℤ ℂ) (coeff_zero_iterate_derivative_Fp_pred T p)
  rw [Finset.Icc_eq_cons_Ioc hdeg, Finset.sum_cons, hfirst,
    ← Finset.Icc_succ_left_eq_Ioc (p - 1) (Fp T p).natDegree]
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
  simp [sumStartpDerivFp, hp']

/-- `∑ᵢ bᵢ exp(aᵢ) ∫₀¹ aᵢ * exp(-(t aᵢ)) * T(t aᵢ) dt` is equal to
`F_{p,d}(0) * ∑ᵢ bᵢ exp(aᵢ) - ∑ᵢ bᵢ F_{p,d}(0)(aᵢ)`. -/
lemma intExpNegPoly_sum_simp (n p : ℕ) (T : ℤ[X]) (a b : Fin n → ℂ) :
  ∑ i : Fin n, b i * cexp (a i) * intExpNegPoly (Fp T p) (a i) =
    aeval 0 (Fpd T p) * ∑ i : Fin n, b i * cexp (a i) -
      ∑ i : Fin n, b i * aeval (a i) (Fpd T p) := by
  rw [Fpd]
  simp_rw [int_exp_neg_mul_poly, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    ac_rfl
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [mul_assoc, ← mul_assoc (cexp (a i)) (cexp (-a i)) (aeval (a i) (sumDeriv (Fp T p))),
      cexp_mul_cexp_neg, one_mul]

/-- `∑ᵢ₌ₚᵈ Fₚ⁽ⁱ⁾ = p! * Gₚ`. -/
lemma factorise_sumIteratedDerivPoly {R : Type*} [Semiring R] (T : R[X]) (p : ℕ) :
    sumStartpDerivFp T p = C (p.factorial : R) * (Gp T p) := by
  rw [sumStartpDerivFp, Gp, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [iterate_derivative_Fp_eq_factorial_Sp, ← natCast_mul,
    ← C_eq_natCast (R := R) (n := i.factorial)]
  conv_rhs => rw [← natCast_mul]
  rw [← C_eq_natCast (R := R) (n := i.factorial / p.factorial), ← mul_assoc, ← C_mul,
    ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.factorial_dvd_factorial (Finset.mem_Icc.mp hi).1)]
