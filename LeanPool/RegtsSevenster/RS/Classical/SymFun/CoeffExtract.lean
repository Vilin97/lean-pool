/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.Bialternant

/-!
# Coefficient extraction from alternants

The coefficient of the diagonal monomial in a power alternant with
injective exponents is `1`: distinct permutations contribute
distinct monomials, and only the identity hits the diagonal.
-/

namespace RS

open Finset MvPolynomial Equiv

variable {k : ℕ}

/-- Evaluation of a sum of single-point Finsupps. -/
theorem sum_single_apply (c : Fin k → ℕ) (j : Fin k) :
    (∑ i, Finsupp.single i (c i)) j = c j := by
  classical
  rw [Finsupp.finsetSum_apply]
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i : Fin k => (Finsupp.single i (c i)) j) j
    (fun b _ hb => Finsupp.single_eq_of_ne (Ne.symm hb))
    (fun h => absurd (Finset.mem_univ j) h)
  rw [h, Finsupp.single_eq_same]

/-- Products of variable powers are monomials. -/
theorem prod_pow_eq_monomial (c : Fin k → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (c i)) =
      monomial (∑ i, Finsupp.single i (c i)) (1 : ℂ) := by
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    X_pow_eq_monomial (n := i) (e := c i))]
  rw [← monomial_sum_prod]
  rw [Finset.prod_const_one]

/-- **The diagonal coefficient of a power alternant** with
injective exponents is `1`. -/
theorem alternant_coeff (e : Fin k → ℕ)
    (hinj : Function.Injective e) :
    MvPolynomial.coeff (∑ i, Finsupp.single i (e i))
      ((Matrix.of fun i j : Fin k =>
        (X j : MvPolynomial (Fin k) ℂ) ^ (e i)).det) = 1 := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_congr rfl
    (fun (τ : Equiv.Perm (Fin k)) (_ : τ ∈ Finset.univ) =>
      show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          ∏ i, (Matrix.of fun i j : Fin k =>
            (X j : MvPolynomial (Fin k) ℂ) ^ (e i)) (τ i) i =
        ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) *
          monomial (∑ i, Finsupp.single i (e (τ i))) (1 : ℂ)
        from by
      rw [show (∏ i, (Matrix.of fun i j : Fin k =>
          (X j : MvPolynomial (Fin k) ℂ) ^ (e i)) (τ i) i) =
        ∏ i, (X i : MvPolynomial (Fin k) ℂ) ^ (e (τ i))
        from rfl]
      rw [prod_pow_eq_monomial])]
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))
    (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · rw [show ((Equiv.Perm.sign (1 : Equiv.Perm (Fin k)) : ℤ) :
        MvPolynomial (Fin k) ℂ) = 1 from by
      rw [map_one]
      exact Int.cast_one]
    rw [one_mul, coeff_monomial]
    rw [if_pos (Finset.sum_congr rfl fun i _ => by
      rw [Equiv.Perm.one_apply])]
  · have hne : (∑ i, Finsupp.single i (e (τ i))) ≠
        ∑ i, Finsupp.single i (e i) := by
      intro heq
      apply hτ
      refine Equiv.ext fun j => ?_
      have h1 := congrArg (fun w : Fin k →₀ ℕ => w j) heq
      rw [sum_single_apply, sum_single_apply] at h1
      exact hinj h1
    rw [show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin k) ℂ) =
        MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : ℂ) from by simp,
      MvPolynomial.coeff_C_mul, coeff_monomial, if_neg hne,
      mul_zero]

end RS
