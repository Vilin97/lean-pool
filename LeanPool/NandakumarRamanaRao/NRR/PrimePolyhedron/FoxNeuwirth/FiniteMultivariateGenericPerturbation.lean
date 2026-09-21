/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteGenericPerturbation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Finite multivariate generic perturbations

A finite family of nonzero real multivariate polynomials can be made simultaneously nonzero by an
arbitrarily small perturbation of any prescribed assignment.  The proof avoids a separate density
or transversality library.

First multiply the finite family.  Since the real numbers form an infinite integral domain,
`MvPolynomial.funext` implies that a nonzero polynomial has at least one nonzero evaluation.  Join
the original assignment to such an evaluation by a straight line.  Every multivariate polynomial
then becomes a nonzero univariate polynomial because its value at parameter one is nonzero.  A
small positive parameter avoiding the finitely many roots gives the required perturbation.
-/

namespace NRR
namespace FiniteMultivariateGenericPerturbation

open scoped BigOperators
open Polynomial MvPolynomial

variable {J I : Type*} [Fintype I]

/-- A nonzero real multivariate polynomial has a nonzero evaluation. -/
theorem exists_eval_ne_zero (P : MvPolynomial J Real) (hP : P ≠ 0) :
    ∃ b : J → Real, MvPolynomial.eval b P ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hP
  apply MvPolynomial.funext
  intro b
  simpa using h b

/-- A finite family of nonzero real multivariate polynomials has one common nonvanishing
assignment. -/
theorem exists_common_eval_ne_zero
    (P : I → MvPolynomial J Real) (hP : ∀ i, P i ≠ 0) :
    ∃ b : J → Real, ∀ i, MvPolynomial.eval b (P i) ≠ 0 := by
  classical
  let Q : MvPolynomial J Real := ∏ i, P i
  have hQ : Q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP i
  obtain ⟨b, hb⟩ := exists_eval_ne_zero Q hQ
  refine ⟨b, ?_⟩
  intro i hi
  apply hb
  rw [show MvPolynomial.eval b Q = ∏ x, MvPolynomial.eval b (P x) by simp [Q]]
  by_contra hprod
  exact (Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)) hi

/-- Substitute the affine line from `a` to `b` into a multivariate polynomial. -/
noncomputable def linePolynomial
    (a b : J → Real) (P : MvPolynomial J Real) : Real[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j - a j)) P

/-- Evaluation of the line polynomial is multivariate evaluation at the affine line. -/
theorem eval_linePolynomial
    (a b : J → Real) (P : MvPolynomial J Real) (t : Real) :
    Polynomial.eval t (linePolynomial a b P) =
      MvPolynomial.eval (fun j => a j + t * (b j - a j)) P := by
  classical
  apply MvPolynomial.induction_on P
  · intro r
    simp [linePolynomial]
  · intro p q hp hq
    simp only [linePolynomial] at hp hq ⊢
    rw [MvPolynomial.eval₂_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  · intro p j hp
    simp only [linePolynomial] at hp ⊢
    rw [MvPolynomial.eval₂_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul,
      MvPolynomial.eval₂_X, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, MvPolynomial.eval_X]
    simp

/-- At parameter one, the line polynomial evaluates at the target assignment. -/
@[simp] theorem eval_one_linePolynomial
    (a b : J → Real) (P : MvPolynomial J Real) :
    Polynomial.eval 1 (linePolynomial a b P) = MvPolynomial.eval b P := by
  rw [eval_linePolynomial]
  apply congrArg (fun x : J → Real => MvPolynomial.eval x P)
  funext j
  ring

/-- A target nonvanishing evaluation makes the corresponding line polynomial nonzero. -/
theorem linePolynomial_ne_zero_of_target
    (a b : J → Real) (P : MvPolynomial J Real)
    (hb : MvPolynomial.eval b P ≠ 0) :
    linePolynomial a b P ≠ 0 := by
  intro hzero
  have hEval := congrArg (Polynomial.eval 1) hzero
  apply hb
  simpa using hEval

/-- Simultaneously avoid a finite family of polynomial degeneracy conditions by an arbitrarily
small positive displacement along one common affine line. -/
theorem exists_small_positive_generic
    (P : I → MvPolynomial J Real) (hP : ∀ i, P i ≠ 0)
    (a : J → Real) {eps : Real} (heps : 0 < eps) :
    ∃ (b : J → Real) (t : Real),
      0 < t ∧ t < eps ∧
        ∀ i, MvPolynomial.eval (fun j => a j + t * (b j - a j)) (P i) ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := exists_common_eval_ne_zero P hP
  let Q : I → Real[X] := fun i => linePolynomial a b (P i)
  have hQ : ∀ i, Q i ≠ 0 :=
    fun i => linePolynomial_ne_zero_of_target a b (P i) (hb i)
  obtain ⟨t, ht0, hteps, ht⟩ :=
    FiniteGenericPerturbation.exists_small_positive_avoiding Q hQ heps
  refine ⟨b, t, ht0, hteps, ?_⟩
  intro i
  simpa [Q, eval_linePolynomial] using ht i

end FiniteMultivariateGenericPerturbation
end NRR
