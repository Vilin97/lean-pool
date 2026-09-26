/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Total degree under affine substitution -/

public section
namespace Nikodym.LowerBound
open MvPolynomial
variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint TR6 (auxiliary): substituting polynomials of total degree at most one does not
increase the total degree. -/
theorem totalDegree_aeval_le_of_totalDegree_le_one {f : Fin d → MvPolynomial (Fin d) K}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (g : MvPolynomial (Fin d) K) :
    (aeval f g).totalDegree ≤ g.totalDegree := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun α hα ↦ ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (α i) (hf i))).trans ?_
  simp only [mul_one]
  exact le_totalDegree hα

end Nikodym.LowerBound
