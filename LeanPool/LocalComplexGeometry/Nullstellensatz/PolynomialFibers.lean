/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Geometry.FiniteProjection
import Mathlib.FieldTheory.Separable

/-!
# Polynomial rigidity on simple finite fibers

The generic-fiber step in Rueckert's analytic Nullstellensatz reduces to a
pointwise polynomial fact.  A polynomial of degree strictly below `d` which
vanishes at every root of a separable monic polynomial of degree `d` is zero.
This file packages that fact for the coefficient-vector convention used by
Weierstrass division.
-/

open scoped BigOperators


namespace LocalComplexGeometry

noncomputable section

/-- A degree-`< d` coefficient vector, evaluated as a polynomial in the last
variable at a fixed base point. -/
def remainderPolynomialAt {n d : ℕ}
    (b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    Polynomial ℂ :=
  ∑ i : Fin d, Polynomial.C (b i z) * Polynomial.X ^ (i : ℕ)

/-- Pointwise evaluation of `remainderPolynomialAt`. -/
@[simp]
theorem remainderPolynomialAt_eval {n d : ℕ}
    (b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) (w : ℂ) :
    (remainderPolynomialAt b z).eval w =
      ∑ i : Fin d, b i z * w ^ (i : ℕ) := by
  change (Polynomial.evalRingHom w) (remainderPolynomialAt b z) = _
  unfold remainderPolynomialAt
  rw [map_sum]
  simp

/-- The assembled remainder polynomial has degree strictly below `d`. -/
theorem remainderPolynomialAt_natDegree_lt {n d : ℕ} (hd : 0 < d)
    (b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n) :
    (remainderPolynomialAt b z).natDegree < d := by
  unfold remainderPolynomialAt
  apply (Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ) (n := d - 1) _ ?_).trans_lt
  · exact Nat.sub_lt hd Nat.zero_lt_one
  · intro i hi
    have hi' : (i : ℕ) ≤ d - 1 := by omega
    exact (Polynomial.natDegree_C_mul_X_pow_le (b i z) (i : ℕ)).trans hi'

/-- A zero assembled remainder polynomial has every displayed coefficient
equal to zero. -/
theorem remainderPolynomialAt_coeff_eq_zero {n d : ℕ}
    (b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n)
    (hzero : remainderPolynomialAt b z = 0) (i : Fin d) :
    b i z = 0 := by
  have hcoeff := congrArg (fun p : Polynomial ℂ ↦ p.coeff (i : ℕ)) hzero
  have hsum :
      (∑ j : Fin d, if (i : ℕ) = (j : ℕ) then b j z else 0) = 0 := by
    simpa [remainderPolynomialAt] using hcoeff
  rw [Finset.sum_eq_single i] at hsum
  · simpa using hsum
  · intro j hj hji
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hji (Fin.ext h.symm)
    simp [hij]
  · simp

/-- A polynomial of degree below a nonzero separable complex polynomial which
vanishes at every root of that polynomial is zero. -/
theorem polynomial_eq_zero_of_natDegree_lt_of_vanishes_on_separableRoots
    {q r : Polynomial ℂ} (hq : q ≠ 0) (hsep : q.Separable)
    (hdegree : r.natDegree < q.natDegree)
    (hvanish : ∀ w : ℂ, q.eval w = 0 → r.eval w = 0) :
    r = 0 := by
  classical
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    r q.roots.toFinset
  · intro w hw
    exact hvanish w <|
      (Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp hw)
  · calc
      r.natDegree < q.natDegree := hdegree
      _ = q.roots.card := (IsAlgClosed.splits q).natDegree_eq_card_roots
      _ = q.roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)).symm

/-- Fiber rigidity: vanishing at every root of a separable prepared polynomial
forces a lower-degree remainder polynomial to be zero. -/
theorem remainderPolynomialAt_eq_zero_of_vanishes_on_preparedRoots
    {n d : ℕ} (hd : 0 < d)
    (a b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n)
    (hsep : (preparedPolynomialAt a z).Separable)
    (hvanish : ∀ w : ℂ, preparedValue a z w = 0 →
      ∑ i : Fin d, b i z * w ^ (i : ℕ) = 0) :
    remainderPolynomialAt b z = 0 := by
  apply polynomial_eq_zero_of_natDegree_lt_of_vanishes_on_separableRoots
    (preparedPolynomialAt_monic a z).ne_zero hsep
  · rw [preparedPolynomialAt_natDegree]
    exact remainderPolynomialAt_natDegree_lt hd b z
  · intro w hqw
    rw [preparedPolynomialAt_eval] at hqw
    exact remainderPolynomialAt_eval b z w |>.trans (hvanish w hqw)

/-- Coefficient form of fiber rigidity. -/
theorem coefficient_eq_zero_of_vanishes_on_preparedRoots
    {n d : ℕ} (hd : 0 < d)
    (a b : Fin d → ComplexEuclidean n → ℂ) (z : ComplexEuclidean n)
    (hsep : (preparedPolynomialAt a z).Separable)
    (hvanish : ∀ w : ℂ, preparedValue a z w = 0 →
      ∑ i : Fin d, b i z * w ^ (i : ℕ) = 0) (i : Fin d) :
    b i z = 0 := by
  apply remainderPolynomialAt_coeff_eq_zero b z
  exact remainderPolynomialAt_eq_zero_of_vanishes_on_preparedRoots
    hd a b z hsep hvanish

end

end LocalComplexGeometry
