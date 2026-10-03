/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Matrix.Basic

/-! # Coefficient matrices of rational polynomial families

The coefficient matrix and its expansion are shared by the Zeta5 and Zeta32
changes of polynomial basis. -/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-- The coefficient matrix of a family of polynomials. -/
@[expose] noncomputable def coeffMat {h : ℕ} (E : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a k => (E a).coeff k

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X]) (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) := by
  conv_lhs => rw [as_sum_range' (E a) h (hE a)]
  rw [Finset.sum_range (fun k => monomial k ((E a).coeff k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeffMat, Matrix.of_apply, C_mul_X_pow_eq_monomial]

end Zeta5Irrational

end
