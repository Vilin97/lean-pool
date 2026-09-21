/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import LeanPool.OperatorTheory.Operator.SpectralSet.Basic

/-!
# Affine changes of variables for complex polynomials

This file records how evaluation, degree, and `polynomialSupNorm` behave when a
complex polynomial is precomposed with the affine map `z ↦ a * z + b`.

## Main declarations

* `Polynomial.affineComposition` — precomposition by `z ↦ a * z + b`;
* `Polynomial.eval_affineComposition` and `Polynomial.aeval_affineComposition` — scalar and
  algebra-valued evaluation;
* `Polynomial.natDegree_affineComposition_le` and
  `Polynomial.natDegree_affineComposition` — the degree bounds, with equality when `a ≠ 0`;
* `polynomialSupNorm_affineComposition_image` — exact transport of the polynomial sup-norm.
-/

open scoped Polynomial

namespace Polynomial

/-- Precomposition of a complex polynomial with the affine map `z ↦ a * z + b`. -/
noncomputable def affineComposition (p : ℂ[X]) (a b : ℂ) : ℂ[X] :=
  p.comp (C a * X + C b)

/-- Evaluating an affine composition is evaluation after the corresponding scalar affine map. -/
@[simp]
theorem eval_affineComposition (p : ℂ[X]) (a b z : ℂ) :
    (affineComposition p a b).eval z = p.eval (a * z + b) := by
  simp only [affineComposition, eval_comp, eval_add, eval_mul, eval_C, eval_X]

/-- Algebra-valued evaluation commutes with affine precomposition. -/
@[simp]
theorem aeval_affineComposition {A : Type*} [Semiring A] [Algebra ℂ A]
    (p : ℂ[X]) (a b : ℂ) (x : A) :
    aeval x (affineComposition p a b) = aeval (a • x + b • (1 : A)) p := by
  simp only [affineComposition, aeval_comp, map_add, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, aeval_X, Algebra.smul_mul_assoc, one_mul]

/-- Affine precomposition cannot increase the natural degree of a polynomial. -/
theorem natDegree_affineComposition_le (p : ℂ[X]) (a b : ℂ) :
    (affineComposition p a b).natDegree ≤ p.natDegree := by
  rw [affineComposition]
  have hq : (C a * X + C b).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [pow_one] using natDegree_C_mul_X_pow_le a 1
  calc
    (p.comp (C a * X + C b)).natDegree
        ≤ p.natDegree * (C a * X + C b).natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hq
    _ = p.natDegree := Nat.mul_one _

/-- Precomposition by a nonconstant affine map preserves natural degree. -/
theorem natDegree_affineComposition (p : ℂ[X]) {a b : ℂ} (ha : a ≠ 0) :
    (affineComposition p a b).natDegree = p.natDegree := by
  rw [affineComposition, natDegree_comp]
  have hdeg : (C a * X + C b).natDegree = 1 := by
    simp only [natDegree_add_C, ne_eq, map_eq_zero, ha, not_false_eq_true, natDegree_mul_X,
      natDegree_C, zero_add]
  rw [hdeg, Nat.mul_one]

end Polynomial

/-- The sup-norm of an affine composition on `X` is the original sup-norm on the affine image
of `X`. This remains exact for unbounded sets: in that case both conditionally complete suprema
use the same unbounded family of values. -/
theorem polynomialSupNorm_affineComposition_image (p : ℂ[X]) (a b : ℂ) (X : Set ℂ) :
    polynomialSupNorm (p.affineComposition a b) X =
      polynomialSupNorm p ((fun z : ℂ => a * z + b) '' X) := by
  simp only [polynomialSupNorm, Polynomial.eval_affineComposition]
  let f : ℂ → ℂ := fun z => a * z + b
  let g : ℂ → ℝ := fun z => ‖p.eval z‖
  change (⨆ z ∈ X, g (f z)) = ⨆ z ∈ f '' X, g z
  by_cases hB : BddAbove (Set.range fun z : X => g (f z))
  · exact (ciSup_image hB (by
      simpa only [Real.sSup_empty] using
        Real.iSup_nonneg fun z : X => norm_nonneg (p.eval (f z)))).symm
  · have hB' : ¬BddAbove (Set.range fun z : f '' X => g z) := by
      intro h
      apply hB
      simpa only [bddAbove_def, Set.mem_range, Subtype.exists, exists_prop,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_image,
        exists_exists_and_eq_and] using h
    rw [cbiSup_of_not_bddAbove hB, cbiSup_of_not_bddAbove hB']

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
