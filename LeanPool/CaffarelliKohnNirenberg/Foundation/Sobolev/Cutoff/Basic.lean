/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Support

/-!
# Euclidean coordinate norms and gradients

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The coordinate-vector norm and gradient API is kept in the
independent `CKN` namespace.

The main definitions are `CKN.vecEuclideanNorm` and `CKN.classicalGradient`.
The norm lemmas give positivity, scalar multiplication and component bounds.
-/

public section

open scoped BigOperators

namespace CKN

/-- The Euclidean dot product on native coordinate vectors. -/
@[expose]
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on native coordinate vectors. -/
@[expose]
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on native coordinate vectors. -/
@[expose]
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d}
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ 0 := by
    simpa [h] using sq_apply_le_vecNormSq x i
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (x i)))

theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

/-- The Euclidean norm is nonnegative. -/
theorem vecEuclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem vecEuclideanNorm_sq {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ^ 2 = vecNormSq x := by
  exact Real.sq_sqrt (vecNormSq_nonneg x)

/-- The Euclidean norm respects scalar multiplication. -/
theorem vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem vecEuclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · intro hx
    rw [hx]
    simp [vecEuclideanNorm, vecNormSq, vecDot]

theorem abs_apply_le_vecEuclideanNorm {d : ℕ}
    (x : Vec d) (i : Fin d) :
    |x i| ≤ vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq x i)

/-- The coordinate gradient of a scalar function in the native vector carrier. -/
@[expose]
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

@[simp]
theorem classicalGradient_apply {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    classicalGradient f x i =
      (fderiv ℝ f x) (basisVec i) :=
  rfl

end CKN
