/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic

/-!
# Finite generic scalar perturbations

A finite family of affine matrix paths can be made simultaneously nonsingular by choosing an
arbitrarily small positive parameter away from the finitely many determinant roots.  This is the
only genericity input needed by the S6 subdivision argument: the perturbation direction is fixed
globally, so face compatibility and prime equivariance are preserved automatically.
-/

namespace NRR
namespace FiniteGenericPerturbation

open scoped BigOperators
open Polynomial

variable {n I : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial-valued straight-line path from `A` to `B`. -/
noncomputable def matrixPath (A B : Matrix n n Real) : Matrix n n Real[X] :=
  Matrix.of fun i j => C (A i j) + X * C (B i j - A i j)

/-- Determinant polynomial of the straight-line matrix path. -/
noncomputable def determinantPath (A B : Matrix n n Real) : Real[X] :=
  Matrix.det (matrixPath A B)

/-- Evaluation of the polynomial matrix path. -/
theorem eval_matrixPath (A B : Matrix n n Real) (t : Real) :
    (evalRingHom t).mapMatrix (matrixPath A B) = (1 - t) • A + t • B := by
  ext i j
  simp [matrixPath]
  ring

/-- Evaluation of the determinant path is the determinant of the evaluated matrix path. -/
theorem eval_determinantPath (A B : Matrix n n Real) (t : Real) :
    eval t (determinantPath A B) = Matrix.det ((1 - t) • A + t • B) := by
  classical
  unfold determinantPath
  change evalRingHom t (Matrix.det (matrixPath A B)) = _
  rw [RingHom.map_det]
  rw [eval_matrixPath]

/-- At parameter one the determinant polynomial evaluates to the target determinant. -/
@[simp] theorem eval_one_determinantPath (A B : Matrix n n Real) :
    eval 1 (determinantPath A B) = Matrix.det B := by
  rw [eval_determinantPath]
  simp

/-- A regular target matrix gives a nonzero determinant polynomial. -/
theorem determinantPath_ne_zero_of_target
    (A B : Matrix n n Real) (hB : Matrix.det B ≠ 0) :
    determinantPath A B ≠ 0 := by
  intro hzero
  have hdet : Matrix.det B = 0 := by
    rw [← eval_one_determinantPath A B, hzero]
    simp
  exact hB hdet

/-- The union of the real root sets of a finite family of nonzero polynomials is finite. -/
theorem finite_badParameters
    [Fintype I] (P : I → Real[X]) (hP : ∀ i, P i ≠ 0) :
    Set.Finite {t : Real | ∃ i, eval t (P i) = 0} := by
  classical
  have hi : ∀ i, Set.Finite (Polynomial.rootSet (P i) Real) :=
    fun i => Polynomial.rootSet_finite (P i) Real
  have hu : Set.Finite (⋃ i, Polynomial.rootSet (P i) Real) :=
    Set.finite_iUnion fun i => hi i
  apply hu.subset
  rintro t ⟨i, hit⟩
  exact Set.mem_iUnion.2 ⟨i, by simpa [Polynomial.mem_rootSet, hP i] using hit⟩

/-- Arbitrarily small positive parameters avoid all roots of a finite nonzero polynomial family. -/
theorem exists_small_positive_avoiding
    [Fintype I] (P : I → Real[X]) (hP : ∀ i, P i ≠ 0)
    {eps : Real} (heps : 0 < eps) :
    ∃ t : Real, 0 < t ∧ t < eps ∧ ∀ i, eval t (P i) ≠ 0 := by
  classical
  let bad : Set Real := {t : Real | ∃ i, eval t (P i) = 0}
  have hbad : bad.Finite := finite_badParameters P hP
  have hinfinite : Set.Infinite (Set.Ioo (0 : Real) eps) := Set.Ioo_infinite heps
  obtain ⟨t, htI, htbad⟩ := hinfinite.exists_notMem_finset hbad.toFinset
  refine ⟨t, htI.1, htI.2, ?_⟩
  intro i hi
  apply htbad
  exact hbad.mem_toFinset.mpr ⟨i, hi⟩

/-- Simultaneous regularization of a finite family of matrix paths. -/
theorem exists_small_positive_regular
    [Fintype I]
    (A B : I → Matrix n n Real)
    (hB : ∀ i, Matrix.det (B i) ≠ 0)
    {eps : Real} (heps : 0 < eps) :
    ∃ t : Real, 0 < t ∧ t < eps ∧
      ∀ i, Matrix.det ((1 - t) • A i + t • B i) ≠ 0 := by
  let P : I → Real[X] := fun i => determinantPath (A i) (B i)
  have hP : ∀ i, P i ≠ 0 := fun i => determinantPath_ne_zero_of_target _ _ (hB i)
  obtain ⟨t, ht0, hteps, ht⟩ := exists_small_positive_avoiding P hP heps
  refine ⟨t, ht0, hteps, ?_⟩
  intro i
  simpa [P, eval_determinantPath] using ht i

end FiniteGenericPerturbation
end NRR
