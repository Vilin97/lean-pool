/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Affine Subdivision Determinant -/

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open SphereOddDegree.BarycentricSubdivisionDiameter

namespace NRR
namespace AffineSubdivisionDeterminant
/-- Matrix whose columns are the vertices of one barycentric subdivision simplex. -/
noncomputable def stepVertexMatrix
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => (prefixBarycenter n pi k).val r

/-- Lower triangular prefix-average matrix before permutation of coordinates. -/
noncomputable def prefixAverageMatrix (n : Nat) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => if r.1 ≤ k.1 then (k.1 + 1 : Real)⁻¹ else 0

/-- Factorization of a one-step vertex matrix. -/
theorem stepVertexMatrix_eq
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    stepVertexMatrix n pi = Equiv.Perm.permMatrix Real pi.symm * prefixAverageMatrix n := by
  ext r k
  rw [Matrix.mul_apply]
  have h_perm : ∀ j, Equiv.Perm.permMatrix Real pi.symm r j = if pi.symm r = j then 1 else 0 := by
    intro j; simp [Equiv.Perm.permMatrix]
  simp_rw [h_perm, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  dsimp [stepVertexMatrix, prefixAverageMatrix]
  have h_bary := congr_fun (prefixBarycenter_val_eq_stepVertices n pi k) r
  rw [h_bary]
  dsimp [stepVertices, stdVerts]
  simp only [Finset.sum_apply, Pi.single_apply]
  have hsum : (∑ j ∈ Finset.Iic k, if r = pi j then (1 : ℝ) else 0)
      = if (pi.symm r).1 ≤ k.1 then 1 else 0 := by
    have heq : (∑ j ∈ Finset.Iic k, if r = pi j then (1 : ℝ) else 0)
        = ∑ j ∈ Finset.Iic k, if j = pi.symm r then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : r = pi j
      · rw [ite_eq_left hj, ite_eq_left (by rw [hj, Equiv.symm_apply_apply])]
      · rw [ite_eq_right hj, ite_eq_right (by intro heq; apply hj; rw [heq, Equiv.apply_symm_apply])]
    rw [heq]
    split_ifs with h
    · have hmem : pi.symm r ∈ Finset.Iic k := Finset.mem_Iic.mpr h
      simp [hmem]
    · have hnmem : pi.symm r ∉ Finset.Iic k := by rw [Finset.mem_Iic]; exact h
      simp [hnmem]
  rw [hsum]
  split_ifs with h
  · ring
  · ring

/-- Determinant of the prefix-average matrix. -/
theorem det_prefixAverageMatrix (n : Nat) :
    Matrix.det (prefixAverageMatrix n) =
      ∏ k : Fin (n + 1), (k.1 + 1 : Real)⁻¹ := by
  rw [Matrix.det_of_isUpperTriangular]
  · congr 1; ext k; dsimp [prefixAverageMatrix]; rw [ite_eq_left (le_refl _)]
  · intro i j hij
    dsimp [prefixAverageMatrix]
    have hnot : ¬ (i.1 ≤ j.1) := by
      intro hle
      have : (i : Fin (n + 1)) ≤ (j : Fin (n + 1)) := Fin.le_iff_val_le_val.mpr hle
      exact (not_le_of_gt hij) this
    rw [ite_eq_right hnot]

/-- One barycentric subdivision simplex is nondegenerate. -/
theorem det_stepVertexMatrix_ne_zero
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    Matrix.det (stepVertexMatrix n pi) ≠ 0 := by
  rw [stepVertexMatrix_eq]
  rw [Matrix.det_mul, Matrix.det_permutation, det_prefixAverageMatrix]
  have hsign : (↑↑(Equiv.Perm.sign pi.symm) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hprod : ∏ k : Fin (n + 1), (k.1 + 1 : Real)⁻¹ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro x _
    exact inv_ne_zero (by positivity)
  exact mul_ne_zero hsign hprod

/-- Vertex matrix of an iterated affine subdivision simplex. -/
noncomputable def iterVertexMatrix
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun r k => (affineCompMap n N rho (SphereOddDegree.FiniteSimplex.vertex (S := Real) k)).val r

@[simp] theorem iterVertexMatrix_zero
    (n : Nat) (rho : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    iterVertexMatrix n 0 rho = 1 := by
  ext r k
  simp [iterVertexMatrix, Matrix.one_apply, SphereOddDegree.FiniteSimplex.vertex, Pi.single_apply]

/-- Appending one subdivision step multiplies vertex matrices. -/
theorem iterVertexMatrix_succ
    (n N : Nat) (rho : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    iterVertexMatrix n (N + 1) rho =
      iterVertexMatrix n N (fun i => rho i.castSucc) *
        stepVertexMatrix n (rho (Fin.last N)) := by
  ext r k
  dsimp [iterVertexMatrix, affineCompMap_succ, Matrix.mul_apply, stepVertexMatrix]
  have h_affine : (affineSubdivMap n (rho (Fin.last N)) (SphereOddDegree.FiniteSimplex.vertex k)).val
      = (prefixBarycenter n (rho (Fin.last N)) k).val := by
    ext j
    rw [← affineSubdivLinear_coe, affineSubdivLinear_apply]
    dsimp [SphereOddDegree.FiniteSimplex.vertex]
    simp only [Pi.single_apply]
    simp_rw [ite_mul, one_mul, zero_mul]
    simp
  have h_coe := affineCompMap_coe n N (fun i => rho i.castSucc) (affineSubdivMap n (rho (Fin.last N)) (SphereOddDegree.FiniteSimplex.vertex k))
  have h_coe_r := congr_fun h_coe r
  rw [h_coe_r, h_affine]
  have h_sum : (affineCompLinear n N (fun i => rho i.castSucc)) (fun j => (prefixBarycenter n (rho (Fin.last N)) k).val j)
      = ∑ j : Fin (n + 1), (prefixBarycenter n (rho (Fin.last N)) k).val j • (affineCompLinear n N (fun i => rho i.castSucc)) (stdVerts n j) := by
    have h_expand : (fun j => (prefixBarycenter n (rho (Fin.last N)) k).val j)
        = ∑ j : Fin (n + 1), (prefixBarycenter n (rho (Fin.last N)) k).val j • (stdVerts n j) := by
      ext a
      dsimp [stdVerts]
      simp [Pi.single_apply]
    conv_lhs => rw [h_expand]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
  have h_val := congr_fun h_sum r
  rw [h_val]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  have h_vert := affineCompMap_coe n N (fun i => rho i.castSucc) (SphereOddDegree.FiniteSimplex.vertex j)
  have h_vert_r := congr_fun h_vert r
  rw [h_vert_r]
  rfl

/-- Every iterated subdivision simplex is nondegenerate. -/
theorem det_iterVertexMatrix_ne_zero
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) :
    Matrix.det (iterVertexMatrix n N rho) ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [iterVertexMatrix_succ, Matrix.det_mul]
      exact mul_ne_zero (ih _) (det_stepVertexMatrix_ne_zero n _)

end AffineSubdivisionDeterminant
end NRR
