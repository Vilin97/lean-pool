/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.WeakHessianEuclidean
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Finite-`p` aggregation for weak Hessians

This file packages rowwise Euclidean `L^p` control of a weak Hessian into the
project's Hilbert matrix carrier.  The norm estimate retains the exact finite
exponent and bounds the matrix norm by the finite sum of its row norms.
-/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- Rowwise Euclidean `L^p` membership packages into matrix-valued `L^p`
membership. -/
theorem hessianHilbertMat_memLp_of_rows (H : HasWeakHessianOn U u)
    (q : FiniteLpExponent) (μ : MeasureTheory.Measure (Vec d))
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent μ) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
      q.exponent μ := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  simpa only [Function.comp_apply, HilbertMat.ofMat, PiLp.toLp_apply] using hrows i

/-- The matrix-valued finite-`p` norm of a weak Hessian is bounded by the
finite sum of the Euclidean finite-`p` norms of its rows. -/
theorem eLpNorm_hessianHilbertMat_le_sum_rows (H : HasWeakHessianOn U u)
    (q : FiniteLpExponent) (μ : MeasureTheory.Measure (Vec d))
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent μ) :
    MeasureTheory.eLpNorm
        (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
        q.exponent μ ≤
      ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent μ := by
  let row : Fin d → Vec d → HilbertVec d :=
    fun i x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)
  let singleRow : Fin d → Vec d → HilbertMat d :=
    fun i x ↦ WithLp.toLp 2 (Pi.single i (row i x))
  have hsingleRow : ∀ i : Fin d,
      MeasureTheory.MemLp (singleRow i) q.exponent μ := by
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro k
    by_cases hik : i = k
    · subst k
      simpa only [singleRow, row, Function.comp_apply, PiLp.toLp_apply,
        Pi.single_eq_same] using hrows i
    · have hzero : MeasureTheory.MemLp
          (fun _ : Vec d ↦ (0 : HilbertVec d)) q.exponent μ :=
        MeasureTheory.MemLp.zero'
      simpa only [singleRow, Function.comp_apply, PiLp.toLp_apply,
        Pi.single_eq_of_ne (Ne.symm hik)] using hzero
  have hmatrix :
      (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) =
        ∑ i : Fin d, singleRow i := by
    funext x
    ext i j
    simp [singleRow, row]
  rw [hmatrix]
  calc
    MeasureTheory.eLpNorm (∑ i : Fin d, singleRow i) q.exponent μ ≤
        ∑ i : Fin d, MeasureTheory.eLpNorm (singleRow i) q.exponent μ := by
      exact MeasureTheory.eLpNorm_sum_le
        q.one_lt.le
    _ = ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply MeasureTheory.eLpNorm_congr_norm_ae
        (hsingleRow i).aestronglyMeasurable (hrows i).aestronglyMeasurable
      exact MeasureTheory.ae_of_all μ fun x ↦ by simp [singleRow, row]

/-- Normalized-cube specialization of
`HasWeakHessianOn.hessianHilbertMat_memLp_of_rows`. -/
theorem hessianHilbertMat_memLp_normalizedCubeMeasure_of_rows
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (q : FiniteLpExponent)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
      q.exponent (normalizedCubeMeasure Q) :=
  H.hessianHilbertMat_memLp_of_rows q (normalizedCubeMeasure Q) hrows

/-- Normalized-cube specialization of the finite-`p` row-sum estimate. -/
theorem eLpNorm_hessianHilbertMat_normalizedCubeMeasure_le_sum_rows
    (Q : TriadicCube d) {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (q : FiniteLpExponent)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent (normalizedCubeMeasure Q)) :
    MeasureTheory.eLpNorm
        (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
        q.exponent (normalizedCubeMeasure Q) ≤
      ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent (normalizedCubeMeasure Q) :=
  H.eLpNorm_hessianHilbertMat_le_sum_rows q (normalizedCubeMeasure Q) hrows

end HasWeakHessianOn

end

end Homogenization
