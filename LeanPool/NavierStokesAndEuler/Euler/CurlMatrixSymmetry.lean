/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
public import Mathlib.Analysis.InnerProductSpace.Symmetric

@[expose] public section

noncomputable section

open EulerSmoothLimit
open scoped RealInnerProductSpace

namespace EulerMeanBoundary

/-- The curl vanishes precisely when the real derivative matrix is symmetric. -/
theorem curlMatrix_eq_zero_iff_isSymmetric (A : Space →L[ℝ] Space) :
    curlMatrix A = 0 ↔ A.IsSymmetric := by
  constructor
  · intro h
    have hc (i : Fin 3) :
        (A (EuclideanSpace.single (i+1) 1)) (i+2) -
          (A (EuclideanSpace.single (i+2) 1)) (i+1) = 0 := by
      exact congrArg (fun v : Space => v i) h
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    change (A (EuclideanSpace.single 1 1)) 2 - (A (EuclideanSpace.single 2 1)) 1 = 0 at h0
    change (A (EuclideanSpace.single 2 1)) 0 - (A (EuclideanSpace.single 0 1)) 2 = 0 at h1
    change (A (EuclideanSpace.single 0 1)) 1 - (A (EuclideanSpace.single 1 1)) 0 = 0 at h2
    have heq (i j : Fin 3) :
        (A (EuclideanSpace.single i 1)) j = (A (EuclideanSpace.single j 1)) i := by
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact sub_eq_zero.mp h0 | exact sub_eq_zero.mp h1 |
          exact sub_eq_zero.mp h2 | exact (sub_eq_zero.mp h0).symm |
          exact (sub_eq_zero.mp h1).symm | exact (sub_eq_zero.mp h2).symm
    intro x y
    have hx := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
    have hy := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      inner_smul_right, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, map_one, one_mul, PiLp.smul_apply, smul_eq_mul,
        starRingEnd_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact heq j i
  · intro h
    ext i
    have hi := h (EuclideanSpace.single (i+1) 1) (EuclideanSpace.single (i+2) 1)
    simpa [curlMatrix, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, sub_eq_zero] using hi

end EulerMeanBoundary
