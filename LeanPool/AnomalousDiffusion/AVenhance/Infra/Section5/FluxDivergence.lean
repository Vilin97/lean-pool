/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Coordinate product rule for divergence of a matrix acting on a vector. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- Divergence of a matrix-vector product, with the two derivative
contributions displayed coordinatewise. -/
theorem vecDiv_matrixMulVec
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    {x : Vec 2} {LA : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LV : Vec 2 →L[ℝ] Vec 2}
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (LA i j) x)
    (hV : HasFDerivAt V LV x) :
    vecDiv (fun y => (A y).mulVec (V y)) x =
      ∑ i : Fin 2, ∑ j : Fin 2,
        ((LA i j) (basisVec i) * V x j +
          A x i j * (LV (basisVec i)) j) := by
  let P : Fin 2 → Vec 2 →L[ℝ] ℝ := fun j => ContinuousLinearMap.proj j
  let D : Fin 2 → Vec 2 →L[ℝ] ℝ := fun i =>
    ∑ j : Fin 2,
      ((V x j) • LA i j + (A x i j) • (P j).comp LV)
  have hVj (j : Fin 2) : HasFDerivAt (fun y => V y j) ((P j).comp LV) x := by
    exact (P j).hasFDerivAt.comp x hV
  have hrow (i : Fin 2) :
      HasFDerivAt (fun y => (A y).mulVec (V y) i) (D i) x := by
    have hfun : (fun y => (A y).mulVec (V y) i) =
        ∑ j : Fin 2, (fun y => A y i j * V y j) := by
      funext y
      simp [Matrix.mulVec, dotProduct]
    rw [hfun]
    have hsum : HasFDerivAt
        (∑ j : Fin 2, fun y => A y i j * V y j)
        (∑ j : Fin 2,
          ((V x j) • LA i j + (A x i j) • (P j).comp LV)) x := by
      apply HasFDerivAt.sum
      intro j hj
      convert (hA i j).mul (hVj j) using 1
      simp [P, add_comm]
    simpa [D] using hsum
  unfold vecDiv
  calc
    (∑ i : Fin 2,
        spaceGrad (fun y => (A y).mulVec (V y) i) x i) =
      ∑ i : Fin 2, (D i) (basisVec i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [spaceGrad, (hrow i).fderiv]
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        ((LA i j) (basisVec i) * V x j +
          A x i j * (LV (basisVec i)) j) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [D, sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        simp [P, smul_apply, ContinuousLinearMap.comp_apply]
        ring_nf

end AVenhance.Infra.Section5
