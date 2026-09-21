/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
import LeanPool.CoarseGraining.Homogenization.Probability.Scalarization

/-! # Origin Cube Symmetry -/

namespace Homogenization

/--
Coordinate formula for the action of a sign-flip matrix on a vector.
-/
theorem matVecMul_signFlipMatrix_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    matVecMul (signFlipMatrix i) x j =
      (if j = i then (-1 : ℝ) else 1) * x j := by
  simpa [signFlipMatrix, matVecMul] using!
    (Matrix.mulVec_diagonal (fun k => if k = i then (-1 : ℝ) else 1) x j)

/--
Coordinate formula for the action of a swap matrix on a vector.
-/
theorem matVecMul_swap_eq_comp {d : ℕ} (i j : Fin d) (x : Vec d) :
    matVecMul (Matrix.swap ℝ i j) x = x ∘ Equiv.swap i j := by
  simpa [matVecMul] using! (Matrix.swap_mulVec (R := ℝ) i j x)

/--
The centered open cube `(-3^m/2, 3^m/2)^d` is invariant under coordinate sign flips.

We record this for `openCubeSet`; the half-open `cubeSet` realization is not literally
sign-flip invariant on boundary points.
-/
theorem mem_openCubeSet_originCube_signFlipMatrix_iff {d : ℕ} {m : ℤ} {x : Vec d}
    (i : Fin d) :
    matVecMul (signFlipMatrix i) x ∈ openCubeSet (originCube d m) ↔
      x ∈ openCubeSet (originCube d m) := by
  rw [mem_openCubeSet_originCube_iff, mem_openCubeSet_originCube_iff]
  constructor
  · intro hx j
    by_cases hji : j = i
    · have hj := hx j
      rw [matVecMul_signFlipMatrix_apply, if_pos hji] at hj
      constructor <;> nlinarith [hj.1, hj.2]
    · simpa [matVecMul_signFlipMatrix_apply, hji] using hx j
  · intro hx j
    by_cases hji : j = i
    · have hj := hx j
      have hneg :
          ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (-1 : ℝ) * x j) ∧
            (((-1 : ℝ) * x j) < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
          constructor <;> nlinarith [hj.1, hj.2]
      simpa [matVecMul_signFlipMatrix_apply, hji] using hneg
    · simpa [matVecMul_signFlipMatrix_apply, hji] using hx j

/--
The centered open cube `(-3^m/2, 3^m/2)^d` is invariant under coordinate swaps.
-/
theorem mem_openCubeSet_originCube_swap_iff {d : ℕ} {m : ℤ} {x : Vec d}
    (i j : Fin d) :
    matVecMul (Matrix.swap ℝ i j) x ∈ openCubeSet (originCube d m) ↔
      x ∈ openCubeSet (originCube d m) := by
  rw [mem_openCubeSet_originCube_iff, mem_openCubeSet_originCube_iff, matVecMul_swap_eq_comp]
  constructor
  · intro hx k
    simpa using hx (Equiv.swap i j k)
  · intro hx k
    simpa using hx (Equiv.swap i j k)

end Homogenization
