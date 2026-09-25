/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.CubeNeumannCZ
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare

/-! # Multiscale Poincare -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal BigOperators

noncomputable section

/-!
# Legacy disjoint-Besov multiscale Poincare compatibility lane

The declarations in this namespace are retained only for compatibility with
the legacy disjoint-positive, totalized-real, componentwise-circ Besov
conventions. They are not the exact manuscript overlap/Euclidean statements.
-/

namespace Legacy

/-- Legacy selected constant for the disjoint-positive, totalized-real,
componentwise-circ compatibility Poincare lane; not an exact manuscript
overlap/Euclidean constant. -/
noncomputable abbrev fullVectorPoincareConstant {d : ℕ} [NeZero d]
    (Q : Cube d) : ℝ :=
  Homogenization.fullVectorPoincareCubeConstant Q

theorem fullVectorPoincareConstant_nonneg {d : ℕ} [NeZero d]
    (Q : Cube d) :
    0 ≤ fullVectorPoincareConstant Q := by
  simpa [fullVectorPoincareConstant] using
    Homogenization.fullVectorPoincareCubeConstant_nonneg Q

/-- Legacy full-dual multiscale Poincare compatibility estimate for `H¹`
functions on cubes; not an exact manuscript overlap/Euclidean statement. -/
theorem h1_fullVectorPoincare {d : ℕ} [NeZero d] (Q : Cube d)
    (u : H1Function (openCubeSet Q)) :
    Homogenization.CubeDualFullVectorPoincareEstimate Q
      (fullVectorPoincareConstant Q)
      (fun x => u x)
      (fun x => u.grad x) := by
  simpa [fullVectorPoincareConstant] using
    Homogenization.CubeDualFullVectorPoincareEstimate.of_h1Function Q u

/-- Legacy descendant full-dual Poincare compatibility estimate for `H¹`
functions on cubes; not an exact manuscript overlap/Euclidean statement. -/
theorem h1_descendantFullVectorPoincare {d : ℕ} [NeZero d] (Q : Cube d)
    (u : H1Function (openCubeSet Q)) (N : ℕ) :
    Homogenization.CubeDescendantDualFullVectorPoincareEstimate Q
      (fullVectorPoincareConstant Q)
      (cubeFluctuation Q (fun x => u x))
      (fun x => u.grad x) N := by
  simpa [fullVectorPoincareConstant] using
    Homogenization.CubeDescendantDualFullVectorPoincareEstimate.of_h1Function Q u N

/-- Legacy descendant H1 Poincare compatibility estimate after componentwise
circ domination. This is not an exact manuscript overlap/Euclidean statement.

This is the honest full-circ bridge available from the full-dual theorem.  The
remaining gradient-to-function cleanup is the separate summation step from
local full-circ control to the finite-partial multiscale corridor, or an
equivalent direct infinite-depth summation theorem. -/
theorem h1_descendantLocalFullCircPoincare {d : ℕ} [NeZero d] (Q : Cube d)
    (u : H1Function (openCubeSet Q)) (N : ℕ) :
    Homogenization.CubeLocalFullCircPoincareVectorEstimate Q
      (fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1))
      (cubeFluctuation Q (fun x => u x))
      (fun x => u.grad x) N := by
  exact
    (h1_descendantFullVectorPoincare Q u N).to_localFullCircEstimate
      (fun i => u.grad_coord_memL2_normalizedCubeMeasure i)
      (fullVectorPoincareConstant_nonneg Q)

/-- Legacy finite-depth, disjoint-positive/totalized-real, componentwise-circ
multiscale Poincare compatibility estimate; not an exact manuscript
overlap/Euclidean statement. -/
theorem h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm
    {d : ℕ} [NeZero d] (Q : Cube d) (s : ℝ) (M : ℕ)
    (u : H1Function (openCubeSet Q)) (hs0 : 0 < s) (hs1 : s < 1) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M
        (cubeFluctuation Q (fun x => u x)) ≤
      (fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ i : Fin d,
          circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i) := by
  let C : ℝ := fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)
  have hC : 0 ≤ C := by
    exact mul_nonneg (fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by positivity) _)
  simpa [C, circNegativeBesovNorm] using
    Homogenization.CubeLocalFullCircPoincareVectorEstimate.fluctuation_partialNormTop_two_le_sum_circNorm
      (h1_descendantLocalFullCircPoincare Q u M)
      (Q := Q) (s := s) (C := C) (u := fun x => u x)
      (G := fun x => u.grad x) (M := M)
      (fun i => u.grad_coord_memL2_normalizedCubeMeasure i) hs0.le hs1 hC

end Legacy

end

end Ch01
end Book
end Homogenization
