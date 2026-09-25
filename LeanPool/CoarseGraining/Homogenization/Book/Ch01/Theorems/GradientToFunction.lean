/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.MultiscalePoincare
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Bounds

/-! # Gradient To Function -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-!
# From gradient control to function control

This file retains the legacy disjoint-positive, totalized-real,
componentwise-circ compatibility surface behind the note's `\nabla u` to `u`
Besov-scale estimate. It is not the exact manuscript overlap/Euclidean
statement.
-/

namespace Legacy

/-- Legacy H1-facing infinite-depth `\nabla u`-to-`u` Besov-scale
compatibility estimate, using the disjoint-positive, totalized-real,
componentwise-circ conventions rather than the exact manuscript
overlap/Euclidean statement.

The full-dual/H1 Poincare theorem supplies the local full-circ bounds
internally, so this statement has no explicit `hlocal` contract. -/
theorem gradientToFunctionBesovScale_from_h1 {d : ℕ} [NeZero d]
    (Q : Cube d) (s : ℝ) (u : H1Function (openCubeSet Q))
    (hs0 : 0 < s) (hs1 : s < 1) :
    positiveBesovNormTop Q s (2 : ℝ≥0∞)
        (cubeFluctuation Q (fun x => u x)) ≤
      (fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ i : Fin d,
          circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i) := by
  let C : ℝ := fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)
  have hC : 0 ≤ C := by
    exact mul_nonneg (fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by positivity) _)
  unfold positiveBesovNormTop
  refine csSup_le ?_ ?_
  · exact
      ⟨cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) 1
        (cubeFluctuation Q (fun x => u x)), ⟨0, by simp⟩⟩
  · intro r hr
    rcases hr with ⟨N, rfl⟩
    simpa [C] using
      Homogenization.CubeLocalFullCircPoincareVectorEstimate.fluctuation_partialNormTop_two_le_sum_circNorm
        (h1_descendantLocalFullCircPoincare Q u (N + 1))
        (Q := Q) (s := s) (C := C) (u := fun x => u x)
        (G := fun x => u.grad x) (M := N + 1)
        (fun i => u.grad_coord_memL2_normalizedCubeMeasure i) hs0.le hs1 hC

end Legacy

end

end Ch01
end Book
end Homogenization
