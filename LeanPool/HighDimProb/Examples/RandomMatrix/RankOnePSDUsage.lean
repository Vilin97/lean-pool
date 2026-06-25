/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.NTKGramUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage
import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import LeanPool.HighDimProb.RandomMatrix.Spectral

/-!
# Rank-one PSD usage example

This examples-only file records the structural facts about rank-one outer
products used by the NTK, random-feature kernel, and gradient covariance
examples. `rankOneOuter` is only a domain-facing alias for the core
`rankOneMatrix`; new reusable matrix facts should live in the core
RandomMatrix modules rather than being reproved here.
-/

namespace HighDimProb.Examples.RandomMatrix.RankOnePSDUsage

open scoped BigOperators

noncomputable section

/-- A finite vector used to build a rank-one covariance or Gram matrix. -/
abbrev RankOneVector (n : Nat) :=
  Fin (n + 1) -> Real

/-- Rank-one outer product `v v^T`. -/
def rankOneOuter {n : Nat} (v : RankOneVector n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  rankOneMatrix v

@[simp]
theorem rankOneOuter_apply {n : Nat} (v : RankOneVector n)
    (i j : Fin (n + 1)) :
    rankOneOuter v i j = v i * v j := by
  rfl

/-- Rank-one outer products are symmetric. -/
theorem rankOneOuter_symmetric {n : Nat} (v : RankOneVector n) :
    IsSymmetricMatrix (rankOneOuter v) := by
  simpa [rankOneOuter] using (isPSDMatrix_rankOneMatrix v).1

/-- Rank-one outer products are self-adjoint over the reals. -/
theorem rankOneOuter_selfAdjoint {n : Nat} (v : RankOneVector n) :
    IsSelfAdjointMatrix (rankOneOuter v) := by
  simpa [rankOneOuter] using isSelfAdjointMatrix_rankOneMatrix v

/-- The quadratic form of `v v^T` is the square of the projection onto `v`. -/
theorem rankOneOuter_matrixQuadraticForm {n : Nat}
    (v x : RankOneVector n) :
    matrixQuadraticForm (rankOneOuter v) x =
      (Finset.univ.sum fun i : Fin (n + 1) => v i * x i) ^ 2 := by
  simpa [rankOneOuter] using rankOneMatrix_quadraticForm_eq_inner_sq v x

/-- The rank-one quadratic form is nonnegative. -/
theorem rankOneOuter_quadraticForm_nonneg {n : Nat}
    (v x : RankOneVector n) :
    0 <= matrixQuadraticForm (rankOneOuter v) x := by
  rw [rankOneOuter_matrixQuadraticForm]
  exact sq_nonneg _

/-- Rank-one outer products are PSD in the HighDimProb matrix-order API. -/
theorem rankOneOuter_psd {n : Nat} (v : RankOneVector n) :
    IsPSDMatrix (rankOneOuter v) := by
  simpa [rankOneOuter] using isPSDMatrix_rankOneMatrix v

/-- The NTK example's outer product is the same rank-one construction. -/
theorem ntkGramOuter_eq_rankOneOuter {n : Nat}
    (v : NTKGramUsage.NTKFeatureVector n) :
    NTKGramUsage.ntkGramOuter v = rankOneOuter v := by
  rfl

/-- The random-feature example's outer product is the same rank-one construction. -/
theorem featureKernelOuter_eq_rankOneOuter {n : Nat}
    (phi : RandomFeatureKernelUsage.FeatureVector n) :
    RandomFeatureKernelUsage.featureKernelOuter phi = rankOneOuter phi := by
  rfl

/-- The gradient covariance example's outer product is the same rank-one construction. -/
theorem gradientOuter_eq_rankOneOuter {n : Nat}
    (g : GradientCovarianceUsage.GradientVector n) :
    GradientCovarianceUsage.gradientOuter g = rankOneOuter g := by
  rfl

/-- Rank-one gradient covariance contributions are PSD pointwise. -/
theorem gradientCovarianceContribution_psd {batch n : Nat}
    (G : GradientCovarianceUsage.GradientTable batch n) (b : Fin batch) :
    IsPSDMatrix (GradientCovarianceUsage.gradientCovarianceContribution G b) := by
  simpa [GradientCovarianceUsage.gradientCovarianceContribution,
    GradientCovarianceUsage.gradientOuter] using isPSDMatrix_rankOneMatrix (G b)

/-- Rank-one random-feature kernel contributions are PSD pointwise. -/
theorem featureKernelContribution_psd {numFeatures n : Nat}
    (Phi : RandomFeatureKernelUsage.FeatureTable numFeatures n)
    (a : Fin numFeatures) :
    IsPSDMatrix (RandomFeatureKernelUsage.featureKernelContribution Phi a) := by
  simpa [RandomFeatureKernelUsage.featureKernelContribution,
    RandomFeatureKernelUsage.featureKernelOuter,
    NTKGramUsage.ntkGramOuter] using isPSDMatrix_rankOneMatrix (Phi a)

end

end HighDimProb.Examples.RandomMatrix.RankOnePSDUsage
