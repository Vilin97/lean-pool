/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import LeanPool.OSforGFF.Measure.GaussianFreeField
import LeanPool.OSforGFF.OS.OS3_ReflectionPositivity
import LeanPool.OSforGFF.OS.OS0_Analyticity
import LeanPool.OSforGFF.OS.OS1_Regularity
import LeanPool.OSforGFF.OS.OS2_Invariance
import LeanPool.OSforGFF.OS.OS4_Clustering
import LeanPool.OSforGFF.OS.OS4_Ergodicity

/-!
# Master Theorem

Assembles OS0–OS4 into `gaussianFreeField_satisfies_all_OS_axioms`:

- OS0 (Analyticity): Hartogs + Fernique — `OS.OS0_Analyticity`
- OS1 (Regularity): Plancherel + momentum bound — `OS.OS1_Regularity`
- OS2 (Euclidean Invariance): C depends on |x−y| — `OS.OS2_Invariance`
- OS3 (Reflection Positivity): Schwinger parametrization + Schur–Hadamard —
`OS.OS3_ReflectionPositivity`
- OS4 (Clustering): Gaussian factorization + convolution decay — `OS.OS4_Clustering`
- OS4 (Ergodicity): polynomial clustering α=6 → L² convergence — `OS.OS4_Ergodicity`

Unconditional theorem: only requires m > 0.
-/

open scoped BigOperators

namespace OSforGFF

noncomputable section

/-! ## Master OS theorem for the free GFF -/

/-- Master theorem: the free GFF satisfies all Osterwalder-Schrader axioms.
- OS0 is supplied by `QFT.gaussianFreeField_satisfies_OS0` via the holomorphic integral theorem
- OS1 is supplied by `gaussianFreeField_satisfies_OS1_revised` via Fourier/momentum space methods
- OS2 is supplied by `gaussian_satisfies_OS2` via Euclidean invariance of the free covariance
- OS3 is supplied by `QFT.gaussianFreeField_OS3` via the Schur-Hadamard argument (complex star
formulation)
- OS4 Clustering is supplied by `QFT.gaussianFreeField_satisfies_OS4` via Gaussian factorization
- OS4 Ergodicity is supplied by polynomial clustering (α=6) → ergodicity

This is an unconditional theorem with no assumptions beyond m > 0.
-/
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF m) where
  -- OS0 from the holomorphic integral theorem (differentiation under the integral)
  os0 := QFT.gaussianFreeField_satisfies_OS0 m
  -- OS1 from the free field theorem using Fourier/momentum space methods
  os1 := gaussianFreeField_satisfies_OS1_revised m
  -- OS2 from Euclidean invariance of free covariance
  os2 := gaussian_satisfies_OS2 (μ_GFF m)
    (by exact isGaussianGJ_gaussianFreeField_free m)
    (QFT.CovarianceEuclideanInvariantℂ_μ_GFF m)
  -- OS3 from the Schur-Hadamard argument (complex star formulation)
  os3 := QFT.gaussianFreeField_OS3 m
  -- OS4 Clustering (Gaussian factorization and covariance decay)
  os4_clustering := QFT.gaussianFreeField_satisfies_OS4 m
  -- OS4 Ergodicity: polynomial clustering (α=6) implies ergodicity
  os4_ergodicity := OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity m
    (QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering m 6 (by norm_num))

end

end OSforGFF
