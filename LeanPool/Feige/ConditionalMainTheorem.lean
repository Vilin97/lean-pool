/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.GeometryBridge
import LeanPool.Feige.Sharpness

/-!
# Conditional assembly of the unit-slack theorem

This module states the `δ = 1` specialization of the paper's main result in
terms of three structural inputs.  The reduction and extremal construction
are fully discharged: Theorem 2.1, the simplex/exponential identification
of (2.1), and the `α = 0` centroid-halfspace inequality are the only inputs.
-/

namespace Feige

/-- The `δ = 1` specialization of Theorem 1.1, assembled from Theorem 2.1
and the two geometric facts identifying and bounding the Dirichlet
statistic. -/
theorem sharp_unit_slack_feige_of_paper_inputs
    {n : ℕ}
    (hcal : UniversalCalibration
      (dirichletK : (Fin n → ℝ) → ℝ))
    (hid : SimplexExponentialIdentification n)
    (hcentroid : SimplexCentroidHalfspaceProperty (ι := Fin n)) :
    IsOptimalFixedDimensionalFeigeBound n (sharpConstant n) := by
  exact sharpConstant_is_optimal_of_structural_inputs
    (dirichletK : (Fin n → ℝ) → ℝ) hcal
    (dirichletK_largeSumBridge_of_simplex hid hcentroid)

end Feige
