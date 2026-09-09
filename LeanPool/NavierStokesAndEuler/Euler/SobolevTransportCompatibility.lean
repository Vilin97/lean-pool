/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransport

/-! Exact identification of the nonlinear Sobolev transport with the operator used in metric energy.
-/

@[expose] public section


noncomputable section

namespace EulerSobolevMetricTransport

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevTransport

variable (period : ℝ) [Fact (0 < period)]

/-- The derivative-losing nonlinear transport has exactly the H¹ transport used in the proved metric
pairing bound. -/
theorem transportBilinear_eq_transportOperator {q : ℕ} (hq : 6 ≤ q)
    (κ : ℝ) (m : Vector3) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    value period (transportBilinear period hq (velocityComponents κ m) (velocityComponents_norm κ m
        hκ hm) u v) =
      transportOperator period (by omega : 3 ≤ q) κ m (truncateOperator period q u)
        (restrictOperator period (by omega : 1 ≤ q+1) v) := by
  rw [transportBilinear_value, transportOperator_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end EulerSobolevMetricTransport
