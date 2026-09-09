/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData

/-! Exact repeated restriction of coherent prescribed coefficient and field data. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionData

open Set EulerCorrectionLowerData EulerCylinderSobolevSpace

variable (period : ℝ) [Fact (0 < period)]

/-- Two genuine lower-data operations return precisely the prescribed lower-order data, including
the approximation and residual paths. -/
theorem Data.lower_twice {T : ℝ} (A : Data period T) (q : ℕ) :
    lowerData period
      (lowerData period (A.atOrder period ((q+1)+1)) (A.metric.jet (q+1)) (A.linear.jet (q+1))
        (fun i => (A.quadratic i).jet (q+1)) (A.metric.continuous (q+1))
        (A.linear.continuous (q+1)) (fun i => (A.quadratic i).continuous (q+1)))
      (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
      (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q) =
        A.atOrder period q := by
  unfold lowerData Data.atOrder
  congr 1
  · rw [A.approximation.truncate period ((q+1)+1),A.approximation.truncate period (q+1)]
  · rw [A.residual.truncate period (q+1),A.residual.truncate period q]

end EulerAllOrderCorrectionData
