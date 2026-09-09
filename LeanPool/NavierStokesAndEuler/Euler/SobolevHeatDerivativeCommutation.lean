/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevLaplacian

@[expose] public section

/-! Exact heat commutation with the genuine Sobolev derivatives and Laplacian. -/

noncomputable section

namespace EulerSobolevLaplacian

open EulerCylinderSobolevSpace EulerSobolevHeat
open scoped NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual heat commutes with every strong coordinate derivative between consecutive Sobolev levels. -/
theorem derivative_heat {q : ℕ} (i : Fin 4) (v : ℝ≥0) (u : SobolevSpace period (q+1)) :
    derivativeOperator period q i (heatOperator period (q+1) v u) =
      heatOperator period q v (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  rfl

/-- Actual heat commutes with the genuine Laplacian between Sobolev levels. -/
theorem laplacian_heat {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period (q+2)) :
    laplacianOperator period q (heatOperator period (q+2) v u) =
      heatOperator period q v (laplacianOperator period q u) := by
  rw [laplacianOperator_apply, laplacianOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_heat, derivative_heat]

end EulerSobolevLaplacian
