/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ArbitraryCubeEndpoint

/-! # Regularity -/

@[expose] public section

namespace Homogenization

/-!
# Legacy positive-test Neumann compatibility package

This module packages the downstream positive-test endpoint for Neumann Poisson
solutions.  It does **not** state the manuscript's weak-Hessian
Calderon--Zygmund estimate; that literal statement lives in the exact
Euclidean-normalized lane.
-/

namespace Legacy

open scoped ENNReal

noncomputable section

/-- Legacy name for the downstream positive-test core estimate.  This is a
compatibility wrapper, not a weak-Hessian Calderon--Zygmund statement. -/
def CubeNeumannW22CalderonZygmundRegularity {d : ℕ}
    (Q : TriadicCube d) (C : ℝ) : Prop :=
  CubePoissonGradientDualTestNormL2CoreEstimate Q C

/-- Dimension-uniform legacy positive-test compatibility predicate on cubes. -/
def CubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : TriadicCube d, CubeNeumannW22CalderonZygmundRegularity Q C

/-- Chosen dimension-only constant for the legacy positive-test compatibility
package, obtained from the reflected-parent depth and component-average
constants. -/
noncomputable def cubeNeumannW22CalderonZygmundConstant
    (d : ℕ) [NeZero d] : ℝ :=
  originCubeWeakInteriorDepthConstantExact d 0 +
    (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue

theorem cubeNeumannW22CalderonZygmundConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ cubeNeumannW22CalderonZygmundConstant d := by
  exact add_nonneg
    (originCubeWeakInteriorDepthConstantExact_nonneg d 0)
    (mul_nonneg (Nat.cast_nonneg d)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)

/-- Selected legacy positive-test compatibility estimate on a cube. -/
theorem cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22CalderonZygmundConstant d) := by
  have hcore :=
    MeanZeroNeumannPoissonSolution.cubePoissonGradientDualTestNormL2CoreEstimate_cube Q
  have hdepth := cubeWeakInteriorDepthConstant_eq_dimensionConstant Q
  have havg := cubePoissonGradientAverageConstant_eq_dimensionConstant Q
  simpa [CubeNeumannW22CalderonZygmundRegularity,
    cubeNeumannW22CalderonZygmundConstant, hdepth, havg] using hcore

/-- The legacy positive-test compatibility package has the explicit constant
above in every dimension. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularityInDimension d C := by
  exact ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundConstant_nonneg d,
    cubeNeumannW22CalderonZygmundRegularity⟩

/-- Local existence form of the legacy positive-test compatibility input. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularity Q C :=
  ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundRegularity Q⟩

/-- Downstream positive-test core estimate from the legacy compatibility
package. -/
theorem exists_cubePoissonGradientDualTestNormL2CoreEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, CubePoissonGradientDualTestNormL2CoreEstimate Q C := by
  exact
    ⟨cubeNeumannW22CalderonZygmundConstant d,
      cubeNeumannW22CalderonZygmundRegularity Q⟩

end

end Legacy

end Homogenization
