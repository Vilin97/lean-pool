/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Embedding

/-! # Cube Besov Poincare -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-!
# Cube Besov-Poincare bridge for H¹ functions

This file exposes the constant-mode-safe full-dual vector Poincare interface
for scalar `H¹` functions on cubes. It is deliberately upstream of the
deterministic Caccioppoli files: the theorem is a pure Sobolev/Besov statement,
with the Neumann/CZ input isolated in the cube Poisson endpoint package.
-/

theorem h1Function_dualFullGradientSum_nonneg
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    0 ≤ ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x i) := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  refine Finset.sum_nonneg ?_
  intro i _hi
  exact cubeBesovDualFullNorm_nonneg
    Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i)
    (by simp [hconj])
    (by simp [hconj])

theorem CubeDualFullVectorPoincareEstimate.of_h1Function_of_analyticInput
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (h : CubeFullVectorPoincareAnalyticInput Q)
    (C : ℝ)
    (hC :
      h.dualityConstant * h.czConstant ≤ C) :
    CubeDualFullVectorPoincareEstimate Q
      C
      (fun x => u x)
      (fun x => u.grad x) := by
  have hdualNonneg := h1Function_dualFullGradientSum_nonneg Q u
  have hanalytic :=
    h.dualFullVectorPoincareEstimate_of_h1Function u hdualNonneg
  have hmono :
      (h.dualityConstant * h.czConstant) *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) := by
    exact mul_le_mul_of_nonneg_right hC hdualNonneg
  exact le_trans hanalytic hmono

/-- Full-dual vector Poincare from the direct `L²` endpoint analytic bundle.
This is the corrected package boundary after the endpoint estimate has already
absorbed the Neumann CZ bound. -/
theorem CubeDualFullVectorPoincareEstimate.of_h1Function_of_l2AnalyticInput
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (C : ℝ)
    (hC : h.endpointConstant ≤ C) :
    CubeDualFullVectorPoincareEstimate Q
      C
      (fun x => u x)
      (fun x => u.grad x) := by
  have hdualNonneg := h1Function_dualFullGradientSum_nonneg Q u
  have hanalytic :=
    h.dualFullVectorPoincareEstimate_of_h1Function u hdualNonneg
  have hmono :
      h.endpointConstant *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) := by
    exact mul_le_mul_of_nonneg_right hC hdualNonneg
  exact le_trans hanalytic hmono

/- Classical cube-local analytic package for the full-dual infinite-depth
vector Poincare theorem.

The Neumann Poisson solver is supplied by the coercive Hilbert layer. The
remaining field-level dependency is the Neumann Calderon-Zygmund estimate,
which feeds the direct `L²` full-dual Poisson-gradient endpoint package. -/

/-- Constant for the cube Neumann Calderon-Zygmund `B¹_{2,∞}` estimate. -/
theorem exists_cubeNeumannPoissonGradientBesovEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, CubeNeumannPoissonGradientBesovEstimate Q C :=
  ⟨cubeNeumannPoissonGradientBesovEnergyConstant Q,
    cubeNeumannPoissonGradientBesovEstimate_of_energy Q⟩

/-- Chosen constant for the cube Neumann Calderon-Zygmund `B¹_{2,∞}` estimate. -/
noncomputable def cubeNeumannPoissonGradientBesovConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  Classical.choose (exists_cubeNeumannPoissonGradientBesovEstimate Q)

/-- Cube Neumann Calderon-Zygmund `B¹_{2,∞}` estimate. -/
theorem cubeNeumannPoissonGradientBesovEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeNeumannPoissonGradientBesovEstimate Q
      (cubeNeumannPoissonGradientBesovConstant Q) :=
  Classical.choose_spec (exists_cubeNeumannPoissonGradientBesovEstimate Q)

/-- Chosen constant for the direct `L²` Poisson-gradient positive dual
test-norm core estimate. -/
noncomputable def cubePoissonGradientDualTestNormL2CoreConstant
    {d : ℕ} [NeZero d] (_Q : TriadicCube d) : ℝ :=
  Legacy.cubeNeumannW22CalderonZygmundConstant d

/-- Direct `L²` positive dual test-norm core estimate for Poisson gradients. -/
theorem cubePoissonGradientDualTestNormL2CoreEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q
      (cubePoissonGradientDualTestNormL2CoreConstant Q) :=
  Legacy.cubeNeumannW22CalderonZygmundRegularity Q

/-- Chosen constant for the direct `L²` Poisson-gradient positive dual
test-norm estimate. The factor `d` is the cost of converting a componentwise
core bound into the summed strictly positive `B` package. -/
noncomputable def cubePoissonGradientDualTestNormL2Constant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  (d : ℝ) * cubePoissonGradientDualTestNormL2CoreConstant Q

/-- Direct `L²` positive dual test-norm estimate for Poisson gradients,
including the strict-positive `B` packaging used by endpoint duality. -/
theorem cubePoissonGradientDualTestNormL2Estimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubePoissonGradientDualTestNormL2Estimate Q
      (cubePoissonGradientDualTestNormL2Constant Q) := by
  simpa [cubePoissonGradientDualTestNormL2Constant] using
    CubePoissonGradientDualTestNormL2CoreEstimate.to_l2Estimate
      (cubePoissonGradientDualTestNormL2CoreEstimate Q)

/-- Chosen constant for the full-dual L² endpoint estimate. -/
noncomputable def cubePoissonGradientFullL2EndpointDualityConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  cubePoissonGradientDualTestNormL2Constant Q

/-- Full-dual Poisson-gradient endpoint estimate with the Poisson-gradient
side already controlled by the normalized `L²` size of the right-hand side. -/
theorem cubePoissonGradientFullL2EndpointDuality
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubePoissonGradientFullL2EndpointDuality Q
      (cubePoissonGradientFullL2EndpointDualityConstant Q) := by
  simpa [cubePoissonGradientFullL2EndpointDualityConstant] using
    CubePoissonGradientFullL2EndpointDuality.of_dualTestNormL2Estimate
      (cubePoissonGradientDualTestNormL2Estimate Q)

/-- Assemble the direct `L²` endpoint analytic input from its named field-level
dependencies. -/
noncomputable def cubeFullVectorPoincareL2AnalyticInput
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeFullVectorPoincareL2AnalyticInput Q where
  poisson := cubeMeanZeroNeumannPoissonSolverOnCube Q
  endpointConstant := cubePoissonGradientFullL2EndpointDualityConstant Q
  endpoint := cubePoissonGradientFullL2EndpointDuality Q

/-- Exact one-cube constant selected by the corrected direct `L²` endpoint
input. -/
noncomputable def cubeFullVectorPoincareAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  cubePoissonGradientFullL2EndpointDualityConstant Q

theorem cubeFullVectorPoincareAnalyticConstant_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    0 ≤ cubeFullVectorPoincareAnalyticConstant Q := by
  exact (cubePoissonGradientFullL2EndpointDuality Q).1

theorem cubeFullVectorPoincareAnalyticConstant_eq_fullL2EndpointDualityConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    cubeFullVectorPoincareAnalyticConstant Q =
      cubePoissonGradientFullL2EndpointDualityConstant Q := by
  rfl

theorem cubeFullVectorPoincareAnalyticConstant_eq_dimensionConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    cubeFullVectorPoincareAnalyticConstant Q =
      (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
  simp [cubeFullVectorPoincareAnalyticConstant,
    cubePoissonGradientFullL2EndpointDualityConstant,
    cubePoissonGradientDualTestNormL2Constant,
    cubePoissonGradientDualTestNormL2CoreConstant]

theorem cubeFullVectorPoincareAnalyticConstant_eq_of_same_dimension
    {d : ℕ} [NeZero d] (Q R : TriadicCube d) :
    cubeFullVectorPoincareAnalyticConstant Q =
      cubeFullVectorPoincareAnalyticConstant R := by
  rw [cubeFullVectorPoincareAnalyticConstant_eq_dimensionConstant Q,
    cubeFullVectorPoincareAnalyticConstant_eq_dimensionConstant R]

/-- Single-cube full-dual vector Poincare with the exact selected corrected
analytic constant. -/
theorem CubeDualFullVectorPoincareEstimate.of_h1Function_analyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    CubeDualFullVectorPoincareEstimate Q
      (cubeFullVectorPoincareAnalyticConstant Q)
      (fun x => u x)
      (fun x => u.grad x) := by
  exact CubeDualFullVectorPoincareEstimate.of_h1Function_of_l2AnalyticInput
    Q u (cubeFullVectorPoincareL2AnalyticInput Q)
    (cubeFullVectorPoincareAnalyticConstant Q)
    (by rfl)

/-- Single-cube full-dual vector Poincare stated with the selected direct
L² endpoint constant. This is definitionally the same constant as
`cubeFullVectorPoincareAnalyticConstant`, but the statement exposes the
endpoint package that future proofs should aim to discharge. -/
theorem CubeDualFullVectorPoincareEstimate.of_h1Function_fullL2EndpointConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    CubeDualFullVectorPoincareEstimate Q
      (cubePoissonGradientFullL2EndpointDualityConstant Q)
      (fun x => u x)
      (fun x => u.grad x) := by
  exact CubeDualFullVectorPoincareEstimate.of_h1Function_of_l2AnalyticInput
    Q u (cubeFullVectorPoincareL2AnalyticInput Q)
    (cubePoissonGradientFullL2EndpointDualityConstant Q)
    (by rfl)

/-- Single-cube full-dual vector Poincare with any constant dominating the
exact selected corrected analytic constant. -/
theorem CubeDualFullVectorPoincareEstimate.of_h1Function_of_analyticConstant_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {C : ℝ} (hC : cubeFullVectorPoincareAnalyticConstant Q ≤ C) :
    CubeDualFullVectorPoincareEstimate Q
      C
      (fun x => u x)
      (fun x => u.grad x) := by
  exact CubeDualFullVectorPoincareEstimate.of_h1Function_of_l2AnalyticInput
    Q u (cubeFullVectorPoincareL2AnalyticInput Q) C
    (by
      simpa [cubeFullVectorPoincareAnalyticConstant, cubeFullVectorPoincareL2AnalyticInput]
        using hC)

/-- Finite-depth descendant full-dual version using an explicit uniform bound
on the selected corrected analytic constants over the descendants that occur
up to depth `N`. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.of_h1Function_of_descendant_analyticConstant_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (N : ℕ) {C : ℝ}
    (hC :
      ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        cubeFullVectorPoincareAnalyticConstant R ≤ C) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      C
      (cubeFluctuation Q (fun x => u x))
      (fun x => u.grad x) N := by
  refine CubeDualFullVectorPoincareEstimate.to_descendant ?_ ?_
  · intro j hj R hR
    simpa using
      (u.restrictToOpenSubcube hR).memL2_normalizedCubeMeasure
  · intro j hj R hR
    simpa using
      CubeDualFullVectorPoincareEstimate.of_h1Function_of_analyticConstant_le
        R (u.restrictToOpenSubcube hR) (hC j hj R hR)

/-! ### Uniform descendant analytic constants -/

/-- Existence of a parent-cube constant that dominates the selected corrected
full-dual analytic Poincare constants on all descendants of the parent. This is
now a formal consequence of the dimension-uniform Neumann `W2,2` / CZ
constant. -/
theorem exists_cubeFullVectorPoincareUniformAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        cubeFullVectorPoincareAnalyticConstant R ≤ C := by
  refine ⟨(d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d, ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg d)
      (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d)
  · intro j R hR
    simp [cubeFullVectorPoincareAnalyticConstant,
      cubePoissonGradientFullL2EndpointDualityConstant,
      cubePoissonGradientDualTestNormL2Constant,
      cubePoissonGradientDualTestNormL2CoreConstant]

/-- Explicit dimension-only parent-cube constant dominating the selected
corrected full-dual analytic constants on all descendants of the parent. -/
noncomputable def cubeFullVectorPoincareUniformAnalyticConstant
    {d : ℕ} [NeZero d] (_Q : TriadicCube d) : ℝ :=
  (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d

theorem cubeFullVectorPoincareUniformAnalyticConstant_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    0 ≤ cubeFullVectorPoincareUniformAnalyticConstant Q := by
  simpa [cubeFullVectorPoincareUniformAnalyticConstant] using
    mul_nonneg (Nat.cast_nonneg d)
      (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d)

theorem cubeFullVectorPoincareAnalyticConstant_le_uniformAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (j : ℕ)
    (R : TriadicCube d) (_hR : R ∈ descendantsAtDepth Q j) :
    cubeFullVectorPoincareAnalyticConstant R ≤
      cubeFullVectorPoincareUniformAnalyticConstant Q := by
  simp [cubeFullVectorPoincareUniformAnalyticConstant,
    cubeFullVectorPoincareAnalyticConstant,
    cubePoissonGradientFullL2EndpointDualityConstant,
    cubePoissonGradientDualTestNormL2Constant,
    cubePoissonGradientDualTestNormL2CoreConstant]

/-- All-depth descendant full-dual theorem with the selected corrected uniform
analytic constant. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.of_h1Function_uniformAnalyticConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      (cubeFullVectorPoincareUniformAnalyticConstant Q)
      (cubeFluctuation Q (fun x => u x))
      (fun x => u.grad x) N :=
  CubeDescendantDualFullVectorPoincareEstimate.of_h1Function_of_descendant_analyticConstant_le
    Q u N
    (by
      intro j _hj R hR
      exact cubeFullVectorPoincareAnalyticConstant_le_uniformAnalyticConstant Q j R hR)

/-- Public cube Poincare constant for the corrected full-dual theorem. It is
the selected parent-cube constant that dominates the exact full-dual analytic
constants on all descendants. -/
noncomputable def fullVectorPoincareCubeConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) : ℝ :=
  cubeFullVectorPoincareUniformAnalyticConstant Q

theorem fullVectorPoincareCubeConstant_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    0 ≤ fullVectorPoincareCubeConstant Q := by
  simpa [fullVectorPoincareCubeConstant] using
    cubeFullVectorPoincareUniformAnalyticConstant_nonneg Q

theorem fullVectorPoincareCubeConstant_eq_dimensionConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    fullVectorPoincareCubeConstant Q =
      (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d := by
  rfl

theorem cubeFullVectorPoincareAnalyticConstant_le_fullVectorPoincareCubeConstant
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    cubeFullVectorPoincareAnalyticConstant Q ≤ fullVectorPoincareCubeConstant Q := by
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  simpa [fullVectorPoincareCubeConstant] using
    cubeFullVectorPoincareAnalyticConstant_le_uniformAnalyticConstant Q 0 Q hQ

theorem CubeDualFullVectorPoincareEstimate.of_h1Function
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    CubeDualFullVectorPoincareEstimate Q
      (fullVectorPoincareCubeConstant Q)
      (fun x => u x)
      (fun x => u.grad x) := by
  exact CubeDualFullVectorPoincareEstimate.of_h1Function_of_analyticConstant_le
    Q u (cubeFullVectorPoincareAnalyticConstant_le_fullVectorPoincareCubeConstant Q)

/-- Descendant infinite-depth full-dual Poincare for an `H¹` function, obtained
from the corrected parent-cube uniform analytic constant on each descendant. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.of_h1Function
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      (fullVectorPoincareCubeConstant Q)
      (cubeFluctuation Q (fun x => u x))
      (fun x => u.grad x) N := by
  simpa [fullVectorPoincareCubeConstant] using
    CubeDescendantDualFullVectorPoincareEstimate.of_h1Function_uniformAnalyticConstant
      Q u N

end Homogenization
