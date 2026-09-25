/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.Definitions

/-! # Full Vector Poincare L2 -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

namespace CubeFullVectorPoincareL2AnalyticInput

variable {d : ℕ} {Q : TriadicCube d}

/-- The chosen Neumann Poisson solution for the fluctuation right-hand side of
an `H¹` function, using the solver bundled with the direct `L²` endpoint input. -/
noncomputable def poissonSolutionFor
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    MeanZeroNeumannPoissonSolution Q (u.cubePoissonRhs Q) :=
  Classical.choose
    (h.poisson (u.cubePoissonRhs Q)
      u.cubePoissonRhs_memL2_normalizedCubeMeasure
      u.cubeAverage_cubePoissonRhs)

theorem poissonSolutionFor_equation
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (φ : H1MeanZeroFunction (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x)
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * φ.toH1Function x
        ∂MeasureTheory.volume :=
  (h.poissonSolutionFor u).equation φ

/-- The direct-`L²` Poisson equation tested against the mean-zero
representative of `u`. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x) (u.grad x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume := by
  simpa using h.poissonSolutionFor_equation u (u.toMeanZeroOnCube Q)

/-- Coordinate expansion of the direct-`L²` Poisson-gradient energy pairing. -/
theorem integral_poissonGradient_vecDot_grad_eq_sum_coord
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x) (u.grad x)
          ∂MeasureTheory.volume =
      ∑ i : Fin d,
        ∫ x in openCubeSet Q,
          (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
            ∂MeasureTheory.volume := by
  calc
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x) (u.grad x)
          ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            ∑ i : Fin d,
              (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
              ∂MeasureTheory.volume := by
            simp [vecDot]
    _ = ∑ i : Fin d,
        ∫ x in openCubeSet Q,
          (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
            ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _hi
          exact (memScalarL2_coord_of_memVectorL2
              (U := openCubeSet Q)
              (h.poissonSolutionFor u).w.toH1Function.grad_memVectorL2 i).integrable_mul
            (memScalarL2_coord_of_memVectorL2
              (U := openCubeSet Q) u.grad_memVectorL2 i)

/-- The direct-`L²` tested Poisson equation in coordinate-sum form. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube_sum_coord
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin d,
        ∫ x in openCubeSet Q,
          (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
            ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume := by
  rw [← h.integral_poissonGradient_vecDot_grad_eq_sum_coord u]
  exact h.poissonSolutionFor_equation_toMeanZeroOnCube u

/-- The direct-`L²` tested Poisson equation rewritten in normalized
Besov-pairing form. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube_sum_pairing
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    cubeVolume Q *
        (∑ i : Fin d,
          cubeBesovPairing Q
            (fun x => u.grad x i)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume := by
  calc
    cubeVolume Q *
        (∑ i : Fin d,
          cubeBesovPairing Q
            (fun x => u.grad x i)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i))
        = ∑ i : Fin d,
            cubeVolume Q *
              cubeBesovPairing Q
                (fun x => u.grad x i)
                (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i) := by
            rw [Finset.mul_sum]
    _ = ∑ i : Fin d,
        ∫ x in openCubeSet Q,
          (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
            ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          calc
            cubeVolume Q *
                cubeBesovPairing Q
                  (fun x => u.grad x i)
                  (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
                = cubeVolume Q *
                    cubeBesovPairing Q
                      (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
                      (fun x => u.grad x i) := by
                    rw [cubeBesovPairing_comm]
            _ = ∫ x in openCubeSet Q,
                  (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
                    ∂MeasureTheory.volume := by
                  rw [← setIntegral_openCubeSet_mul_eq_cubeVolume_mul_cubeBesovPairing]
    _ = ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume :=
          h.poissonSolutionFor_equation_toMeanZeroOnCube_sum_coord u

/-- Direct `L²` endpoint control for an `H¹` gradient paired against the
chosen Neumann Poisson gradient. -/
theorem gradient_l2Endpoint_poissonSolutionFor
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.endpointConstant *
        (∑ i : Fin d,
          cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
  exact h.endpoint.2 (u.cubePoissonRhs Q)
    u.cubePoissonRhs_memL2_normalizedCubeMeasure
    u.cubeAverage_cubePoissonRhs
    (h.poissonSolutionFor u)
    (fun x => u.grad x)
    (fun i => u.grad_coord_memL2_normalizedCubeMeasure i)

/-- Absolute-value bound for the full gradient pairing sum from the direct
`L²` endpoint. -/
theorem abs_gradient_pairing_sum_poissonSolutionFor_le_l2Endpoint
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.endpointConstant *
        (∑ i : Fin d,
          cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ ∑ i : Fin d,
            |cubeBesovPairing Q
              (fun x => u.grad x i)
              (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| := by
            exact Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun i : Fin d =>
                cubeBesovPairing Q
                  (fun x => u.grad x i)
                  (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i))
    _ ≤ h.endpointConstant *
        (∑ i : Fin d,
          cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) :=
          h.gradient_l2Endpoint_poissonSolutionFor u

/-- The squared fluctuation energy is bounded by the absolute full-gradient
Poisson pairing sum for the direct `L²` endpoint route. -/
theorem poissonEnergy_le_cubeVolume_mul_abs_gradient_pairing_sum
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume ≤
      cubeVolume Q *
        |∑ i : Fin d,
          cubeBesovPairing Q
            (fun x => u.grad x i)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| := by
  rw [← h.poissonSolutionFor_equation_toMeanZeroOnCube_sum_pairing u]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (cubeVolume_nonneg Q)

/-- Squared fluctuation energy bounded by the direct full-dual `L²` endpoint
constant. -/
theorem poissonEnergy_le_full_l2Endpoint
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume ≤
      cubeVolume Q *
        (h.endpointConstant *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
  calc
    ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume
        ≤ cubeVolume Q *
            |∑ i : Fin d,
              cubeBesovPairing Q
                (fun x => u.grad x i)
                (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| :=
            h.poissonEnergy_le_cubeVolume_mul_abs_gradient_pairing_sum u
    _ ≤ cubeVolume Q *
        (h.endpointConstant *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
          exact mul_le_mul_of_nonneg_left
            (h.abs_gradient_pairing_sum_poissonSolutionFor_le_l2Endpoint u)
            (cubeVolume_nonneg Q)

/-- Normalized `L²` fluctuation estimate obtained directly from the full-dual
`L²` endpoint package. -/
theorem cubeLpNorm_cubePoissonRhs_le_full_l2Endpoint
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) ≤
      h.endpointConstant *
        (∑ i : Fin d,
          cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) := by
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x i)
  let K : ℝ := h.endpointConstant
  have henergy := h.poissonEnergy_le_full_l2Endpoint u
  have henergy_norm :
      cubeVolume Q * L ^ (2 : ℝ) ≤ cubeVolume Q * (K * A * L) := by
    calc
      cubeVolume Q * L ^ (2 : ℝ)
          = ∫ x in openCubeSet Q,
              u.cubePoissonRhs Q x * u.cubePoissonRhs Q x ∂MeasureTheory.volume := by
              rw [setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
                Q (u.cubePoissonRhs Q) u.cubePoissonRhs_memL2_normalizedCubeMeasure]
      _ ≤ cubeVolume Q * (K * A * L) := by
            simpa [L, A, K, mul_assoc] using henergy
  have hsq : L ^ (2 : ℝ) ≤ K * A * L := by
    exact (mul_le_mul_iff_of_pos_left (cubeVolume_pos Q)).mp henergy_norm
  have hK_nonneg : 0 ≤ K := by
    exact h.endpointConstant_nonneg
  have hy_nonneg : 0 ≤ K * A := by
    exact mul_nonneg hK_nonneg hdualNonneg
  have hL_nonneg : 0 ≤ L := by
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  have hsq' : L ^ 2 ≤ (K * A) * L := by
    simpa [mul_assoc] using hsq
  exact nonneg_le_of_sq_le_mul_self hL_nonneg hy_nonneg hsq'

/-- Infinite-depth full-dual vector Poincare estimate from the direct
`L²` endpoint input bundle. -/
theorem dualFullVectorPoincareEstimate_of_h1Function
    (h : CubeFullVectorPoincareL2AnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    CubeDualFullVectorPoincareEstimate Q
      h.endpointConstant
      (fun x => u x)
      (fun x => u.grad x) := by
  simpa [CubeDualFullVectorPoincareEstimate] using
    h.cubeLpNorm_cubePoissonRhs_le_full_l2Endpoint u hdualNonneg

end CubeFullVectorPoincareL2AnalyticInput

end Homogenization
