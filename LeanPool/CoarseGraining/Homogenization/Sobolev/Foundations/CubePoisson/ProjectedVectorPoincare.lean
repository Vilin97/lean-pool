/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput
import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.Definitions

/-! # Projected Vector Poincare -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

namespace CubeProjectedVectorPoincareAnalyticInput

variable {d : ℕ} {Q : TriadicCube d}

/-- The chosen Neumann Poisson solution for the fluctuation right-hand side of
an `H¹` function, using the solver bundled in the analytic input. -/
noncomputable def poissonSolutionFor
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    MeanZeroNeumannPoissonSolution Q (u.cubePoissonRhs Q) :=
  Classical.choose
    (h.poisson (u.cubePoissonRhs Q)
      u.cubePoissonRhs_memL2_normalizedCubeMeasure
      u.cubeAverage_cubePoissonRhs)

theorem poissonSolutionFor_equation
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (φ : H1MeanZeroFunction (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x)
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * φ.toH1Function x
        ∂MeasureTheory.volume :=
  (h.poissonSolutionFor u).equation φ

/-- The Poisson equation tested against the mean-zero representative of `u`.
This is the integration-by-parts entry point for the single-cube Poincare
proof. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        vecDot ((h.poissonSolutionFor u).w.toH1Function.grad x) (u.grad x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume := by
  simpa using h.poissonSolutionFor_equation u (u.toMeanZeroOnCube Q)

/-- Coordinate expansion of the Poisson-gradient energy pairing. -/
theorem integral_poissonGradient_vecDot_grad_eq_sum_coord
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
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

/-- The tested Poisson equation in coordinate-sum form. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube_sum_coord
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin d,
        ∫ x in openCubeSet Q,
          (h.poissonSolutionFor u).w.toH1Function.grad x i * u.grad x i
            ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume := by
  rw [← h.integral_poissonGradient_vecDot_grad_eq_sum_coord u]
  exact h.poissonSolutionFor_equation_toMeanZeroOnCube u

/-- The tested Poisson equation rewritten in normalized Besov-pairing form.
The remaining analytic step is to replace the unprojected `u`-gradient
pairings by their projected limits. -/
theorem poissonSolutionFor_equation_toMeanZeroOnCube_sum_pairing
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
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

/-- The finite-depth projected gradient pairings converge to the unprojected
pairing sum appearing in the tested Poisson identity. -/
theorem tendsto_projectedGradient_pairing_sum_poissonSolutionFor
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∑ i : Fin d,
          cubeBesovPairing Q
            (cubeProjection Q (n + 1) (fun x => u.grad x i))
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i))
      Filter.atTop
      (𝓝
        (∑ i : Fin d,
          cubeBesovPairing Q
            (fun x => u.grad x i)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i))) := by
  refine tendsto_finsetSum Finset.univ ?_
  intro i _hi
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hconjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    simp [hconj]
  have hW :
      MeasureTheory.MemLp
        (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
        (cubeBesovConjExponent (2 : ℝ≥0∞)) (normalizedCubeMeasure Q) := by
    simpa [hconj] using
      ((h.poissonSolutionFor u).w.toH1Function.grad_coord_memL2_normalizedCubeMeasure i)
  simpa [hconj] using
    tendsto_cubeBesovPairing_projection_left_of_memLp
      Q (2 : ℝ≥0∞)
      (fun x => u.grad x i)
      (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
      (u.grad_coord_memL2_normalizedCubeMeasure i)
      hW
      (by norm_num) (by simp) hconjTop

/-- Calderon-Zygmund control for the chosen Poisson solution associated to an
`H¹` function's fluctuation right-hand side. -/
theorem poissonSolutionFor_cz
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin d,
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i) ≤
      h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) :=
  h.cz.2 (u.cubePoissonRhs Q)
    u.cubePoissonRhs_memL2_normalizedCubeMeasure
    u.cubeAverage_cubePoissonRhs
    (h.poissonSolutionFor u)

/-- Endpoint projected Besov duality between an `H¹` gradient and the gradient
of the chosen Neumann Poisson solution. -/
theorem projectedGradient_duality_poissonSolutionFor
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) (N : ℕ) :
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.dualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) := by
  exact h.duality.2 N (fun x => u.grad x)
    (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x)
    (fun i => u.grad_coord_memL2_normalizedCubeMeasure i)
    (fun i => (h.poissonSolutionFor u).w.toH1Function.grad_memL2_normalizedCubeMeasure i)

/-- Endpoint Besov duality between an `H¹` gradient and the gradient of the
chosen Neumann Poisson solution, using the full negative Besov seminorm. -/
theorem gradient_duality_poissonSolutionFor
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.fullDualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) := by
  exact h.fullDuality.2 (fun x => u.grad x)
    (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x)
    (fun i => u.grad_coord_memL2_normalizedCubeMeasure i)
    (fun i => (h.poissonSolutionFor u).w.toH1Function.grad_memL2_normalizedCubeMeasure i)

/-- Fixed-depth endpoint-duality bound for the projected gradient pairing sum
against the chosen Poisson solution. -/
theorem abs_projectedGradient_pairing_sum_poissonSolutionFor_le
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) (N : ℕ) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.dualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) := by
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ ∑ i : Fin d,
            |cubeBesovPairing Q
              (cubeProjection Q N (fun x => u.grad x i))
              (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| := by
            exact Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun i : Fin d =>
                cubeBesovPairing Q
                  (cubeProjection Q N (fun x => u.grad x i))
                  (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i))
    _ ≤ h.dualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) :=
          h.projectedGradient_duality_poissonSolutionFor u N

/-- Endpoint-duality bound for the full gradient pairing sum against the
chosen Poisson solution. -/
theorem abs_gradient_pairing_sum_poissonSolutionFor_le
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.fullDualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) := by
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
    _ ≤ h.fullDualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        (∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)) :=
          h.gradient_duality_poissonSolutionFor u

/-- Fixed-depth projected Poisson pairing bound after inserting the
Calderon-Zygmund estimate for the chosen Poisson solution. The nonnegativity
hypothesis is the only algebraic side condition needed to multiply the CZ
inequality into the endpoint-duality bound. -/
theorem abs_projectedGradient_pairing_sum_poissonSolutionFor_le_cz
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) (N : ℕ)
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (cubeProjection Q N (fun x => u.grad x i))) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.dualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (cubeProjection Q N (fun x => u.grad x i))
  let B : ℝ :=
    ∑ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
  let D : ℝ := h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  have hfactor_nonneg : 0 ≤ h.dualityConstant * A := by
    exact mul_nonneg h.dualityConstant_nonneg hdualNonneg
  have hcz : B ≤ D := by
    simpa [B, D] using h.poissonSolutionFor_cz u
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ h.dualityConstant * A * B := by
            simpa [A, B] using h.abs_projectedGradient_pairing_sum_poissonSolutionFor_le u N
    _ ≤ h.dualityConstant * A * D := by
          exact mul_le_mul_of_nonneg_left hcz hfactor_nonneg
    _ = h.dualityConstant * A *
        (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
          rfl

/-- Full-gradient Poisson pairing bound after inserting the Calderon-Zygmund
estimate for the chosen Poisson solution. -/
theorem abs_gradient_pairing_sum_poissonSolutionFor_le_cz
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      h.fullDualityConstant *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x i)
  let B : ℝ :=
    ∑ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)
  let D : ℝ := h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  have hfactor_nonneg : 0 ≤ h.fullDualityConstant * A := by
    exact mul_nonneg h.fullDualityConstant_nonneg hdualNonneg
  have hcz : B ≤ D := by
    simpa [B, D] using h.poissonSolutionFor_cz u
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ h.fullDualityConstant * A * B := by
            simpa [A, B] using h.abs_gradient_pairing_sum_poissonSolutionFor_le u
    _ ≤ h.fullDualityConstant * A * D := by
          exact mul_le_mul_of_nonneg_left hcz hfactor_nonneg
    _ = h.fullDualityConstant * A *
        (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
          rfl

/-- Constant-grouped version of
`abs_projectedGradient_pairing_sum_poissonSolutionFor_le_cz`. -/
theorem abs_projectedGradient_pairing_sum_poissonSolutionFor_le_cz_grouped
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q)) (N : ℕ)
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (cubeProjection Q N (fun x => u.grad x i))) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      (h.dualityConstant * h.czConstant) *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (cubeProjection Q N (fun x => u.grad x i))
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ h.dualityConstant *
            (∑ i : Fin d,
              cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (cubeProjection Q N (fun x => u.grad x i))) *
            (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
            exact h.abs_projectedGradient_pairing_sum_poissonSolutionFor_le_cz
              u N hdualNonneg
    _ = (h.dualityConstant * h.czConstant) *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection Q N (fun x => u.grad x i))) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
          ring

/-- Constant-grouped version of
`abs_gradient_pairing_sum_poissonSolutionFor_le_cz`. -/
theorem abs_gradient_pairing_sum_poissonSolutionFor_le_cz_grouped
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)| ≤
      (h.fullDualityConstant * h.czConstant) *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
  calc
    |∑ i : Fin d,
        cubeBesovPairing Q
          (fun x => u.grad x i)
          (fun x => (h.poissonSolutionFor u).w.toH1Function.grad x i)|
        ≤ h.fullDualityConstant *
            (∑ i : Fin d,
              cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => u.grad x i)) *
            (h.czConstant * cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
            exact h.abs_gradient_pairing_sum_poissonSolutionFor_le_cz
              u hdualNonneg
    _ = (h.fullDualityConstant * h.czConstant) *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) := by
          ring

/-- The squared fluctuation energy is bounded by the absolute full-gradient
Poisson pairing sum. -/
theorem poissonEnergy_le_cubeVolume_mul_abs_gradient_pairing_sum
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
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

/-- Squared fluctuation energy bounded by the full endpoint-duality and
Calderon-Zygmund constants. -/
theorem poissonEnergy_le_full_duality_cz
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    ∫ x in openCubeSet Q, u.cubePoissonRhs Q x * u.cubePoissonRhs Q x
        ∂MeasureTheory.volume ≤
      cubeVolume Q *
        ((h.fullDualityConstant * h.czConstant) *
          (∑ i : Fin d,
            cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
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
        ((h.fullDualityConstant * h.czConstant) *
          (∑ i : Fin d,
            cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)) := by
          exact mul_le_mul_of_nonneg_left
            (h.abs_gradient_pairing_sum_poissonSolutionFor_le_cz_grouped
              u hdualNonneg)
            (cubeVolume_nonneg Q)

/-- Normalized `L²` fluctuation estimate obtained from the full endpoint
duality and Calderon-Zygmund inputs. This is the analytic core of the
infinite-depth vector Poincare theorem. -/
theorem cubeLpNorm_cubePoissonRhs_le_full_duality_cz
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q) ≤
      (h.fullDualityConstant * h.czConstant) *
        (∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) := by
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x i)
  let K : ℝ := h.fullDualityConstant * h.czConstant
  have henergy := h.poissonEnergy_le_full_duality_cz u hdualNonneg
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
    exact mul_nonneg h.fullDualityConstant_nonneg h.czConstant_nonneg
  have hy_nonneg : 0 ≤ K * A := by
    exact mul_nonneg hK_nonneg hdualNonneg
  have hL_nonneg : 0 ≤ L := by
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (u.cubePoissonRhs Q)
  have hsq' : L ^ 2 ≤ (K * A) * L := by
    simpa [mul_assoc] using hsq
  exact nonneg_le_of_sq_le_mul_self hL_nonneg hy_nonneg hsq'

/-- Infinite-depth vector Poincare estimate with the natural constant supplied
by the cube-local analytic input bundle. -/
theorem dualMeanZeroVectorPoincareEstimate_of_h1Function
    (h : CubeProjectedVectorPoincareAnalyticInput Q)
    (u : H1Function (openCubeSet Q))
    (hdualNonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) :
    CubeDualMeanZeroVectorPoincareEstimate Q
      (h.fullDualityConstant * h.czConstant)
      (fun x => u x)
      (fun x => u.grad x) := by
  simpa [CubeDualMeanZeroVectorPoincareEstimate] using
    h.cubeLpNorm_cubePoissonRhs_le_full_duality_cz u hdualNonneg

end CubeProjectedVectorPoincareAnalyticInput

end Homogenization
