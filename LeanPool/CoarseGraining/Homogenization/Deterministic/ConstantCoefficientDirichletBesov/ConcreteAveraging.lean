/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingGradientExplicit
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.DirichletBridge

/-! # Concrete Averaging -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Residual constant for the concrete smooth overlap averaging operator. -/
noncomputable def concreteOverlapAveragingResidualConstant (d : ℕ) : ℝ :=
  Real.sqrt (((3 ^ d : ℕ) : ℝ) * (3 ^ d : ℝ) *
    (Fintype.card (Fin d) : ℝ))

theorem concreteOverlapAveragingResidualConstant_nonneg (d : ℕ) :
    0 ≤ concreteOverlapAveragingResidualConstant d := by
  unfold concreteOverlapAveragingResidualConstant
  exact Real.sqrt_nonneg _

/-- Gradient constant for the concrete smooth overlap averaging operator. -/
noncomputable def concreteOverlapAveragingGradientConstant (d : ℕ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
    (Real.sqrt ((3 ^ d : ℝ) * ((3 ^ d : ℝ) *
        (Fintype.card (Fin d) : ℝ))) *
      smoothOverlapPartitionDerivativeConstant d)

theorem concreteOverlapAveragingGradientConstant_nonneg (d : ℕ) :
    0 ≤ concreteOverlapAveragingGradientConstant d := by
  unfold concreteOverlapAveragingGradientConstant
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (mul_nonneg (Real.sqrt_nonneg _)
      (smoothOverlapPartitionDerivativeConstant_nonneg d))

/-- Dimension-only constant controlling both the residual and the scaled
gradient of the concrete smooth overlap averaging competitor. -/
noncomputable def concreteOverlapAveragingCompetitorConstant (d : ℕ) : ℝ :=
  concreteOverlapAveragingResidualConstant d +
    concreteOverlapAveragingGradientConstant d

theorem concreteOverlapAveragingCompetitorConstant_nonneg (d : ℕ) :
    0 ≤ concreteOverlapAveragingCompetitorConstant d := by
  unfold concreteOverlapAveragingCompetitorConstant
  exact add_nonneg
    (concreteOverlapAveragingResidualConstant_nonneg d)
    (concreteOverlapAveragingGradientConstant_nonneg d)

theorem concreteSmoothOverlapPartition_residualConstant
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (concreteSmoothOverlapPartition Q j).residualConstant =
      concreteOverlapAveragingResidualConstant d := by
  rfl

theorem concreteSmoothOverlapPartition_gradientConstant
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (concreteSmoothOverlapPartition Q j).gradientConstant =
      concreteOverlapAveragingGradientConstant d := by
  rfl

theorem concreteSmoothOverlapPartition_residualConstant_le_competitorConstant
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (concreteSmoothOverlapPartition Q j).residualConstant ≤
      concreteOverlapAveragingCompetitorConstant d := by
  rw [concreteSmoothOverlapPartition_residualConstant]
  unfold concreteOverlapAveragingCompetitorConstant
  exact le_add_of_nonneg_right
    (concreteOverlapAveragingGradientConstant_nonneg d)

theorem concreteSmoothOverlapPartition_gradientConstant_le_competitorConstant
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (concreteSmoothOverlapPartition Q j).gradientConstant ≤
      concreteOverlapAveragingCompetitorConstant d := by
  rw [concreteSmoothOverlapPartition_gradientConstant]
  unfold concreteOverlapAveragingCompetitorConstant
  exact le_add_of_nonneg_left
    (concreteOverlapAveragingResidualConstant_nonneg d)

/-- The concrete normalized smooth overlap partition supplies the one-depth
averaging competitor estimate with a dimension-only constant. -/
theorem cubeKBesovOverlapAveragingCompetitorEstimate_concrete
    (d : ℕ) :
    CubeKBesovOverlapAveragingCompetitorEstimate d
      (concreteOverlapAveragingCompetitorConstant d) := by
  intro Q h j hh
  let P : SmoothOverlapPartition Q j := concreteSmoothOverlapPartition Q j
  have hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S) := by
    intro S hS
    exact memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
      hS hh
  refine ⟨P.averagingCompetitor h, ?_, ?_⟩
  · have hres :
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => h x - P.averagingField h x) ≤
          P.residualConstant *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
      P.cubeLpNorm_sub_averagingField_le_residualConstant_mul_sqrt_depthAverage
        h hloc
    have hconst :
        P.residualConstant ≤ concreteOverlapAveragingCompetitorConstant d := by
      simpa [P] using
        concreteSmoothOverlapPartition_residualConstant_le_competitorConstant
          Q j
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
      Real.sqrt_nonneg _
    calc
      cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => h x - (P.averagingCompetitor h).toField x)
          =
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => h x - P.averagingField h x) := by
            rfl
      _ ≤
          P.residualConstant *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
        hres
      _ ≤
          concreteOverlapAveragingCompetitorConstant d *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
        mul_le_mul_of_nonneg_right hconst hsqrt_nonneg
  · have hgrad :
        Real.rpow (3 : ℝ) (-(j : ℝ)) *
            (P.averagingCompetitor h).relativeGradientCoordL2NormSum ≤
          P.gradientConstant *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
      P.rpow_neg_mul_relativeGradientCoordL2NormSum_averagingCompetitor_le_sqrt_depthAverage
        h hloc
    have hconst :
        P.gradientConstant ≤ concreteOverlapAveragingCompetitorConstant d := by
      simpa [P] using
        concreteSmoothOverlapPartition_gradientConstant_le_competitorConstant
          Q j
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) :=
      Real.sqrt_nonneg _
    exact hgrad.trans
      (mul_le_mul_of_nonneg_right hconst hsqrt_nonneg)

/-- Concrete replacement for the finite-level K/overlapping comparison input
used by the public constant-coefficient Dirichlet Besov theorem. -/
theorem cubeKBesovPartialBoundByOverlappingPositiveUniform_concrete
    (d : ℕ) :
    CubeKBesovPartialBoundByOverlappingPositiveUniform d
      (2 * concreteOverlapAveragingCompetitorConstant d) :=
  cubeKBesovPartialBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
    (concreteOverlapAveragingCompetitorConstant_nonneg d)
    (cubeKBesovOverlapAveragingCompetitorEstimate_concrete d)

/-- Concrete replacement for the finite-level K/overlapping comparison input
used by the public constant-coefficient Dirichlet Besov theorem. -/
theorem cubeKBesovPartialBoundByOverlappingPositive_concrete
    (d : ℕ) :
    CubeKBesovPartialBoundByOverlappingPositive d :=
  (cubeKBesovPartialBoundByOverlappingPositiveUniform_concrete d).to_partialBound

end

end Homogenization
