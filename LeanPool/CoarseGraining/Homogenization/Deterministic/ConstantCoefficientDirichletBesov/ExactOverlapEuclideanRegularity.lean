/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanFullComparison

/-!
# Exact overlap-Besov regularity for the centered-cube Dirichlet problem

This module proves the manuscript-facing fractional Dirichlet estimate from
`coarsegraining/chapters/ch1_function_spaces.tex:782-930`.  It combines the
exact overlap-Besov/physical-Sobolev full-norm equivalence with the all-scale
constant-coefficient Dirichlet estimate.  All comparison, endpoint, scale,
and representative inputs remain proof-internal.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- Fractional Dirichlet regularity for constant-coefficient equations,
formalizing `coarsegraining/chapters/ch1_function_spaces.tex:782-930`.

One finite constant depending only on `s` and `d` is chosen before the cube
scale, datum, and solution.  The only analytic premises are the source
fractional-Sobolev membership of the datum and the weak Dirichlet equation. -/
theorem exists_centeredCubeDirichletExactOverlapEuclideanNormTwoRegularity
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (h : CenteredCubeEuclideanL2Field d m)
        (w : H10Function (openCubeSet (originCube d m))),
        MemCenteredCubeEuclideanHs s h →
          CubeDirichletDivergenceProblem (originCube d m) w h →
            exactOverlapEuclideanNormTwo s (originCube d m)
                (centeredCubeGradientEuclideanL2Field w)
                (centeredCubeGradientEuclideanL2Field w).exactOverlapEuclideanIntegrable ≤
              C * exactOverlapEuclideanNormTwo s (originCube d m) h
                h.exactOverlapEuclideanIntegrable := by
  rcases exists_centeredCubeEuclideanHs_exactOverlapEuclideanNormTwo_comparison d s with
    ⟨Ccomparison, hCcomparison, hcomparison⟩
  rcases exists_centeredCubeDirichletEuclideanHsFullENormRegularity d s with
    ⟨Cpde, hCpde, hpde⟩
  let C : ℝ≥0∞ := Ccomparison * Cpde * Ccomparison
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCcomparison hCpde) hCcomparison
  · intro m h w _hHs hproblem
    let out : CenteredCubeEuclideanL2Field d m :=
      centeredCubeGradientEuclideanL2Field w
    have houtComparison := (hcomparison m out).1
    have hinComparison := (hcomparison m h).2
    have hpdeEstimate := hpde m h w hproblem
    calc
      exactOverlapEuclideanNormTwo s (originCube d m)
          (centeredCubeGradientEuclideanL2Field w)
          (centeredCubeGradientEuclideanL2Field w).exactOverlapEuclideanIntegrable =
        centeredCubeExactOverlapEuclideanNormTwo s out := by
          rfl
      _ ≤ Ccomparison * centeredCubeEuclideanHsFullENorm s out :=
        houtComparison
      _ ≤ Ccomparison *
          (Cpde * centeredCubeEuclideanHsFullENorm s h) := by
        simpa only [mul_comm] using mul_le_mul_left hpdeEstimate Ccomparison
      _ ≤ Ccomparison *
          (Cpde * (Ccomparison * centeredCubeExactOverlapEuclideanNormTwo s h)) := by
        simpa only [mul_comm] using
          mul_le_mul_left (mul_le_mul_left hinComparison Cpde) Ccomparison
      _ = C * exactOverlapEuclideanNormTwo s (originCube d m) h
          h.exactOverlapEuclideanIntegrable := by
        simp only [C, centeredCubeExactOverlapEuclideanNormTwo]
        ring

end

end Homogenization
