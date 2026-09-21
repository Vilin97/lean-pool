/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Aggregation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12LocalPoincare
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12NormalizedPartition

/-!
# Triadic-cube `W^{1,2}` to positive Besov embedding

This module exposes the exact source-facing normalized `W^{1,2}` estimate.
The local Poincare estimate and the normalized descendant-energy partition
are assembled by the generic finite-depth `B^1_{2,∞}` aggregation lemma.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- Dimensional constant for the triadic-cube `W^{1,2} → B^1_{2,∞}` embedding. -/
noncomputable def cubeBesovW12EmbeddingConstant (d : ℕ) : ℝ :=
  cubeBesovW12LocalPoincareConstant d

theorem cubeBesovW12EmbeddingConstant_nonneg (d : ℕ) :
    0 ≤ cubeBesovW12EmbeddingConstant d :=
  cubeBesovW12LocalPoincareConstant_nonneg d

/-- Triadic-cube Poincare embedding of the normalized `W^{1,2}` unit ball
into the positive Besov `B^1_{2,∞}` ball. Scale-free constant. -/
theorem cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (N : ℕ)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) :
    cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N u.toFun ≤
      cubeBesovW12EmbeddingConstant d *
        BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
          ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
            (Book.Ch02.openCubeSet_nonempty Q))
          (2 : ℝ≥0∞) (by norm_num) (by norm_num) u := by
  let E : TriadicCube d → ℝ :=
    fun R => cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
  have hE : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j, 0 ≤ E R := by
    intro _ _ R _
    exact cubeLpNorm_nonneg R (2 : ℝ≥0∞) _
  have hosc : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u.toFun ≤
        cubeBesovW12EmbeddingConstant d * cubeScaleFactor R * E R := by
    intro j _ R hR
    let uR : W1pFunction (openCubeSet R) (2 : ℝ≥0∞) :=
      u.restrictToOpenSubcube hR
    have hlocal :=
      cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm R uR
    rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad R uR] at hlocal
    simpa [uR, E, cubeBesovW12EmbeddingConstant, mul_assoc] using hlocal
  have havg : ∀ j ∈ Finset.range (N + 1),
      descendantsAverage Q j (fun R => E R ^ 2) ≤
        BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
          ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
            (Book.Ch02.openCubeSet_nonempty Q))
          (2 : ℝ≥0∞) (by norm_num) (by norm_num) u ^ 2 := by
    intro j _
    rw [show (fun R => E R ^ 2) =
      (fun R => cubeLpNorm R (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x)) ^ 2) by rfl]
    calc
      descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x)) ^ 2) =
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x)) ^ 2 :=
        descendantsAverage_cubeLpNorm_euclideanGrad_two_sq_eq Q u j
      _ = BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
          ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
            (Book.Ch02.openCubeSet_nonempty Q))
          (2 : ℝ≥0∞) (by norm_num) (by norm_num) u ^ 2 := by
        rw [← openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad Q u]
      _ ≤ BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
          ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
            (Book.Ch02.openCubeSet_nonempty Q))
          (2 : ℝ≥0∞) (by norm_num) (by norm_num) u ^ 2 := le_rfl
  have hG : 0 ≤ BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
      ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty Q))
      (2 : ℝ≥0∞) (by norm_num) (by norm_num) u := by
    rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad Q u]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  exact cubeBesovPartialSeminormTop_one_two_le_of_localOscillation
    Q N u.toFun (cubeBesovW12EmbeddingConstant d)
    (BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
      ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty Q))
      (2 : ℝ≥0∞) (by norm_num) (by norm_num) u)
    E (cubeBesovW12EmbeddingConstant_nonneg d) hG hE hosc havg

end

end Homogenization
