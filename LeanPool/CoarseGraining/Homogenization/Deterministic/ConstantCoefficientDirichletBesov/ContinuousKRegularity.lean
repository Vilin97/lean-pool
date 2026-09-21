/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PublicTheorems
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge

/-!
# Continuous K-functional regularity for the unit-cube Dirichlet problem

This module transfers the concrete constant-coefficient Dirichlet endpoint
estimates to the exact continuous `K`-functional on the centered unit cube.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The gradient of a zero-trace unit-cube function, packaged as the exact
Euclidean `L²` field consumed by the continuous `K`-functional. -/
noncomputable def unitCubeGradientEuclideanL2Field {d : ℕ}
    (w : H10Function (openCubeSet (originCube d 0))) :
    UnitCubeEuclideanL2Field d where
  toField := fun x => w.toH1Function.grad x
  euclideanMemL2 := by
    rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      w.toH1Function.grad_memL2_normalizedCubeMeasure (Q := originCube d 0) i

@[simp] theorem unitCubeGradientEuclideanL2Field_apply {d : ℕ}
    (w : H10Function (openCubeSet (originCube d 0))) (x : Vec d) :
    unitCubeGradientEuclideanL2Field w x = w.toH1Function.grad x :=
  rfl

private theorem UnitCubeEuclideanL2Field.memLp_originCube_normalizedCubeMeasure
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
  rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

/-- The exact continuous `K`-functional estimate for the constant-coefficient
zero-Dirichlet divergence problem on the centered unit cube. The constant is
chosen before the datum, solution, and interpolation scale, so it depends only
on the dimension. -/
theorem exists_unitCubeDirichletContinuousKFunctionalRegularity
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0)))
        (t : ContinuousKScale),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          continuousKFunctional t (unitCubeGradientEuclideanL2Field w) ≤
            C * continuousKFunctional t h := by
  rcases cubeKFunctionalDirichletPointwiseRegularity d with ⟨Cₚ, hCₚ, hpoint⟩
  let D : ℝ := continuousDiscreteKBridgeConstant d
  refine ⟨D * Cₚ * D, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (continuousDiscreteKBridgeConstant_nonneg d) hCₚ)
      (continuousDiscreteKBridgeConstant_nonneg d)
  · intro h w t hweak
    let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field w
    have hdisc := hpoint (originCube d 0) h w t.1
      h.memLp_originCube_normalizedCubeMeasure hweak
    calc
      continuousKFunctional t out ≤
          D * cubeVectorKFunctional (originCube d 0) t.1 out := by
            simpa only [D] using continuousKFunctional_le_mul_cubeVectorKFunctional t out
      _ ≤ D * (Cₚ * cubeVectorKFunctional (originCube d 0) t.1 h) := by
            apply mul_le_mul_of_nonneg_left
            · simpa only [out, unitCubeGradientEuclideanL2Field] using hdisc
            · exact continuousDiscreteKBridgeConstant_nonneg d
      _ ≤ D * (Cₚ * (D * continuousKFunctional t h)) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left
              · simpa only [D] using cubeVectorKFunctional_le_mul_continuousKFunctional t h
              · exact hCₚ
            · exact continuousDiscreteKBridgeConstant_nonneg d
      _ = (D * Cₚ * D) * continuousKFunctional t h := by ring

end

end Homogenization
