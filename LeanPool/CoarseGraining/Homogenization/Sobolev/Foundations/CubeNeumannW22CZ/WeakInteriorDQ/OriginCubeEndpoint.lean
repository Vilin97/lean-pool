/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.GradientAverage
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentEnergyFactor
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ScaledCoerciveDepth

/-! # Origin Cube Endpoint -/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- The origin-cube depth constant obtained by combining the reflected-parent
Hessian estimate with the parent-normalized descendant Poincare handoff. -/
noncomputable def originCubeWeakInteriorDepthConstant (d : ℕ) (m : ℤ) : ℝ :=
  let Q : TriadicCube d := originCube d m
  (((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
    (((d : ℝ) * (d : ℝ)) *
      MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstant d m)

theorem originCubeWeakInteriorDepthConstant_nonneg (d : ℕ) (m : ℤ) :
    0 ≤ originCubeWeakInteriorDepthConstant d m := by
  let Q : TriadicCube d := originCube d m
  have hparent :
      0 ≤ ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant := by
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hcount :
      0 ≤ ((d : ℝ) * (d : ℝ)) *
        MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstant d m := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d))
      (MeanZeroNeumannPoissonSolution.originCubeParentReducedSolverEnergyConstant_nonneg d m)
  dsimp [originCubeWeakInteriorDepthConstant, Q]
  exact mul_nonneg hparent hcount

namespace MeanZeroNeumannPoissonSolution

theorem originCube_sum_reducedSolverEnergyBound_le_depthConstant_mul_cubeLpNorm
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ} :
    (((cubeVolume (originCube d m))⁻¹) ^ (1 / (2 : ℝ)) *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (∑ k : Fin d, ∑ _l : Fin d,
          originCubeParentReducedSolverEnergyBound d m F k) ≤
      originCubeWeakInteriorDepthConstant d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let Q : TriadicCube d := originCube d m
  let P : ℝ :=
    ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  let K : ℝ := originCubeParentReducedSolverEnergyConstant d m
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hsum_eq :
      (∑ k : Fin d, ∑ _l : Fin d,
        originCubeParentReducedSolverEnergyBound d m F k) =
        ((d : ℝ) * (d : ℝ)) * (K * L) := by
    calc
      (∑ k : Fin d, ∑ _l : Fin d,
        originCubeParentReducedSolverEnergyBound d m F k)
          = ∑ k : Fin d, ∑ _l : Fin d, K * L := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              refine Finset.sum_congr rfl ?_
              intro _l _hl
              simpa [K, L, Q] using
                originCubeParentReducedSolverEnergyBound_eq_constant_mul_cubeLpNorm d m F k
      _ = ((d : ℝ) * (d : ℝ)) * (K * L) := by
            simp
            ring
  calc
    P * (∑ k : Fin d, ∑ _l : Fin d,
          originCubeParentReducedSolverEnergyBound d m F k)
        = P * (((d : ℝ) * (d : ℝ)) * (K * L)) := by
          rw [hsum_eq]
    _ = originCubeWeakInteriorDepthConstant d m * L := by
          dsimp [originCubeWeakInteriorDepthConstant, P, K, L, Q]
          ring
    _ ≤ originCubeWeakInteriorDepthConstant d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
          exact le_rfl

theorem cubeBesovDepthSeminorm_grad_originCube_le_weakInteriorDepthConstant
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ}
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (hmean : cubeAverage (originCube d m) F = 0)
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (i : Fin d) (_N j : ℕ) (_hj : j ∈ Finset.range (_N + 1)) :
    cubeBesovDepthSeminorm (originCube d m) 1 (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) j ≤
      originCubeWeakInteriorDepthConstant d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  rcases
    W.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBound
      hmean hF with
    ⟨_uP, _huP_toFun, _huP_grad, H, hH⟩
  let Q : TriadicCube d := originCube d m
  let P : ℝ :=
    ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hdepth :
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x i) j ≤
        P * H.hessianCoordL2NormSum := by
    simpa [Q, P] using
      H.cubeBesovDepthSeminorm_gradCoord_le_parentVolume_scaledCoercive i j
  calc
    cubeBesovDepthSeminorm (originCube d m) 1 (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i) j
        ≤ P * H.hessianCoordL2NormSum := by
          simpa [Q] using hdepth
    _ ≤ P * (∑ k : Fin d, ∑ _l : Fin d,
          originCubeParentReducedSolverEnergyBound d m F k) := by
          exact mul_le_mul_of_nonneg_left hH hP_nonneg
    _ ≤ originCubeWeakInteriorDepthConstant d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
          simpa [Q, P] using
            originCube_sum_reducedSolverEnergyBound_le_depthConstant_mul_cubeLpNorm
              (d := d) (m := m) (F := F)

theorem cubePoissonGradientDualTestNormL2CoreEstimate_originCube
    {d : ℕ} (m : ℤ) :
    CubePoissonGradientDualTestNormL2CoreEstimate (originCube d m)
      (originCubeWeakInteriorDepthConstant d m +
        cubePoissonGradientAverageConstant (originCube d m)) := by
  refine
    cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm
      (originCubeWeakInteriorDepthConstant_nonneg d m) ?_
  intro F hF hmean W i N j hj
  exact
    cubeBesovDepthSeminorm_grad_originCube_le_weakInteriorDepthConstant
      hF hmean W i N j hj

end MeanZeroNeumannPoissonSolution

end

end Homogenization
