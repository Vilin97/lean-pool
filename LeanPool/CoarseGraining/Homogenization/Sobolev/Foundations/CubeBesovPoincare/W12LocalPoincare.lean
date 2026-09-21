/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapLp
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardOverlapComparison
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12NormalizedPartition

/-!
# Local normalized `W^{1,2}` Poincare estimate on triadic cubes

The overlap-cube `H^1` estimate is used only at the middle child of a
triadic cube.  There its overlap is the original cube, so the estimate has a
dimension-only constant and the exact normalized open-cube Sobolev carrier.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The dimension-only constant in the local normalized cube Poincare
estimate. -/
noncomputable def cubeBesovW12LocalPoincareConstant (d : ℕ) : ℝ :=
  (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue

theorem cubeBesovW12LocalPoincareConstant_nonneg (d : ℕ) :
    0 ≤ cubeBesovW12LocalPoincareConstant d :=
  (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg

private def W1pFunction.toH1AtTwo {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient

private def castH1Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

@[simp] private theorem castH1Domain_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] private theorem castH1Domain_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

private theorem cubeLpNorm_grad_le_cubeLpNorm_euclideanGrad {d : ℕ}
    (Q : TriadicCube d) (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u.grad ≤
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) := by
  unfold cubeLpNorm
  apply ENNReal.toReal_mono
  · let U : BoundedMeasurableDomain d :=
      (isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (Book.Ch02.openCubeSet_nonempty Q)
    have hmem : MeasureTheory.MemLp (fun x => euclideanNorm (u.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa only [U,
        openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using u.gradEuclideanMemLp U (2 : ℝ≥0∞)
    exact hmem.eLpNorm_ne_top
  · apply MeasureTheory.eLpNorm_mono_ae
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (euclideanNorm_nonneg _),
      euclideanNorm_eq_norm_ofVec] using HilbertVec.norm_le_norm_ofVec (u.grad x)

/-- The local Poincare estimate on a triadic cube in the exact normalized
`W^{1,2}` carrier used by the Besov embedding. -/
theorem cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (u : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) u.toFun ≤
      cubeBesovW12LocalPoincareConstant d * cubeScaleFactor Q *
        BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
          ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
            (Book.Ch02.openCubeSet_nonempty Q))
          (2 : ℝ≥0∞) (by norm_num) (by norm_num) u := by
  let S : TriadicCube d := middleChildCube Q
  let v : H1Function (openCubeSet Q) := u.toH1AtTwo
  have hdomain : openOverlapCubeSet S = openCubeSet Q := by
    dsimp [S]
    ext x
    simp only [openOverlapCubeSet, openCubeSet, Set.mem_ofPred_eq]
    constructor <;> intro hx i <;> rcases hx i with ⟨hlo, hhi⟩
    · have hscale : cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
        simpa [middleChildCube] using
          cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
      have hindex : (((middleChildCube Q).index i : ℤ) : ℝ) =
          3 * (Q.index i : ℝ) := by simp [middleChildCube]
      have hlower :
          ((((middleChildCube Q).index i : ℤ) : ℝ) - (3 / 2 : ℝ)) *
              cubeScaleFactor (middleChildCube Q) =
            (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
        rw [hscale, hindex]
        ring
      have hupper :
          ((((middleChildCube Q).index i : ℤ) : ℝ) + (3 / 2 : ℝ)) *
              cubeScaleFactor (middleChildCube Q) =
            (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
        rw [hscale, hindex]
        ring
      exact ⟨by simpa only [hlower] using hlo, by simpa only [hupper] using hhi⟩
    · have hscale : cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
        simpa [middleChildCube] using
          cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
      have hindex : (((middleChildCube Q).index i : ℤ) : ℝ) =
          3 * (Q.index i : ℝ) := by simp [middleChildCube]
      have hlower :
          ((((middleChildCube Q).index i : ℤ) : ℝ) - (3 / 2 : ℝ)) *
              cubeScaleFactor (middleChildCube Q) =
            (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
        rw [hscale, hindex]
        ring
      have hupper :
          ((((middleChildCube Q).index i : ℤ) : ℝ) + (3 / 2 : ℝ)) *
              cubeScaleFactor (middleChildCube Q) =
            (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
        rw [hscale, hindex]
        ring
      exact ⟨by simpa only [hlower] using hlo, by simpa only [hupper] using hhi⟩
  let vS : H1Function (openOverlapCubeSet S) := castH1Domain hdomain.symm v
  have hlocal := overlapCubeLpNorm_two_sub_overlapCubeAverage_le_scale_mul_grad S vS
  have hlocal' :
      cubeBesovOscillation Q (2 : ℝ≥0∞) u.toFun ≤
        (cubeScaleFactor Q * cubeBesovW12LocalPoincareConstant d) *
          cubeLpNorm Q (2 : ℝ≥0∞) u.grad := by
    simpa [cubeBesovOscillation, cubeFluctuation, S, v, vS,
      cubeBesovW12LocalPoincareConstant, mul_comm] using! hlocal
  have hgrad := cubeLpNorm_grad_le_cubeLpNorm_euclideanGrad Q u
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) u.toFun ≤
        (cubeScaleFactor Q * cubeBesovW12LocalPoincareConstant d) *
          cubeLpNorm Q (2 : ℝ≥0∞) u.grad := hlocal'
    _ ≤ (cubeScaleFactor Q * cubeBesovW12LocalPoincareConstant d) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) := by
      exact mul_le_mul_of_nonneg_left hgrad
        (mul_nonneg (by
          simpa [cubeScaleFactor] using
            (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale).le)
          (cubeBesovW12LocalPoincareConstant_nonneg d))
    _ = cubeBesovW12LocalPoincareConstant d * cubeScaleFactor Q *
          BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
            ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
              (Book.Ch02.openCubeSet_nonempty Q))
            (2 : ℝ≥0∞) (by norm_num) (by norm_num) u := by
      rw [← openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad Q u]
      ring

end

end Homogenization
