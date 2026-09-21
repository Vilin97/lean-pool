/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.Solver
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.PositiveBesovCore

/-! # Gradient Average -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

/-!
# Average mode for the cube Neumann CZ endpoint

The `B^1_{2,1}` dual-test norm contains a cube-average term for each gradient
component. This file packages the existing Neumann energy estimate and the
standard `‖average‖ ≤ L²` bound into the exact average-mode estimate needed by
the endpoint handoff.
-/

/-- The current cube-dependent constant supplied by the existing Neumann
energy estimate for controlling the average mode of the Poisson gradient. -/
noncomputable def cubePoissonGradientAverageConstant {d : ℕ}
    (Q : TriadicCube d) : ℝ :=
  cubeBesovScaleWeight 1 Q *
    ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ)) * (d : ℝ) *
      cubeMeanZeroH1CoerciveConstant Q * ((cubeVolume Q) ^ (1 / 2 : ℝ)))

theorem cubePoissonGradientAverageConstant_nonneg {d : ℕ}
    (Q : TriadicCube d) :
    0 ≤ cubePoissonGradientAverageConstant Q := by
  have hscale : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  have hvolInvSqrt :
      0 ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
  have hvolSqrt : 0 ≤ (cubeVolume Q) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (cubeVolume_nonneg Q) _
  have hmain :
      0 ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (d : ℝ) *
        cubeMeanZeroH1CoerciveConstant Q * (cubeVolume Q) ^ (1 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hvolInvSqrt (Nat.cast_nonneg d))
        (cubeMeanZeroH1CoerciveConstant_nonneg Q))
      hvolSqrt
  exact mul_nonneg hscale hmain

theorem cubePoissonGradientAverageConstant_eq_dimensionConstant {d : ℕ}
    (Q : TriadicCube d) :
    cubePoissonGradientAverageConstant Q =
      (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constant := by
  let S : ℝ := cubeBesovScaleWeight 1 Q
  let A : ℝ := ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ)
  let D : ℝ := (d : ℝ)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let B : ℝ := (cubeVolume Q) ^ (1 / 2 : ℝ)
  let C₀ : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  have hV_cancel : A * B = 1 := by
    have hV_pos : 0 < cubeVolume Q := cubeVolume_pos Q
    have hB_pos : 0 < B := by
      dsimp [B]
      exact Real.rpow_pos_of_pos hV_pos _
    dsimp [A, B]
    rw [Real.inv_rpow (le_of_lt hV_pos) (1 / 2 : ℝ)]
    exact inv_mul_cancel₀ hB_pos.ne'
  have hSC : S * C = C₀ := by
    have hscale_pos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    dsimp [S, C, C₀]
    rw [cubeMeanZeroH1CoerciveConstant_eq_scale_mul_unit]
    unfold cubeBesovScaleWeight
    rw [Real.rpow_neg_one]
    field_simp [hscale_pos.ne']
  calc
    cubePoissonGradientAverageConstant Q = S * (A * D * C * B) := by
      simp [cubePoissonGradientAverageConstant, S, A, D, C, B]
    _ = (S * C) * (A * B) * D := by ring
    _ = C₀ * 1 * D := by rw [hSC, hV_cancel]
    _ = (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constant := by
      simp [C₀, D, mul_comm]

/-- Component-average bound for the Poisson gradient, in exactly the weighted
form consumed by
`cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm_and_average`. -/
theorem meanZeroNeumannPoissonSolution_cubeBesovScaleWeight_norm_cubeAverage_grad_le
    {d : ℕ} (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d) :
    cubeBesovScaleWeight 1 Q *
        ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ ≤
      cubePoissonGradientAverageConstant Q *
        cubeLpNorm Q (2 : ℝ≥0∞) F := by
  let C : ℝ :=
    (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * (d : ℝ) *
      cubeMeanZeroH1CoerciveConstant Q * (cubeVolume Q) ^ (1 / 2 : ℝ))
  have hscale : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  have hcomponentAvg :
      ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ ≤
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) :=
    norm_cubeAverage_le_cubeLpNorm_two Q
      (fun x => W.w.toH1Function.grad x i)
      (W.w.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hcomponentSum :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) ≤
        ∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x k) := by
    exact Finset.single_le_sum
      (fun k _hk => cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x k))
      (Finset.mem_univ i)
  have hsum :
      ∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x k) ≤
        C * cubeLpNorm Q (2 : ℝ≥0∞) F := by
    simpa [C] using meanZeroNeumannPoissonSolution_sum_cubeLpNorm_grad_le_exact Q hF W
  calc
    cubeBesovScaleWeight 1 Q *
        ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖
        ≤ cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (fun x => W.w.toH1Function.grad x i) := by
          exact mul_le_mul_of_nonneg_left hcomponentAvg hscale
    _ ≤ cubeBesovScaleWeight 1 Q *
          (∑ k : Fin d, cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x k)) := by
          exact mul_le_mul_of_nonneg_left hcomponentSum hscale
    _ ≤ cubeBesovScaleWeight 1 Q *
          (C * cubeLpNorm Q (2 : ℝ≥0∞) F) := by
          exact mul_le_mul_of_nonneg_left hsum hscale
    _ = cubePoissonGradientAverageConstant Q *
          cubeLpNorm Q (2 : ℝ≥0∞) F := by
          simp [cubePoissonGradientAverageConstant, C]
          ring

/-- Endpoint handoff with the average mode already discharged by the Neumann
energy estimate. After this lemma, the remaining endpoint input is only the
uniform depth-seminorm estimate for each gradient component. -/
theorem cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm
    {d : ℕ} {Q : TriadicCube d} {Cdepth : ℝ}
    (hCdepth : 0 ≤ Cdepth)
    (hdepth :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d) (N j : ℕ),
        j ∈ Finset.range (N + 1) →
          cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
              (fun x => W.w.toH1Function.grad x i) j ≤
            Cdepth * cubeLpNorm Q (2 : ℝ≥0∞) F) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q
      (Cdepth + cubePoissonGradientAverageConstant Q) := by
  refine
    cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm_and_average
      hCdepth (cubePoissonGradientAverageConstant_nonneg Q) hdepth ?_
  intro F hF _hmean W i
  exact
    meanZeroNeumannPoissonSolution_cubeBesovScaleWeight_norm_cubeAverage_grad_le
      Q hF W i

end

end Homogenization
