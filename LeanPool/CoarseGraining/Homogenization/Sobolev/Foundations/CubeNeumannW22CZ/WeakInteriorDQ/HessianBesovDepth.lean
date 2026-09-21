/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.PositiveBesovCore

/-! # Hessian Besov Depth -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

/-!
# Descendant Poincare to Besov depth bounds

This file combines the gradient-coordinate Poincare bridge with the scalar
Besov depth handoff. The remaining quantitative input is deliberately explicit:
a uniform bound over all descendants at one depth for the local Hessian-row
Poincare quantities.
-/

namespace HasWeakHessianOn

variable {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}

/-- Descendant Poincare plus the scalar depth handoff. If the local
Poincare-controlled Hessian-row quantity is bounded by `A` on every
depth-`j` descendant, then the depth-`j` Besov seminorm of the gradient
component is bounded by the depth weight times `A`. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_of_descendant_hessianRow_bound
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {A : ℝ} (hA : 0 ≤ A)
    (hrow :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant *
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ ≤
          A) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j * A := by
  refine
    cubeBesovDepthSeminorm_two_le_depthWeight_mul_of_descendant_oscillation_le
      Q 1 (fun x => u.grad x i) j hA ?_
  intro R hR
  exact
    (H.cubeBesovOscillation_gradCoord_descendant_le_volumeFactor_mul_coerciveConst
      hR i (hC R hR)).trans (hrow R hR)

/-- Averaged descendant Poincare handoff for a Hessian row. This avoids the
too-strong descendant supremum from
`cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_of_descendant_hessianRow_bound`;
the right side is the descendant `L²` average of the local Poincare-controlled
Hessian-row quantities. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_descendantsAverage_sq_rpow_half
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R)) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (descendantsAverage Q j
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant *
                ‖((H.restrict (isOpen_openCubeSet R)
                    (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2)) ^ (1 / 2 : ℝ) := by
  let A : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant *
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    else
      0
  have hA_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        A R =
          ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant *
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ((cubeVolume R)⁻¹ + 1) * (hC R hR').constant *
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR')).gradCoordH1Function i).gradToVectorL2‖
      else
        0) =
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant *
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    rw [dif_pos hR]
  refine
    cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
      Q 1 (fun x => u.grad x i) j A ?_ ?_
  · intro R hR
    rw [hA_eval R hR]
    have hvolInv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
    have hvolFactor : 0 ≤ (cubeVolume R)⁻¹ + 1 := by linarith
    exact mul_nonneg
      (mul_nonneg hvolFactor (hC R hR).constant_nonneg)
      (norm_nonneg _)
  · intro R hR
    rw [hA_eval R hR]
    exact
      H.cubeBesovOscillation_gradCoord_descendant_le_volumeFactor_mul_coerciveConst
        hR i (hC R hR)

/-- Scale-sharp averaged descendant Poincare handoff for a Hessian row.

This is the q=2 version of the previous averaged estimate with the exact
normalized `L²` factor `volume^{-1/2}`. It is the correct summation shape for
the reflection proof: descendant volumes and the number of descendants can
cancel when the restricted Hessian-row norms are squared and averaged. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_descendantsAverage_volumeInvRpowHalf_sq_rpow_half
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R)) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (descendantsAverage Q j
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant *
                ‖((H.restrict (isOpen_openCubeSet R)
                    (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2)) ^ (1 / 2 : ℝ) := by
  let A : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant *
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    else
      0
  have hA_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        A R =
          ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant *
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR').constant *
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR')).gradCoordH1Function i).gradToVectorL2‖
      else
        0) =
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant *
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    rw [dif_pos hR]
  refine
    cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
      Q 1 (fun x => u.grad x i) j A ?_ ?_
  · intro R hR
    rw [hA_eval R hR]
    have hvolInv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hvolInv _) (hC R hR).constant_nonneg)
      (norm_nonneg _)
  · intro R hR
    rw [hA_eval R hR]
    exact
      H.cubeBesovOscillation_gradCoord_descendant_le_volumeInvRpowHalf_mul_coerciveConst
        hR i (hC R hR)

/-- Scale-sharp averaged Hessian-row handoff with the remaining quantitative
inputs explicit: a uniform bound `K` on
`volume(R)^{-1/2} * PoincareConstant(R)`, and an `L²` descendant-average bound
`B` on the restricted Hessian row. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_of_descendantsAverage_volumeInvRpowHalf_hessianRow
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant ≤ K)
    (havg :
      descendantsAverage Q j
        (fun R =>
          (if hR : R ∈ descendantsAtDepth Q j then
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
          else
            0) ^ 2) ≤ B ^ 2) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j * (K * B) := by
  let Row : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ‖((H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    else
      0
  let P : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant * Row R
    else
      0
  have hRow_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        Row R =
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR')).gradCoordH1Function i).gradToVectorL2‖
      else
        0) =
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    rw [dif_pos hR]
  have hP_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        P R = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant * Row R := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR').constant * Row R
      else
        0) =
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).constant * Row R
    rw [dif_pos hR]
  have hP_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ P R := by
    intro R hR
    rw [hP_eval R hR, hRow_eval R hR]
    have hvolInv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hvolInv _) (hC R hR).constant_nonneg)
      (norm_nonneg _)
  have hosc :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i) ≤ P R := by
    intro R hR
    rw [hP_eval R hR, hRow_eval R hR]
    simpa [mul_assoc] using
      H.cubeBesovOscillation_gradCoord_descendant_le_volumeInvRpowHalf_mul_coerciveConst
        hR i (hC R hR)
  have hdepth :
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
        cubeBesovDepthWeight Q 1 j *
          (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact
      cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
        Q 1 (fun x => u.grad x i) j P hP_nonneg hosc
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j, P R ≤ K * Row R := by
    intro R hR
    rw [hP_eval R hR]
    have hRow_nonneg : 0 ≤ Row R := by
      rw [hRow_eval R hR]
      exact norm_nonneg _
    exact mul_le_mul_of_nonneg_right (hfactor R hR) hRow_nonneg
  have hsq :
      descendantsAverage Q j (fun R => (P R) ^ 2) ≤
        descendantsAverage Q j (fun R => (K * Row R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hPR_nonneg : 0 ≤ P R := hP_nonneg R hR
    exact pow_le_pow_left₀ hPR_nonneg (hpoint R hR) 2
  have hscaled :
      descendantsAverage Q j (fun R => (K * Row R) ^ 2) =
        K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := by
    calc
      descendantsAverage Q j (fun R => (K * Row R) ^ 2)
          = descendantsAverage Q j (fun R => K ^ 2 * (Row R) ^ 2) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              ring
      _ = K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := by
              rw [descendantsAverage_mul_left Q j (K ^ 2) (fun R => (Row R) ^ 2)]
  have hinside :
      descendantsAverage Q j (fun R => (P R) ^ 2) ≤ (K * B) ^ 2 := by
    calc
      descendantsAverage Q j (fun R => (P R) ^ 2)
          ≤ descendantsAverage Q j (fun R => (K * Row R) ^ 2) := hsq
      _ = K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := hscaled
      _ ≤ K ^ 2 * B ^ 2 := by
            change descendantsAverage Q j (fun R => (Row R) ^ 2) ≤ B ^ 2 at havg
            exact mul_le_mul_of_nonneg_left havg (sq_nonneg K)
      _ = (K * B) ^ 2 := by ring
  have hroot :
      (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) ≤ K * B := by
    have hleftNonneg :
        0 ≤ descendantsAverage Q j (fun R => (P R) ^ 2) :=
      descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
    have hKB_nonneg : 0 ≤ K * B := mul_nonneg hK hB
    calc
      (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ)
          ≤ ((K * B) ^ 2) ^ (1 / 2 : ℝ) := by
              exact Real.rpow_le_rpow hleftNonneg hinside (by norm_num)
      _ = K * B := by
              rw [sq_rpow_half_eq_of_nonneg hKB_nonneg]
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j
        ≤ cubeBesovDepthWeight Q 1 j *
          (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) := hdepth
    _ ≤ cubeBesovDepthWeight Q 1 j * (K * B) := by
          exact mul_le_mul_of_nonneg_left hroot
            (cubeBesovDepthWeight_nonneg Q 1 j)

/-- Averaged Hessian-row handoff with the two remaining quantitative inputs
made explicit: a uniform bound `K` on the descendant-local Poincare prefactor,
and an `L²` descendant-average bound `B` on the restricted Hessian row. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_of_descendantsAverage_hessianRow
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant ≤ K)
    (havg :
      descendantsAverage Q j
        (fun R =>
          (if hR : R ∈ descendantsAtDepth Q j then
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
          else
            0) ^ 2) ≤ B ^ 2) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j * (K * B) := by
  let Row : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ‖((H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    else
      0
  let P : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant * Row R
    else
      0
  have hRow_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        Row R =
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR')).gradCoordH1Function i).gradToVectorL2‖
      else
        0) =
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
    rw [dif_pos hR]
  have hP_eval :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        P R = ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant * Row R := by
    intro R hR
    change
      (if hR' : R ∈ descendantsAtDepth Q j then
        ((cubeVolume R)⁻¹ + 1) * (hC R hR').constant * Row R
      else
        0) =
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant * Row R
    rw [dif_pos hR]
  have hP_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ P R := by
    intro R hR
    rw [hP_eval R hR, hRow_eval R hR]
    have hvolInv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_nonneg R)
    have hvolFactor : 0 ≤ (cubeVolume R)⁻¹ + 1 := by linarith
    exact mul_nonneg
      (mul_nonneg hvolFactor (hC R hR).constant_nonneg)
      (norm_nonneg _)
  have hosc :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i) ≤ P R := by
    intro R hR
    rw [hP_eval R hR, hRow_eval R hR]
    simpa [mul_assoc] using
      H.cubeBesovOscillation_gradCoord_descendant_le_volumeFactor_mul_coerciveConst
        hR i (hC R hR)
  have hdepth :
      cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
        cubeBesovDepthWeight Q 1 j *
          (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact
      cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
        Q 1 (fun x => u.grad x i) j P hP_nonneg hosc
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j, P R ≤ K * Row R := by
    intro R hR
    rw [hP_eval R hR]
    have hRow_nonneg : 0 ≤ Row R := by
      rw [hRow_eval R hR]
      exact norm_nonneg _
    exact mul_le_mul_of_nonneg_right (hfactor R hR) hRow_nonneg
  have hsq :
      descendantsAverage Q j (fun R => (P R) ^ 2) ≤
        descendantsAverage Q j (fun R => (K * Row R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact pow_le_pow_left₀ (hP_nonneg R hR) (hpoint R hR) 2
  have hscaled :
      descendantsAverage Q j (fun R => (K * Row R) ^ 2) =
        K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := by
    calc
      descendantsAverage Q j (fun R => (K * Row R) ^ 2)
          = descendantsAverage Q j (fun R => K ^ 2 * (Row R) ^ 2) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              ring
      _ = K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := by
            rw [descendantsAverage_mul_left Q j (K ^ 2) (fun R => (Row R) ^ 2)]
  have hrowAvg :
      descendantsAverage Q j (fun R => (Row R) ^ 2) ≤ B ^ 2 := by
    change descendantsAverage Q j (fun R => (Row R) ^ 2) ≤ B ^ 2 at havg
    exact havg
  have hinside :
      descendantsAverage Q j (fun R => (P R) ^ 2) ≤ K ^ 2 * B ^ 2 := by
    calc
      descendantsAverage Q j (fun R => (P R) ^ 2)
          ≤ descendantsAverage Q j (fun R => (K * Row R) ^ 2) := hsq
      _ = K ^ 2 * descendantsAverage Q j (fun R => (Row R) ^ 2) := hscaled
      _ ≤ K ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_left hrowAvg (sq_nonneg K)
  have hleftNonneg :
      0 ≤ descendantsAverage Q j (fun R => (P R) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R _hR => sq_nonneg _
  have hroot :
      (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) ≤
        K * B := by
    calc
      (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ)
          ≤ (K ^ 2 * B ^ 2) ^ (1 / 2 : ℝ) := by
              exact Real.rpow_le_rpow hleftNonneg hinside (by norm_num)
      _ = K * B := by
            rw [show K ^ 2 * B ^ 2 = (K * B) ^ 2 by ring]
            exact sq_rpow_half_eq_of_nonneg (mul_nonneg hK hB)
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j
        ≤ cubeBesovDepthWeight Q 1 j *
            (descendantsAverage Q j (fun R => (P R) ^ 2)) ^ (1 / 2 : ℝ) := hdepth
    _ ≤ cubeBesovDepthWeight Q 1 j * (K * B) := by
          exact mul_le_mul_of_nonneg_left hroot
            (cubeBesovDepthWeight_nonneg Q 1 j)

/-- Variant of the averaged Hessian-row handoff using only the global Hessian
row norm. The localization input is discharged by monotonicity of the `L²`
norm under restriction; the remaining quantitative hypothesis is the uniform
bound `K` for the descendant-local Poincare prefactor. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_global_hessianRow
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K : ℝ} (hK : 0 ≤ K)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant ≤ K) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (K * ‖(H.gradCoordH1Function i).gradToVectorL2‖) := by
  let B : ℝ := ‖(H.gradCoordH1Function i).gradToVectorL2‖
  have hB : 0 ≤ B := by
    change 0 ≤ ‖(H.gradCoordH1Function i).gradToVectorL2‖
    exact norm_nonneg _
  have havg :
      descendantsAverage Q j
        (fun R =>
          (if hR : R ∈ descendantsAtDepth Q j then
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
          else
            0) ^ 2) ≤ B ^ 2 := by
    have hstep :
        descendantsAverage Q j
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ‖((H.restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2) ≤
          descendantsAverage Q j (fun _R => B ^ 2) := by
      refine descendantsAverage_le_descendantsAverage Q j ?_
      intro R hR
      rw [dif_pos hR]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (by
          change
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖ ≤
              ‖(H.gradCoordH1Function i).gradToVectorL2‖
          exact H.restrict_gradCoordH1Function_gradToVectorL2_norm_le
              (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR) i)
        2
    rw [descendantsAverage_const] at hstep
    exact hstep
  exact
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_of_descendantsAverage_hessianRow
      i j hC hK hB hfactor havg

/-- Depth estimate stated in terms of the global Hessian-coordinate sum. This
is the form aligned with the reflected interior estimate, which controls
`H.hessianCoordL2NormSum`. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_hessianCoordL2NormSum
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K : ℝ} (hK : 0 ≤ K)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹ + 1) * (hC R hR).constant ≤ K) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j * (K * H.hessianCoordL2NormSum) := by
  have hdepth :=
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_global_hessianRow
      i j hC hK hfactor
  have hrow :
      ‖(H.gradCoordH1Function i).gradToVectorL2‖ ≤ H.hessianCoordL2NormSum :=
    H.gradCoordH1Function_gradToVectorL2_norm_le_hessianCoordL2NormSum i
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j
        ≤ cubeBesovDepthWeight Q 1 j *
          (K * ‖(H.gradCoordH1Function i).gradToVectorL2‖) := hdepth
    _ ≤ cubeBesovDepthWeight Q 1 j * (K * H.hessianCoordL2NormSum) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrow hK)
            (cubeBesovDepthWeight_nonneg Q 1 j)

end HasWeakHessianOn

end

end Homogenization
