/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianBesovDepth

/-! # Hessian Besov Summation -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

noncomputable section

/-!
# Descendant summation for the C.2 Hessian-to-Besov bridge

This file packages the finite summation side of the scale-sharp C.2 handoff.
The analytic disjoint-restriction estimate is still supplied as an explicit
sum hypothesis; the theorem below converts that sum bound into the descendant
average required by `HessianBesovDepth`.
-/

namespace HasWeakHessianOn

variable {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}

/-- Scale-sharp depth handoff from a finite descendant sum bound on the
restricted Hessian row. This is the exact form meant to receive the future
disjoint-restriction estimate
`∑_R ‖row‖²_{L²(R)} ≤ ‖row‖²_{L²(Q)}`. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvSum_volumeInvRpowHalf_hessianRow
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K B : ℝ} (hK : 0 ≤ K)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).fixedValue ≤ K)
    (hsum :
      ∑ R ∈ descendantsAtDepth Q j,
        (if hR : R ∈ descendantsAtDepth Q j then
          ‖((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth hR)
            ).gradCoordH1Function i).gradToVectorL2‖
        else
          0) ^ 2 ≤ B ^ 2) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (K * ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * B ^ 2) ^ (1 / 2 : ℝ))) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let Bavg : ℝ := (((D.card : ℝ)⁻¹ * B ^ 2) ^ (1 / 2 : ℝ))
  have hx_nonneg : 0 ≤ (D.card : ℝ)⁻¹ * B ^ 2 := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg B)
  have hBavg : 0 ≤ Bavg := by
    dsimp [Bavg]
    exact Real.rpow_nonneg hx_nonneg _
  have hBavg_sq : Bavg ^ 2 = (D.card : ℝ)⁻¹ * B ^ 2 := by
    dsimp [Bavg]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx_nonneg]
    norm_num
  have havg :
      descendantsAverage Q j
        (fun R =>
          (if hR : R ∈ descendantsAtDepth Q j then
            ‖((H.restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
          else
            0) ^ 2) ≤ Bavg ^ 2 := by
    have hsum_if :
        D.sum
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ‖((H.restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2) ≤ B ^ 2 := by
      change
        D.sum
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ‖((H.restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2) ≤ B ^ 2 at hsum
      exact hsum
    have hraw :
        descendantsAverage Q j
          (fun R =>
            (if hR : R ∈ descendantsAtDepth Q j then
              ‖((H.restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR)).gradCoordH1Function i).gradToVectorL2‖
            else
              0) ^ 2) ≤ (D.card : ℝ)⁻¹ * B ^ 2 := by
      dsimp [descendantsAverage, D]
      exact mul_le_mul_of_nonneg_left hsum_if
        (inv_nonneg.mpr (by positivity))
    rw [hBavg_sq]
    exact hraw
  change
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j * (K * Bavg)
  exact
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_of_descendantsAverage_volumeInvRpowHalf_hessianRow
      i j hC hK hBavg hfactor havg

end HasWeakHessianOn

end

end Homogenization
