/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianBesovSummation

/-! # Hessian Restriction Sum -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal Topology

noncomputable section

/-!
# Disjoint restriction summation for Hessian rows

This file proves the measure-theoretic part of the C.2 depth summation: the
sum of squared `L²` norms of a Hessian row over disjoint descendant open cubes
is bounded by the parent-cube row norm.
-/

namespace HasWeakHessianOn

variable {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}

private theorem toReal_eLpNorm_two_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : MeasureTheory.Measure α} {f : α → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hpow : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by
    norm_num
  have hnorm :=
    hf.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  have hsq_norm :
      (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    rw [hnorm, hpow]
    have hint_nonneg :
        0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg (f x)) _)
    rw [ENNReal.toReal_ofReal]
    · rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hint_nonneg
    · exact Real.rpow_nonneg hint_nonneg _
  calc
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hsq_norm
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
          congr 1 with x
          rw [Real.rpow_two]

private theorem norm_toVectorL2_sq_eq_integral_norm_sq
    {U : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 U F) :
    ‖Homogenization.toVectorL2 hF‖ ^ 2 =
      ∫ x in U, ‖F x‖ ^ 2 ∂MeasureTheory.volume := by
  rw [Homogenization.toVectorL2, MeasureTheory.Lp.norm_toLp]
  simpa [volumeMeasureOn] using
    toReal_eLpNorm_two_sq_eq_integral_norm_sq (μ := volumeMeasureOn U) hF

/-- Squared `L²` norms of a Hessian row over depth-`j` descendant open cubes
sum to at most the parent-cube squared row norm. -/
theorem descendants_sum_restrict_gradCoordH1Function_gradToVectorL2_norm_sq_le
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ) :
    ∑ R ∈ descendantsAtDepth Q j,
      (if hR : R ∈ descendantsAtDepth Q j then
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          ).gradCoordH1Function i).gradToVectorL2‖
      else
        0) ^ 2 ≤
      ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2 := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let row : Vec d → Vec d := fun x => fun k : Fin d => H.hess i k x
  let energy : Vec d → ℝ := fun x => ‖row x‖ ^ 2
  have hrow_mem : MemVectorL2 (openCubeSet Q) row := by
    simpa [row] using! (H.gradCoordH1Function i).grad_memVectorL2
  have henergy_int_Q :
      MeasureTheory.IntegrableOn energy (openCubeSet Q) MeasureTheory.volume := by
    have hint :
        MeasureTheory.Integrable (fun x => ‖row x‖ ^ 2)
          (volumeMeasureOn (openCubeSet Q)) := by
      simpa using hrow_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, energy] using hint
  have hlocal_norm :
      ∀ R (hR : R ∈ D),
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
          ).gradCoordH1Function i).gradToVectorL2‖ ^ 2 =
          ∫ x in openCubeSet R, energy x ∂MeasureTheory.volume := by
    intro R hR
    have hmem :
        MemVectorL2 (openCubeSet R)
          (((H.restrict (isOpen_openCubeSet R)
              (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
            ).gradCoordH1Function i).grad) :=
      ((H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
        ).gradCoordH1Function i).grad_memVectorL2
    simpa [H1Function.gradToVectorL2, row, energy, HasWeakHessianOn.gradCoordH1Function,
      HasWeakHessianOn.restrict, H1Function.restrict] using
      norm_toVectorL2_sq_eq_integral_norm_sq hmem
  have hglobal_norm :
      ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2 =
        ∫ x in openCubeSet Q, energy x ∂MeasureTheory.volume := by
    simpa [H1Function.gradToVectorL2, row, energy, HasWeakHessianOn.gradCoordH1Function] using
      norm_toVectorL2_sq_eq_integral_norm_sq hrow_mem
  have hmeas : ∀ R ∈ D, MeasurableSet (openCubeSet R) := by
    intro R _hR
    exact measurableSet_openCubeSet R
  have hpair : (D : Set (TriadicCube d)).PairwiseDisjoint openCubeSet := by
    simpa [D] using pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j
  have hint_local :
      ∀ R ∈ D, MeasureTheory.IntegrableOn energy (openCubeSet R) MeasureTheory.volume := by
    intro R hR
    exact henergy_int_Q.mono_set
      (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
  have hsum_int :
      ∫ x in ⋃ R ∈ D, openCubeSet R, energy x ∂MeasureTheory.volume =
        ∑ R ∈ D, ∫ x in openCubeSet R, energy x ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_biUnion_finset D hmeas hpair hint_local
  have hunion_subset : (⋃ R ∈ D, openCubeSet R) ⊆ openCubeSet Q := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨R, hxR⟩
    rcases Set.mem_iUnion.mp hxR with ⟨hR, hxOpen⟩
    exact openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR) hxOpen
  have hmono :
      ∫ x in ⋃ R ∈ D, openCubeSet R, energy x ∂MeasureTheory.volume ≤
        ∫ x in openCubeSet Q, energy x ∂MeasureTheory.volume := by
    exact MeasureTheory.setIntegral_mono_set henergy_int_Q
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖row x‖)
      (Filter.Eventually.of_forall hunion_subset)
  calc
    ∑ R ∈ descendantsAtDepth Q j,
      (if hR : R ∈ descendantsAtDepth Q j then
        ‖((H.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          ).gradCoordH1Function i).gradToVectorL2‖
      else
        0) ^ 2
        = ∑ R ∈ D, ∫ x in openCubeSet R, energy x ∂MeasureTheory.volume := by
            dsimp [D]
            refine Finset.sum_congr rfl ?_
            intro R hR
            rw [dif_pos hR]
            exact hlocal_norm R (by simpa [D] using hR)
    _ = ∫ x in ⋃ R ∈ D, openCubeSet R, energy x ∂MeasureTheory.volume := hsum_int.symm
    _ ≤ ∫ x in openCubeSet Q, energy x ∂MeasureTheory.volume := hmono
    _ = ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2 := hglobal_norm.symm

/-- Scale-sharp depth handoff after disjoint restriction summation, stated
with the global Hessian row norm. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvGlobalRow_volumeInvRpowHalf
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K : ℝ} (hK : 0 ≤ K)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).fixedValue ≤ K) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (K *
          ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2) ^ (1 / 2 : ℝ))) := by
  exact
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvSum_volumeInvRpowHalf_hessianRow
      i j hC hK hfactor
      (H.descendants_sum_restrict_gradCoordH1Function_gradToVectorL2_norm_sq_le i j)

/-- Scale-sharp depth handoff after disjoint restriction summation, in the
global Hessian-coordinate-sum form produced by the reflected interior theorem. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvGlobal_hessianCoordL2NormSum
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ)
    (hC :
      ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R))
    {K : ℝ} (hK : 0 ≤ K)
    (hfactor :
      ∀ R (hR : R ∈ descendantsAtDepth Q j),
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * (hC R hR).fixedValue ≤ K) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (K *
          ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            H.hessianCoordL2NormSum ^ 2) ^ (1 / 2 : ℝ))) := by
  have hrowDepth :=
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvGlobalRow_volumeInvRpowHalf
      i j hC hK hfactor
  have hrow :
      ‖(H.gradCoordH1Function i).gradToVectorL2‖ ≤ H.hessianCoordL2NormSum :=
    H.gradCoordH1Function_gradToVectorL2_norm_le_hessianCoordL2NormSum i
  have hcard_nonneg : 0 ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ :=
    inv_nonneg.mpr (by positivity)
  have hrow_nonneg : 0 ≤ ‖(H.gradCoordH1Function i).gradToVectorL2‖ :=
    norm_nonneg _
  have hinside_nonneg :
      0 ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2 := by
    exact mul_nonneg hcard_nonneg (sq_nonneg _)
  have hinside :
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2 ≤
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          H.hessianCoordL2NormSum ^ 2 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hrow_nonneg hrow 2) hcard_nonneg
  have hroot :
      (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2) ^ (1 / 2 : ℝ) ≤
        (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          H.hessianCoordL2NormSum ^ 2) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hinside_nonneg hinside (by norm_num)
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j
        ≤ cubeBesovDepthWeight Q 1 j *
          (K *
            ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
              ‖(H.gradCoordH1Function i).gradToVectorL2‖ ^ 2) ^ (1 / 2 : ℝ))) := hrowDepth
    _ ≤ cubeBesovDepthWeight Q 1 j *
          (K *
            ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
              H.hessianCoordL2NormSum ^ 2) ^ (1 / 2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hroot hK)
            (cubeBesovDepthWeight_nonneg Q 1 j)

end HasWeakHessianOn

end

end Homogenization
