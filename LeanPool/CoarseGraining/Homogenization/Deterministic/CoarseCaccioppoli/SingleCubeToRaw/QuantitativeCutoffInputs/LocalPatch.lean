/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalPatchCutoff

/-! # Local Patch -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch cutoff input scalars

This file contains the scalar cutoff bookkeeping for the arbitrary-center
local-patch Caccioppoli route.  The cutoff lives at radius `cubeRadius Q / 3`,
while descendants are taken one generation deeper than the centered route.
-/

/-- Canonical `L∞` gradient bound for the arbitrary-center local-patch cutoff. -/
def coarseCaccioppoliLocalPatchCutoffGradientBound {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) : ℝ :=
  quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * (cubeRadius Q / 3))

/-- Canonical Hessian bound for the arbitrary-center local-patch cutoff. -/
def coarseCaccioppoliLocalPatchCutoffHessianBound {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) : ℝ :=
  quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * (cubeRadius Q / 3)) ^ 2)

/-- Hessian contribution after the extra local-patch descendant generation. -/
def coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (ρ₁ ρ₂ : ℝ) : ℝ :=
  (cubeScaleFactor Q / (3 : ℝ) ^ (j + 1)) *
    coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρ₂

theorem cubeScaleFactor_mul_coarseCaccioppoliLocalPatchCutoffHessianBound_eq_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q (j + 1)) (ρ₁ ρ₂ : ℝ) :
    cubeScaleFactor R * coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρ₂ =
      coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ := by
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  rfl

/-- The local-patch midpoint cutoff has the same normalized gradient size as
the parent midpoint cutoff one generation earlier. -/
theorem cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_eq_depthGap
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1)) (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
      (4 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * coarseCaccioppoliGapInv ρ₁ ρ₂) := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hscaleQ_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow_pos : 0 < (3 : ℝ) ^ (j + 1) := by positivity
  rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor]
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  unfold coarseCaccioppoliLocalPatchCutoffGradientBound
  rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
  rw [coarseCaccioppoliGapInv_eq_inv]
  unfold cubeRadius
  field_simp [hgap_pos.ne', hscaleQ_pos.ne', hpow_pos.ne']
  ring

/-- LaTeX-shaped normalized gradient bound for the local-patch midpoint
cutoff. -/
theorem cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hgap_le_pow :
      coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k := by
    have hmain :
        27 * coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k :=
      coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
        hchoice hlt
    have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_nonneg hlt
    nlinarith
  have hfront_nonneg : 0 ≤ 4 * quantitativeCubeCutoffGradientConst d := by
    exact mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d)
  have hdepth_nonneg : 0 ≤ ((3 : ℝ) ^ j)⁻¹ := by positivity
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      (4 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * coarseCaccioppoliGapInv ρ₁ ρ₂) :=
          cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_eq_depthGap
            hR hlt
    _ ≤
      (4 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgap_le_pow hdepth_nonneg)
            hfront_nonneg
    _ =
      (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          rw [inv_pow_mul_pow_eq_rpow_sub k j]

/-- Algebraic normal form for the local-patch Hessian contribution in the
centered coefficient.  The local scale `cubeRadius Q / 3` is exactly offset by
the extra descendant generation. -/
theorem cubeBesovScaleWeight_neg_one_mul_localPatchDescendantBufferedCutoffHessianScaleBound_eq_depthGap
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1)) (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
      (16 * quantitativeCubeCutoffHessianConst d) *
        (((3 : ℝ) ^ j)⁻¹ *
          (((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ))) := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hscaleQ_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow_pos : 0 < (3 : ℝ) ^ (j + 1) := by positivity
  have hpowj_pos : 0 < (3 : ℝ) ^ j := by positivity
  rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor]
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  unfold coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound
    coarseCaccioppoliLocalPatchCutoffHessianBound
  rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
  rw [coarseCaccioppoliGapInv_eq_inv]
  unfold cubeRadius
  field_simp [hgap_pos.ne', hscaleQ_pos.ne', hpow_pos.ne', hpowj_pos.ne']
  ring

/-- LaTeX-shaped normalized Hessian bound for the local-patch midpoint cutoff. -/
theorem cubeBesovScaleWeight_neg_one_mul_localPatchDescendantBufferedCutoffHessianScaleBound_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (16 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hdepth :
      ((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) ≤
        (3 : ℝ) ^ k :=
    coarseCaccioppoliGapInv_sq_mul_depthFactor_le_pow_of_triadicGapScaleChoice
      hchoice hlt hjk
  have hfront_nonneg : 0 ≤ 16 * quantitativeCubeCutoffHessianConst d := by
    exact mul_nonneg (by norm_num) (quantitativeCubeCutoffHessianConst_nonneg d)
  have hdepth_nonneg : 0 ≤ ((3 : ℝ) ^ j)⁻¹ := by positivity
  have hscaled_depth :
      ((3 : ℝ) ^ j)⁻¹ *
          (((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ)) ≤
        ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k := by
    exact mul_le_mul_of_nonneg_left hdepth hdepth_nonneg
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      (16 * quantitativeCubeCutoffHessianConst d) *
        (((3 : ℝ) ^ j)⁻¹ *
          (((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ))) :=
          cubeBesovScaleWeight_neg_one_mul_localPatchDescendantBufferedCutoffHessianScaleBound_eq_depthGap
            hR hlt
    _ ≤
      (16 * quantitativeCubeCutoffHessianConst d) *
        (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left hscaled_depth hfront_nonneg
    _ =
      (16 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          rw [inv_pow_mul_pow_eq_rpow_sub k j]

/-- The raw local-patch Hessian bracket in the constant branch is controlled
by the full-gap triadic scale. -/
theorem coarseCaccioppoliLocalPatchDescendantBufferedCutoffHessianScaleBound_le_radiusConst_mul_pow
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeScaleFactor R *
        coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ))) * (3 : ℝ) ^ k := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hscaleQ_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow_pos : 0 < (3 : ℝ) ^ (j + 1) := by positivity
  have hpowj_pos : 0 < (3 : ℝ) ^ j := by positivity
  have hdepth :
      ((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) ≤
        (3 : ℝ) ^ k :=
    coarseCaccioppoliGapInv_sq_mul_depthFactor_le_pow_of_triadicGapScaleChoice
      hchoice hlt hjk
  have hfront_nonneg :
      0 ≤ 12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) := by
    exact mul_nonneg (by norm_num)
      (div_nonneg
        (mul_nonneg (quantitativeCubeCutoffHessianConst_nonneg d)
          (cubeScaleFactor_nonneg Q))
        (sq_nonneg (cubeRadius Q)))
  have heq :
      cubeScaleFactor R *
          coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ))) *
          (((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ)) := by
    rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
    unfold coarseCaccioppoliLocalPatchCutoffHessianBound
    rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
    rw [coarseCaccioppoliGapInv_eq_inv]
    unfold cubeRadius
    field_simp [hgap_pos.ne', hscaleQ_pos.ne', hpow_pos.ne', hpowj_pos.ne']
    ring
  calc
    cubeScaleFactor R *
        coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ))) *
        (((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ)) := heq
    _ ≤
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ))) * (3 : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hdepth hfront_nonneg

/-- Raw local-patch gradient bound for the constant branch. -/
theorem coarseCaccioppoliLocalPatchBufferedCutoffGradientBound_le_radiusConst_mul_pow
    {d : ℕ} (Q : TriadicCube d) {k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
  have hgap_le_pow :
      coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k := by
    have hmain :
        27 * coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k :=
      coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
        hchoice hlt
    have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_nonneg hlt
    nlinarith
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hradius_pos : 0 < cubeRadius Q := cubeRadius_pos Q
  have hfront_nonneg :
      0 ≤ 6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q) := by
    exact mul_nonneg (by norm_num)
      (div_nonneg (quantitativeCubeCutoffGradientConst_nonneg d) hradius_pos.le)
  have heq :
      coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
        (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
          coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    unfold coarseCaccioppoliLocalPatchCutoffGradientBound
    rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
    rw [coarseCaccioppoliGapInv_eq_inv]
    field_simp [hgap_pos.ne', hradius_pos.ne']
    ring
  calc
    coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ := heq
    _ ≤
      (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hgap_le_pow hfront_nonneg

/-- Descendant form of the local-patch buffered cutoff bracket used by the
constant branch. -/
theorem cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoff_terms_le_radiusConst_mul_pow
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) ≤
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
  have hH :
      cubeScaleFactor R *
          coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ))) * (3 : ℝ) ^ k :=
    coarseCaccioppoliLocalPatchDescendantBufferedCutoffHessianScaleBound_le_radiusConst_mul_pow
      (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk
  have hG :
      coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
        (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
          (3 : ℝ) ^ k :=
    coarseCaccioppoliLocalPatchBufferedCutoffGradientBound_le_radiusConst_mul_pow
      Q hchoice hlt
  calc
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        =
      cubeScaleFactor R *
          coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) := by
          rw [cubeBesovScaleWeight_neg_one_mul_add_weighted_eq_scale_mul_add]
    _ ≤
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ))) * (3 : ℝ) ^ k +
        (6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
          (3 : ℝ) ^ k := by
          exact add_le_add hH hG
    _ =
      (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
          ring

/-- Constant-branch exact coefficient comparison for the arbitrary-center
local-patch midpoint cutoff.  The cutoff is supported on the `m-1` patch, so
descendants are taken one generation deeper than the height depth. -/
theorem
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_localPatch_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant_succ
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d)
    {Ceff : ℝ} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤ Ceff) :
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
  let K : ℝ :=
    12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
        (cubeRadius Q) ^ (2 : ℕ)) +
      6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)
  let P : ℝ := (3 : ℝ) ^ k
  let L : ℝ := Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)
  let A0 : ℝ :=
    (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹
  let S : ℝ :=
    cubeBesovScaleWeight (-1) R *
      (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
  have hcutoff : S ≤ K * P := by
    simpa [S, K, P] using
      (cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoff_terms_le_radiusConst_mul_pow
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hdisc_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0]
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (inv_nonneg.mpr hdisc_pos.le)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg
      (multiscale_ellipticity_LambdaSq_one_nonneg R 1 a (by norm_num)) _
  have hAL_nonneg : 0 ≤ A0 * L := mul_nonneg hA0_nonneg hL_nonneg
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hPL_nonneg : 0 ≤ P * L := mul_nonneg hP_nonneg hL_nonneg
  have hlarge' : A0 * K ≤ Ceff := by
    simpa [A0, K, mul_assoc] using hlarge
  have hleft_eq :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
        (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) =
        (A0 * L) * S := by
    dsimp [A0, L, S]
    unfold coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound
      coarseCaccioppoliLambdaFactor
    simp
    ring_nf
  have hright_eq :
      Ceff * (P * L) =
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
    dsimp [P, L]
    unfold coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff
    simp [Real.rpow_natCast]
    ring
  calc
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        = (A0 * L) * S := hleft_eq
    _ ≤ (A0 * L) * (K * P) :=
          mul_le_mul_of_nonneg_left hcutoff hAL_nonneg
    _ = (A0 * K) * (P * L) := by ring
    _ ≤ Ceff * (P * L) :=
          mul_le_mul_of_nonneg_right hlarge' hPL_nonneg
    _ = coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) :=
          hright_eq

end

end Homogenization
