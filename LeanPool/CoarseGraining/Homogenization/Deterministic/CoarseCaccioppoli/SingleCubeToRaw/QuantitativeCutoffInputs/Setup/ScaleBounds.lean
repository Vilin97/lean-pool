/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.RadiusInputs
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.WeakTesting
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Projection

/-! # Scale Bounds -/

@[expose] public section

namespace Homogenization

/-!
# Quantitative cutoff inputs: scale bounds
-/

noncomputable section

open scoped ENNReal

/-- Canonical `L^∞` bound supplied by the quantitative cube cutoff gradient
estimate. -/
def coarseCaccioppoliQuantitativeCutoffGradientBound {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) : ℝ :=
  quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)

/-- Canonical derivative bound supplied by the quantitative cube cutoff
Hessian estimate. -/
def coarseCaccioppoliQuantitativeCutoffHessianBound {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) : ℝ :=
  quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)

/-- The midpoint cutoff has twice the gradient scale of the full-gap cutoff. -/
theorem coarseCaccioppoliQuantitativeCutoffGradientBound_buffered_eq_two_mul
    {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
      2 * coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hradius_pos : 0 < cubeRadius Q := cubeRadius_pos Q
  unfold coarseCaccioppoliQuantitativeCutoffGradientBound
  rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
  field_simp [hgap_pos.ne', hradius_pos.ne']

/-- The midpoint cutoff has four times the Hessian scale of the full-gap
cutoff. -/
theorem coarseCaccioppoliQuantitativeCutoffHessianBound_buffered_eq_four_mul
    {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
      4 * coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hradius_pos : 0 < cubeRadius Q := cubeRadius_pos Q
  unfold coarseCaccioppoliQuantitativeCutoffHessianBound
  rw [coarseCaccioppoliBufferedCutoffRadius_inner_gap]
  field_simp [hgap_pos.ne', hradius_pos.ne']
  ring

theorem quantitativeCubeCutoffGradientConst_nonneg (d : ℕ) :
    0 ≤ quantitativeCubeCutoffGradientConst d := by
  unfold quantitativeCubeCutoffGradientConst
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    smoothTransitionProfile.derivBound_nonneg

theorem quantitativeCubeCutoffHessianConst_nonneg (d : ℕ) :
    0 ≤ quantitativeCubeCutoffHessianConst d := by
  unfold quantitativeCubeCutoffHessianConst
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ)))
    (sq_nonneg _)

/-- The small-cube Hessian contribution after multiplying the parent-cube
cutoff Hessian bound by a depth-`j` descendant scale.  This is the formal
`3^{-j}` gain used in the LaTeX Caccioppoli proof. -/
def coarseCaccioppoliDescendantCutoffHessianScaleBound {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (ρ₁ ρ₂ : ℝ) : ℝ :=
  (cubeScaleFactor Q / (3 : ℝ) ^ j) *
    coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂

theorem cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor {d : ℕ}
    (Q : TriadicCube d) :
    cubeBesovScaleWeight (-1) Q = cubeScaleFactor Q := by
  simp [cubeBesovScaleWeight]

theorem cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one {d : ℕ}
    (Q : TriadicCube d) :
    cubeBesovScaleWeight (-1) Q * cubeBesovScaleWeight 1 Q = 1 := by
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  simp [cubeBesovScaleWeight, Real.rpow_neg hpos.le, mul_inv_cancel₀ hpos.ne']

/-- The constant-branch cutoff bracket, after multiplying by the exact
negative Besov scale weight, splits into the local Hessian-scale term plus the
gradient term. -/
theorem cubeBesovScaleWeight_neg_one_mul_add_weighted_eq_scale_mul_add
    {d : ℕ} (Q : TriadicCube d) (B Xi : ℝ) :
    cubeBesovScaleWeight (-1) Q *
        (B + cubeBesovScaleWeight 1 Q * Xi) =
      cubeScaleFactor Q * B + Xi := by
  have hmul :
      cubeBesovScaleWeight (-1) Q * cubeBesovScaleWeight 1 Q = 1 :=
    cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one Q
  have hscale :
      cubeBesovScaleWeight (-1) Q = cubeScaleFactor Q :=
    cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q
  calc
    cubeBesovScaleWeight (-1) Q *
        (B + cubeBesovScaleWeight 1 Q * Xi)
        =
      cubeBesovScaleWeight (-1) Q * B +
        (cubeBesovScaleWeight (-1) Q * cubeBesovScaleWeight 1 Q) * Xi := by
          ring
    _ = cubeScaleFactor Q * B + Xi := by
          rw [hmul, hscale]
          ring

/-- On a depth-`j` descendant, `cubeScaleFactor R` converts the parent cutoff
Hessian bound into the descendant small-cube scale bound. -/
theorem cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (ρ₁ ρ₂ : ℝ) :
    cubeScaleFactor R * coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ =
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ := by
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  rfl

/-- Inequality form of
`cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant`,
for feeding cutoff-product coefficient estimates. -/
theorem cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_le_of_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (ρ₁ ρ₂ : ℝ) {D : ℝ}
    (hD : coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤ D) :
    cubeScaleFactor R * coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ ≤ D := by
  simpa [cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant
    hR ρ₁ ρ₂] using hD

/-- On a depth-`j` descendant, a local length divided by the parent radius is
exactly the expected `3^{-j}` factor, up to the radius normalization `1/2`. -/
theorem cubeScaleFactor_div_parent_cubeRadius_eq_two_mul_depthFactor
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeScaleFactor R / cubeRadius Q = 2 * ((3 : ℝ) ^ j)⁻¹ := by
  have hQ_ne : cubeScaleFactor Q ≠ 0 := by
    have hQ_pos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact ne_of_gt hQ_pos
  have hpow_ne : (3 : ℝ) ^ j ≠ 0 := by positivity
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  unfold cubeRadius
  field_simp [hQ_ne, hpow_ne]

/-- Parent cutoff constants rewritten in the depth-`j` descendant scale used by
the constant branch. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_cutoff_terms_eq_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (ρ₁ ρ₂ : ℝ) :
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂) =
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
  calc
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        =
      cubeScaleFactor R * coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
          rw [cubeBesovScaleWeight_neg_one_mul_add_weighted_eq_scale_mul_add]
    _ =
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
          rw [cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant
            hR ρ₁ ρ₂]

/-- The parent cutoff gradient bound is controlled by the triadic gap scale,
with the fixed parent radius carried as a front constant. -/
theorem coarseCaccioppoliQuantitativeCutoffGradientBound_le_radiusConst_mul_pow
    {d : ℕ} (Q : TriadicCube d) {k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
      (quantitativeCubeCutoffGradientConst d / cubeRadius Q) * (3 : ℝ) ^ k := by
  have hgap_le_pow :
      coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k := by
    have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_nonneg hlt
    have hmain :
        27 * coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k :=
      coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
        hchoice hlt
    nlinarith
  have hfront_nonneg :
      0 ≤ quantitativeCubeCutoffGradientConst d / cubeRadius Q :=
    div_nonneg (quantitativeCubeCutoffGradientConst_nonneg d) (cubeRadius_nonneg Q)
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hradius_ne : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  calc
    coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
        =
      (quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ := by
          unfold coarseCaccioppoliQuantitativeCutoffGradientBound
          rw [coarseCaccioppoliGapInv_eq_inv]
          field_simp [hgap_pos.ne', hradius_ne]
    _ ≤ (quantitativeCubeCutoffGradientConst d / cubeRadius Q) * (3 : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hgap_le_pow hfront_nonneg

/-- On a depth-`j` descendant, the parent cutoff-gradient bound gains the
small-cube length scale `3^{-j}`.  This is the centered-branch analogue of the
constant-branch cutoff-scale normalization. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_eq_depthGap
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j) (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ =
      (2 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * coarseCaccioppoliGapInv ρ₁ ρ₂) := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hrad_ne : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
        =
      cubeScaleFactor R *
        (quantitativeCubeCutoffGradientConst d /
          ((ρ₂ - ρ₁) * cubeRadius Q)) := by
          rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor]
          rfl
    _ =
      quantitativeCubeCutoffGradientConst d *
        (cubeScaleFactor R / cubeRadius Q) *
          coarseCaccioppoliGapInv ρ₁ ρ₂ := by
          rw [coarseCaccioppoliGapInv_eq_inv]
          field_simp [hgap_pos.ne', hrad_ne]
    _ =
      (2 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * coarseCaccioppoliGapInv ρ₁ ρ₂) := by
          rw [cubeScaleFactor_div_parent_cubeRadius_eq_two_mul_depthFactor hR]
          ring

/-- After the triadic gap scale is chosen, the descendant-normalized parent
cutoff-gradient term is bounded by `3^{-j} 3^k` times a fixed cutoff constant. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_depth_pow
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
      (2 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) := by
  have hgap_le_pow :
      coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k := by
    have hmain :
        27 * coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k :=
      coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
        hchoice hlt
    have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_nonneg hlt
    nlinarith
  have hfront_nonneg : 0 ≤ 2 * quantitativeCubeCutoffGradientConst d := by
    exact mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d)
  have hdepth_nonneg : 0 ≤ ((3 : ℝ) ^ j)⁻¹ := by positivity
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
        =
      (2 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * coarseCaccioppoliGapInv ρ₁ ρ₂) :=
          cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_eq_depthGap
            hR hlt
    _ ≤
      (2 * quantitativeCubeCutoffGradientConst d) *
        (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgap_le_pow hdepth_nonneg)
            hfront_nonneg

/-- Convert the descendant-depth/gap-scale product to the usual real-power
notation `3^(k-j)`. -/
theorem inv_pow_mul_pow_eq_rpow_sub (k j : ℕ) :
    (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) =
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hpowj : (3 : ℝ) ^ j = Real.rpow (3 : ℝ) (j : ℝ) := by
    exact (Real.rpow_natCast (3 : ℝ) j).symm
  have hpowk : (3 : ℝ) ^ k = Real.rpow (3 : ℝ) (k : ℝ) := by
    exact (Real.rpow_natCast (3 : ℝ) k).symm
  have hneg :
      Real.rpow (3 : ℝ) (-(j : ℝ)) =
        (Real.rpow (3 : ℝ) (j : ℝ))⁻¹ := by
    simp
  calc
    (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k)
        =
      Real.rpow (3 : ℝ) (-(j : ℝ)) *
        Real.rpow (3 : ℝ) (k : ℝ) := by
          rw [hpowj, hpowk, hneg]
    _ =
      Real.rpow (3 : ℝ) (-(j : ℝ) + (k : ℝ)) := by
          exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) (-(j : ℝ)) (k : ℝ)).symm
    _ =
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          congr 1
          ring

/-- LaTeX-shaped version of
`cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_depth_pow`. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
      (2 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  simpa [inv_pow_mul_pow_eq_rpow_sub k j] using
    (cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_depth_pow
      (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt)

/-- Buffered LaTeX-shaped gradient cutoff bound.  The midpoint cutoff doubles
the full-gap gradient bound, while the triadic scale is still chosen from the
full outer gap. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_buffered_cutoffGradient_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hG :
      cubeBesovScaleWeight (-1) R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
        (2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) :=
    cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_rpow_sub
      (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      2 * (cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂) := by
          rw [coarseCaccioppoliQuantitativeCutoffGradientBound_buffered_eq_two_mul Q hlt]
          ring
    _ ≤ 2 * ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 2)
    _ =
      (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          ring

/-- The Hessian gap factor gains one descendant scale.  This is the
`3^{-j} gap^{-2} ≤ 3^k` line used after choosing the triadic gap scale and
taking descendants at depth `j ≥ k`. -/
theorem coarseCaccioppoliGapInv_sq_mul_depthFactor_le_pow_of_triadicGapScaleChoice
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    ((3 : ℝ) ^ j)⁻¹ * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) ≤
      (3 : ℝ) ^ k := by
  let A : ℝ := (3 : ℝ) ^ k
  let B : ℝ := (3 : ℝ) ^ j
  let G : ℝ := coarseCaccioppoliGapInv ρ₁ ρ₂
  have hG_nonneg : 0 ≤ G := by
    exact coarseCaccioppoliGapInv_nonneg hlt
  have hG_le_A : G ≤ A := by
    have hmain : 27 * G ≤ A := by
      simpa [A, G] using
        (coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
          hchoice hlt)
    nlinarith
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by positivity
  have hA_le_B : A ≤ B := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hjk
  have hinv_le : B⁻¹ ≤ A⁻¹ := by
    exact (inv_le_inv₀ hB_pos hA_pos).2 hA_le_B
  have hG_sq : G ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hG_nonneg hG_le_A 2
  have hmul : B⁻¹ * G ^ (2 : ℕ) ≤ A⁻¹ * A ^ (2 : ℕ) := by
    exact mul_le_mul hinv_le hG_sq (pow_nonneg hG_nonneg 2)
      (inv_nonneg.mpr hA_pos.le)
  have hright : A⁻¹ * A ^ (2 : ℕ) = A := by
    field_simp [hA_pos.ne']
  simpa [A, B, G, hright] using hmul

/-- Algebraic normal form for the descendant Hessian cutoff contribution:
parent Hessian bound times the small-cube volume scale is a fixed parent
front constant times `3^{-j} gap^{-2}`. -/
theorem coarseCaccioppoliDescendantCutoffHessianScaleBound_eq_radiusConst_mul_depthGap
    {d : ℕ} (Q : TriadicCube d) {j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ =
      (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) *
        (((3 : ℝ) ^ j)⁻¹ *
          (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ)) := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hradius_ne : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  have hpow_ne : (3 : ℝ) ^ j ≠ 0 := by positivity
  unfold coarseCaccioppoliDescendantCutoffHessianScaleBound
    coarseCaccioppoliQuantitativeCutoffHessianBound
  rw [coarseCaccioppoliGapInv_eq_inv]
  field_simp [hgap_pos.ne', hradius_ne, hpow_ne]

/-- The descendant Hessian cutoff contribution is controlled by the note's
triadic gap scale, with only a fixed parent-radius front constant remaining. -/
theorem coarseCaccioppoliDescendantCutoffHessianScaleBound_le_radiusConst_mul_pow
    {d : ℕ} (Q : TriadicCube d) {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
      (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k := by
  have hdepth :
      ((3 : ℝ) ^ j)⁻¹ *
          (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) ≤ (3 : ℝ) ^ k :=
    coarseCaccioppoliGapInv_sq_mul_depthFactor_le_pow_of_triadicGapScaleChoice
      hchoice hlt hjk
  have hfront_nonneg :
      0 ≤ quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ) := by
    exact div_nonneg
      (mul_nonneg (quantitativeCubeCutoffHessianConst_nonneg d)
        (cubeScaleFactor_nonneg Q))
      (sq_nonneg (cubeRadius Q))
  calc
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂
        =
      (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) *
        (((3 : ℝ) ^ j)⁻¹ *
          (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ)) :=
          coarseCaccioppoliDescendantCutoffHessianScaleBound_eq_radiusConst_mul_depthGap
            Q hlt
    _ ≤ (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_left hdepth hfront_nonneg

/-- The centered Hessian cutoff contribution has one extra small-cube scale,
so after the triadic gap choice it also has the `3^(k-j)` normalization. -/
theorem cubeBesovScaleWeight_neg_one_mul_descendantCutoffHessianScaleBound_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
      (4 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hH :
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
        (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k :=
    coarseCaccioppoliDescendantCutoffHessianScaleBound_le_radiusConst_mul_pow
      Q hchoice hlt hjk
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight (-1) R :=
    cubeBesovScaleWeight_nonneg (-1) R
  have hscaled :=
    mul_le_mul_of_nonneg_left hH hscale_nonneg
  have hrad_ne : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  have hscale_eq :
      cubeBesovScaleWeight (-1) R *
          ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k) =
        (4 * quantitativeCubeCutoffHessianConst d) *
          (((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k) := by
    have hscale :
        cubeBesovScaleWeight (-1) R =
          (2 * ((3 : ℝ) ^ j)⁻¹) * cubeRadius Q := by
      rw [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor]
      calc
        cubeScaleFactor R =
            (cubeScaleFactor R / cubeRadius Q) * cubeRadius Q := by
              field_simp [hrad_ne]
        _ = (2 * ((3 : ℝ) ^ j)⁻¹) * cubeRadius Q := by
              rw [cubeScaleFactor_div_parent_cubeRadius_eq_two_mul_depthFactor hR]
    have hQscale : cubeScaleFactor Q = 2 * cubeRadius Q := by
      unfold cubeRadius
      ring
    rw [hscale, hQscale]
    field_simp [hrad_ne]
    ring
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂
        ≤
      cubeBesovScaleWeight (-1) R *
        ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k) := hscaled
    _ =
      (4 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          rw [hscale_eq, inv_pow_mul_pow_eq_rpow_sub]

/-- Buffered LaTeX-shaped Hessian cutoff bound.  The midpoint cutoff quadruples
the full-gap Hessian scale, while the triadic scale is still chosen from the
full outer gap. -/
theorem cubeBesovScaleWeight_neg_one_mul_descendantBufferedCutoffHessianScaleBound_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (16 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
  have hH :
      cubeBesovScaleWeight (-1) R *
          coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
        (4 * quantitativeCubeCutoffHessianConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) :=
    cubeBesovScaleWeight_neg_one_mul_descendantCutoffHessianScaleBound_le_rpow_sub
      (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk
  have hHbuf :
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
        4 * coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ := by
    unfold coarseCaccioppoliDescendantCutoffHessianScaleBound
    rw [coarseCaccioppoliQuantitativeCutoffHessianBound_buffered_eq_four_mul Q hlt]
    ring
  calc
    cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      4 * (cubeBesovScaleWeight (-1) R *
        coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂) := by
          rw [hHbuf]
          ring
    _ ≤ 4 * ((4 * quantitativeCubeCutoffHessianConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 4)
    _ =
      (16 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
          ring

/-- Combined small-cube cutoff contribution bounded by the note's triadic
scale.  This packages the Hessian `3^{-j} gap^{-2}` gain together with the
gradient `gap^{-1}` contribution. -/
theorem coarseCaccioppoliDescendantCutoffTerms_le_radiusConst_mul_pow
    {d : ℕ} (Q : TriadicCube d) {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
      ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
        (3 : ℝ) ^ k := by
  have hH :
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
        (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k :=
    coarseCaccioppoliDescendantCutoffHessianScaleBound_le_radiusConst_mul_pow
      Q hchoice hlt hjk
  have hG :
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
        (quantitativeCubeCutoffGradientConst d / cubeRadius Q) * (3 : ℝ) ^ k :=
    coarseCaccioppoliQuantitativeCutoffGradientBound_le_radiusConst_mul_pow
      Q hchoice hlt
  calc
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
        ≤
      (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k +
        (quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
          (3 : ℝ) ^ k := by
          exact add_le_add hH hG
    _ =
      ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
        (3 : ℝ) ^ k := by
          ring

/-- Descendant form of the combined cutoff bound, in the scaled bracket used by
the constant branch of the exact single-cube estimate. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_cutoff_terms_le_radiusConst_mul_pow
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂) ≤
      ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
        (3 : ℝ) ^ k := by
  calc
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        =
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ :=
          cubeBesovScaleWeight_neg_one_mul_parent_cutoff_terms_eq_descendant
            hR ρ₁ ρ₂
    _ ≤
      ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
        (3 : ℝ) ^ k :=
          coarseCaccioppoliDescendantCutoffTerms_le_radiusConst_mul_pow
            Q hchoice hlt hjk

/-- Buffered version of `coarseCaccioppoliDescendantCutoffTerms_le_radiusConst_mul_pow`.
The midpoint cutoff inflates the Hessian contribution by `4` and the gradient
contribution by `2`, while the triadic scale is still the full outer gap. -/
theorem coarseCaccioppoliDescendantCutoffTerms_buffered_le_radiusConst_mul_pow
    {d : ℕ} (Q : TriadicCube d) {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) ≤
      (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
  have hH :
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ ≤
        (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k :=
    coarseCaccioppoliDescendantCutoffHessianScaleBound_le_radiusConst_mul_pow
      Q hchoice hlt hjk
  have hG :
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ≤
        (quantitativeCubeCutoffGradientConst d / cubeRadius Q) * (3 : ℝ) ^ k :=
    coarseCaccioppoliQuantitativeCutoffGradientBound_le_radiusConst_mul_pow
      Q hchoice hlt
  have hHbuf :
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
        4 * coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ := by
    unfold coarseCaccioppoliDescendantCutoffHessianScaleBound
    rw [coarseCaccioppoliQuantitativeCutoffHessianBound_buffered_eq_four_mul Q hlt]
    ring
  have hGbuf :
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) =
        2 * coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffGradientBound_buffered_eq_two_mul Q hlt
  calc
    coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
        (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
        =
      4 * coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂ +
        2 * coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
          rw [hHbuf, hGbuf]
    _ ≤
      4 * ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) * (3 : ℝ) ^ k) +
        2 * ((quantitativeCubeCutoffGradientConst d / cubeRadius Q) *
          (3 : ℝ) ^ k) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 4))
            (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 2))
    _ =
      (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
          ring

/-- Descendant form of the buffered combined cutoff bound, in the scaled
bracket used by the constant branch. -/
theorem cubeBesovScaleWeight_neg_one_mul_parent_buffered_cutoff_terms_le_radiusConst_mul_pow
    {d : ℕ} {Q R : TriadicCube d} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) ≤
      (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k := by
  calc
    cubeBesovScaleWeight (-1) R *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        =
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) :=
          cubeBesovScaleWeight_neg_one_mul_parent_cutoff_terms_eq_descendant
            hR ρ₁ (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)
    _ ≤
      (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
            (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) *
        (3 : ℝ) ^ k :=
          coarseCaccioppoliDescendantCutoffTerms_buffered_le_radiusConst_mul_pow
            Q hchoice hlt hjk

end

end Homogenization
