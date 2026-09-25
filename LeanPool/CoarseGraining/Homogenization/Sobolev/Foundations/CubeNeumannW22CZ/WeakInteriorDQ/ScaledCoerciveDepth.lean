/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianRestrictionSum

/-! # Scaled Coercive Depth -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

/-!
# Scale-correct coercivity constants for C.2 depth estimates

This file plugs the dilation-scaled cube Poincare estimate into the
scale-sharp Hessian-to-Besov depth handoff.  The main point is that all
depth-`j` descendants of a triadic cube have the same scale, so the prefactor
`volume(R)^{-1/2} * PoincareConstant(R)` is uniform over descendants.
-/

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  rw [cubeScaleFactor]
  positivity

private theorem cubeScaleFactor_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeScaleFactor Q :=
  le_of_lt (cubeScaleFactor_pos Q)

/-- The scaled mean-zero coercivity estimate on every depth-`j` descendant. -/
noncomputable def scaledDescendantMeanZeroH1CoerciveEstimate {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    ∀ R ∈ descendantsAtDepth Q j, H1CoerciveEstimate (openCubeSet R) :=
  fun R _hR => scaledTranslatedCubeMeanZeroH1CoerciveEstimate R

/-- Uniform depth constant for the scale-sharp C.2 Poincare prefactor. -/
noncomputable def scaledDescendantCoercivePrefactor {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) : ℝ :=
  ((cubeVolume (originCube d (Q.scale - j)))⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor (originCube d (Q.scale - j)) *
      (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue)

theorem scaledDescendantCoercivePrefactor_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    0 ≤ scaledDescendantCoercivePrefactor Q j := by
  unfold scaledDescendantCoercivePrefactor
  have hvolInv :
      0 ≤ (cubeVolume (originCube d (Q.scale - j)))⁻¹ :=
    inv_nonneg.mpr (cubeVolume_nonneg _)
  exact mul_nonneg
    (Real.rpow_nonneg hvolInv _)
    (mul_nonneg (cubeScaleFactor_nonneg _)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)

theorem scaledDescendantCoercivePrefactor_eq {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (scaledDescendantMeanZeroH1CoerciveEstimate Q j R hR).fixedValue =
      scaledDescendantCoercivePrefactor Q j := by
  have hscale : R.scale = Q.scale - j :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hfactor :
      cubeScaleFactor R = cubeScaleFactor (originCube d (Q.scale - j)) := by
    simp [cubeScaleFactor, originCube, hscale]
  have hvol :
      cubeVolume R = cubeVolume (originCube d (Q.scale - j)) := by
    simp [cubeVolume_eq_scaleFactor_pow, hfactor]
  unfold scaledDescendantMeanZeroH1CoerciveEstimate
    scaledDescendantCoercivePrefactor
  rw [scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant, hvol, hfactor]

theorem scaledDescendantCoercivePrefactor_bound {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (scaledDescendantMeanZeroH1CoerciveEstimate Q j R hR).fixedValue ≤
      scaledDescendantCoercivePrefactor Q j := by
  exact le_of_eq (scaledDescendantCoercivePrefactor_eq hR)

theorem cubeBesovDepthWeight_mul_scaledDescendantCoercivePrefactor {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeBesovDepthWeight Q 1 j * scaledDescendantCoercivePrefactor Q j =
      ((cubeVolume (originCube d (Q.scale - j)))⁻¹) ^ (1 / 2 : ℝ) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
  let R0 : TriadicCube d := originCube d (Q.scale - j)
  have hscale :
      cubeScaleFactor Q / (3 : ℝ) ^ j = cubeScaleFactor R0 := by
    dsimp [R0, cubeScaleFactor, originCube]
    rw [zpow_sub₀]
    · simp [div_eq_mul_inv]
    · norm_num
  have hR0_pos : 0 < cubeScaleFactor R0 := cubeScaleFactor_pos R0
  unfold cubeBesovDepthWeight scaledDescendantCoercivePrefactor
  dsimp [R0] at hscale hR0_pos ⊢
  rw [hscale]
  rw [show -(1 : ℝ) = (-1 : ℝ) by norm_num]
  rw [Real.rpow_neg_one]
  field_simp [hR0_pos.ne']

private theorem cubeVolume_originCube_eq_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeVolume (originCube d (Q.scale - j)) = cubeVolume R := by
  have hscale : R.scale = Q.scale - j :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hfactor :
      cubeScaleFactor R = cubeScaleFactor (originCube d (Q.scale - j)) := by
    simp [cubeScaleFactor, originCube, hscale]
  simp [cubeVolume_eq_scaleFactor_pow, hfactor]

private theorem descendant_card_volume_rpow_half_mul_cardInv_sq_rpow_half {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {A : ℝ} (hA : 0 ≤ A) :
    ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ)) =
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * A := by
  let c : ℝ := ((descendantsAtDepth Q j).card : ℝ)
  let v : ℝ := cubeVolume R
  have hcard_ne : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hcard_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hv_pos : 0 < v := by
    dsimp [v]
    exact cubeVolume_pos R
  have hv_nonneg : 0 ≤ v := le_of_lt hv_pos
  have hv_ne : v ≠ 0 := hv_pos.ne'
  have hQvol : cubeVolume Q = c * v := by
    dsimp [c, v]
    exact cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR
  have hQ_pos : 0 < cubeVolume Q := cubeVolume_pos Q
  have hinside_nonneg : 0 ≤ c⁻¹ * A ^ 2 := by
    exact mul_nonneg (inv_nonneg.mpr hcard_nonneg) (sq_nonneg A)
  have hmul :
      v⁻¹ * (c⁻¹ * A ^ 2) = (cubeVolume Q)⁻¹ * A ^ 2 := by
    rw [hQvol]
    field_simp [hcard_ne, hv_ne]
  have hroot_sq : (A ^ 2) ^ (1 / 2 : ℝ) = A := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hA]
  calc
    ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ))
        = (v⁻¹) ^ (1 / 2 : ℝ) * ((c⁻¹ * A ^ 2) ^ (1 / 2 : ℝ)) := by
            simp [c, v]
    _ = (v⁻¹ * (c⁻¹ * A ^ 2)) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (inv_nonneg.mpr hv_nonneg) hinside_nonneg]
    _ = ((cubeVolume Q)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ) := by
          rw [hmul]
    _ = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * ((A ^ 2) ^ (1 / 2 : ℝ)) := by
          rw [Real.mul_rpow (inv_nonneg.mpr (le_of_lt hQ_pos)) (sq_nonneg A)]
    _ = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * A := by
          rw [hroot_sq]

theorem scaledDepthPrefactor_mul_cardInvHessianRoot_eq_parentVolume {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    cubeBesovDepthWeight Q 1 j *
        (scaledDescendantCoercivePrefactor Q j *
          ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ))) =
      (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) * A := by
  rcases descendantsAtDepth_nonempty Q j with ⟨R, hR⟩
  have hvol :
      cubeVolume (originCube d (Q.scale - j)) = cubeVolume R :=
    cubeVolume_originCube_eq_of_mem_descendantsAtDepth hR
  have hroot :
      ((cubeVolume (originCube d (Q.scale - j)))⁻¹) ^ (1 / 2 : ℝ) *
          ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ)) =
        ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * A := by
    rw [hvol]
    exact descendant_card_volume_rpow_half_mul_cardInv_sq_rpow_half hR hA
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let V0 : ℝ := ((cubeVolume (originCube d (Q.scale - j)))⁻¹) ^ (1 / 2 : ℝ)
  let root : ℝ :=
    ((((descendantsAtDepth Q j).card : ℝ)⁻¹ * A ^ 2) ^ (1 / 2 : ℝ))
  have hweight :
      cubeBesovDepthWeight Q 1 j * scaledDescendantCoercivePrefactor Q j = V0 * C0 := by
    simpa [V0, C0] using cubeBesovDepthWeight_mul_scaledDescendantCoercivePrefactor Q j
  have hroot' : V0 * root = ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * A := by
    simpa [V0, root] using hroot
  calc
    cubeBesovDepthWeight Q 1 j *
        (scaledDescendantCoercivePrefactor Q j * root)
        = (cubeBesovDepthWeight Q 1 j * scaledDescendantCoercivePrefactor Q j) * root := by
            ring
    _ = (V0 * C0) * root := by
          rw [hweight]
    _ = C0 * (V0 * root) := by
          ring
    _ = C0 * (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * A) := by
          rw [hroot']
    _ = (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * C0) * A := by
          ring

namespace HasWeakHessianOn

variable {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}

/-- Scale-correct C.2 depth handoff with the descendant Poincare constants
discharged by dilation-scaled cube coercivity. -/
theorem cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_scaledCoercivePrefactor
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      cubeBesovDepthWeight Q 1 j *
        (scaledDescendantCoercivePrefactor Q j *
          ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            H.hessianCoordL2NormSum ^ 2) ^ (1 / 2 : ℝ))) := by
  exact
    H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_const_mul_cardInvGlobal_hessianCoordL2NormSum
      i j (scaledDescendantMeanZeroH1CoerciveEstimate Q j)
      (scaledDescendantCoercivePrefactor_nonneg Q j)
      (fun R hR => scaledDescendantCoercivePrefactor_bound hR)

theorem cubeBesovDepthSeminorm_gradCoord_le_parentVolume_scaledCoercive
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) (j : ℕ) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j ≤
      (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
        H.hessianCoordL2NormSum := by
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j
        ≤ cubeBesovDepthWeight Q 1 j *
            (scaledDescendantCoercivePrefactor Q j *
              ((((descendantsAtDepth Q j).card : ℝ)⁻¹ *
                H.hessianCoordL2NormSum ^ 2) ^ (1 / 2 : ℝ))) :=
          H.cubeBesovDepthSeminorm_gradCoord_le_depthWeight_mul_scaledCoercivePrefactor i j
    _ = (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
          H.hessianCoordL2NormSum :=
        scaledDepthPrefactor_mul_cardInvHessianRoot_eq_parentVolume Q j
          H.hessianCoordL2NormSum_nonneg

end HasWeakHessianOn

end

end Homogenization
