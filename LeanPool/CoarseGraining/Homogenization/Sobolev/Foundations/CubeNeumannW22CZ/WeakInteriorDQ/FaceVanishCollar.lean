/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CutoffBoundaryError
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Face Vanish Collar -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

/-- Projection onto the lower `i`-normal face, changing only coordinate `i`. -/
def cubeLowerFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (cubeLowerFaceCoord Q i)

/-- Projection onto the upper `i`-normal face, changing only coordinate `i`. -/
def cubeUpperFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (cubeUpperFaceCoord Q i)

theorem cubeLowerFaceCoord_eq_cubeCenter_sub_cubeRadius {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeLowerFaceCoord Q i = cubeCenter Q i - cubeRadius Q := by
  simp [cubeLowerFaceCoord, cubeCenter, cubeRadius]
  ring_nf

theorem cubeUpperFaceCoord_eq_cubeCenter_add_cubeRadius {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeUpperFaceCoord Q i = cubeCenter Q i + cubeRadius Q := by
  simp [cubeUpperFaceCoord, cubeCenter, cubeRadius]
  ring_nf

private theorem norm_sub_update_coord_le_abs_sub {d : ℕ}
    (x : Vec d) (i : Fin d) (a : ℝ) :
    ‖x - Function.update x i a‖ ≤ |x i - a| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 ?_
  intro j
  by_cases hji : j = i
  · subst hji
    simp [Function.update, Real.norm_eq_abs]
  · simp [Function.update, hji]

theorem norm_sub_cubeLowerFaceProjection_le {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖x - cubeLowerFaceProjection Q i x‖ ≤ |x i - cubeLowerFaceCoord Q i| :=
  norm_sub_update_coord_le_abs_sub x i (cubeLowerFaceCoord Q i)

theorem norm_sub_cubeUpperFaceProjection_le {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    ‖x - cubeUpperFaceProjection Q i x‖ ≤ |x i - cubeUpperFaceCoord Q i| :=
  norm_sub_update_coord_le_abs_sub x i (cubeUpperFaceCoord Q i)

theorem norm_sub_le_mul_norm_sub_of_fderiv_bound {d : ℕ}
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {L : ℝ}
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L) (x y : Vec d) :
    ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ := by
  simpa using
    (Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := ψ) (s := Set.univ) (C := L) (x := y) (y := x)
      (fun z _ => hψ.differentiable (by simp) z)
      (fun z _ => hbound z) convex_univ trivial trivial)

theorem norm_le_mul_abs_sub_lowerFace_of_face_zero {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (x : Vec d) (hzero : ψ (cubeLowerFaceProjection Q i x) = 0) :
    ‖ψ x‖ ≤ L * |x i - cubeLowerFaceCoord Q i| := by
  calc
    ‖ψ x‖ = ‖ψ x - ψ (cubeLowerFaceProjection Q i x)‖ := by
      rw [hzero, sub_zero]
    _ ≤ L * ‖x - cubeLowerFaceProjection Q i x‖ :=
      norm_sub_le_mul_norm_sub_of_fderiv_bound hψ hbound x (cubeLowerFaceProjection Q i x)
    _ ≤ L * |x i - cubeLowerFaceCoord Q i| :=
      mul_le_mul_of_nonneg_left (norm_sub_cubeLowerFaceProjection_le Q i x) hL

theorem norm_le_mul_abs_sub_upperFace_of_face_zero {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (x : Vec d) (hzero : ψ (cubeUpperFaceProjection Q i x) = 0) :
    ‖ψ x‖ ≤ L * |x i - cubeUpperFaceCoord Q i| := by
  calc
    ‖ψ x‖ = ‖ψ x - ψ (cubeUpperFaceProjection Q i x)‖ := by
      rw [hzero, sub_zero]
    _ ≤ L * ‖x - cubeUpperFaceProjection Q i x‖ :=
      norm_sub_le_mul_norm_sub_of_fderiv_bound hψ hbound x (cubeUpperFaceProjection Q i x)
    _ ≤ L * |x i - cubeUpperFaceCoord Q i| :=
      mul_le_mul_of_nonneg_left (norm_sub_cubeUpperFaceProjection_le Q i x) hL

/-- In the inner coordinate collar, a point that still lies in the full cube is
within `(1 - ρ₁) * radius` of one of the two `i`-normal faces. -/
theorem face_distance_le_of_mem_scaledClosedCubeSet_coordInnerCollar {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₂_le_one : ρ₂ ≤ 1)
    (i : Fin d) {x : Vec d}
    (hxouter : x ∈ scaledClosedCubeSet Q ρ₂)
    (hxcollar : x ∈ cubeCoordInnerCollar Q ρ₁ i) :
    |x i - cubeLowerFaceCoord Q i| ≤ (1 - ρ₁) * cubeRadius Q ∨
      |x i - cubeUpperFaceCoord Q i| ≤ (1 - ρ₁) * cubeRadius Q := by
  let t : ℝ := x i - cubeCenter Q i
  have hrad_pos : 0 < cubeRadius Q := cubeRadius_pos Q
  have hrad_nonneg : 0 ≤ cubeRadius Q := le_of_lt hrad_pos
  have houter_abs : |t| ≤ ρ₂ * cubeRadius Q := by
    simpa [t] using hxouter i
  have hcollar_abs : ρ₁ * cubeRadius Q ≤ |t| := by
    simpa [cubeCoordInnerCollar, t] using hxcollar
  have hρ₂rad_le : ρ₂ * cubeRadius Q ≤ cubeRadius Q := by
    simpa using mul_le_mul_of_nonneg_right hρ₂_le_one hrad_nonneg
  have ht_le_rad : t ≤ cubeRadius Q := by
    exact (le_abs_self t).trans (houter_abs.trans hρ₂rad_le)
  have hneg_t_le_rad : -t ≤ cubeRadius Q := by
    exact (neg_le_abs t).trans (houter_abs.trans hρ₂rad_le)
  by_cases ht_nonneg : 0 ≤ t
  · right
    have hρ_le_t : ρ₁ * cubeRadius Q ≤ t := by
      simpa [abs_of_nonneg ht_nonneg] using hcollar_abs
    have hnonpos :
        x i - cubeUpperFaceCoord Q i ≤ 0 := by
      rw [cubeUpperFaceCoord_eq_cubeCenter_add_cubeRadius]
      have ht_eq : x i - cubeCenter Q i = t := rfl
      linarith
    calc
      |x i - cubeUpperFaceCoord Q i|
          = cubeUpperFaceCoord Q i - x i := by
            rw [abs_of_nonpos hnonpos]
            ring
      _ = cubeRadius Q - t := by
            rw [cubeUpperFaceCoord_eq_cubeCenter_add_cubeRadius]
            ring
      _ ≤ (1 - ρ₁) * cubeRadius Q := by
            nlinarith
  · left
    have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
    have hρ_le_neg_t : ρ₁ * cubeRadius Q ≤ -t := by
      simpa [abs_of_neg ht_neg] using hcollar_abs
    have hnonneg :
        0 ≤ x i - cubeLowerFaceCoord Q i := by
      rw [cubeLowerFaceCoord_eq_cubeCenter_sub_cubeRadius]
      have ht_eq : x i - cubeCenter Q i = t := rfl
      linarith
    calc
      |x i - cubeLowerFaceCoord Q i|
          = x i - cubeLowerFaceCoord Q i := by
            rw [abs_of_nonneg hnonneg]
      _ = cubeRadius Q + t := by
            rw [cubeLowerFaceCoord_eq_cubeCenter_sub_cubeRadius]
            ring
      _ ≤ (1 - ρ₁) * cubeRadius Q := by
            nlinarith

/-- Smooth functions vanishing on the two `i`-normal face projections are small
on the coordinate collar, with the expected distance-to-face factor. -/
theorem norm_le_of_face_zero_on_coordInnerCollar {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ L : ℝ} (hρ₂_le_one : ρ₂ ≤ 1)
    (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hL : 0 ≤ L)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0)
    {x : Vec d} (hxouter : x ∈ scaledClosedCubeSet Q ρ₂)
    (hxcollar : x ∈ cubeCoordInnerCollar Q ρ₁ i) :
    ‖ψ x‖ ≤ L * ((1 - ρ₁) * cubeRadius Q) := by
  rcases face_distance_le_of_mem_scaledClosedCubeSet_coordInnerCollar
      Q hρ₂_le_one i hxouter hxcollar with hlower | hupper
  · exact (norm_le_mul_abs_sub_lowerFace_of_face_zero Q i hψ hL hbound
      x (hlower_zero x)).trans (mul_le_mul_of_nonneg_left hlower hL)
  · exact (norm_le_mul_abs_sub_upperFace_of_face_zero Q i hψ hL hbound
      x (hupper_zero x)).trans (mul_le_mul_of_nonneg_left hupper hL)

/-- Inside the open cube, a coordinate inner collar is contained in an ordinary
cube boundary layer. The boundary layer thickness is intentionally twice the
sharp thickness; this avoids half-open face bookkeeping and is still
asymptotically sharp enough for the cutoff limit. -/
theorem cubeCoordInnerCollar_inter_openCubeSet_subset_cubeBoundaryLayer {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ_lt_one : ρ < 1) (i : Fin d) :
    cubeCoordInnerCollar Q ρ i ∩ openCubeSet Q ⊆ cubeBoundaryLayer Q (1 - ρ) := by
  intro x hx
  refine ⟨openCubeSet_subset_cubeSet Q hx.2, ?_⟩
  intro hxshr
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hshr_i := hxshr i
  have hlow :
      -(ρ * cubeRadius Q) < x i - cubeCenter Q i := by
    dsimp [cubeShrunkSet, cubeCenter, cubeRadius] at hshr_i ⊢
    nlinarith
  have hhigh :
      x i - cubeCenter Q i < ρ * cubeRadius Q := by
    dsimp [cubeShrunkSet, cubeCenter, cubeRadius] at hshr_i ⊢
    nlinarith
  have habs : |x i - cubeCenter Q i| < ρ * cubeRadius Q :=
    abs_lt.mpr ⟨hlow, hhigh⟩
  exact not_le_of_gt habs hx.1

theorem volumeMeasureOn_openCubeSet_cubeCoordInnerCollar_le_cubeBoundaryLayer {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ_lt_one : ρ < 1) (i : Fin d) :
    volumeMeasureOn (openCubeSet Q) (cubeCoordInnerCollar Q ρ i) ≤
      MeasureTheory.volume (cubeBoundaryLayer Q (1 - ρ)) := by
  rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply
    (measurableSet_cubeCoordInnerCollar Q ρ i)]
  exact MeasureTheory.measure_mono
    (cubeCoordInnerCollar_inter_openCubeSet_subset_cubeBoundaryLayer Q hρ_lt_one i)

private theorem norm_basisVec {d : ℕ} (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

private theorem quantitativeCubeCutoffGradientConst_nonneg (d : ℕ) :
    0 ≤ quantitativeCubeCutoffGradientConst d := by
  dsimp [quantitativeCubeCutoffGradientConst]
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ)),
    smoothTransitionProfile.derivBound_nonneg]

/-- Face-vanishing version of the cutoff derivative error. The derivative of
the cutoff supplies both localizations: it is supported in the coordinate
collar and in the outer cutoff cube. -/
theorem norm_canonicalFun_coordDeriv_mul_le_of_face_zero {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ L A : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂_le_one : ρ₂ ≤ 1)
    (hL : 0 ≤ L) (hA_nonneg : 0 ≤ A)
    (hA_width : 1 - ρ₁ ≤ A * (ρ₂ - ρ₁))
    (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0) :
    ∀ x : Vec d,
      ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
          ψ x‖ ≤
        (L * A) * quantitativeCubeCutoffGradientConst d := by
  intro x
  by_cases hderiv_zero :
      (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) = 0
  · simp [hderiv_zero,
      mul_nonneg (mul_nonneg hL hA_nonneg) (quantitativeCubeCutoffGradientConst_nonneg d)]
  · have hx_collar :
        x ∈ cubeCoordInnerCollar Q ρ₁ i :=
      support_canonicalFun_fderiv_apply_basisVec_subset_cubeCoordInnerCollar
        Q hρ₁ hρ₁₂ i hderiv_zero
    have hx_outer :
        x ∈ scaledClosedCubeSet Q ρ₂ :=
      QuantitativeCubeCutoff.support_fderiv_canonicalFun_apply_basisVec_subset_scaledClosedCubeSet
        Q hρ₁ hρ₁₂ i hderiv_zero
    have hgap_pos : 0 < (ρ₂ - ρ₁) * cubeRadius Q :=
      mul_pos (sub_pos.mpr hρ₁₂) (cubeRadius_pos Q)
    have hgap_nonneg : 0 ≤ (ρ₂ - ρ₁) * cubeRadius Q := le_of_lt hgap_pos
    have hconst_nonneg : 0 ≤ quantitativeCubeCutoffGradientConst d :=
      quantitativeCubeCutoffGradientConst_nonneg d
    have hψ_face :
        ‖ψ x‖ ≤ L * ((1 - ρ₁) * cubeRadius Q) :=
      norm_le_of_face_zero_on_coordInnerCollar
        Q hρ₂_le_one i hψ hL hbound hlower_zero hupper_zero hx_outer hx_collar
    have hwidth :
        (1 - ρ₁) * cubeRadius Q ≤
          (A * (ρ₂ - ρ₁)) * cubeRadius Q :=
      mul_le_mul_of_nonneg_right hA_width (cubeRadius_nonneg Q)
    have hψ_bound :
        ‖ψ x‖ ≤ (L * A) * ((ρ₂ - ρ₁) * cubeRadius Q) := by
      calc
        ‖ψ x‖ ≤ L * ((1 - ρ₁) * cubeRadius Q) := hψ_face
        _ ≤ L * ((A * (ρ₂ - ρ₁)) * cubeRadius Q) :=
          mul_le_mul_of_nonneg_left hwidth hL
        _ = (L * A) * ((ρ₂ - ρ₁) * cubeRadius Q) := by ring
    have hcoord :
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖ ≤
          quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
      calc
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖
            ≤ ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x‖ *
                ‖basisVec i‖ := by
              exact (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x).le_opNorm
                (basisVec i)
        _ = ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x‖ := by
              simp [norm_basisVec]
        _ ≤ quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
              let η : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
                QuantitativeCubeCutoff.canonical Q ρ₁ ρ₂ hρ₁ hρ₁₂
              simpa [η, QuantitativeCubeCutoff.canonical] using η.gradient_bound x
    calc
      ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
          ψ x‖
          =
        ‖(fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i)‖ *
          ‖ψ x‖ := norm_mul _ _
      _ ≤
          (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) *
            ((L * A) * ((ρ₂ - ρ₁) * cubeRadius Q)) := by
        exact mul_le_mul hcoord hψ_bound
          (norm_nonneg (ψ x))
          (div_nonneg hconst_nonneg hgap_nonneg)
      _ = (L * A) * quantitativeCubeCutoffGradientConst d := by
        rw [show
          (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)) *
              ((L * A) * ((ρ₂ - ρ₁) * cubeRadius Q)) =
            (L * A) * ((quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) * ((ρ₂ - ρ₁) * cubeRadius Q)) by
          ring]
        rw [div_mul_cancel₀ _ hgap_pos.ne']

/-- `L²` form of the face-vanishing cutoff derivative error. -/
theorem eLpNorm_canonicalFun_coordDeriv_mul_le_of_face_zero {d : ℕ}
    {U : Set (Vec d)} (Q : TriadicCube d) {ρ₁ ρ₂ L A : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂_le_one : ρ₂ ≤ 1)
    (hL : 0 ≤ L) (hA_nonneg : 0 ≤ A)
    (hA_width : 1 - ρ₁ ≤ A * (ρ₂ - ρ₁))
    (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0) :
    MeasureTheory.eLpNorm
        (fun x : Vec d =>
          (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
            ψ x)
        2 (volumeMeasureOn U) ≤
      ENNReal.ofReal ((L * A) * quantitativeCubeCutoffGradientConst d) *
        (volumeMeasureOn U (cubeCoordInnerCollar Q ρ₁ i)) ^
          (1 / (2 : ENNReal).toReal) := by
  let F : Vec d → ℝ :=
    fun x =>
      (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x) (basisVec i) *
        ψ x
  have hC_nonneg : 0 ≤ (L * A) * quantitativeCubeCutoffGradientConst d :=
    mul_nonneg (mul_nonneg hL hA_nonneg) (quantitativeCubeCutoffGradientConst_nonneg d)
  have hdist : ∀ x : Vec d, dist (F x) 0 ≤
      (L * A) * quantitativeCubeCutoffGradientConst d := by
    intro x
    simpa [F, dist_eq_norm] using
      norm_canonicalFun_coordDeriv_mul_le_of_face_zero
        Q hρ₁ hρ₁₂ hρ₂_le_one hL hA_nonneg hA_width
        i ψ hψ hbound hlower_zero hupper_zero x
  have hsupport :
      Function.support F ⊆ cubeCoordInnerCollar Q ρ₁ i := by
    simpa [F] using
      support_canonicalFun_coordDeriv_mul_subset_cubeCoordInnerCollar
        Q hρ₁ hρ₁₂ i ψ
  have hzero_support :
      Function.support (0 : Vec d → ℝ) ⊆ cubeCoordInnerCollar Q ρ₁ i := by
    simp
  have hmain :=
    MeasureTheory.eLpNorm_sub_le_of_dist_bdd
      (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      (s := cubeCoordInnerCollar Q ρ₁ i)
      (by norm_num : (2 : ENNReal) ≠ ∞)
      (measurableSet_cubeCoordInnerCollar Q ρ₁ i)
      hC_nonneg hdist hsupport hzero_support
  have hsub : F - (fun _ : Vec d => (0 : ℝ)) = F := by
    funext x
    simp
  rw [hsub] at hmain
  simpa [F] using hmain

/-- If the active coordinate collar has vanishing measure and the cutoff
annuli have uniformly bounded aspect ratio, then the cutoff-gradient face error
goes to zero in `L²`. -/
theorem tendsto_eLpNorm_canonicalFun_coordDeriv_mul_of_face_zero_of_collar_measure
    {d : ℕ} {U : Set (Vec d)} (Q : TriadicCube d)
    {ρ₁ ρ₂ : ℕ → ℝ} {L A : ℝ}
    (hρ₁ : ∀ n, 0 < ρ₁ n) (hρ₁₂ : ∀ n, ρ₁ n < ρ₂ n)
    (hρ₂_le_one : ∀ n, ρ₂ n ≤ 1)
    (hL : 0 ≤ L) (hA_nonneg : 0 ≤ A)
    (hA_width : ∀ n, 1 - ρ₁ n ≤ A * (ρ₂ n - ρ₁ n))
    (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0)
    (hcollar :
      Filter.Tendsto
        (fun n => volumeMeasureOn U (cubeCoordInnerCollar Q (ρ₁ n) i))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x : Vec d =>
            (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q (ρ₁ n) (ρ₂ n)) x)
                (basisVec i) * ψ x)
          2 (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal ((L * A) * quantitativeCubeCutoffGradientConst d)
  let pexp : ℝ := 1 / (2 : ENNReal).toReal
  have hpow :
      Filter.Tendsto
        (fun n => (volumeMeasureOn U (cubeCoordInnerCollar Q (ρ₁ n) i)) ^ pexp)
        Filter.atTop (nhds 0) := by
    have h := hcollar.ennrpow_const pexp
    have hpexp_pos : 0 < pexp := by
      dsimp [pexp]
      norm_num
    simpa [pexp, ENNReal.zero_rpow_of_pos hpexp_pos] using h
  have hrhs :
      Filter.Tendsto
        (fun n => C *
          (volumeMeasureOn U (cubeCoordInnerCollar Q (ρ₁ n) i)) ^ pexp)
        Filter.atTop (nhds 0) := by
    have hC_ne_top : C ≠ ⊤ := by
      simp [C]
    have h := ENNReal.Tendsto.const_mul (a := C) hpow (Or.inr hC_ne_top)
    simpa [C] using h
  have hle :
      ∀ n,
        MeasureTheory.eLpNorm
            (fun x : Vec d =>
              (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Q (ρ₁ n) (ρ₂ n)) x)
                  (basisVec i) * ψ x)
            2 (volumeMeasureOn U) ≤
          C * (volumeMeasureOn U (cubeCoordInnerCollar Q (ρ₁ n) i)) ^ pexp := by
    intro n
    simpa [C, pexp] using
      eLpNorm_canonicalFun_coordDeriv_mul_le_of_face_zero
        (U := U) Q (hρ₁ n) (hρ₁₂ n) (hρ₂_le_one n)
        hL hA_nonneg (hA_width n) i ψ hψ hbound hlower_zero hupper_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ => bot_le) hle

/-- A concrete inner radius schedule approaching the cube boundary. The
denominator starts at `5` only to keep the associated boundary-layer thickness
at most `1/2` for every index. -/
def faceCutoffInnerRadius (n : ℕ) : ℝ :=
  1 - 2 / ((n : ℝ) + 5)

/-- The matching outer radius schedule. -/
def faceCutoffOuterRadius (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 5)

theorem faceCutoffInnerRadius_pos (n : ℕ) :
    0 < faceCutoffInnerRadius n := by
  have hden : 0 < (n : ℝ) + 5 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  dsimp [faceCutoffInnerRadius]
  field_simp [hden.ne']
  nlinarith

theorem faceCutoffInnerRadius_lt_outer (n : ℕ) :
    faceCutoffInnerRadius n < faceCutoffOuterRadius n := by
  have hden : 0 < (n : ℝ) + 5 := by positivity
  dsimp [faceCutoffInnerRadius, faceCutoffOuterRadius]
  field_simp [hden.ne']
  linarith

theorem faceCutoffOuterRadius_le_one (n : ℕ) :
    faceCutoffOuterRadius n ≤ 1 := by
  have hden : 0 < (n : ℝ) + 5 := by positivity
  dsimp [faceCutoffOuterRadius]
  have hnonneg : 0 ≤ 1 / ((n : ℝ) + 5) := by positivity
  linarith

theorem faceCutoffOuterRadius_nonneg (n : ℕ) :
    0 ≤ faceCutoffOuterRadius n :=
  le_of_lt (lt_trans (faceCutoffInnerRadius_pos n) (faceCutoffInnerRadius_lt_outer n))

theorem faceCutoffOuterRadius_lt_one (n : ℕ) :
    faceCutoffOuterRadius n < 1 := by
  have hden : 0 < (n : ℝ) + 5 := by positivity
  dsimp [faceCutoffOuterRadius]
  have hpos : 0 < 1 / ((n : ℝ) + 5) := by positivity
  linarith

theorem faceCutoffInnerOuter_width_control (n : ℕ) :
    1 - faceCutoffInnerRadius n ≤
      2 * (faceCutoffOuterRadius n - faceCutoffInnerRadius n) := by
  dsimp [faceCutoffInnerRadius, faceCutoffOuterRadius]
  ring_nf
  exact le_rfl

theorem faceCutoffInnerRadius_lt_one (n : ℕ) :
    faceCutoffInnerRadius n < 1 := by
  have hden : 0 < (n : ℝ) + 5 := by positivity
  dsimp [faceCutoffInnerRadius]
  have hpos : 0 < 2 / ((n : ℝ) + 5) := by positivity
  linarith

theorem tendsto_faceCutoffInnerRadius_one :
    Filter.Tendsto faceCutoffInnerRadius Filter.atTop (nhds 1) := by
  have hdenCast :
      Filter.Tendsto (fun n : ℕ => (((n + 5 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 5)
  have hden :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) + 5)
        Filter.atTop Filter.atTop := by
    convert hdenCast using 1
    ext n
    simp [Nat.cast_add]
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 5)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hfrac : Filter.Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 5))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_const_nhds.mul hinv : Filter.Tendsto
        (fun n : ℕ => (2 : ℝ) * ((n : ℝ) + 5)⁻¹) Filter.atTop (nhds (2 * 0)))
  simpa [faceCutoffInnerRadius] using! tendsto_const_nhds.sub hfrac

/-- The canonical face-cutoff sequence used to trim smooth functions away from
the cube boundary while letting the inner cube fill the whole cube. -/
noncomputable def faceCutoff {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    QuantitativeCubeCutoff Q (faceCutoffInnerRadius n) (faceCutoffOuterRadius n) :=
  QuantitativeCubeCutoff.canonical Q
    (faceCutoffInnerRadius n) (faceCutoffOuterRadius n)
    (faceCutoffInnerRadius_pos n) (faceCutoffInnerRadius_lt_outer n)

/-- The open triadic cube is contained in the closed concentric cube with
relative radius `1`. -/
theorem openCubeSet_subset_scaledClosedCubeSet_one {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q ⊆ scaledClosedCubeSet Q 1 := by
  intro x hx i
  have hxball : x ∈ Metric.ball (cubeCenter Q) (cubeRadius Q) := by
    simpa [ball_cubeCenter_eq_openCubeSet Q] using hx
  have hcoord :
      ‖(x - cubeCenter Q) i‖ ≤ ‖x - cubeCenter Q‖ :=
    norm_le_pi_norm (x - cubeCenter Q) i
  calc
    |x i - cubeCenter Q i| = ‖(x - cubeCenter Q) i‖ := by
      simp [Real.norm_eq_abs]
    _ ≤ ‖x - cubeCenter Q‖ := hcoord
    _ = dist x (cubeCenter Q) := by simp [dist_eq_norm]
    _ ≤ 1 * cubeRadius Q := by
      simpa using le_of_lt (Metric.mem_ball.mp hxball)

/-- A fixed compactly supported cutoff that is identically `1` on the open
triadic cube. -/
noncomputable def faceCompactifyingCutoff {d : ℕ} (Q : TriadicCube d) :
    QuantitativeCubeCutoff Q 1 2 :=
  QuantitativeCubeCutoff.canonical Q 1 2 (by norm_num) (by norm_num)

theorem faceCompactifyingCutoff_eq_one_on_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    faceCompactifyingCutoff Q x = 1 :=
  (faceCompactifyingCutoff Q).eq_one_on_inner x
    (openCubeSet_subset_scaledClosedCubeSet_one Q hx)

private theorem tendsto_faceBoundaryLayer_volume_zero {d : ℕ}
    (Q : TriadicCube d) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.volume (cubeBoundaryLayer Q (2 / ((n : ℝ) + 5))))
      Filter.atTop (nhds 0) := by
  let t : ℕ → ℝ := fun n => 2 / ((n : ℝ) + 5)
  have ht_nonneg : ∀ n, 0 ≤ t n := by
    intro n
    dsimp [t]
    positivity
  have ht_half : ∀ n, t n ≤ (1 / 2 : ℝ) := by
    intro n
    have hden : 0 < (n : ℝ) + 5 := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [t]
    rw [div_le_iff₀ hden]
    nlinarith
  have hfinite :
      ∀ n, MeasureTheory.volume (cubeBoundaryLayer Q (t n)) ≠ ⊤ := by
    intro n
    exact MeasureTheory.measure_ne_top_of_subset
      (cubeBoundaryLayer_subset_cubeSet Q (t n)) (volume_cubeSet_lt_top Q).ne
  have htoReal :
      ∀ n,
        (MeasureTheory.volume (cubeBoundaryLayer Q (t n))).toReal =
          cubeVolume Q - ((1 - 2 * t n) * cubeScaleFactor Q) ^ d := by
    intro n
    exact volume_cubeBoundaryLayer_toReal_of_nonneg_le_half
      Q (ht_nonneg n) (ht_half n)
  have hdenCast :
      Filter.Tendsto (fun n : ℕ => (((n + 5 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 5)
  have hden :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) + 5)
        Filter.atTop Filter.atTop := by
    convert hdenCast using 1
    ext n
    simp [Nat.cast_add]
  have ht_tendsto : Filter.Tendsto t Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 5)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_const_nhds.mul hinv : Filter.Tendsto
        (fun n : ℕ => (2 : ℝ) * ((n : ℝ) + 5)⁻¹) Filter.atTop (nhds (2 * 0)))
  have hfactor :
      Filter.Tendsto (fun n : ℕ => 1 - 2 * t n) Filter.atTop (nhds 1) := by
    have htwo_t : Filter.Tendsto (fun n : ℕ => 2 * t n) Filter.atTop (nhds 0) := by
      simpa using ht_tendsto.const_mul 2
    simpa using tendsto_const_nhds.sub htwo_t
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ => (1 - 2 * t n) * cubeScaleFactor Q)
        Filter.atTop (nhds (cubeScaleFactor Q)) := by
    simpa using hfactor.mul tendsto_const_nhds
  have hreal_expr :
      Filter.Tendsto
        (fun n : ℕ => cubeVolume Q -
          ((1 - 2 * t n) * cubeScaleFactor Q) ^ d)
        Filter.atTop (nhds 0) := by
    have hpow := hscaled.pow d
    have hconst :
        Filter.Tendsto (fun _ : ℕ => cubeVolume Q)
          Filter.atTop (nhds (cubeVolume Q)) :=
      tendsto_const_nhds
    have hsub := hconst.sub hpow
    simpa [cubeVolume_eq_scaleFactor_pow] using hsub
  have hreal :
      Filter.Tendsto
        (fun n : ℕ => (MeasureTheory.volume (cubeBoundaryLayer Q (t n))).toReal)
        Filter.atTop (nhds 0) := by
    refine hreal_expr.congr' ?_
    filter_upwards with n
    exact (htoReal n).symm
  have hboundary :
      Filter.Tendsto
        (fun n : ℕ => MeasureTheory.volume (cubeBoundaryLayer Q (t n)))
        Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfinite).1 hreal
  simpa [t] using hboundary

theorem tendsto_volumeMeasureOn_openCubeSet_cubeCoordInnerCollar_faceCutoffInnerRadius
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ =>
        volumeMeasureOn (openCubeSet Q)
          (cubeCoordInnerCollar Q (faceCutoffInnerRadius n) i))
      Filter.atTop (nhds 0) := by
  have hboundary := tendsto_faceBoundaryLayer_volume_zero Q
  have hle :
      ∀ n : ℕ,
        volumeMeasureOn (openCubeSet Q)
            (cubeCoordInnerCollar Q (faceCutoffInnerRadius n) i) ≤
          MeasureTheory.volume (cubeBoundaryLayer Q (2 / ((n : ℝ) + 5))) := by
    intro n
    calc
      volumeMeasureOn (openCubeSet Q)
          (cubeCoordInnerCollar Q (faceCutoffInnerRadius n) i)
          ≤ MeasureTheory.volume
              (cubeBoundaryLayer Q (1 - faceCutoffInnerRadius n)) :=
            volumeMeasureOn_openCubeSet_cubeCoordInnerCollar_le_cubeBoundaryLayer
              Q (faceCutoffInnerRadius_lt_one n) i
      _ = MeasureTheory.volume (cubeBoundaryLayer Q (2 / ((n : ℝ) + 5))) := by
            congr 1
            dsimp [faceCutoffInnerRadius]
            ring_nf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundary
    (fun _ => bot_le) hle

/-- The canonical face cutoff has vanishing derivative error along each
coordinate for smooth functions that vanish on the two corresponding faces. -/
theorem tendsto_eLpNorm_canonicalFun_coordDeriv_mul_of_face_zero_faceCutoffRadii
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (ψ : Vec d → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x : Vec d =>
            (fderiv ℝ
              (QuantitativeCubeCutoff.canonicalFun Q
                (faceCutoffInnerRadius n) (faceCutoffOuterRadius n)) x)
              (basisVec i) * ψ x)
          2 (volumeMeasureOn (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  exact
    tendsto_eLpNorm_canonicalFun_coordDeriv_mul_of_face_zero_of_collar_measure
      (U := openCubeSet Q) Q
      (ρ₁ := faceCutoffInnerRadius) (ρ₂ := faceCutoffOuterRadius)
      (L := L) (A := 2)
      faceCutoffInnerRadius_pos
      faceCutoffInnerRadius_lt_outer
      faceCutoffOuterRadius_le_one
      hL (by norm_num)
      faceCutoffInnerOuter_width_control
      i ψ hψ hbound hlower_zero hupper_zero
      (tendsto_volumeMeasureOn_openCubeSet_cubeCoordInnerCollar_faceCutoffInnerRadius Q i)

/-- Boundary-error form of the face cutoff theorem, stated for the packaged
`QuantitativeCubeCutoff` sequence. -/
theorem tendsto_eLpNorm_euclideanCoordDeriv_faceCutoff_mul_of_face_zero
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (ψ : Vec d → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x : Vec d =>
            euclideanCoordDeriv i (faceCutoff Q n : Vec d → ℝ) x * ψ x)
          2 (volumeMeasureOn (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  simpa [faceCutoff, euclideanCoordDeriv] using!
    tendsto_eLpNorm_canonicalFun_coordDeriv_mul_of_face_zero_faceCutoffRadii
      Q i ψ hL hψ hbound hlower_zero hupper_zero

/-- Product-rule convergence for the face-cutoff sequence.  For smooth compactly
supported functions vanishing on the two `i`-faces, multiplying by the canonical
inner cutoffs does not change the `i`th derivative in `L²(openCubeSet Q)`. -/
theorem tendsto_eLpNorm_euclideanCoordDeriv_faceCutoff_mul_sub_of_face_zero
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (ψ : Vec d → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x : Vec d =>
            euclideanCoordDeriv i (fun y => faceCutoff Q n y * ψ y) x -
              euclideanCoordDeriv i ψ x)
          2 (volumeMeasureOn (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  exact
    QuantitativeCubeCutoff.tendsto_eLpNorm_euclideanCoordDeriv_mul_sub_of_tendsto_inner_of_boundary_error
      (Q := Q) (ψ := ψ)
      (ρ₁ := faceCutoffInnerRadius) (ρ₂ := faceCutoffOuterRadius)
      (η := fun n => faceCutoff Q n)
      tendsto_faceCutoffInnerRadius_one hψ hψ_compact i
      (tendsto_eLpNorm_euclideanCoordDeriv_faceCutoff_mul_of_face_zero
        Q i ψ hL hψ hbound hlower_zero hupper_zero)

namespace H10Function

/-- A smooth compactly supported function on a cube whose trace vanishes on
every coordinate face belongs to the zero-trace `H¹₀` closure.  The approximants
are the canonical inner face cutoffs times the function. -/
noncomputable def ofContDiffFaceZeroOnOpenCubeSet
    {d : ℕ} (Q : TriadicCube d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeUpperFaceProjection Q i x) = 0) :
    H10Function (openCubeSet Q) := by
  let uH1 : H1Function (openCubeSet Q) :=
    H1Function.ofContDiff (isOpen_openCubeSet Q) (hψ.of_le (by simp)) hψ_compact
  let L : ℝ := Classical.choose
    (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ hψ_compact)
  have hL : 0 ≤ L :=
    (Classical.choose_spec
      (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ hψ_compact)).1
  have hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L :=
    (Classical.choose_spec
      (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ hψ_compact)).2
  refine
    { toH1Function := uH1
      approx := fun n x => faceCutoff Q n x * ψ x
      approx_smooth := ?_
      approx_hasCompactSupport := ?_
      approx_support_subset := ?_
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }
  · intro n
    exact (faceCutoff Q n).smooth.mul hψ
  · intro n
    simpa using! ((faceCutoff Q n).hasCompactSupport.mul_right :
      HasCompactSupport (fun x : Vec d => faceCutoff Q n x * ψ x))
  · intro n
    exact (tsupport_mul_subset_left
      (f := (faceCutoff Q n : Vec d → ℝ)) (g := ψ)).trans
        ((faceCutoff Q n).tsupport_subset_openCubeSet_of_nonneg_of_lt_one
          (faceCutoffOuterRadius_nonneg n) (faceCutoffOuterRadius_lt_one n))
  · have hψ_mem : MemScalarL2 (openCubeSet Q) ψ := by
      simpa [uH1, H1Function.ofContDiff, MemScalarL2, volumeMeasureOn] using
        uH1.memL2
    have htail :
        Filter.Tendsto
          (fun n : ℕ =>
            MeasureTheory.eLpNorm
              (fun x => ψ x - faceCutoff Q n x * ψ x) 2
              (volumeMeasureOn (openCubeSet Q)))
          Filter.atTop (nhds 0) :=
      QuantitativeCubeCutoff.tendsto_eLpNorm_sub_mul_of_tendsto_inner
        (Q := Q) (g := ψ)
        (ρ₁ := faceCutoffInnerRadius) (ρ₂ := faceCutoffOuterRadius)
        (η := fun n => faceCutoff Q n)
        tendsto_faceCutoffInnerRadius_one hψ_mem
    refine htail.congr' ?_
    filter_upwards with n
    have hfun :
        (fun x : Vec d => faceCutoff Q n x * ψ x - uH1.toFun x) =
          fun x : Vec d => -(ψ x - faceCutoff Q n x * ψ x) := by
      funext x
      simp [uH1, H1Function.ofContDiff]
    rw [hfun]
    change
      MeasureTheory.eLpNorm (fun x : Vec d => ψ x - faceCutoff Q n x * ψ x)
          2 (volumeMeasureOn (openCubeSet Q)) =
        MeasureTheory.eLpNorm (-(fun x : Vec d => ψ x - faceCutoff Q n x * ψ x))
          2 (volumeMeasureOn (openCubeSet Q))
    rw [MeasureTheory.eLpNorm_neg]
  · intro i
    have hgrad :=
      tendsto_eLpNorm_euclideanCoordDeriv_faceCutoff_mul_sub_of_face_zero
        Q i ψ hL hψ hψ_compact hbound (hlower_zero i) (hupper_zero i)
    simpa [uH1, H1Function.ofContDiff, euclideanCoordDeriv, volumeMeasureOn]
      using hgrad

@[simp] theorem ofContDiffFaceZeroOnOpenCubeSet_toFun
    {d : ℕ} (Q : TriadicCube d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeUpperFaceProjection Q i x) = 0) :
    (ofContDiffFaceZeroOnOpenCubeSet Q hψ hψ_compact hlower_zero hupper_zero).toH1Function.toFun =
      ψ :=
  by
    simp [ofContDiffFaceZeroOnOpenCubeSet, H1Function.ofContDiff]

@[simp] theorem ofContDiffFaceZeroOnOpenCubeSet_grad
    {d : ℕ} (Q : TriadicCube d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeUpperFaceProjection Q i x) = 0) :
    (ofContDiffFaceZeroOnOpenCubeSet Q hψ hψ_compact hlower_zero hupper_zero).toH1Function.grad =
      fun x i => (fderiv ℝ ψ x) (basisVec i) :=
  by
    simp [ofContDiffFaceZeroOnOpenCubeSet, H1Function.ofContDiff]

/-- A smooth function on a cube whose trace vanishes on every coordinate face
belongs to the zero-trace `H¹₀` closure.  The proof first multiplies by a fixed
smooth cutoff that is identically `1` on the cube, so no compact-support
hypothesis is needed on the original function. -/
noncomputable def ofContDiffFaceZeroOnOpenCubeSetNoCompact
    {d : ℕ} (Q : TriadicCube d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeUpperFaceProjection Q i x) = 0) :
    H10Function (openCubeSet Q) := by
  let χ : Vec d → ℝ := faceCompactifyingCutoff Q
  let ψc : Vec d → ℝ := fun x => χ x * ψ x
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψc := by
    simpa [ψc, χ] using (faceCompactifyingCutoff Q).smooth.mul hψ
  have hψc_compact : HasCompactSupport ψc := by
    simpa [ψc, χ] using!
      ((faceCompactifyingCutoff Q).hasCompactSupport.mul_right :
        HasCompactSupport (fun x : Vec d => faceCompactifyingCutoff Q x * ψ x))
  have hlower_zero_c : ∀ i : Fin d, ∀ x : Vec d,
      ψc (cubeLowerFaceProjection Q i x) = 0 := by
    intro i x
    simp [ψc, hlower_zero i x]
  have hupper_zero_c : ∀ i : Fin d, ∀ x : Vec d,
      ψc (cubeUpperFaceProjection Q i x) = 0 := by
    intro i x
    simp [ψc, hupper_zero i x]
  exact ofContDiffFaceZeroOnOpenCubeSet Q hψc hψc_compact
    hlower_zero_c hupper_zero_c

theorem ofContDiffFaceZeroOnOpenCubeSetNoCompact_toFun_ae
    {d : ℕ} (Q : TriadicCube d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      ψ (cubeUpperFaceProjection Q i x) = 0) :
    (ofContDiffFaceZeroOnOpenCubeSetNoCompact Q hψ hlower_zero hupper_zero).toH1Function.toFun
        =ᵐ[volumeMeasureOn (openCubeSet Q)] ψ := by
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  simp [ofContDiffFaceZeroOnOpenCubeSetNoCompact, faceCompactifyingCutoff_eq_one_on_openCubeSet Q hx]

end H10Function

end
end Homogenization
