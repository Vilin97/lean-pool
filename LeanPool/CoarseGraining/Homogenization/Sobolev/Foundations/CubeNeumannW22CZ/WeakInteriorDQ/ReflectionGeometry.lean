/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Folding.Geometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Cube
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Reflection Geometry -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

/-- The centered cube of scale `m` is the one-third scaled open subcube of the
centered cube at the next larger scale. This is the basic geometry behind
using an all-face reflection block as an interior domain after translating to
the centered cube. -/
theorem scaledOpenCubeSet_originCube_succ_one_div_three
    (d : ℕ) (m : ℤ) :
    scaledOpenCubeSet (originCube d (m + 1)) (1 / 3 : ℝ) =
      openCubeSet (originCube d m) := by
  have hbound :
      (3 : ℝ)⁻¹ * (2⁻¹ * ((3 : ℝ) ^ m * 3)) = 2⁻¹ * (3 : ℝ) ^ m := by
    field_simp [show (3 : ℝ) ≠ 0 by norm_num]
  ext x
  simp [scaledOpenCubeSet, openCubeSet, cubeCenter, cubeRadius, originCube,
    cubeScaleFactor, abs_lt, sub_eq_add_neg, zpow_add₀,
    show (3 : ℝ) ≠ 0 by norm_num, hbound]

/-- The centered all-face reflection block of `originCube d m` lies inside the
centered cube at the next larger scale. The reverse inclusion only fails on
the internal reflecting faces. -/
theorem cubeFaceReflectionBlockSet_originCube_subset_openCubeSet_succ
    (d : ℕ) (m : ℤ) :
    cubeFaceReflectionBlockSet (originCube d m) ⊆
      openCubeSet (originCube d (m + 1)) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hleft :
      (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m + 1) =
        (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m - (3 : ℝ) ^ m := by
    rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
    ring
  have hright :
      (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) =
        (1 / 2 : ℝ) * (3 : ℝ) ^ m + (3 : ℝ) ^ m := by
    rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
    ring
  have hi :
      ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m - (3 : ℝ) ^ m < x i ∧
          x i < (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m) ∨
        ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < x i ∧
          x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∨
        ((1 / 2 : ℝ) * (3 : ℝ) ^ m < x i ∧
          x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m + (3 : ℝ) ^ m) := by
    simpa [cubeFaceReflectionBlockSet, cubeLowerFaceCoord,
      cubeUpperFaceCoord, originCube, cubeScaleFactor, sub_eq_add_neg]
      using hx i
  rcases hi with hLower | hMiddle | hUpper
  · constructor
    · rw [hleft]
      exact hLower.1
    · rw [hright]
      linarith
  · constructor
    · rw [hleft]
      linarith
    · rw [hright]
      linarith
  · constructor
    · rw [hleft]
      linarith
    · rw [hright]
      exact hUpper.2

/-- Almost every point avoids the two internal reflecting faces of the
centered reflection block in every coordinate. -/
theorem ae_forall_ne_originCube_reflection_faces
    (d : ℕ) (m : ℤ) :
    ∀ᵐ x : Vec d ∂MeasureTheory.volume,
      ∀ i : Fin d,
        x i ≠ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m ∧
          x i ≠ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  rw [Filter.eventually_all]
  intro i
  exact
    (MeasureTheory.Measure.ae_eval_ne
      (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      i ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m)).and
    (MeasureTheory.Measure.ae_eval_ne
      (μ := fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      i ((1 / 2 : ℝ) * (3 : ℝ) ^ m))

/-- The centered all-face reflection block is the next larger centered open
cube modulo the null union of internal reflecting faces. -/
theorem cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ
    (d : ℕ) (m : ℤ) :
    cubeFaceReflectionBlockSet (originCube d m) =ᵐ[MeasureTheory.volume]
      openCubeSet (originCube d (m + 1)) := by
  have hnoFaces := ae_forall_ne_originCube_reflection_faces d m
  filter_upwards [hnoFaces] with x hxnoFaces
  apply propext
  constructor
  · intro hxBlock
    exact cubeFaceReflectionBlockSet_originCube_subset_openCubeSet_succ d m hxBlock
  · intro hxParent
    change x ∈ openCubeSet (originCube d (m + 1)) at hxParent
    change x ∈ cubeFaceReflectionBlockSet (originCube d m)
    rw [mem_openCubeSet_originCube_iff] at hxParent
    intro i
    have hleft :
        -(2⁻¹ * (3 : ℝ) ^ (m + 1)) =
          (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m - (3 : ℝ) ^ m := by
      rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
      ring
    have hright :
        2⁻¹ * (3 : ℝ) ^ (m + 1) =
          (1 / 2 : ℝ) * (3 : ℝ) ^ m + (3 : ℝ) ^ m := by
      rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
      ring
    have hparentLeft :
        (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m - (3 : ℝ) ^ m < x i := by
      simpa [hleft] using (hxParent i).1
    have hparentRight :
        x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m + (3 : ℝ) ^ m := by
      simpa [hright] using (hxParent i).2
    have hblock :
        ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m - (3 : ℝ) ^ m < x i ∧
            x i < (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m) ∨
          ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < x i ∧
            x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) ∨
          ((1 / 2 : ℝ) * (3 : ℝ) ^ m < x i ∧
            x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m + (3 : ℝ) ^ m) := by
      by_cases hxLower : x i < (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m
      · exact Or.inl ⟨hparentLeft, hxLower⟩
      · have hLowerLt :
            (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < x i :=
          lt_of_le_of_ne (le_of_not_gt hxLower) (hxnoFaces i).1.symm
        by_cases hxUpper : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m
        · exact Or.inr <| Or.inl ⟨hLowerLt, hxUpper⟩
        · have hUpperLt :
              (1 / 2 : ℝ) * (3 : ℝ) ^ m < x i :=
            lt_of_le_of_ne (le_of_not_gt hxUpper) (hxnoFaces i).2.symm
          exact Or.inr <| Or.inr ⟨hUpperLt, hparentRight⟩
    simpa [cubeFaceReflectionBlockSet, cubeLowerFaceCoord,
      cubeUpperFaceCoord, originCube, cubeScaleFactor, sub_eq_add_neg]
      using hblock

/-- Set integrals over the next larger centered open cube can be evaluated on
the centered reflection block, since the two domains differ only by internal
faces. -/
theorem setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℤ) (f : Vec d → E) :
    ∫ x in openCubeSet (originCube d (m + 1)), f x ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet (originCube d m), f x ∂MeasureTheory.volume := by
  exact MeasureTheory.setIntegral_congr_set
    (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm

end

end Homogenization
