/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Euclidean cross-sections inside an affine subspace

This file contains one temporary support theorem adapted from mathlib PR #37910 by Weiyi Wang:

https://github.com/leanprover-community/mathlib4/pull/37910

The theorem extends the existing full-dimensional Hausdorff-measure slicing formula to a set
contained in a lower-dimensional affine subspace.  This is the form needed for the standard
simplex, whose affine hull is a hyperplane in its ambient coordinate space.

TODO: If PR #37910 is merged into Mathlib, remove this file and replace uses of
`euclideanHausdorffMeasure_eq_lintegral_of_subset_affineSubspace` by the upstream theorem
`EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral'`.
-/

open MeasureTheory Measure Module Submodule AffineSubspace
open scoped ENNReal NNReal

public noncomputable section

namespace EuclideanGeometry

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]

/-- Hausdorff measure of a measurable set contained in an affine subspace, expressed as the
integral of its perpendicular cross-sections along a line in that subspace.

This proof is adapted from `EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral'` in
mathlib PR #37910. -/
theorem euclideanHausdorffMeasure_eq_lintegral_of_subset_affineSubspace
    (p : P) {v : V} (hv : v ≠ 0) {t : Set P} (ht : MeasurableSet t)
    {s : AffineSubspace ℝ P} (hvs : v ∈ s.direction) (hts : t ⊆ s)
    [FiniteDimensional ℝ s.direction] :
    μHE[finrank ℝ s.direction] t = ‖v‖ₑ * ∫⁻ (x : ℝ),
      μHE[finrank ℝ s.direction - 1]
        (t ∩ AffineSubspace.mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ) := by
  open AffineSubspace in
  by_cases! hs : s = ⊥
  · simp_all
  have : Nonempty s := (s.nonempty_iff_ne_bot.mpr hs).to_subtype
  let v' : s.direction := ⟨v, hvs⟩
  convert EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral
    (EuclideanGeometry.orthogonalProjection s p) (show v' ≠ 0 by simpa [v'] using hv)
      (ht.preimage (s.subtypeA.continuous.measurable : Measurable s.subtypeA)) with x
  · rw [← s.euclideanHausdorffMeasure_coe_image, coe_subtypeA,
      Set.image_preimage_eq_of_subset (by simpa using hts)]
  · rfl
  · have h1 : x • v +ᵥ (EuclideanGeometry.orthogonalProjection s p).val ∈
        mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ := by
      rw [mem_mk', vadd_vsub_vadd_cancel_left]
      refine SetLike.mem_of_subset ?_
        (EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal s _)
      exact Submodule.orthogonal_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hvs)
    have h2 : x • v +ᵥ (EuclideanGeometry.orthogonalProjection s p).val ∈ s :=
      vadd_mem_of_mem_direction (Submodule.smul_mem _ _ hvs)
        (EuclideanGeometry.orthogonalProjection s p).prop
    have h : (mk' (x • v' +ᵥ EuclideanGeometry.orthogonalProjection s p)
        (ℝ ∙ v')ᗮ).map s.subtype =
        mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ ⊓ s := by
      rw [map_mk']
      apply ext_of_direction_eq
      · ext u
        simp [direction_inf_of_mem h1 h2, v',
          Submodule.mem_orthogonal_singleton_iff_inner_right]
      · exact ⟨x • v +ᵥ (EuclideanGeometry.orthogonalProjection s p).val,
          self_mem_mk' _ _, h1, h2⟩
    have h : Subtype.val ''
        (mk' (x • v' +ᵥ EuclideanGeometry.orthogonalProjection s p)
          (ℝ ∙ v')ᗮ : Set s) =
        (mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ : Set P) ∩ (s : Set P) := by
      calc
        Subtype.val ''
            (mk' (x • v' +ᵥ EuclideanGeometry.orthogonalProjection s p)
              (ℝ ∙ v')ᗮ : Set s) =
            s.subtype ''
              (mk' (x • v' +ᵥ EuclideanGeometry.orthogonalProjection s p)
                (ℝ ∙ v')ᗮ : Set s) := by
              ext y
              constructor <;> rintro ⟨z, hz, rfl⟩ <;> exact ⟨z, hz, rfl⟩
        _ = (↑((mk' (x • v' +ᵥ EuclideanGeometry.orthogonalProjection s p)
              (ℝ ∙ v')ᗮ).map s.subtype) : Set P) :=
            (AffineSubspace.coe_map s.subtype _).symm
        _ = (↑(mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ ⊓ s) : Set P) :=
            congrArg (fun q : AffineSubspace ℝ P => (q : Set P)) h
        _ = (mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ : Set P) ∩ (s : Set P) :=
            AffineSubspace.coe_inf _ _
    rw [← s.euclideanHausdorffMeasure_coe_image, Set.image_inter Subtype.val_injective,
      coe_subtypeA, Set.image_preimage_eq_of_subset (by simpa using hts), h,
      ← Set.inter_assoc, Set.inter_right_comm, Set.inter_eq_left.mpr hts]

end EuclideanGeometry
