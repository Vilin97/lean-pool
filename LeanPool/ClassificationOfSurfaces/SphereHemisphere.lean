/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.SphereCarrierGeometry
import LeanPool.ClassificationOfSurfaces.Representatives

/-!
# Hemisphere maps for the two-monogon sphere

This file maps the two disk faces of `SurfaceCellComplex.sphere` to the upper and lower unit
hemispheres. The lower face uses complex conjugation, so the existing opposite-direction monogon
pairing has identical images.

The two possible directed sphere identifications are classified explicitly. The resulting
continuous facewise map on the polygonal pre-realization respects every raw gluing generator.
`SphereQuotientHomeomorph` descends this map and proves that it is a homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- The squared radius of a point in an indexed polygon cell is at most one. -/
theorem normSq_le_one {n : ℕ} (z : PolygonCell n) : Complex.normSq z.val ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq, sq_le_one_iff_abs_le_one, abs_norm]
  simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property

/-- The nonnegative height above the equatorial plane associated to a disk point. -/
noncomputable def hemisphereHeight {n : ℕ} (z : PolygonCell n) : ℝ :=
  Real.sqrt (1 - Complex.normSq z.val)

theorem hemisphereHeight_nonneg {n : ℕ} (z : PolygonCell n) :
    0 ≤ hemisphereHeight z :=
  Real.sqrt_nonneg _

@[simp]
theorem hemisphereHeight_sq {n : ℕ} (z : PolygonCell n) :
    hemisphereHeight z ^ 2 = 1 - Complex.normSq z.val := by
  exact Real.sq_sqrt (sub_nonneg.mpr (normSq_le_one z))

@[fun_prop]
theorem continuous_hemisphereHeight {n : ℕ} :
    Continuous (hemisphereHeight : PolygonCell n → ℝ) := by
  unfold hemisphereHeight
  exact Real.continuous_sqrt.comp
    (continuous_const.sub (Complex.continuous_normSq.comp PolygonCell.continuous_val))

/-- A disk point placed on the upper unit hemisphere. -/
noncomputable def upperHemisphereVector (z : PolygonCell 1) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[z.val.re, z.val.im, hemisphereHeight z]

/-- A conjugated disk point placed on the lower unit hemisphere. -/
noncomputable def lowerHemisphereVector (z : PolygonCell 1) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[(conj z.val).re, (conj z.val).im, -hemisphereHeight z]

theorem upperHemisphereVector_norm (z : PolygonCell 1) :
    ‖upperHemisphereVector z‖ = 1 := by
  have hsquare : ‖upperHemisphereVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [upperHemisphereVector, Fin.sum_univ_succ, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (upperHemisphereVector z)]

theorem lowerHemisphereVector_norm (z : PolygonCell 1) :
    ‖lowerHemisphereVector z‖ = 1 := by
  have hsquare : ‖lowerHemisphereVector z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [lowerHemisphereVector, Fin.sum_univ_succ, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (lowerHemisphereVector z)]

@[fun_prop]
theorem continuous_upperHemisphereVector : Continuous upperHemisphereVector := by
  unfold upperHemisphereVector
  fun_prop

@[fun_prop]
theorem continuous_lowerHemisphereVector : Continuous lowerHemisphereVector := by
  unfold lowerHemisphereVector
  fun_prop

/-- The continuous map from a monogon disk to the upper unit hemisphere. -/
noncomputable def upperHemisphere : C(PolygonCell 1, SphereRepresentative) where
  toFun z := ⟨upperHemisphereVector z, by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using upperHemisphereVector_norm z⟩
  continuous_toFun := continuous_upperHemisphereVector.subtype_mk fun z ↦ by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using upperHemisphereVector_norm z

/-- The continuous map from a monogon disk to the lower unit hemisphere. -/
noncomputable def lowerHemisphere : C(PolygonCell 1, SphereRepresentative) where
  toFun z := ⟨lowerHemisphereVector z, by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using lowerHemisphereVector_norm z⟩
  continuous_toFun := continuous_lowerHemisphereVector.subtype_mk fun z ↦ by
    rw [Metric.mem_sphere]
    simpa only [dist_eq_norm, sub_zero] using lowerHemisphereVector_norm z

@[simp]
theorem hemisphereHeight_side_monogon (t : unitInterval) :
    hemisphereHeight (side (0 : Fin 1) t) = 0 := by
  unfold hemisphereHeight
  have hnorm : ‖((side (0 : Fin 1) t : PolygonCell 1).val : ℂ)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (side_mem_sphere (0 : Fin 1) t)
  rw [Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- The positive-to-negative monogon pairing has the same upper and lower hemisphere image. -/
theorem upperHemisphere_side_eq_lowerHemisphere_side_symm (t : unitInterval) :
    upperHemisphere (side (0 : Fin 1) t) =
      lowerHemisphere (side (0 : Fin 1) (unitInterval.symm t)) := by
  apply Subtype.ext
  change upperHemisphereVector (side (0 : Fin 1) t) =
    lowerHemisphereVector (side (0 : Fin 1) (unitInterval.symm t))
  unfold upperHemisphereVector lowerHemisphereVector
  rw [conj_side_symm_monogon]
  ext i
  fin_cases i <;> simp

/-- The swapped monogon pairing has the same lower and upper hemisphere image. -/
theorem lowerHemisphere_side_eq_upperHemisphere_side_symm (t : unitInterval) :
    lowerHemisphere (side (0 : Fin 1) t) =
      upperHemisphere (side (0 : Fin 1) (unitInterval.symm t)) := by
  simpa only [unitInterval.symm_symm] using
    (upperHemisphere_side_eq_lowerHemisphere_side_symm (unitInterval.symm t)).symm

end PolygonCell

namespace SurfaceCellComplex

/-- Every boundary occurrence of the sphere is one of its two monogon occurrences. -/
theorem sphereBoundaryOccurrence_eq (occurrence : sphere.BoundaryOccurrence) :
    occurrence = spherePositiveOccurrence ∨ occurrence = sphereNegativeOccurrence := by
  rcases occurrence with ⟨face, index⟩
  cases face
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    exact Or.inl rfl
  · change Fin 1 at index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    exact Or.inr rfl

/-- The two directed forms of the unique sphere side pairing exhaust its identifications. -/
theorem mem_sphere_polygonalIdentifications_iff
    (identification :
      PolygonGluing.Identification sphere.Face sphere.faceBoundaryLength) :
    identification ∈ sphere.polygonalIdentifications sphere_occurrencePairingValid ↔
      identification = sphereBoundaryPairing.identification ∨
        identification = swapIdentification sphereBoundaryPairing.identification := by
  change identification ∈ Set.range BoundaryPairing.identification ↔ _
  constructor
  · rintro
      ⟨⟨source, target, hne, _hsource, _htarget, direction, hcompatible⟩, rfl⟩
    rcases sphereBoundaryOccurrence_eq source with rfl | rfl
    · rcases sphereBoundaryOccurrence_eq target with rfl | rfl
      · exact (hne rfl).elim
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inl rfl
    · rcases sphereBoundaryOccurrence_eq target with rfl | rfl
      · cases direction with
        | same => simp at hcompatible
        | opposite => exact Or.inr rfl
      · exact (hne rfl).elim
  · rintro (rfl | rfl)
    · exact sphereBoundaryPairing_mem
    · exact swapIdentification_mem_polygonalIdentifications
        sphere_occurrencePairingValid sphereBoundaryPairing_mem

/-- The continuous facewise map from the two monogon disks to the corresponding hemispheres. -/
noncomputable abbrev spherePreMap : C(sphere.PolygonalPreRealization, SphereRepresentative) where
  toFun
    | ⟨false, z⟩ => PolygonCell.upperHemisphere z
    | ⟨true, z⟩ => PolygonCell.lowerHemisphere z
  continuous_toFun := by
    apply continuous_sigma
    intro face
    cases face
    · exact PolygonCell.upperHemisphere.continuous
    · exact PolygonCell.lowerHemisphere.continuous

@[simp]
theorem spherePreMap_false (z : PolygonCell 1) :
    spherePreMap ⟨false, z⟩ = PolygonCell.upperHemisphere z :=
  rfl

@[simp]
theorem spherePreMap_true (z : PolygonCell 1) :
    spherePreMap ⟨true, z⟩ = PolygonCell.lowerHemisphere z :=
  rfl

/-- The facewise map respects the canonical directed sphere boundary pairing. -/
theorem spherePreMap_sphereBoundaryPairing (t : unitInterval) :
    spherePreMap (sphereBoundaryPairing.identification.source.point t) =
      spherePreMap
        (sphereBoundaryPairing.identification.target.point
          (sphereBoundaryPairing.identification.parameter t)) := by
  change PolygonCell.upperHemisphere (PolygonCell.side (0 : Fin 1) t) =
    PolygonCell.lowerHemisphere
      (PolygonCell.side (0 : Fin 1) (unitInterval.symm t))
  exact PolygonCell.upperHemisphere_side_eq_lowerHemisphere_side_symm t

/-- The facewise map respects the swapped directed sphere boundary pairing. -/
theorem spherePreMap_swapSphereBoundaryPairing (t : unitInterval) :
    spherePreMap
        ((swapIdentification sphereBoundaryPairing.identification).source.point t) =
      spherePreMap
        ((swapIdentification sphereBoundaryPairing.identification).target.point
          ((swapIdentification sphereBoundaryPairing.identification).parameter t)) := by
  change PolygonCell.lowerHemisphere (PolygonCell.side (0 : Fin 1) t) =
    PolygonCell.upperHemisphere
      (PolygonCell.side (0 : Fin 1) (unitInterval.symm t))
  exact PolygonCell.lowerHemisphere_side_eq_upperHemisphere_side_symm t

/-- The facewise sphere map identifies the endpoints of every raw polygon gluing generator. -/
theorem spherePreMap_eq_of_generator
    {x y : sphere.PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        (sphere.polygonalIdentifications sphere_occurrencePairingValid) x y) :
    spherePreMap x = spherePreMap y := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_sphere_polygonalIdentifications_iff] at hidentification
      rcases hidentification with rfl | rfl
      · exact spherePreMap_sphereBoundaryPairing t
      · exact spherePreMap_swapSphereBoundaryPairing t

end SurfaceCellComplex

end ClassificationOfSurfaces
end Topology
end LeanEval
