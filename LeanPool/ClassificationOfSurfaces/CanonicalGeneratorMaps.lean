/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.CanonicalCoordinates

/-!
# Generator maps for the canonical Eval representatives

This file upgrades the explicit carrier-coordinate comparisons to maps between the full raw
generator relations.  Together with the reverse maps from the trusted Eval constructors, these
maps identify the generated equivalence relations and descend the one-face carrier homeomorphisms
to the canonical quotient spaces.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces.NormalForm

open Complex
open SurfaceCellComplex

/-- Every orientable polygon generator maps into the trusted equivalence closure. -/
theorem orientableGenerator_to_eqvGen
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid)) x y) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n) x)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n) y) := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_orientable_polygonalIdentifications_iff hvalid] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨i, rfl | rfl⟩ | ⟨j, rfl | rfl⟩
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
              (unitInterval.symm t)))
        exact orientableCarrier_handle_a_eqvGen (n := n) i t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 2) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_handle_a_eqvGen (n := n) i (unitInterval.symm t))
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
              (unitInterval.symm t)))
        exact orientableCarrier_handle_b_eqvGen (n := n) i t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 3) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableHandlePosition p n i 1)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_handle_b_eqvGen (n := n) i (unitInterval.symm t))
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
              (unitInterval.symm t)))
        exact orientableCarrier_boundary_c_eqvGen (p := p) j t
      · change Relation.EqvGen (OrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2) t))
          (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
            (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (orientableCarrier_boundary_c_eqvGen (p := p) j (unitInterval.symm t))

/-- Every nonorientable polygon generator maps into the trusted equivalence closure. -/
theorem nonOrientableGenerator_to_eqvGen
    {p n : ℕ} (hp : 1 ≤ p)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy :
      PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp)) x y) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n) x)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n) y) := by
  cases hxy with
  | glue identification hidentification t =>
      rw [mem_nonOrientable_polygonalIdentifications_iff hp] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨j, rfl | rfl⟩
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 0) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 1) t))
        exact nonOrientableCarrier_crosscap_a_eqvGen (n := n) i t
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 1) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableCrosscapPosition p n i 0) t))
        exact Relation.EqvGen.symm _ _
          (nonOrientableCarrier_crosscap_a_eqvGen (n := n) i t)
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 0) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 2)
              (unitInterval.symm t)))
        exact nonOrientableCarrier_boundary_c_eqvGen (p := p) j t
      · change Relation.EqvGen (NonOrientableRel p n)
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 2) t))
          (oneFacePolygonalPreRealizationHomeomorph
            (nonOrientableBoundaryWord p n)
            (nonOrientableOccurrencePoint p n
              (nonOrientableBoundaryPosition p n j 0)
              (unitInterval.symm t)))
        simpa using Relation.EqvGen.symm _ _
          (nonOrientableCarrier_boundary_c_eqvGen
            (p := p) j (unitInterval.symm t))

/-- Every trusted orientable generator maps back into the polygonal equivalence closure. -/
theorem orientableRel_to_polygonEqvGen
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    {x y : ClosedUnitDisc} (hxy : OrientableRel p n x y) :
    Relation.EqvGen
      (PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid)))
      ((oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)).symm x)
      ((oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)).symm y) := by
  cases hxy with
  | a t i =>
      rw [← orientableCarrier_handle_a_pos i t,
        ← orientableCarrier_handle_a_neg i t]
      simp only [Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (orientableHandleAIdentification (n := n) i)
          (orientableHandleAIdentification_mem (n := n) hvalid i) t)
  | b t i =>
      rw [← orientableCarrier_handle_b_pos i t,
        ← orientableCarrier_handle_b_neg i t]
      simp only [Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (orientableHandleBIdentification (n := n) i)
          (orientableHandleBIdentification_mem (n := n) hvalid i) t)
  | c t i =>
      have hsource :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (orientableBoundaryWord p n)
              (orientableOccurrencePoint p n
                (orientableBoundaryPosition p n (Fin.rev i) 2)
                (unitInterval.symm t)) := by
        simpa using
          orientableBoundary_trustedSource_eq_carrier_c_neg
            (p := p) (Fin.rev i) t
      have htarget :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (orientableBoundaryWord p n)
              (orientableOccurrencePoint p n
                (orientableBoundaryPosition p n (Fin.rev i) 0) t) := by
        simpa using
          orientableBoundary_trustedTarget_eq_carrier_c_pos
            (p := p) (Fin.rev i) t
      rw [hsource, htarget]
      simp only [Homeomorph.symm_apply_apply]
      change Relation.EqvGen
        (PolygonGluing.Generator
          ((orientableCellComplex p n).polygonalIdentifications
            (orientableCellComplex_occurrencePairingValid hvalid)))
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n (Fin.rev i) 2)
          (unitInterval.symm t))
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n (Fin.rev i) 0) t)
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (PolygonGluing.Generator.glue
            (orientableBoundaryIdentification (p := p) (Fin.rev i))
            (orientableBoundaryIdentification_mem
              (p := p) hvalid (Fin.rev i)) t))

/-- Every trusted nonorientable generator maps back into the polygonal equivalence closure. -/
theorem nonOrientableRel_to_polygonEqvGen
    {p n : ℕ} (hp : 1 ≤ p)
    {x y : ClosedUnitDisc} (hxy : NonOrientableRel p n x y) :
    Relation.EqvGen
      (PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp)))
      ((oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)).symm x)
      ((oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)).symm y) := by
  cases hxy with
  | a t i =>
      rw [← nonOrientableCarrier_crosscap_a_first i t,
        ← nonOrientableCarrier_crosscap_a_second i t]
      simp only [Homeomorph.symm_apply_apply]
      exact Relation.EqvGen.rel _ _
        (PolygonGluing.Generator.glue
          (nonOrientableCrosscapIdentification (n := n) i)
          (nonOrientableCrosscapIdentification_mem (n := n) hp i) t)
  | c t i =>
      have hsource :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (nonOrientableBoundaryWord p n)
              (nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n (Fin.rev i) 2)
                (unitInterval.symm t)) := by
        simpa using
          nonOrientableBoundary_trustedSource_eq_carrier_c_neg
            (p := p) (Fin.rev i) t
      have htarget :
          ClosedUnitDisc.bdyPtOfReal
              (-(3 * (i : ℝ) + 3 - (t : ℝ)) / (2 * p + 3 * n)) =
            oneFacePolygonalPreRealizationHomeomorph
              (nonOrientableBoundaryWord p n)
              (nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n (Fin.rev i) 0) t) := by
        simpa using
          nonOrientableBoundary_trustedTarget_eq_carrier_c_pos
            (p := p) (Fin.rev i) t
      rw [hsource, htarget]
      simp only [Homeomorph.symm_apply_apply]
      change Relation.EqvGen
        (PolygonGluing.Generator
          ((nonOrientableCellComplex p n).polygonalIdentifications
            (nonOrientableCellComplex_occurrencePairingValid hp)))
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n (Fin.rev i) 2)
          (unitInterval.symm t))
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n (Fin.rev i) 0) t)
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (PolygonGluing.Generator.glue
            (nonOrientableBoundaryIdentification (p := p) (Fin.rev i))
            (nonOrientableBoundaryIdentification_mem
              (p := p) hp (Fin.rev i)) t))

/-- The canonical orientable polygonal realization is the trusted Eval quotient. -/
noncomputable def orientablePolygonalRealizationHomeomorph
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    (orientableCellComplex p n).PolygonalRealization
        (orientableCellComplex_occurrencePairingValid hvalid) ≃ₜ
      Quot (OrientableRel p n) :=
  eqvGenQuotientCongrRawOfGeneratorMaps
    (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n))
    (fun _ _ hxy ↦ orientableGenerator_to_eqvGen hvalid hxy)
    (fun _ _ hxy ↦ orientableRel_to_polygonEqvGen hvalid hxy)

/-- The canonical nonorientable polygonal realization is the trusted Eval quotient. -/
noncomputable def nonOrientablePolygonalRealizationHomeomorph
    {p n : ℕ} (hp : 1 ≤ p) :
    (nonOrientableCellComplex p n).PolygonalRealization
        (nonOrientableCellComplex_occurrencePairingValid hp) ≃ₜ
      Quot (NonOrientableRel p n) :=
  eqvGenQuotientCongrRawOfGeneratorMaps
    (oneFacePolygonalPreRealizationHomeomorph
      (nonOrientableBoundaryWord p n))
    (fun _ _ hxy ↦ nonOrientableGenerator_to_eqvGen hp hxy)
    (fun _ _ hxy ↦ nonOrientableRel_to_polygonEqvGen hp hxy)

end LeanEval.Topology.ClassificationOfSurfaces.NormalForm
