/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepCollar
/-!
# Reversal of an endpoint-identified relative affine collar

Reflection in the interval coordinate exchanges the two horizontal boundaries.  To retain the
standard boundary convention `upper - lower`, all top-cell coefficients are negated.  This module
performs that construction at the level of explicit affine cells, quotient facets, pointwise
incidence, and endpoint-chain identification.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarReverse

open scoped BigOperators
open ExplicitAffineRelativeCollar
open EquivariantPrismVertexParameters
open RefinedAffineMap

variable {p N₀ N₁ M L : Nat}
variable {hp : Nat.Prime p}

/-- Reflection of the realization cylinder in its interval coordinate. -/
def reflectPoint (z : CylinderPoint p) : CylinderPoint p :=
  ⟨z.spatial, ⟨1 - z.time.1, by constructor <;> linarith [z.time.2.1, z.time.2.2]⟩⟩

@[simp] theorem reflectPoint_spatial (z : CylinderPoint p) :
    (reflectPoint z).spatial = z.spatial := rfl

@[simp] theorem reflectPoint_time (z : CylinderPoint p) :
    (reflectPoint z).time.1 = 1 - z.time.1 := rfl

@[simp] theorem reflectPoint_involutive (z : CylinderPoint p) :
    reflectPoint (reflectPoint z) = z := by
  obtain ⟨s, t, ht⟩ := z
  simp [reflectPoint]

/-- Reflection is injective. -/
theorem reflectPoint_injective : Function.Injective (@reflectPoint p) :=
  Function.Involutive.injective reflectPoint_involutive

@[simp] theorem reflectPoint_smul
    (g : PrimeSymmetry p) (z : CylinderPoint p) :
    reflectPoint (g • z) = g • reflectPoint z := rfl

/-- Reverse the affine cells and negate their oriented coefficients. -/
noncomputable abbrev reverseCells
    (C : RelativeAffineCellSystem hp N₀ N₁ M L) :
    RelativeAffineCellSystem hp N₁ N₀ M L where
  lower_le_common := C.upper_le_common
  upper_le_common := C.lower_le_common
  Cell := C.Cell
  cell_nonempty := C.cell_nonempty
  instCellFintype := C.instCellFintype
  instCellDecidableEq := C.instCellDecidableEq
  coefficient q := -C.coefficient q
  vertex q i := reflectPoint (C.vertex q i)
  chart q w := reflectPoint (C.chart q w)
  chart_vertex := by
    intro q i
    simp [C.chart_vertex]
  chart_spatial_affine := by
    intro q w c
    simpa [reflectPoint] using C.chart_spatial_affine q w c
  chart_time_affine := by
    intro q w
    simp only [reflectPoint_time]
    rw [C.chart_time_affine]
    have hw : ∑ i : Fin (p + 1), w i * (1 - (C.vertex q i).time.1) =
        (∑ i : Fin (p + 1), (w : Fin (p + 1) → Real) i) -
          ∑ i : Fin (p + 1), w i * (C.vertex q i).time.1 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hw, stdSimplex.sum_eq_one]
  chart_injective := by
    intro q x y h
    apply C.chart_injective q
    exact reflectPoint_injective h
  vertex_injective := by
    intro q i j h
    apply C.vertex_injective q
    exact reflectPoint_injective h
  vertex_orbit_injective := by
    intro q g i j h
    apply C.vertex_orbit_injective q g i j
    apply reflectPoint_injective
    simpa using h

/-- Reversal carries original facet signatures to reflected signatures. -/
theorem reverse_facetSignature
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (o : C.FacetOccurrence) :
    (reverseCells C).facetSignature o =
      fun i => reflectPoint (C.facetSignature o i) := rfl

/-- The facet orbit relations before and after reflection coincide. -/
theorem reverse_facetSetoid_iff
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a b : C.FacetOccurrence) :
    (reverseCells C).facetSetoid.r a b ↔ C.facetSetoid.r a b := by
  constructor
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    funext i
    have hi := congrFun h i
    apply reflectPoint_injective
    simpa [reverse_facetSignature] using hi
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    funext i
    simpa [reverse_facetSignature] using congrArg reflectPoint (congrFun h i)

/-- Canonical equivalence between reflected and original quotient facets. -/
noncomputable def facetEquiv
    (C : RelativeAffineCellSystem hp N₀ N₁ M L) :
    (reverseCells C).Facet ≃ C.Facet :=
  Quotient.congr (Equiv.refl _) (reverse_facetSetoid_iff C)

@[simp] theorem facetEquiv_facetClass
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (o : C.FacetOccurrence) :
    facetEquiv C ((reverseCells C).facetClass o) = C.facetClass o := rfl

/-- Reflection negates every pointwise facet incidence. -/
theorem reverse_facetIncidence
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : (reverseCells C).Facet) :
    (reverseCells C).facetIncidence s = -C.facetIncidence (facetEquiv C s) := by
  classical
  unfold RelativeAffineCellSystem.facetIncidence
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro o ho
  have heq : (reverseCells C).facetClass o = s ↔
      C.facetClass o = facetEquiv C s := by
    constructor <;> intro h
    · exact congrArg (facetEquiv C) h
    · apply (facetEquiv C).injective
      exact h
  simp only [heq]
  split_ifs <;> simp [reverseCells]

/-- Lower-horizontal reflected facets are precisely upper-horizontal original facets. -/
theorem reverse_isLower_iff_isUpper
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : (reverseCells C).Facet) :
    (reverseCells C).IsLowerFacet s ↔ C.IsUpperFacet (facetEquiv C s) := by
  refine Quotient.inductionOn s ?_
  intro o
  change (∀ i, 1 - (C.facetSignature o i).time.1 = 0) ↔
    ∀ i, (C.facetSignature o i).time.1 = 1
  constructor <;> intro h i
  · linarith [h i]
  · linarith [h i]

/-- Upper-horizontal reflected facets are precisely lower-horizontal original facets. -/
theorem reverse_isUpper_iff_isLower
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (s : (reverseCells C).Facet) :
    (reverseCells C).IsUpperFacet s ↔ C.IsLowerFacet (facetEquiv C s) := by
  refine Quotient.inductionOn s ?_
  intro o
  change (∀ i, 1 - (C.facetSignature o i).time.1 = 1) ↔
    ∀ i, (C.facetSignature o i).time.1 = 0
  constructor <;> intro h i
  · linarith [h i]
  · linarith [h i]

/-- Reverse a pointwise relative affine collar. -/
noncomputable def reverseCollar
    (C : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L) :
    FoxNeuwirthRelativeAffineCollar hp N₁ N₀ M L where
  cells := reverseCells C.cells
  lowerBoundaryCoefficient s := C.upperBoundaryCoefficient (facetEquiv C.cells s)
  upperBoundaryCoefficient s := C.lowerBoundaryCoefficient (facetEquiv C.cells s)
  lower_zero_of_not_lower := by
    intro s hs
    apply C.upper_zero_of_not_upper
    intro hu
    apply hs
    exact (reverse_isLower_iff_isUpper C.cells s).2 hu
  upper_zero_of_not_upper := by
    intro s hs
    apply C.lower_zero_of_not_lower
    intro hl
    apply hs
    exact (reverse_isUpper_iff_isLower C.cells s).2 hl
  incidence_eq_boundary := by
    intro s
    rw [reverse_facetIncidence, C.incidence_eq_boundary]
    ring

@[simp] theorem reverseCollar_cells
    (C : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L) :
    (reverseCollar C).cells = reverseCells C.cells := rfl

@[simp] theorem reflect_lowerCylinderPoint (x : Realization p) :
    reflectPoint (lowerCylinderPoint x) = upperCylinderPoint x := by
  simp [reflectPoint, lowerCylinderPoint, upperCylinderPoint]

@[simp] theorem reflect_upperCylinderPoint (x : Realization p) :
    reflectPoint (upperCylinderPoint x) = lowerCylinderPoint x := by
  simp [reflectPoint, lowerCylinderPoint, upperCylinderPoint]

/-- Reverse an endpoint-identified collar. -/
noncomputable def reverseEndpointCollar
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M L) :
    EndpointIdentifiedRelativeAffineCollar hp N₁ N₀ M L where
  toFoxNeuwirthRelativeAffineCollar := reverseCollar C.toFoxNeuwirthRelativeAffineCollar
  lowerFacet q := (facetEquiv C.cells).symm (C.upperFacet q)
  upperFacet q := (facetEquiv C.cells).symm (C.lowerFacet q)
  lowerFacet_isLower := by
    intro q
    apply (reverse_isLower_iff_isUpper C.cells _).2
    simp [C.upperFacet_isUpper]
  upperFacet_isUpper := by
    intro q
    apply (reverse_isUpper_iff_isLower C.cells _).2
    simp [C.lowerFacet_isLower]
  lowerFacet_exhaustive := by
    intro s hs
    have hu : C.cells.IsUpperFacet (facetEquiv C.cells s) :=
      (reverse_isLower_iff_isUpper C.cells s).1 hs
    obtain ⟨q, hq⟩ := C.upperFacet_exhaustive _ hu
    exact ⟨q, by apply (facetEquiv C.cells).injective; simpa using hq⟩
  upperFacet_exhaustive := by
    intro s hs
    have hl : C.cells.IsLowerFacet (facetEquiv C.cells s) :=
      (reverse_isUpper_iff_isLower C.cells s).1 hs
    obtain ⟨q, hq⟩ := C.lowerFacet_exhaustive _ hl
    exact ⟨q, by apply (facetEquiv C.cells).injective; simpa using hq⟩
  lowerBoundaryPairing_eq := by
    intro W
    have h := C.upperBoundaryPairing_eq
      (fun s => W ((facetEquiv C.cells).symm s))
    refine Eq.trans ?_ h
    refine Fintype.sum_equiv (facetEquiv C.cells) _ _ ?_
    intro s
    simp [reverseCollar]
  upperBoundaryPairing_eq := by
    intro W
    have h := C.lowerBoundaryPairing_eq
      (fun s => W ((facetEquiv C.cells).symm s))
    refine Eq.trans ?_ h
    refine Fintype.sum_equiv (facetEquiv C.cells) _ _ ?_
    intro s
    simp [reverseCollar]
  lowerFacetOccurrenceVertex_eq := by
    intro q o ho
    have ho' : C.cells.facetClass o = C.upperFacet q := by
      have := congrArg (facetEquiv C.cells) ho
      simp only [Equiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg⟩ := C.upperFacetOccurrenceVertex_eq q o ho'
    refine ⟨g, ?_⟩
    intro i
    change reflectPoint (C.cells.facetSignature o i) = _
    simpa only [reflectPoint_smul, reflect_upperCylinderPoint, reflect_lowerCylinderPoint] using
      congrArg reflectPoint (hg i)
  upperFacetOccurrenceVertex_eq := by
    intro q o ho
    have ho' : C.cells.facetClass o = C.lowerFacet q := by
      have := congrArg (facetEquiv C.cells) ho
      simp only [Equiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg⟩ := C.lowerFacetOccurrenceVertex_eq q o ho'
    refine ⟨g, ?_⟩
    intro i
    change reflectPoint (C.cells.facetSignature o i) = _
    simpa only [reflectPoint_smul, reflect_upperCylinderPoint, reflect_lowerCylinderPoint] using
      congrArg reflectPoint (hg i)

end ExplicitAffineRelativeCollarReverse
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
