/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollar
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGlobalCancellation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RegularApproximationStability
import Mathlib.LinearAlgebra.Matrix.Reindex
/-!
# Finite Stokes theorem for explicit relative affine collars

This module proves the local-to-global cancellation theorem for the abstract finite affine-cell
system introduced in `ExplicitAffineRelativeCollar`.  It no longer relies on the standard product
prism or on a common endpoint subdivision level.

For a compatible global vertex assignment, the unsigned positive-ray index of a local facet
depends only on its ordered geometric facet class.  Summing the local affine boundary identity over
all top cells and regrouping by geometric facets gives the collar boundary pairing.  The incidence
formula of `FoxNeuwirthRelativeAffineCollar` then implies equality of the lower and upper horizontal
contributions.

Endpoint identification with the two refined Fox--Neuwirth counts is deliberately separated from
this finite Stokes theorem.  It requires the boundary assignment to equal the two supplied stable
endpoint maps on all frozen horizontal vertices.
-/

namespace NRR

open scoped BigOperators
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismGlobalCancellation
open Parameters
open Polynomials

variable {p : Nat}
variable {N₀ N₁ M L : Nat}

namespace FoxNeuwirthRelativeAffineCollar

variable (hp : Nat.Prime p)
variable (C : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L)

/-- Equal ordered quotient-facet classes carry ordered local output values that differ by one
simultaneous prime relabelling.  This is the correct representative-independence statement for the
prime-orbit facet quotient. -/
theorem facetValue_eq_primeSmul_of_facetClass_eq
    (a : Assignment hp C.cells)
    {o o' : C.cells.FacetOccurrence}
    (h : C.cells.facetClass o = C.cells.facetClass o') :
    ∃ g : PrimeSymmetry p, ∀ i : Fin p,
      facetValue (localVertexMap hp C.cells a o'.1) o'.2 i =
        g • facetValue (localVertexMap hp C.cells a o.1) o.2 i := by
  rcases Quotient.exact h with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro i
  let s : C.cells.VertexSlot := (o.1, o.2.succAbove i)
  let t : C.cells.VertexSlot := (o'.1, o'.2.succAbove i)
  have hpoint : g • C.cells.slotPoint s = C.cells.slotPoint t := by
    change g • C.cells.vertex o.1 (o.2.succAbove i) =
      C.cells.vertex o'.1 (o'.2.succAbove i)
    exact congrFun hg i
  have hvertex : g • sampleVertex hp C.cells s = sampleVertex hp C.cells t := by
    apply Quotient.sound
    change coverPoint hp C.cells (g, s) = coverPoint hp C.cells (1, t)
    simpa [coverPoint] using hpoint
  change vectorValue hp C.cells a (sampleVertex hp C.cells t) =
    g • vectorValue hp C.cells a (sampleVertex hp C.cells s)
  rw [← hvertex, vectorValue_smul]

/-- The unsigned positive-ray index of a local facet occurrence. -/
noncomputable def occurrenceUnsignedFacetIndex
    (a : Assignment hp C.cells) (o : C.cells.FacetOccurrence) : ZMod p :=
  unsignedFacetIndex hp (localVertexMap hp C.cells a o.1) o.2

/-- Equal geometric prime-orbit facet classes have equal unsigned positive-ray indices. -/
theorem occurrenceUnsignedFacetIndex_eq_of_facetClass_eq
    (a : Assignment hp C.cells)
    {o o' : C.cells.FacetOccurrence}
    (h : C.cells.facetClass o = C.cells.facetClass o') :
    C.occurrenceUnsignedFacetIndex hp a o =
      C.occurrenceUnsignedFacetIndex hp a o' := by
  rcases C.facetValue_eq_primeSmul_of_facetClass_eq hp a h with ⟨g, hg⟩
  exact (unsignedFacetIndex_eq_of_facetValue_eq_primeSmul hp g
    (localVertexMap hp C.cells a o.1)
    (localVertexMap hp C.cells a o'.1) o.2 o'.2 hg).symm

/-- Common unsigned positive-ray weight of one ordered geometric facet class. -/
noncomputable def facetWeight
    (a : Assignment hp C.cells) (s : C.cells.Facet) : ZMod p := by
  classical
  by_cases h : ∃ o : C.cells.FacetOccurrence, C.cells.facetClass o = s
  · exact C.occurrenceUnsignedFacetIndex hp a (Classical.choose h)
  · exact 0

/-- On a represented facet class, the common weight equals every occurrence index. -/
theorem facetWeight_facetClass
    (a : Assignment hp C.cells) (o : C.cells.FacetOccurrence) :
    C.facetWeight hp a (C.cells.facetClass o) =
      C.occurrenceUnsignedFacetIndex hp a o := by
  classical
  unfold facetWeight
  split_ifs with h
  · exact C.occurrenceUnsignedFacetIndex_eq_of_facetClass_eq hp a
      (Classical.choose_spec h)
  · exact (h ⟨o, rfl⟩).elim

/-- Expanded signed positive-ray boundary sum over all local facet occurrences. -/
noncomputable def globalSignedFacetSum
    (a : Assignment hp C.cells) : ZMod p :=
  ∑ o : C.cells.FacetOccurrence,
    C.cells.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
      C.facetWeight hp a (C.cells.facetClass o)

/-- Regroup the expanded occurrence sum by ordered geometric facet classes. -/
theorem globalSignedFacetSum_eq_facet_sum
    (a : Assignment hp C.cells) :
    C.globalSignedFacetSum hp a =
      ∑ s : C.cells.Facet,
        C.cells.facetIncidence s * C.facetWeight hp a s := by
  classical
  unfold globalSignedFacetSum RelativeAffineCellSystem.facetIncidence
  calc
    (∑ o : C.cells.FacetOccurrence,
        C.cells.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2 *
          C.facetWeight hp a (C.cells.facetClass o)) =
      ∑ o : C.cells.FacetOccurrence,
        ∑ s : C.cells.Facet,
          if C.cells.facetClass o = s then
            (C.cells.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2) *
              C.facetWeight hp a s
          else 0 := by
      apply Finset.sum_congr rfl
      intro o ho
      simp [eq_comm]
    _ = ∑ s : C.cells.Facet,
        ∑ o : C.cells.FacetOccurrence,
          if C.cells.facetClass o = s then
            (C.cells.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2) *
              C.facetWeight hp a s
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ s : C.cells.Facet,
        (∑ o : C.cells.FacetOccurrence,
          if C.cells.facetClass o = s then
            C.cells.coefficient o.1 * RelativeAffineCellSystem.alternatingSign o.2
          else 0) * C.facetWeight hp a s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro o ho
      split_ifs <;> ring

/-- The exact local hypothesis consumed by finite affine Stokes: on every top cell, the signed
positive-ray indices of the facets sum to zero. -/
def LocalPositiveRayStokes (a : Assignment hp C.cells) : Prop :=
  ∀ q : C.cells.Cell,
    ∑ k : Fin (p + 1), facetIndex hp (localVertexMap hp C.cells a q) k = 0

/-- Cellwise positive-ray Stokes makes the expanded global signed facet sum vanish. -/
theorem globalSignedFacetSum_eq_zero_of_localPositiveRayStokes
    (a : Assignment hp C.cells)
    (hlocal : C.LocalPositiveRayStokes hp a) :
    C.globalSignedFacetSum hp a = 0 := by
  classical
  unfold globalSignedFacetSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro q hq
  calc
    (∑ k : Fin (p + 1),
        C.cells.coefficient q * RelativeAffineCellSystem.alternatingSign k *
          C.facetWeight hp a (C.cells.facetClass (q, k))) =
      C.cells.coefficient q *
        ∑ k : Fin (p + 1), facetIndex hp (localVertexMap hp C.cells a q) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [C.facetWeight_facetClass hp a (q, k)]
      rw [facetIndex_eq_faceSign_mul_unsignedFacetIndex]
      simp [occurrenceUnsignedFacetIndex,
        RelativeAffineCellSystem.alternatingSign,
        SimplicialChain.faceSign]
      ring
    _ = 0 := by rw [hlocal q, mul_zero]

/-- Positive-ray-relative general position is sufficient for the exact cellwise Stokes
hypothesis. -/
theorem localPositiveRayStokes_of_positiveRayGeneralPosition
    (a : Assignment hp C.cells)
    (hgp : ∀ q : C.cells.Cell,
      PositiveRayGeneralPosition hp (localVertexMap hp C.cells a q)) :
    C.LocalPositiveRayStokes hp a := by
  intro q
  exact alternating_facetIndex_sum_eq_zero_of_positiveRayGeneralPosition hp
    (localVertexMap hp C.cells a q) (hgp q)

/-- Full local general position remains a sufficient way to obtain the exact local Stokes
hypothesis. -/
theorem localPositiveRayStokes_of_generalPosition
    (a : Assignment hp C.cells)
    (hgp : ∀ q : C.cells.Cell,
      GeneralPosition hp (localVertexMap hp C.cells a q)) :
    C.LocalPositiveRayStokes hp a :=
  C.localPositiveRayStokes_of_positiveRayGeneralPosition hp a
    (fun q => (hgp q).toPositiveRayGeneralPosition)

/-- Local general position makes the expanded signed facet sum vanish. -/
theorem globalSignedFacetSum_eq_zero
    (a : Assignment hp C.cells)
    (hgp : ∀ q : C.cells.Cell,
      GeneralPosition hp (localVertexMap hp C.cells a q)) :
    C.globalSignedFacetSum hp a = 0 :=
  C.globalSignedFacetSum_eq_zero_of_localPositiveRayStokes hp a
    (C.localPositiveRayStokes_of_generalPosition hp a hgp)

/-- Lower horizontal contribution of an explicit relative collar. -/
noncomputable def lowerHorizontalContribution
    (a : Assignment hp C.cells) : ZMod p :=
  ∑ s : C.cells.Facet,
    C.lowerBoundaryCoefficient s * C.facetWeight hp a s

/-- Upper horizontal contribution of an explicit relative collar. -/
noncomputable def upperHorizontalContribution
    (a : Assignment hp C.cells) : ZMod p :=
  ∑ s : C.cells.Facet,
    C.upperBoundaryCoefficient s * C.facetWeight hp a s

/-- The collar incidence formula rewrites the geometric-facet sum as upper minus lower. -/
theorem facet_sum_eq_upper_sub_lower
    (a : Assignment hp C.cells) :
    (∑ s : C.cells.Facet,
        C.cells.facetIncidence s * C.facetWeight hp a s) =
      C.upperHorizontalContribution hp a - C.lowerHorizontalContribution hp a := by
  classical
  unfold upperHorizontalContribution lowerHorizontalContribution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [C.incidence_eq_boundary s]
  ring

/-- Finite Stokes theorem from the exact cellwise positive-ray boundary identity. -/
theorem lowerHorizontalContribution_eq_upperHorizontalContribution_of_localPositiveRayStokes
    (a : Assignment hp C.cells)
    (hlocal : C.LocalPositiveRayStokes hp a) :
    C.lowerHorizontalContribution hp a = C.upperHorizontalContribution hp a := by
  have hzero :=
    C.globalSignedFacetSum_eq_zero_of_localPositiveRayStokes hp a hlocal
  rw [C.globalSignedFacetSum_eq_facet_sum hp a,
    C.facet_sum_eq_upper_sub_lower hp a] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Finite Stokes theorem for an explicit relative affine collar under full local general
position. -/
theorem lowerHorizontalContribution_eq_upperHorizontalContribution
    (a : Assignment hp C.cells)
    (hgp : ∀ q : C.cells.Cell,
      GeneralPosition hp (localVertexMap hp C.cells a q)) :
    C.lowerHorizontalContribution hp a = C.upperHorizontalContribution hp a :=
  C.lowerHorizontalContribution_eq_upperHorizontalContribution_of_localPositiveRayStokes hp a
    (C.localPositiveRayStokes_of_generalPosition hp a hgp)

end FoxNeuwirthRelativeAffineCollar

/-! ## Identification of fixed horizontal facets with refined endpoint indices -/

/-- Canonical identification of the `p` facet vertices with the vertex index type used by a
`(p - 1)`-simplex.  Keeping this transport named prevents repeated dependent casts. -/
def refinedVertexEquiv (hp : Nat.Prime p) :
    Fin p ≃ Fin (p - 1 + 1) :=
  augmentedRowEquiv hp

/-- The corresponding transported refined vertex index. -/
def refinedVertexIndex (hp : Nat.Prime p) (i : Fin p) :
    Fin (p - 1 + 1) :=
  refinedVertexEquiv hp i

theorem refinedVertexEquiv_symm_apply_index
    (hp : Nat.Prime p) (i : Fin p) :
    (refinedVertexEquiv hp).symm (refinedVertexIndex hp i) = i := by
  simp [refinedVertexIndex]

@[simp] theorem refinedVertexIndex_eq_facetCoordinateIndex
    (hp : Nat.Prime p) (i : Fin p) :
    refinedVertexIndex hp i = facetCoordinateIndex i := by
  apply Fin.ext
  rfl

/-- Reindex a finite sum from refined simplex vertices to facet vertices. -/
theorem sum_refinedVertexIndex
    (hp : Nat.Prime p) {R : Type} [AddCommMonoid R]
    (f : Fin (p - 1 + 1) → R) :
    (∑ i : Fin p, f (refinedVertexIndex hp i)) = ∑ j, f j := by
  simpa [refinedVertexIndex] using (refinedVertexEquiv hp).sum_comp f

/-- Matching ordered vertex values identify the affine facet determinant with the determinant of
 the corresponding refined Fox--Neuwirth top cell. -/
theorem facetDeterminant_eq_refinedDeterminant
    (hp : Nat.Prime p)
    (V : VertexMap p) (k : Fin (p + 1))
    (N : Nat) (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : RefinedAffineMap.TopCell hp N)
    (hvertex : ∀ i : Fin p,
      facetValue V k i = RefinedAffineMap.vertexValue hp N F q
        (refinedVertexIndex hp i)) :
    facetDeterminant hp V k = RefinedAffineMap.determinant hp N F q := by
  classical
  let e : Fin p ≃ Fin (p - 1 + 1) := refinedVertexEquiv hp
  have hmatrix :
      (Matrix.reindexLinearEquiv Real Real e e) (facetMatrix hp V k) =
        RefinedAffineMap.augmentedMatrix hp N F q := by
    ext r i
    refine Fin.lastCases ?_ (fun t => ?_) r
    · simp [e, refinedVertexEquiv, facetMatrix, RefinedAffineMap.augmentedMatrix]
    · simp [e, refinedVertexEquiv, refinedVertexIndex, facetMatrix,
        RefinedAffineMap.augmentedMatrix, RefinedAffineMap.deviationVertexValue,
        VertexMap.deviation, hvertex]
  unfold facetDeterminant RefinedAffineMap.determinant
  calc
    Matrix.det (facetMatrix hp V k) =
        Matrix.det ((Matrix.reindexLinearEquiv Real Real e e)
          (facetMatrix hp V k)) :=
      (Matrix.det_reindexLinearEquiv_self Real e (facetMatrix hp V k)).symm
    _ = Matrix.det (RefinedAffineMap.augmentedMatrix hp N F q) :=
      congrArg Matrix.det hmatrix

/-- A simultaneous prime relabelling of a regular endpoint facet still has nonzero
determinant. -/
theorem facetDeterminant_ne_zero_of_eq_refined_primeSmul
    (hp : Nat.Prime p)
    (V : VertexMap p) (k : Fin (p + 1))
    (N : Nat) (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : RefinedAffineMap.TopCell hp N)
    (g : PrimeSymmetry p)
    (hvertex : ∀ i : Fin p,
      facetValue V k i = g • RefinedAffineMap.vertexValue hp N F q (refinedVertexIndex hp i))
    (hregular : RefinedAffineMap.determinant hp N F q ≠ 0) :
    facetDeterminant hp V k ≠ 0 := by
  let W : VertexMap p := primeSmulVertexMap p g⁻¹ V
  have hWvertex : ∀ i : Fin p,
      facetValue W k i = RefinedAffineMap.vertexValue hp N F q (refinedVertexIndex hp i) := by
    intro i
    rw [show facetValue W k i = g⁻¹ • facetValue V k i by rfl, hvertex i]
    simp [refinedVertexIndex_eq_facetCoordinateIndex]
  have hWdet : facetDeterminant hp W k ≠ 0 := by
    rw [facetDeterminant_eq_refinedDeterminant hp W k N F q hWvertex]
    exact hregular
  exact (facetDeterminant_primeSmul_ne_zero_iff hp g⁻¹ V k).mp hWdet

/-- An ordered affine facet with the same vertex values and affine interpolation as a refined
Fox--Neuwirth top cell has exactly that cell's unsigned positive-ray index. -/
theorem unsignedFacetIndex_eq_refinedLocalIndex
    (hp : Nat.Prime p)
    (V : VertexMap p) (k : Fin (p + 1))
    (N : Nat) (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : RefinedAffineMap.TopCell hp N)
    (hvertex : ∀ i : Fin p,
      facetValue V k i = RefinedAffineMap.vertexValue hp N F q (refinedVertexIndex hp i))
    (haffine : ∀ w : StandardSimplex (p - 1),
      facetAffineValue V k w = RefinedAffineMap.value hp N F q w) :
    unsignedFacetIndex hp V k = RefinedAffineMap.localIndex hp N F q := by
  classical
  have hdet : facetDeterminant hp V k = RefinedAffineMap.determinant hp N F q :=
    facetDeterminant_eq_refinedDeterminant hp V k N F q hvertex
  have hinter : FacetHasPositiveRayIntersection hp V k ↔
      RefinedAffineMap.HasPositiveInteriorZero hp N F q := by
    constructor
    · rintro ⟨w, hw, hdev, hmean⟩
      refine ⟨w, hw, ?_, ?_⟩
      · intro r
        have hr := hdev r
        rw [haffine w] at hr
        exact sub_eq_zero.mp hr
      · simpa [VertexMap.mean, haffine w] using hmean
    · rintro ⟨w, hw, hdev, hmean⟩
      refine ⟨w, hw, ?_, ?_⟩
      · intro r
        rw [haffine w]
        exact sub_eq_zero.mpr (hdev r)
      · simpa [VertexMap.mean, haffine w] using hmean
  unfold unsignedFacetIndex RefinedAffineMap.localIndex
  by_cases hfacet : FacetHasPositiveRayIntersection hp V k
  · have hrefined : RefinedAffineMap.HasPositiveInteriorZero hp N F q :=
      hinter.mp hfacet
    rw [ite_eq_left hfacet, ite_eq_left hrefined, hdet]
  · have hrefined : ¬ RefinedAffineMap.HasPositiveInteriorZero hp N F q :=
      fun h => hfacet (hinter.mpr h)
    rw [ite_eq_right hfacet, ite_eq_right hrefined]

/-- Affine interpolation commutes with simultaneous prime relabelling of all vertex values. -/
private theorem facetAffineValue_primeSmul_local
    (p : Nat) (g : PrimeSymmetry p)
    (V : VertexMap p) (k : Fin (p + 1)) (w : StandardSimplex (p - 1)) :
    facetAffineValue (primeSmulVertexMap p g V) k w =
      g • facetAffineValue V k w := by
  funext r
  simp [facetAffineValue, facetValue, primeSmulVertexMap,
    PrimeSymmetry.smul_coordinate_apply]

/-- A simultaneous prime relabelling of all ordered endpoint values has the same unsigned
positive-ray index as the endpoint refined cell. -/
theorem unsignedFacetIndex_eq_refinedLocalIndex_primeSmul
    (hp : Nat.Prime p)
    (V : VertexMap p) (k : Fin (p + 1))
    (N : Nat) (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : RefinedAffineMap.TopCell hp N)
    (g : PrimeSymmetry p)
    (hvertex : ∀ i : Fin p,
      facetValue V k i = g • RefinedAffineMap.vertexValue hp N F q (refinedVertexIndex hp i))
    (haffine : ∀ w : StandardSimplex (p - 1),
      facetAffineValue V k w = g • RefinedAffineMap.value hp N F q w) :
    unsignedFacetIndex hp V k = RefinedAffineMap.localIndex hp N F q := by
  let W : VertexMap p := primeSmulVertexMap p g⁻¹ V
  have hWvertex : ∀ i : Fin p,
      facetValue W k i = RefinedAffineMap.vertexValue hp N F q (refinedVertexIndex hp i) := by
    intro i
    rw [show facetValue W k i = g⁻¹ • facetValue V k i by rfl, hvertex i]
    simp [refinedVertexIndex_eq_facetCoordinateIndex]
  have hWaffine : ∀ w : StandardSimplex (p - 1),
      facetAffineValue W k w = RefinedAffineMap.value hp N F q w := by
    intro w
    rw [facetAffineValue_primeSmul_local]
    rw [haffine w]
    simp []
  calc
    unsignedFacetIndex hp V k = unsignedFacetIndex hp W k := by
      exact (unsignedFacetIndex_primeSmul hp g⁻¹ V k).symm
    _ = RefinedAffineMap.localIndex hp N F q :=
      unsignedFacetIndex_eq_refinedLocalIndex hp W k N F q hWvertex hWaffine

/-- Exact boundary fixing for an endpoint-identified relative affine collar.  Every local
representative of a prescribed horizontal quotient facet agrees with the endpoint data after one
simultaneous prime relabelling. -/
structure EndpointBoundaryFixed
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (hp : Nat.Prime p)
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (a : Assignment hp C.cells) : Prop where
  lowerData : ∀ (q : RefinedAffineMap.TopCell hp A₀.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence),
    C.cells.facetClass o = C.lowerFacet q →
      ∃ g : PrimeSymmetry p,
        (∀ i : Fin p,
          facetValue (localVertexMap hp C.cells a o.1) o.2 i =
            g • RefinedAffineMap.vertexValue hp A₀.toRegularApproximation.level
              A₀.toRegularApproximation.map q (refinedVertexIndex hp i)) ∧
        (∀ w : StandardSimplex (p - 1),
          facetAffineValue (localVertexMap hp C.cells a o.1) o.2 w =
            g • RefinedAffineMap.value hp A₀.toRegularApproximation.level
              A₀.toRegularApproximation.map q w)
  upperData : ∀ (q : RefinedAffineMap.TopCell hp A₁.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence),
    C.cells.facetClass o = C.upperFacet q →
      ∃ g : PrimeSymmetry p,
        (∀ i : Fin p,
          facetValue (localVertexMap hp C.cells a o.1) o.2 i =
            g • RefinedAffineMap.vertexValue hp A₁.toRegularApproximation.level
              A₁.toRegularApproximation.map q (refinedVertexIndex hp i)) ∧
        (∀ w : StandardSimplex (p - 1),
          facetAffineValue (localVertexMap hp C.cells a o.1) o.2 w =
            g • RefinedAffineMap.value hp A₁.toRegularApproximation.level
              A₁.toRegularApproximation.map q w)

/-- Implementable horizontal boundary condition: every local vertex lying in the lower or upper
horizontal layer carries exactly the corresponding supplied endpoint value.  Compatibility across
shared vertices is already enforced by the global parameter quotient. -/
structure HorizontalVertexFixed
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (hp : Nat.Prime p)
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (a : Assignment hp C.cells) : Prop where
  lowerValue : ∀ s : C.cells.VertexSlot,
    (C.cells.slotPoint s).time.1 = 0 →
      vectorValue hp C.cells a (sampleVertex hp C.cells s) =
        A₀.toRegularApproximation.map (C.cells.slotPoint s).spatial
  upperValue : ∀ s : C.cells.VertexSlot,
    (C.cells.slotPoint s).time.1 = 1 →
      vectorValue hp C.cells a (sampleVertex hp C.cells s) =
        A₁.toRegularApproximation.map (C.cells.slotPoint s).spatial

namespace HorizontalVertexFixed

variable {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
variable (hp : Nat.Prime p)
variable (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
variable (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
variable {M L : Nat}
variable (C : EndpointIdentifiedRelativeAffineCollar hp
  A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
variable (a : Assignment hp C.cells)
variable (B : HorizontalVertexFixed hp A₀ A₁ C a)
include B

/-- Slotwise lower boundary fixing gives the ordered endpoint values up to the simultaneous prime
relabeling carried by the chosen quotient-facet representative. -/
theorem lowerFacetVertexValuePrimeSmul
    (q : RefinedAffineMap.TopCell hp A₀.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence)
    (ho : C.cells.facetClass o = C.lowerFacet q) :
    ∃ g : PrimeSymmetry p, ∀ i : Fin p,
      facetValue (localVertexMap hp C.cells a o.1) o.2 i =
        g • RefinedAffineMap.vertexValue hp A₀.toRegularApproximation.level
          A₀.toRegularApproximation.map q (refinedVertexIndex hp i) := by
  rcases C.lowerFacetOccurrenceVertex_eq q o ho with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro i
  let s : C.cells.VertexSlot := (o.1, o.2.succAbove i)
  have hpoint : C.cells.slotPoint s =
      g • lowerCylinderPoint (RefinedAffineMap.vertex hp
        A₀.toRegularApproximation.level q (refinedVertexIndex hp i)) := by
    simpa [s, RelativeAffineCellSystem.facetSignature,
      RelativeAffineCellSystem.slotPoint, refinedVertexIndex,
      refinedVertexEquiv, augmentedRowEquiv] using hg i
  change vectorValue hp C.cells a (sampleVertex hp C.cells s) =
    g • A₀.toRegularApproximation.map
      (RefinedAffineMap.vertex hp A₀.toRegularApproximation.level q (refinedVertexIndex hp i))
  calc
    vectorValue hp C.cells a (sampleVertex hp C.cells s) =
        A₀.toRegularApproximation.map (C.cells.slotPoint s).spatial :=
      HorizontalVertexFixed.lowerValue B s (by rw [hpoint]; simp [lowerCylinderPoint])
    _ = A₀.toRegularApproximation.map
        (g • RefinedAffineMap.vertex hp A₀.toRegularApproximation.level q (refinedVertexIndex hp i)) := by
      rw [hpoint]
      rfl
    _ = g • A₀.toRegularApproximation.map
        (RefinedAffineMap.vertex hp A₀.toRegularApproximation.level q (refinedVertexIndex hp i)) :=
      A₀.toRegularApproximation.equivariant g _

/-- Slotwise upper boundary fixing gives the ordered endpoint values up to the simultaneous prime
relabeling carried by the chosen quotient-facet representative. -/
theorem upperFacetVertexValuePrimeSmul
    (q : RefinedAffineMap.TopCell hp A₁.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence)
    (ho : C.cells.facetClass o = C.upperFacet q) :
    ∃ g : PrimeSymmetry p, ∀ i : Fin p,
      facetValue (localVertexMap hp C.cells a o.1) o.2 i =
        g • RefinedAffineMap.vertexValue hp A₁.toRegularApproximation.level
          A₁.toRegularApproximation.map q (refinedVertexIndex hp i) := by
  rcases C.upperFacetOccurrenceVertex_eq q o ho with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro i
  let s : C.cells.VertexSlot := (o.1, o.2.succAbove i)
  have hpoint : C.cells.slotPoint s =
      g • upperCylinderPoint (RefinedAffineMap.vertex hp
        A₁.toRegularApproximation.level q (refinedVertexIndex hp i)) := by
    simpa [s, RelativeAffineCellSystem.facetSignature,
      RelativeAffineCellSystem.slotPoint, refinedVertexIndex,
      refinedVertexEquiv, augmentedRowEquiv] using hg i
  change vectorValue hp C.cells a (sampleVertex hp C.cells s) =
    g • A₁.toRegularApproximation.map
      (RefinedAffineMap.vertex hp A₁.toRegularApproximation.level q (refinedVertexIndex hp i))
  calc
    vectorValue hp C.cells a (sampleVertex hp C.cells s) =
        A₁.toRegularApproximation.map (C.cells.slotPoint s).spatial :=
      HorizontalVertexFixed.upperValue B s (by rw [hpoint]; simp [upperCylinderPoint])
    _ = A₁.toRegularApproximation.map
        (g • RefinedAffineMap.vertex hp A₁.toRegularApproximation.level q (refinedVertexIndex hp i)) := by
      rw [hpoint]
      rfl
    _ = g • A₁.toRegularApproximation.map
        (RefinedAffineMap.vertex hp A₁.toRegularApproximation.level q (refinedVertexIndex hp i)) :=
      A₁.toRegularApproximation.equivariant g _

/-- Slotwise horizontal boundary fixing induces the quotient-representative endpoint condition. -/
theorem toEndpointBoundaryFixed : EndpointBoundaryFixed hp A₀ A₁ C a := by
  constructor
  · intro q o ho
    rcases HorizontalVertexFixed.lowerFacetVertexValuePrimeSmul
      hp A₀ A₁ C a B q o ho with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    intro w
    funext j
    let f : Fin (p - 1 + 1) → Real := fun i =>
      w i * RefinedAffineMap.vertexValue hp A₀.toRegularApproximation.level
        A₀.toRegularApproximation.map q i
          ((PrimeSymmetry.toPerm p g).symm j)
    simpa [facetAffineValue, RefinedAffineMap.value, hg,
      PrimeSymmetry.smul_coordinate_apply,
      refinedVertexIndex_eq_facetCoordinateIndex, f] using
        sum_refinedVertexIndex hp f
  · intro q o ho
    rcases HorizontalVertexFixed.upperFacetVertexValuePrimeSmul
      hp A₀ A₁ C a B q o ho with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    intro w
    funext j
    let f : Fin (p - 1 + 1) → Real := fun i =>
      w i * RefinedAffineMap.vertexValue hp A₁.toRegularApproximation.level
        A₁.toRegularApproximation.map q i
          ((PrimeSymmetry.toPerm p g).symm j)
    simpa [facetAffineValue, RefinedAffineMap.value, hg,
      PrimeSymmetry.smul_coordinate_apply,
      refinedVertexIndex_eq_facetCoordinateIndex, f] using
        sum_refinedVertexIndex hp f

end HorizontalVertexFixed

/-- Every movable perturbation of the endpoint-adjusted base assignment fixes the two supplied
endpoint approximations exactly on the horizontal vertices. -/
theorem horizontalVertexFixed_replaceMovable_endpointAdjustedAssignment
    (hp : Nat.Prime p)
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (move : MovableParameter hp C.cells → Real) :
    HorizontalVertexFixed hp A₀ A₁ C
      (replaceMovable hp C.cells
        (endpointAdjustedAssignment hp C.cells H
          A₀.toRegularApproximation A₁.toRegularApproximation)
        move) := by
  constructor
  · intro s hs
    rw [replaceMovable_horizontal_localValue hp C.cells
      (endpointAdjustedAssignment hp C.cells H
        A₀.toRegularApproximation A₁.toRegularApproximation)
      move s (Or.inl hs)]
    simpa using vectorValue_endpointAdjustedAssignment_lower hp C.cells H
      A₀.toRegularApproximation A₁.toRegularApproximation
      (sampleVertex hp C.cells s) (by simpa using hs)
  · intro s hs
    rw [replaceMovable_horizontal_localValue hp C.cells
      (endpointAdjustedAssignment hp C.cells H
        A₀.toRegularApproximation A₁.toRegularApproximation)
      move s (Or.inr hs)]
    simpa using vectorValue_endpointAdjustedAssignment_upper hp C.cells H
      A₀.toRegularApproximation A₁.toRegularApproximation
      (sampleVertex hp C.cells s) (by simpa using hs)

namespace EndpointBoundaryFixed

variable {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
variable (hp : Nat.Prime p)
variable (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
variable (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
variable {M L : Nat}
variable (C : EndpointIdentifiedRelativeAffineCollar hp
  A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
variable (a : Assignment hp C.cells)
variable (B : EndpointBoundaryFixed hp A₀ A₁ C a)
include B

/-- Weight of a lower horizontal facet is the refined local index of its prescribed endpoint cell. -/
theorem lower_facetWeight_eq_localIndex
    (q : RefinedAffineMap.TopCell hp A₀.toRegularApproximation.level) :
    C.toFoxNeuwirthRelativeAffineCollar.facetWeight hp a (C.lowerFacet q) =
      RefinedAffineMap.localIndex hp A₀.toRegularApproximation.level
        A₀.toRegularApproximation.map q := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (C.lowerFacet q)
  rw [← ho]
  change C.toFoxNeuwirthRelativeAffineCollar.facetWeight hp a
    (C.cells.facetClass o) = _
  rw [C.toFoxNeuwirthRelativeAffineCollar.facetWeight_facetClass hp a o]
  rcases B.lowerData q o ho with ⟨g, hvertex, haffine⟩
  exact unsignedFacetIndex_eq_refinedLocalIndex_primeSmul hp
    (localVertexMap hp C.cells a o.1) o.2
    A₀.toRegularApproximation.level A₀.toRegularApproximation.map q
    g hvertex haffine

/-- Weight of an upper horizontal facet is the refined local index of its prescribed endpoint cell. -/
theorem upper_facetWeight_eq_localIndex
    (q : RefinedAffineMap.TopCell hp A₁.toRegularApproximation.level) :
    C.toFoxNeuwirthRelativeAffineCollar.facetWeight hp a (C.upperFacet q) =
      RefinedAffineMap.localIndex hp A₁.toRegularApproximation.level
        A₁.toRegularApproximation.map q := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (C.upperFacet q)
  rw [← ho]
  change C.toFoxNeuwirthRelativeAffineCollar.facetWeight hp a
    (C.cells.facetClass o) = _
  rw [C.toFoxNeuwirthRelativeAffineCollar.facetWeight_facetClass hp a o]
  rcases B.upperData q o ho with ⟨g, hvertex, haffine⟩
  exact unsignedFacetIndex_eq_refinedLocalIndex_primeSmul hp
    (localVertexMap hp C.cells a o.1) o.2
    A₁.toRegularApproximation.level A₁.toRegularApproximation.map q
    g hvertex haffine

/-- The lower horizontal collar contribution is exactly the lower stable refined count. -/
theorem lowerHorizontalContribution_eq_zeroCount :
    C.toFoxNeuwirthRelativeAffineCollar.lowerHorizontalContribution hp a = A₀.zeroCount := by
  classical
  unfold FoxNeuwirthRelativeAffineCollar.lowerHorizontalContribution
  rw [C.lowerBoundaryPairing_eq]
  simp only [EndpointBoundaryFixed.lower_facetWeight_eq_localIndex
    hp A₀ A₁ C a B]
  rfl

/-- The upper horizontal collar contribution is exactly the upper stable refined count. -/
theorem upperHorizontalContribution_eq_zeroCount :
    C.toFoxNeuwirthRelativeAffineCollar.upperHorizontalContribution hp a = A₁.zeroCount := by
  classical
  unfold FoxNeuwirthRelativeAffineCollar.upperHorizontalContribution
  rw [C.upperBoundaryPairing_eq]
  simp only [EndpointBoundaryFixed.upper_facetWeight_eq_localIndex
    hp A₀ A₁ C a B]
  rfl

end EndpointBoundaryFixed

end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
