/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Topology.MetricSpace.Pseudo.Pi
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpointsCore
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpoints
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarStokes
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismSubdivisionMargin
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RegularApproximationStability
/-!
# Stable endpoint approximations and a boundary-relative prism perturbation

The unrestricted finite generic perturbation already produces transverse horizontal boundary data.
This module turns those finite boundary samples into genuine continuous equivariant coordinate maps.
The construction uses finite cardinal interpolation on the sampled horizontal vertices, followed by
averaging over the prime symmetry group.  It therefore has three properties simultaneously:

* it is continuous and prime-equivariant;
* it agrees exactly with the generic prism assignment at every horizontal sampled vertex;
* its refined affine samples inherit facet regularity and codimension-two avoidance from the prism.

The resulting lower and upper maps are `StableRegularApproximation`s at the exact horizontal
triangulation level.  The original generic prism assignment is then a relative perturbation with
those two boundary maps fixed by construction; no second generic perturbation is required.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantCoordinateHomotopy
open EquivariantPrismVertexParameters
open EquivariantPrismGenericPerturbation
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGlobalCancellation
open EquivariantPrismSubdivisionMargin
open EquivariantPrismHorizontalEndpointIdentification
open EndpointFaceRefinement
open RelativeCollarMiddlePrismEndpointsCore
open RefinedAffineMap
open SubdivisionPrismCharts

variable {p : Nat}

/-- The two horizontal components of the prism boundary. -/
inductive EndpointSide
  | lower
  | upper
  deriving DecidableEq

instance : Fintype EndpointSide where
  elems := {EndpointSide.lower, EndpointSide.upper}
  complete := by intro x; cases x <;> simp

namespace EndpointSide

/-- Numerical time attached to an endpoint side. -/
def time : EndpointSide → Real
  | lower => 0
  | upper => 1

@[simp] theorem time_lower : EndpointSide.lower.time = 0 := rfl
@[simp] theorem time_upper : EndpointSide.upper.time = 1 := rfl

/-- The endpoint map associated with a side. -/
noncomputable def zeroFreeMap
    (s : EndpointSide) {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp} : ZeroFreeMap hp :=
  match s with
  | lower => F₀
  | upper => F₁

end EndpointSide

/-- A sampled global prism vertex lies on a specified horizontal boundary. -/
def IsEndpointVertex
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (x : GlobalVertex hp N L) : Prop :=
  (globalPoint hp N L x).time.1 = s.time

noncomputable instance endpointVertexDecidable
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (x : GlobalVertex hp N L) : Decidable (IsEndpointVertex hp N L s x) :=
  Classical.propDecidable _

/-- Finite set of global sampled vertices on one horizontal component. -/
abbrev EndpointVertex
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide) :=
  {x : GlobalVertex hp N L // IsEndpointVertex hp N L s x}

noncomputable instance endpointVertexFintype
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide) :
    Fintype (EndpointVertex hp N L s) :=
  Fintype.ofFinite _

noncomputable instance endpointVertexDecidableEq
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide) :
    DecidableEq (EndpointVertex hp N L s) :=
  Classical.decEq _

/-- Spatial point represented by a horizontal sampled vertex. -/
noncomputable def endpointSpatialPoint
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (x : EndpointVertex hp N L s) : Realization p :=
  (globalPoint hp N L x.1).spatial

/-- On a fixed horizontal component, the spatial point determines the global sampled vertex. -/
theorem endpointSpatialPoint_injective
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide) :
    Function.Injective (endpointSpatialPoint hp N L s) := by
  classical
  intro x y hxy
  apply Subtype.ext
  have hglobal : Function.Injective (globalPoint hp N L) := by
    intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro u v huv
    exact Quotient.sound huv
  apply hglobal
  cases hx : globalPoint hp N L x.1 with
  | mk xs xt =>
    cases hy : globalPoint hp N L y.1 with
    | mk ys yt =>
      congr
      · simpa [endpointSpatialPoint, hx, hy] using hxy
      · have hxt : xt.1 = s.time := by
          simpa [IsEndpointVertex, hx] using x.property
        have hyt : yt.1 = s.time := by
          simpa [IsEndpointVertex, hy] using y.property
        apply Subtype.ext
        exact hxt.trans hyt.symm

/-- Cardinal interpolation weight for one horizontal sampled vertex. -/
noncomputable def endpointCardinalWeight
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (v : EndpointVertex hp N L s) (x : Realization p) : Real :=
  ∏ u ∈ (Finset.univ.erase v),
    dist x (endpointSpatialPoint hp N L s u) /
      dist (endpointSpatialPoint hp N L s v)
        (endpointSpatialPoint hp N L s u)

/-- A cardinal weight is one at its own sampled vertex. -/
@[simp] theorem endpointCardinalWeight_self
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (v : EndpointVertex hp N L s) :
    endpointCardinalWeight hp N L s v
      (endpointSpatialPoint hp N L s v) = 1 := by
  classical
  unfold endpointCardinalWeight
  apply Finset.prod_eq_one
  intro u hu
  have huv : u ≠ v := Finset.ne_of_mem_erase hu
  have hne : endpointSpatialPoint hp N L s v ≠
      endpointSpatialPoint hp N L s u := by
    intro h
    exact huv ((endpointSpatialPoint_injective hp N L s h).symm)
  simp [hne]

/-- A cardinal weight vanishes at every other sampled vertex. -/
@[simp] theorem endpointCardinalWeight_other
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    {u v : EndpointVertex hp N L s} (huv : u ≠ v) :
    endpointCardinalWeight hp N L s v
      (endpointSpatialPoint hp N L s u) = 0 := by
  classical
  unfold endpointCardinalWeight
  have hu : u ∈ Finset.univ.erase v := by simp [huv]
  apply Finset.prod_eq_zero hu
  simp

/-- Raw finite cardinal interpolation of the boundary samples. -/
noncomputable def rawEndpointInterpolant
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) (x : Realization p) : Fin p → Real :=
  ∑ v : EndpointVertex hp N L s,
    endpointCardinalWeight hp N L s v x •
      vectorValue hp N L a v.1

/-- The raw interpolant realizes every prescribed horizontal sample. -/
@[simp] theorem rawEndpointInterpolant_sample
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) (v : EndpointVertex hp N L s) :
    rawEndpointInterpolant hp N L s a
      (endpointSpatialPoint hp N L s v) =
        vectorValue hp N L a v.1 := by
  classical
  unfold rawEndpointInterpolant
  rw [Finset.sum_eq_single v]
  · simp
  · intro u hu huv
    simp [endpointCardinalWeight_other hp N L s huv.symm]
  · simp

/-- Each cardinal basis weight is continuous on the realization. -/
private theorem continuous_endpointCardinalWeight
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (v : EndpointVertex hp N L s) :
    Continuous (endpointCardinalWeight hp N L s v) := by
  unfold endpointCardinalWeight
  fun_prop

/-- The finite raw endpoint interpolant is continuous. -/
private theorem continuous_rawEndpointInterpolant
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) :
    Continuous (rawEndpointInterpolant hp N L s a) := by
  unfold rawEndpointInterpolant
  apply continuous_finsetSum
  intro v hv
  exact (continuous_endpointCardinalWeight hp N L s v).smul continuous_const

/-- Prime-symmetrization of the raw interpolant.  Averaging makes equivariance automatic while
preserving all already-equivariant sampled values. -/
noncomputable def endpointInterpolant
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) : ContinuousCoordinateMap p where
  toFun x :=
    ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) •
      ∑ g : PrimeSymmetry p,
        g⁻¹ • rawEndpointInterpolant hp N L s a (g • x)
  continuous_toFun := by
    have hsum : Continuous fun x : Realization p =>
        ∑ g : PrimeSymmetry p,
          g⁻¹ • rawEndpointInterpolant hp N L s a (g • x) := by
      apply continuous_finsetSum
      intro g hg
      have hraw : Continuous fun x : Realization p =>
          rawEndpointInterpolant hp N L s a (g • x) :=
        (continuous_rawEndpointInterpolant hp N L s a).comp
          (Realization.continuous_smul hp g)
      apply continuous_pi
      intro j
      change Continuous fun x =>
        rawEndpointInterpolant hp N L s a (g • x)
          ((PrimeSymmetry.toPerm p g⁻¹).symm j)
      exact (continuous_apply ((PrimeSymmetry.toPerm p g⁻¹).symm j)).comp hraw
    change Continuous fun x =>
      (Fintype.card (PrimeSymmetry p) : Real)⁻¹ •
        ∑ g : PrimeSymmetry p,
          g⁻¹ • rawEndpointInterpolant hp N L s a (g • x)
    have hconst : Continuous fun _ : Realization p =>
        (Fintype.card (PrimeSymmetry p) : Real)⁻¹ := continuous_const
    exact hconst.smul hsum

/-- The symmetrized endpoint interpolant is prime-equivariant. -/
theorem endpointInterpolant_equivariant
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) :
    IsEquivariantCoordinateMap hp (endpointInterpolant hp N L s a) := by
  classical
  intro h x
  change
    ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) •
        ∑ g : PrimeSymmetry p,
          g⁻¹ • rawEndpointInterpolant hp N L s a (g • (h • x)) =
      h • (((Fintype.card (PrimeSymmetry p) : Real)⁻¹) •
        ∑ g : PrimeSymmetry p,
          g⁻¹ • rawEndpointInterpolant hp N L s a (g • x))
  have hsum :
      (∑ g : PrimeSymmetry p,
          g⁻¹ • rawEndpointInterpolant hp N L s a (g • (h • x))) =
        ∑ g : PrimeSymmetry p,
          (g * h⁻¹)⁻¹ • rawEndpointInterpolant hp N L s a ((g * h⁻¹) • (h • x)) := by
    apply Finset.sum_bij (fun g : PrimeSymmetry p => fun _ => g * h)
    · intro g hg
      simp
    · intro g₁ hg₁ g₂ hg₂ heq
      exact mul_right_cancel heq
    · intro g hg
      exact ⟨g * h⁻¹, by simp, by simp⟩
    · intro g hg
      simp [mul_assoc]
  rw [hsum]
  simp only [mul_smul]
  congr 1
  funext j
  simp only [Finset.sum_apply, PrimeSymmetry.smul_coordinate_apply]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  simp [← mul_smul, mul_assoc]

/-- The symmetrized interpolant still realizes every horizontal sample. -/
@[simp] theorem endpointInterpolant_sample
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L) (v : EndpointVertex hp N L s) :
    endpointInterpolant hp N L s a
      (endpointSpatialPoint hp N L s v) =
        vectorValue hp N L a v.1 := by
  classical
  change ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) •
      ∑ g : PrimeSymmetry p,
        g⁻¹ • rawEndpointInterpolant hp N L s a
          (g • endpointSpatialPoint hp N L s v) = _
  have hcard : (Fintype.card (PrimeSymmetry p) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ g : PrimeSymmetry p,
      g⁻¹ • rawEndpointInterpolant hp N L s a
          (g • endpointSpatialPoint hp N L s v) =
        vectorValue hp N L a v.1 := by
    intro g
    let gv : EndpointVertex hp N L s :=
      ⟨g • v.1, by simpa [IsEndpointVertex] using v.2⟩
    have hpoint : endpointSpatialPoint hp N L s gv =
        g • endpointSpatialPoint hp N L s v := by
      have hg := congrArg CylinderPoint.spatial
        (globalPoint_smul hp N L g v.1)
      simpa [endpointSpatialPoint, gv] using hg
    rw [← hpoint, rawEndpointInterpolant_sample]
    simpa [gv, vectorValue_smul hp N L a g v.1]
  calc
    _ = ((Fintype.card (PrimeSymmetry p) : Real)⁻¹) •
        ∑ _g : PrimeSymmetry p, vectorValue hp N L a v.1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      exact hterm g
    _ = _ := by
      funext j
      simp [hcard]

/-- Canonical prism cell used to realize one endpoint simplex. -/
noncomputable def endpointPrismCell
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (q : TopCell hp N) (eta : RefinementWord p L) : PrismCell hp N L :=
  match s with
  | .lower => lowerPrismCell hp N L q eta
  | .upper => upperPrismCell hp N L q eta

/-- Facet omitted from the canonical endpoint prism cell. -/
def endpointOmittedIndex
    (L : Nat) (s : EndpointSide) : Fin (p + 1) :=
  match s with
  | .lower => endpointOmittedPrime L (Fin.last p)
  | .upper => endpointOmittedPrime L 0

/-- Canonical facet occurrence realizing one endpoint simplex. -/
noncomputable def endpointOccurrence
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (q : TopCell hp N) (eta : RefinementWord p L) : FacetOccurrence hp N L :=
  (endpointPrismCell hp N L s q eta, endpointOmittedIndex L s)

private theorem facetCoordinateIndex_eq_endpointIndex
    (hp : Nat.Prime p) (i : Fin p) :
    AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i =
      Fin.cast (Nat.sub_add_cancel hp.pos).symm i := by
  apply Fin.ext
  rfl

/-- The canonical endpoint occurrence has exactly the expected refined endpoint vertices. -/
theorem endpointOccurrence_facetSignature
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (q : TopCell hp N) (eta : RefinementWord p L) (i : Fin p) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (endpointOccurrence hp N L s q eta) i =
      match s with
      | .lower => ExplicitAffineRelativeCollar.lowerCylinderPoint
          (RefinedAffineMap.vertex hp (N + L)
            (endpointTopCell hp N L q eta)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))
      | .upper => ExplicitAffineRelativeCollar.upperCylinderPoint
          (RefinedAffineMap.vertex hp (N + L)
            (endpointTopCell hp N L q eta)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  cases s
  · exact lowerOccurrence_facetSignature hp N L q eta i
  · exact upperOccurrence_facetSignature hp N L q eta i

/-- Boundary samples of an assignment agree with the corresponding endpoint interpolant. -/
theorem endpointInterpolant_vertexValue
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L)
    (q : TopCell hp N) (eta : RefinementWord p L)
    (i : Fin p) :
    endpointInterpolant hp N L s a
        (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) =
      vectorValue hp N L a
        (sampleVertex hp N L
          ((endpointOccurrence hp N L s q eta).1,
            (endpointOccurrence hp N L s q eta).2.succAbove i)) := by
  let o : FacetOccurrence hp N L := endpointOccurrence hp N L s q eta
  have hsig := endpointOccurrence_facetSignature hp N L s q eta i
  have hendpoint : IsEndpointVertex hp N L s
      (sampleVertex hp N L (o.1, o.2.succAbove i)) := by
    cases s
    · unfold IsEndpointVertex
      rw [globalPoint_sampleVertex]
      change ((RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (endpointOccurrence hp N L EndpointSide.lower q eta) i).time.1 = 0
      simpa [ExplicitAffineRelativeCollar.lowerCylinderPoint] using
        congrArg (fun z : CylinderPoint p => z.time.1) hsig
    · unfold IsEndpointVertex
      rw [globalPoint_sampleVertex]
      change ((RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (endpointOccurrence hp N L EndpointSide.upper q eta) i).time.1 = 1
      simpa [ExplicitAffineRelativeCollar.upperCylinderPoint] using
        congrArg (fun z : CylinderPoint p => z.time.1) hsig
  let v : EndpointVertex hp N L s :=
    ⟨sampleVertex hp N L (o.1, o.2.succAbove i), hendpoint⟩
  have hspatial : endpointSpatialPoint hp N L s v =
      endpointSpatialMap hp N L q eta
        (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
    cases s
    · unfold endpointSpatialPoint
      rw [globalPoint_sampleVertex]
      change ((RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (endpointOccurrence hp N L EndpointSide.lower q eta) i).spatial = _
      simpa [endpointSpatialMap_eq_chart,
        ExplicitAffineRelativeCollar.lowerCylinderPoint,
        RefinedAffineMap.vertex] using
        congrArg (fun z : CylinderPoint p => z.spatial) hsig
    · unfold endpointSpatialPoint
      rw [globalPoint_sampleVertex]
      change ((RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (endpointOccurrence hp N L EndpointSide.upper q eta) i).spatial = _
      simpa [endpointSpatialMap_eq_chart,
        ExplicitAffineRelativeCollar.upperCylinderPoint,
        RefinedAffineMap.vertex] using
        congrArg (fun z : CylinderPoint p => z.spatial) hsig
  rw [← hspatial]
  simpa [v, o] using endpointInterpolant_sample hp N L s a v
/-- Endpoint regularity inherited from the corresponding canonical horizontal facets of a generic
prism assignment. -/
theorem endpointInterpolant_regular
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L)
    (hregular : ∀ q : PrismCell hp N L,
      FacetRegular hp (localVertexMap hp N L a q)) :
    ∀ q : TopCell hp (N + L),
      determinant hp (N + L) (endpointInterpolant hp N L s a) q ≠ 0 := by
  intro q
  obtain ⟨q₀, eta, rfl⟩ := endpointTopCell_surjective hp N L q
  let prismCell : PrismCell hp N L := endpointPrismCell hp N L s q₀ eta
  let omitted : Fin (p + 1) := endpointOmittedIndex L s
  have hvertex : ∀ i : Fin p,
      AffinePositiveRayBoundary.VertexMap.facetValue
          (localVertexMap hp N L a prismCell) omitted i =
        RefinedAffineMap.vertexValue hp (N + L)
          (endpointInterpolant hp N L s a) (endpointTopCell hp N L q₀ eta)
          (ExplicitAffineRelativeCollar.refinedVertexIndex hp i) := by
    intro i
    rw [ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex]
    rw [facetCoordinateIndex_eq_endpointIndex hp i]
    symm
    change endpointInterpolant hp N L s a
        (RefinedAffineMap.vertex hp (N + L) (endpointTopCell hp N L q₀ eta)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) =
      vectorValue hp N L a (sampleVertex hp N L
        ((endpointOccurrence hp N L s q₀ eta).1,
          (endpointOccurrence hp N L s q₀ eta).2.succAbove i))
    simpa [endpointSpatialMap_eq_chart, RefinedAffineMap.vertex] using
      endpointInterpolant_vertexValue hp N L s a q₀ eta i
  rw [← ExplicitAffineRelativeCollar.facetDeterminant_eq_refinedDeterminant
    hp (localVertexMap hp N L a prismCell) omitted (N + L)
      (endpointInterpolant hp N L s a) (endpointTopCell hp N L q₀ eta) hvertex]
  exact hregular prismCell omitted

/-- Endpoint skeleton transversality inherited from prism codimension-two avoidance. -/
theorem endpointInterpolant_skeletonFree
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    (a : Assignment hp N L)
    (hcodim : ∀ q : PrismCell hp N L,
      AvoidsCodimTwoDeviationZero hp (localVertexMap hp N L a q)) :
    PositiveRaySkeletonFree hp (N + L)
      (endpointInterpolant hp N L s a) := by
  intro q w hdev hmean
  obtain ⟨q₀, eta, rfl⟩ := endpointTopCell_surjective hp N L q
  by_contra hnot
  simp only [StandardSimplex.IsInterior, not_forall] at hnot
  obtain ⟨i, hi⟩ := hnot
  have hi0 : w i = 0 :=
    le_antisymm (not_lt.mp hi) (w.nonneg i)
  let prismCell : PrismCell hp N L := endpointPrismCell hp N L s q₀ eta
  let omitted : Fin (p + 1) := endpointOmittedIndex L s
  let full : StandardSimplex p :=
    AffinePositiveRayBoundary.VertexMap.fullSimplexOfFacet hp omitted w
  have haffine :
      AffinePositiveRayBoundary.VertexMap.facetAffineValue
          (localVertexMap hp N L a prismCell) omitted w =
        RefinedAffineMap.value hp (N + L) (endpointInterpolant hp N L s a)
          (endpointTopCell hp N L q₀ eta) w := by
    funext j
    unfold AffinePositiveRayBoundary.VertexMap.facetAffineValue RefinedAffineMap.value
    rw [← ExplicitAffineRelativeCollar.sum_refinedVertexIndex hp]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex]
    rw [facetCoordinateIndex_eq_endpointIndex hp i]
    symm
    simpa [prismCell, omitted, endpointOccurrence, endpointSpatialMap_eq_chart,
      AffinePositiveRayBoundary.VertexMap.facetValue,
      AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex,
      EquivariantPrismGenericityPolynomials.localVertexMap,
      EquivariantPrismVertexParameters.localVertexValue,
      ExplicitAffineRelativeCollar.refinedVertexIndex,
      RefinedAffineMap.vertexValue, RefinedAffineMap.vertex] using
      congrFun (endpointInterpolant_vertexValue hp N L s a q₀ eta i) j
  have hfullDev : ∀ r : Fin (p - 1),
      AffinePositiveRayBoundary.VertexMap.deviation hp
        (AffinePositiveRayBoundary.VertexMap.affineValue
          (localVertexMap hp N L a prismCell) full) r = 0 := by
    intro r
    rw [AffinePositiveRayBoundary.VertexMap.deviation_affineValue_fullSimplexOfFacet,
      haffine]
    exact sub_eq_zero.mpr (hdev r)
  let i' : Fin p :=
    AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp i
  have hzero1 : full omitted = 0 := by
    exact AffinePositiveRayBoundary.VertexMap.fullSimplexOfFacet_omitted_eq_zero hp omitted w
  have hzero2 : full (omitted.succAbove i') = 0 := by
    rw [show full (omitted.succAbove i') = w i by
      exact AffinePositiveRayBoundary.VertexMap.fullSimplexOfFacet_succAbove_facetIndexEquiv
        hp omitted w i]
    exact hi0
  exact hcodim prismCell full omitted (omitted.succAbove i')
    (Fin.succAbove_ne omitted i').symm hfullDev ⟨hzero1, hzero2⟩

/-- Quantitative endpoint closeness needed for the stored zero-free straight-line field. -/
def EndpointStraightLineSafe
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    {F₀ F₁ : ZeroFreeMap hp}
    (a : Assignment hp N L) : Prop :=
  ∀ (q : TopCell hp (N + L)) (w : StandardSimplex (p - 1))
    (u : Set.Icc (0 : Real) 1),
    (1 - u.1) • (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
        (chart hp (N + L) q (StandardSimplex.toDelta w)) +
      u.1 • value hp (N + L) (endpointInterpolant hp N L s a) q w ≠ 0

/-- Stable endpoint approximation extracted from one generic prism assignment. -/
noncomputable def stableEndpointApproximation
    (hp : Nat.Prime p) (N L : Nat) (s : EndpointSide)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (a : Assignment hp N L)
    (hregular : ∀ q : PrismCell hp N L,
      FacetRegular hp (localVertexMap hp N L a q))
    (hcodim : ∀ q : PrismCell hp N L,
      AvoidsCodimTwoDeviationZero hp (localVertexMap hp N L a q))
    (hsafe : EndpointStraightLineSafe hp N L s (F₀ := F₀) (F₁ := F₁) a) :
    StableRegularApproximation hp (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map where
  toRegularApproximation := {
    level := N + L
    map := endpointInterpolant hp N L s a
    equivariant := endpointInterpolant_equivariant hp N L s a
    regular := endpointInterpolant_regular hp N L s a hregular
    zeroFreeStraightLine := hsafe
  }
  positiveRaySkeletonFree :=
    endpointInterpolant_skeletonFree hp N L s a hcodim

/-- A vector segment cannot hit the origin when its second endpoint is closer to the first
than the norm of the first. -/
theorem segment_ne_zero_of_norm_sub_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x y : E} {r : Real} (hr : r ≤ ‖x‖) (hxy : ‖y - x‖ < r)
    (u : Set.Icc (0 : Real) 1) :
    (1 - u.1) • x + u.1 • y ≠ 0 := by
  intro hzero
  have hx : x = u.1 • (x - y) := by
    apply eq_of_sub_eq_zero
    calc
      x - u.1 • (x - y) = (1 - u.1) • x + u.1 • y := by module
      _ = 0 := hzero
  have hu0 : 0 ≤ u.1 := u.2.1
  have hu1 : u.1 ≤ 1 := u.2.2
  have hnorm : ‖x‖ ≤ ‖y - x‖ := by
    calc
      ‖x‖ = ‖u.1 • (x - y)‖ := congrArg norm hx
      _ = u.1 * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0]
      _ ≤ ‖x - y‖ := by
        nlinarith [norm_nonneg (x - y)]
      _ = ‖y - x‖ := by rw [← norm_neg, neg_sub]
  linarith

/-- Quantitative endpoint information used to construct stable approximations from a prism result. -/
structure EndpointControl
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (a : Assignment hp N L) (r : Real) : Prop where
  positive : 0 < r
  normLower : ∀ s : EndpointSide,
    ∀ (q : TopCell hp (N + L)) (w : StandardSimplex (p - 1)),
      r ≤ ‖(EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
        (chart hp (N + L) q (StandardSimplex.toDelta w))‖
  close : ∀ s : EndpointSide,
    ∀ (q : TopCell hp (N + L)) (w : StandardSimplex (p - 1)),
      ‖value hp (N + L) (endpointInterpolant hp N L s a) q w -
        (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
          (chart hp (N + L) q (StandardSimplex.toDelta w))‖ < r

/-- Endpoint control makes both straight-line interpolations zero-free. -/
theorem endpointStraightLineSafe_of_control
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (a : Assignment hp N L) {r : Real}
    (C : EndpointControl hp N L H a r) :
    ∀ s : EndpointSide,
      EndpointStraightLineSafe hp N L s (F₀ := F₀) (F₁ := F₁) a := by
  intro s q w u
  exact segment_ne_zero_of_norm_sub_lt
    (C.normLower s q w) (C.close s q w) u

/-- A generic prism result with controlled horizontal approximation determines a stable lower
endpoint approximation at the exact horizontal triangulation level. -/
noncomputable def Result.lowerStableApproximation
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {m r : Real} (R : Result hp N L H m)
    (C : EndpointControl hp N L H R.assignment r) :
    StableRegularApproximation hp F₀.map :=
  stableEndpointApproximation hp N L .lower H R.assignment
    R.facetRegular R.avoidsCodimTwo
    (endpointStraightLineSafe_of_control hp N L H R.assignment C .lower)

/-- Stable upper endpoint approximation extracted from the same controlled prism result. -/
noncomputable def Result.upperStableApproximation
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {m r : Real} (R : Result hp N L H m)
    (C : EndpointControl hp N L H R.assignment r) :
    StableRegularApproximation hp F₁.map :=
  stableEndpointApproximation hp N L .upper H R.assignment
    R.facetRegular R.avoidsCodimTwo
    (endpointStraightLineSafe_of_control hp N L H R.assignment C .upper)

/-- An assignment is relative to two endpoint approximations when its horizontal samples agree
exactly with their sampled maps. -/
def BoundaryFixed
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp}
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (a : Assignment hp N L) : Prop :=
  A₀.toRegularApproximation.level = N + L ∧
  A₁.toRegularApproximation.level = N + L ∧
  (∀ q : TopCell hp N, ∀ eta : RefinementWord p L, ∀ i : Fin p,
    A₀.toRegularApproximation.map
        (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) =
      endpointInterpolant hp N L .lower a
        (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)))) ∧
  (∀ q : TopCell hp N, ∀ eta : RefinementWord p L, ∀ i : Fin p,
    A₁.toRegularApproximation.map
        (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) =
      endpointInterpolant hp N L .upper a
        (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex (S := Real)
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))))

/-- The endpoint approximations extracted from a result are fixed boundaries for that same prism
assignment. -/
theorem Result.boundaryFixed
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {m r : Real} (R : Result hp N L H m)
    (C : EndpointControl hp N L H R.assignment r) :
    BoundaryFixed hp N L
      (Result.lowerStableApproximation hp N L H R C)
      (Result.upperStableApproximation hp N L H R C)
      R.assignment := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    intro q eta i <;> rfl

/-- Complete boundary-relative output: two stable endpoint approximations and one compatible
prime-equivariant prism assignment which keeps their horizontal samples fixed. -/
structure RelativeResult
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) where
  /-- The generic prism perturbation underlying the relative-boundary result. -/
  prism : Result hp N L H m
  /-- The stable regular approximation fixed on the lower endpoint. -/
  lower : StableRegularApproximation hp F₀.map
  /-- The stable regular approximation fixed on the upper endpoint. -/
  upper : StableRegularApproximation hp F₁.map
  boundaryFixed : BoundaryFixed hp N L lower upper prism.assignment

/-- Construct stable endpoint approximations and a generic prism perturbation relative to their
fixed transverse horizontal boundaries. -/
noncomputable def Result.toRelativeResult
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {m r : Real} (R : Result hp N L H m)
    (C : EndpointControl hp N L H R.assignment r) :
    RelativeResult hp N L H m where
  prism := R
  lower := Result.lowerStableApproximation hp N L H R C
  upper := Result.upperStableApproximation hp N L H R C
  boundaryFixed := Result.boundaryFixed hp N L H R C


/-- Oscillation on level `N` persists on every further barycentric refinement. -/
theorem oscillation_further_refinement
    (hp : Nat.Prime p) (F : ContinuousCoordinateMap p)
    (N K : Nat) {eps : Real}
    (hosc : ∀ (q : TopCell hp N) (u v : StandardSimplex (p - 1)),
      dist (F (chart hp N q (StandardSimplex.toDelta u)))
        (F (chart hp N q (StandardSimplex.toDelta v))) < eps) :
    ∀ (q : TopCell hp (N + K)) (u v : StandardSimplex (p - 1)),
      dist (F (chart hp (N + K) q (StandardSimplex.toDelta u)))
        (F (chart hp (N + K) q (StandardSimplex.toDelta v))) < eps := by
  intro q u v
  let q₀ : TopCell hp N := (q.1, (splitRefinementWord N K q.2).1)
  let eta : RefinementWord p K := (splitRefinementWord N K q.2).2
  let eta' : Fin K → Equiv.Perm (Fin (p - 1 + 1)) :=
    fun i => Simplex.refinementIndexPerm (eta i)
  have hchart : ∀ x : Delta (p - 1),
      RefinedAffineMap.chart hp (N + K) q x =
        RefinedAffineMap.chart hp N q₀ (affineCompMap (p - 1) K eta' x) := by
    intro x
    have hword :
        (fun k : Fin (N + K) => Simplex.refinementIndexPerm (q.2 k)) =
          appendRefinementWord N K
            (fun k => Simplex.refinementIndexPerm (q.2 (Fin.castAdd K k))) eta' := by
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp [appendRefinementWord]
      · intro i
        simp [appendRefinementWord, eta', eta, splitRefinementWord]
    simp only [q₀, eta, eta', RefinedAffineMap.chart, splitRefinementWord,
      Simplex.refinedContinuousMap, ContinuousMap.comp_apply]
    rw [hword, affineCompMap_append]
    rfl
  rw [hchart, hchart]
  exact hosc q₀
    (StandardSimplex.ofDelta (affineCompMap (p - 1) K eta'
      (StandardSimplex.toDelta u)))
    (StandardSimplex.ofDelta (affineCompMap (p - 1) K eta'
      (StandardSimplex.toDelta v)))

/-- One spatial level can be chosen so that both endpoint maps have small oscillation on every
refined top simplex. -/
theorem exists_common_endpoint_oscillation
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp) {eps : Real} (heps : 0 < eps) :
    ∃ N : Nat,
      (∀ (q : TopCell hp N) (u v : StandardSimplex (p - 1)),
        dist (F₀.map (chart hp N q (StandardSimplex.toDelta u)))
          (F₀.map (chart hp N q (StandardSimplex.toDelta v))) < eps) ∧
      (∀ (q : TopCell hp N) (u v : StandardSimplex (p - 1)),
        dist (F₁.map (chart hp N q (StandardSimplex.toDelta u)))
          (F₁.map (chart hp N q (StandardSimplex.toDelta v))) < eps) := by
  obtain ⟨N₀, h₀⟩ := exists_common_refinement_oscillation hp F₀.map heps
  obtain ⟨N₁, h₁⟩ := exists_common_refinement_oscillation hp F₁.map heps
  refine ⟨N₀ + N₁,
    oscillation_further_refinement hp F₀.map N₀ N₁ h₀, ?_⟩
  rw [Nat.add_comm N₀ N₁]
  exact oscillation_further_refinement hp F₁.map N₁ N₀ h₁

/-- Coordinatewise closeness of global assignments bounds the endpoint affine interpolants in the
finite product norm. -/
theorem norm_endpoint_value_sub_homotopy_value_le
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (a : Assignment hp N L) {eps : Real}
    (hclose : AssignmentClose a (homotopyAssignment hp N L H) eps)
    (s : EndpointSide) (q : TopCell hp (N + L))
    (w : StandardSimplex (p - 1)) :
    ‖value hp (N + L) (endpointInterpolant hp N L s a) q w -
      value hp (N + L)
        (endpointInterpolant hp N L s (homotopyAssignment hp N L H)) q w‖ ≤ eps := by
  classical
  have heps : 0 ≤ eps := by
    obtain ⟨q₀, eta, hq⟩ := endpointTopCell_surjective hp N L q
    let prismCell : PrismCell hp N L := endpointPrismCell hp N L s q₀ eta
    let x : GlobalVertex hp N L := sampleVertex hp N L (prismCell, 0)
    let j : Fin p := ⟨0, hp.pos⟩
    let t : Parameter hp N L :=
      Quotient.mk (MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp N L)) (x, j)
    exact le_trans (abs_nonneg (a t - homotopyAssignment hp N L H t))
      (le_of_lt (hclose t))
  rw [show
    ‖value hp (N + L) (endpointInterpolant hp N L s a) q w -
        value hp (N + L)
          (endpointInterpolant hp N L s (homotopyAssignment hp N L H)) q w‖ =
      dist
        (value hp (N + L) (endpointInterpolant hp N L s a) q w -
          value hp (N + L)
            (endpointInterpolant hp N L s (homotopyAssignment hp N L H)) q w)
        0 by simp]
  rw [dist_pi_le_iff heps]
  intro j
  rw [show (0 : Fin p → Real) j = 0 by rfl, Real.dist_eq]
  simp only [Pi.sub_apply, sub_zero]
  unfold RefinedAffineMap.value RefinedAffineMap.vertexValue
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : Fin (p - 1 + 1),
        (w i * endpointInterpolant hp N L s a (RefinedAffineMap.vertex hp (N + L) q i) j -
          w i * endpointInterpolant hp N L s
            (homotopyAssignment hp N L H) (RefinedAffineMap.vertex hp (N + L) q i) j)‖
        ≤ ∑ i : Fin (p - 1 + 1),
          ‖w i * endpointInterpolant hp N L s a (RefinedAffineMap.vertex hp (N + L) q i) j -
            w i * endpointInterpolant hp N L s
              (homotopyAssignment hp N L H) (RefinedAffineMap.vertex hp (N + L) q i) j‖ := by
      simpa using norm_sum_le (Finset.univ : Finset (Fin (p - 1 + 1)))
        (fun i => w i * endpointInterpolant hp N L s a
          (RefinedAffineMap.vertex hp (N + L) q i) j -
          w i * endpointInterpolant hp N L s (homotopyAssignment hp N L H)
            (RefinedAffineMap.vertex hp (N + L) q i) j)
    _ ≤ ∑ i : Fin (p - 1 + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show
        w i * endpointInterpolant hp N L s a (RefinedAffineMap.vertex hp (N + L) q i) j -
            w i * endpointInterpolant hp N L s
              (homotopyAssignment hp N L H) (RefinedAffineMap.vertex hp (N + L) q i) j =
          w i * (endpointInterpolant hp N L s a (RefinedAffineMap.vertex hp (N + L) q i) j -
            endpointInterpolant hp N L s
              (homotopyAssignment hp N L H) (RefinedAffineMap.vertex hp (N + L) q i) j) by ring,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
      obtain ⟨q₀, eta, hq⟩ := endpointTopCell_surjective hp N L q
      subst hq
      let i' : Fin p := Fin.cast (Nat.sub_add_cancel hp.pos) i
      have ha := congrFun (endpointInterpolant_vertexValue hp N L s a q₀ eta i') j
      have hb := congrFun (endpointInterpolant_vertexValue hp N L s
        (homotopyAssignment hp N L H) q₀ eta i') j
      rw [show RefinedAffineMap.vertex hp (N + L) (endpointTopCell hp N L q₀ eta) i =
          endpointSpatialMap hp N L q₀ eta
            (stdSimplex.vertex (Fin.cast (Nat.sub_add_cancel hp.pos).symm i')) by
        simp [i', RefinedAffineMap.vertex, endpointSpatialMap_eq_chart]]
      rw [ha, hb]
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (hclose _)) (w.nonneg i)
    _ = eps := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- At a horizontal endpoint, the interpolant of the unperturbed homotopy assignment is the affine
interpolation of the corresponding endpoint map samples. -/
theorem endpointInterpolant_homotopyAssignment_value
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (s : EndpointSide) (q : TopCell hp (N + L))
    (w : StandardSimplex (p - 1)) :
    RefinedAffineMap.value hp (N + L)
      (endpointInterpolant hp N L s (homotopyAssignment hp N L H)) q w =
    RefinedAffineMap.value hp (N + L) (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map q w := by
  funext j
  unfold RefinedAffineMap.value RefinedAffineMap.vertexValue
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  obtain ⟨q₀, eta, hq⟩ := endpointTopCell_surjective hp N L q
  subst hq
  let i' : Fin p := Fin.cast (Nat.sub_add_cancel hp.pos) i
  have hv := endpointInterpolant_vertexValue hp N L s
    (homotopyAssignment hp N L H) q₀ eta i'
  rw [show RefinedAffineMap.vertex hp (N + L) (endpointTopCell hp N L q₀ eta) i =
      endpointSpatialMap hp N L q₀ eta
        (stdSimplex.vertex (Fin.cast (Nat.sub_add_cancel hp.pos).symm i')) by
    simp [i', RefinedAffineMap.vertex, endpointSpatialMap_eq_chart]]
  rw [hv]
  cases s
  · have hsig := endpointOccurrence_facetSignature hp N L EndpointSide.lower q₀ eta i'
    have hpoint :
        CylinderPoint.toProd (slotPoint hp N L
          ((endpointOccurrence hp N L EndpointSide.lower q₀ eta).1,
            (endpointOccurrence hp N L EndpointSide.lower q₀ eta).2.succAbove i')) =
          (endpointSpatialMap hp N L q₀ eta
            (stdSimplex.vertex (Fin.cast (Nat.sub_add_cancel hp.pos).symm i')), 0) := by
      apply Prod.ext
      · simpa [slotPoint, RelativeCollarMiddlePrism.cellSystem,
          RelativeCollarMiddlePrism.vertex,
          ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature,
          EquivariantPrismVertexParameters.CylinderPoint.ofProd,
          CylinderPoint.toProd,
          endpointSpatialMap_eq_chart, ExplicitAffineRelativeCollar.lowerCylinderPoint,
          RefinedAffineMap.vertex] using
          congrArg (fun z : CylinderPoint p => z.spatial) hsig
      · simpa [slotPoint, RelativeCollarMiddlePrism.cellSystem,
          RelativeCollarMiddlePrism.vertex,
          ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature,
          EquivariantPrismVertexParameters.CylinderPoint.ofProd,
          CylinderPoint.toProd,
          ExplicitAffineRelativeCollar.lowerCylinderPoint] using
          congrArg (fun z : CylinderPoint p => z.time) hsig
    rw [vectorValue_homotopyAssignment, globalPoint_sampleVertex, hpoint]
    exact congrFun (H.map_zero _) j
  · have hsig := endpointOccurrence_facetSignature hp N L EndpointSide.upper q₀ eta i'
    have hpoint :
        CylinderPoint.toProd (slotPoint hp N L
          ((endpointOccurrence hp N L EndpointSide.upper q₀ eta).1,
            (endpointOccurrence hp N L EndpointSide.upper q₀ eta).2.succAbove i')) =
          (endpointSpatialMap hp N L q₀ eta
            (stdSimplex.vertex (Fin.cast (Nat.sub_add_cancel hp.pos).symm i')), 1) := by
      apply Prod.ext
      · simpa [slotPoint, RelativeCollarMiddlePrism.cellSystem,
          RelativeCollarMiddlePrism.vertex,
          ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature,
          EquivariantPrismVertexParameters.CylinderPoint.ofProd,
          CylinderPoint.toProd,
          endpointSpatialMap_eq_chart, ExplicitAffineRelativeCollar.upperCylinderPoint,
          RefinedAffineMap.vertex] using
          congrArg (fun z : CylinderPoint p => z.spatial) hsig
      · simpa [slotPoint, RelativeCollarMiddlePrism.cellSystem,
          RelativeCollarMiddlePrism.vertex,
          ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature,
          EquivariantPrismVertexParameters.CylinderPoint.ofProd,
          CylinderPoint.toProd,
          ExplicitAffineRelativeCollar.upperCylinderPoint] using
          congrArg (fun z : CylinderPoint p => z.time) hsig
    rw [vectorValue_homotopyAssignment, globalPoint_sampleVertex, hpoint]
    exact congrFun (H.map_one _) j

/-- A sufficiently fine generic prism perturbation comes with quantitative endpoint control. -/
theorem exists_controlled_generic_perturbation
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ (N L : Nat) (m r : Real), 0 < m ∧
      ∃ R : Result hp N L H m,
        EndpointControl hp N L H R.assignment r := by
  classical
  obtain ⟨M, hM, hglobal⟩ :=
    EquivariantPrismSubdivisionMargin.exists_positive_homotopy_norm_margin hp H
  obtain ⟨N, hendpoint₀, hendpoint₁⟩ :=
    exists_common_endpoint_oscillation hp F₀ F₁
      (show 0 < M / 8 by positivity)
  obtain ⟨L, hprismOsc⟩ :=
    EquivariantPrismSubdivisionMargin.exists_staircase_refinement_oscillation
      hp N H (show 0 < M / 8 by positivity)
  let m : Real := 3 * M / 4
  have hm : 0 < m := by dsimp [m]; positivity
  have hmargin : LocalAffineCoordinateNormMargin hp N L
      (homotopyAssignment hp N L H) m := by
    intro q w
    let y : Fin p → Real := H.map (SubdivisionPrismCharts.chart hp N L q
      (StandardSimplex.toDelta w))
    let z : Fin p → Real :=
      VertexMap.affineValue
        (localVertexMap hp N L (homotopyAssignment hp N L H) q) w
    have hclose : ‖z - y‖ ≤ M / 8 := by
      simpa [z, y] using
        EquivariantPrismSubdivisionMargin.norm_affineValue_sub_homotopy_le_of_oscillation
          hp N L H q (M / 8) (hprismOsc q) w
    have hy : M ≤ ‖y‖ := hglobal _
    have hz : m ≤ ‖z‖ := by
      have hy_le : ‖y‖ ≤ ‖z - y‖ + ‖z‖ := by
        calc
          ‖y‖ = ‖-(z - y) + z‖ := by congr 1; module
          _ ≤ ‖-(z - y)‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z - y‖ + ‖z‖ := by rw [norm_neg]
      dsimp [m]
      linarith
    obtain ⟨j, hj⟩ :=
      EquivariantPrismSubdivisionMargin.exists_coordinate_abs_ge_norm hp z
    exact ⟨j, le_trans hz (by simpa [z, Real.norm_eq_abs] using hj)⟩
  obtain ⟨R⟩ := exists_generic_perturbation hp N L H hm hmargin
  let r : Real := M
  refine ⟨N, L, m, r, hm, R, ?_⟩
  refine {
    positive := hM
    normLower := ?_
    close := ?_ }
  · intro s q w
    cases s
    · have h0 := hglobal (chart hp (N + L) q (StandardSimplex.toDelta w),
          ⟨0, by simp⟩)
      rw [H.map_zero] at h0
      simpa [EndpointSide.zeroFreeMap, r] using h0
    · have h1 := hglobal (chart hp (N + L) q (StandardSimplex.toDelta w),
          ⟨1, by simp⟩)
      rw [H.map_one] at h1
      simpa [EndpointSide.zeroFreeMap, r] using h1
  · intro s q w
    have hperturb := norm_endpoint_value_sub_homotopy_value_le
      hp N L H R.assignment R.closeToHomotopy s q w
    rw [endpointInterpolant_homotopyAssignment_value hp N L H s q w] at hperturb
    have hoscCombined :
        ∀ (q : TopCell hp (N + L)) (u v : StandardSimplex (p - 1)),
          dist ((EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
            (chart hp (N + L) q (StandardSimplex.toDelta u)))
            ((EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
              (chart hp (N + L) q (StandardSimplex.toDelta v))) < M / 8 := by
      cases s
      · exact oscillation_further_refinement hp F₀.map N L hendpoint₀
      · exact oscillation_further_refinement hp F₁.map N L hendpoint₁
    have hsample := norm_value_sub_original_le_of_oscillation
      hp (N + L) (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map q (M / 8)
      (hoscCombined q) w
    let A := RefinedAffineMap.value hp (N + L)
      (endpointInterpolant hp N L s R.assignment) q w
    let B := RefinedAffineMap.value hp (N + L)
      (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map q w
    let O := (EndpointSide.zeroFreeMap (hp := hp) (F₀ := F₀) (F₁ := F₁) s).map
      (chart hp (N + L) q (StandardSimplex.toDelta w))
    have hdecomp : A - O = (A - B) + (B - O) := by module
    have htri : ‖A - O‖ ≤ ‖A - B‖ + ‖B - O‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    dsimp [A, B, O, m, r] at htri R hperturb hsample ⊢
    linarith

/-- Stable endpoint approximations and a boundary-relative generic prism exist for every zero-free
equivariant homotopy. -/
theorem exists_stable_relative_result
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ (N L : Nat) (m : Real), 0 < m ∧
      Nonempty (RelativeResult hp N L H m) := by
  obtain ⟨N, L, m, r, hm, R, C⟩ :=
    exists_controlled_generic_perturbation hp H
  exact ⟨N, L, m, hm, ⟨Result.toRelativeResult hp N L H R C⟩⟩

private theorem lower_realizedFacetWeight_eq_localIndex
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : TopCell hp N) (eta : RefinementWord p L)
    (hfix : ∀ i : Fin p,
      F (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) =
        endpointInterpolant hp N L EndpointSide.lower a
          (endpointSpatialMap hp N L q eta
            (stdSimplex.vertex
              (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)))) :
    EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.lowerEndpointMap
          (endpointSpatialMap hp N L q eta)) =
      RefinedAffineMap.localIndex hp (N + L) F
        (endpointTopCell hp N L q eta) := by
  let o :=
    RelativeCollarMiddlePrismEndpointsCore.lowerOccurrence hp N L q eta

  have hmap :
      EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap
          hp N L o =
        EquivariantPrismNonhorizontalCancellation.lowerEndpointMap
          (endpointSpatialMap hp N L q eta) := by
    simpa [o] using
      RelativeCollarMiddlePrismEndpointsCore.lowerOccurrenceFacetMap_eq
        hp N L q eta

  have hvertex : ∀ i : Fin p,
      AffinePositiveRayBoundary.VertexMap.facetValue
          (localVertexMap hp N L a o.1) o.2 i =
        RefinedAffineMap.vertexValue hp (N + L) F
          (endpointTopCell hp N L q eta)
          (ExplicitAffineRelativeCollar.refinedVertexIndex hp i) := by
    intro i
    rw [
      ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex
    ]
    rw [facetCoordinateIndex_eq_endpointIndex hp i]
    symm
    have h :=
      (hfix i).trans
        (endpointInterpolant_vertexValue
          hp N L EndpointSide.lower a q eta i)
    change F (RefinedAffineMap.vertex hp (N + L)
        (endpointTopCell hp N L q eta)
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) =
      vectorValue hp N L a (sampleVertex hp N L
        ((endpointOccurrence hp N L EndpointSide.lower q eta).1,
          (endpointOccurrence hp N L EndpointSide.lower q eta).2.succAbove i))
    simpa [endpointSpatialMap_eq_chart, RefinedAffineMap.vertex] using h

  have haffine : ∀ w : StandardSimplex (p - 1),
      AffinePositiveRayBoundary.VertexMap.facetAffineValue
          (localVertexMap hp N L a o.1) o.2 w =
        RefinedAffineMap.value hp (N + L) F
          (endpointTopCell hp N L q eta) w := by
    intro w
    funext j
    unfold AffinePositiveRayBoundary.VertexMap.facetAffineValue
      RefinedAffineMap.value
    rw [← ExplicitAffineRelativeCollar.sum_refinedVertexIndex hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [
      ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex
    ]
    rw [facetCoordinateIndex_eq_endpointIndex hp i]
    congr 1
    exact congrFun (hvertex i) j

  calc
    EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.lowerEndpointMap
          (endpointSpatialMap hp N L q eta)) =
      EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap
          hp N L o) := by
            rw [hmap]
    _ = EquivariantPrismGlobalCancellation.signatureWeight
        hp N L a
        (EquivariantPrismGlobalCancellation.facetSignature hp N L o) :=
      EquivariantPrismNonhorizontalCancellation.realizedFacetWeight_occurrence
        hp N L a o
    _ = unsignedFacetIndex hp
        (localVertexMap hp N L a o.1) o.2 :=
      EquivariantPrismGlobalCancellation.signatureWeight_facetSignature
        hp N L a o
    _ = RefinedAffineMap.localIndex hp (N + L) F
        (endpointTopCell hp N L q eta) :=
      ExplicitAffineRelativeCollar.unsignedFacetIndex_eq_refinedLocalIndex
        hp (localVertexMap hp N L a o.1) o.2
        (N + L) F (endpointTopCell hp N L q eta)
        hvertex haffine

private theorem upper_realizedFacetWeight_eq_localIndex
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (F : RefinedAffineMap.ContinuousCoordinateMap p)
    (q : TopCell hp N) (eta : RefinementWord p L)
    (hfix : ∀ i : Fin p,
      F (endpointSpatialMap hp N L q eta
          (stdSimplex.vertex
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) =
        endpointInterpolant hp N L EndpointSide.upper a
          (endpointSpatialMap hp N L q eta
            (stdSimplex.vertex
              (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)))) :
    EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.upperEndpointMap
          (endpointSpatialMap hp N L q eta)) =
      RefinedAffineMap.localIndex hp (N + L) F
        (endpointTopCell hp N L q eta) := by
  let o :=
    RelativeCollarMiddlePrismEndpointsCore.upperOccurrence hp N L q eta

  have hmap :
      EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap
          hp N L o =
        EquivariantPrismNonhorizontalCancellation.upperEndpointMap
          (endpointSpatialMap hp N L q eta) := by
    simpa [o] using
      RelativeCollarMiddlePrismEndpointsCore.upperOccurrenceFacetMap_eq
        hp N L q eta

  have hvertex : ∀ i : Fin p,
      AffinePositiveRayBoundary.VertexMap.facetValue
          (localVertexMap hp N L a o.1) o.2 i =
        RefinedAffineMap.vertexValue hp (N + L) F
          (endpointTopCell hp N L q eta)
          (ExplicitAffineRelativeCollar.refinedVertexIndex hp i) := by
    intro i
    rw [
      ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex
    ]
    rw [facetCoordinateIndex_eq_endpointIndex hp i]
    symm
    have h :=
      (hfix i).trans
        (endpointInterpolant_vertexValue
          hp N L EndpointSide.upper a q eta i)
    change F (RefinedAffineMap.vertex hp (N + L)
        (endpointTopCell hp N L q eta)
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) =
      vectorValue hp N L a (sampleVertex hp N L
        ((endpointOccurrence hp N L EndpointSide.upper q eta).1,
          (endpointOccurrence hp N L EndpointSide.upper q eta).2.succAbove i))
    simpa [endpointSpatialMap_eq_chart, RefinedAffineMap.vertex] using h

  have haffine : ∀ w : StandardSimplex (p - 1),
      AffinePositiveRayBoundary.VertexMap.facetAffineValue
          (localVertexMap hp N L a o.1) o.2 w =
        RefinedAffineMap.value hp (N + L) F
          (endpointTopCell hp N L q eta) w := by
    intro w
    funext j
    unfold AffinePositiveRayBoundary.VertexMap.facetAffineValue
      RefinedAffineMap.value
    rw [← ExplicitAffineRelativeCollar.sum_refinedVertexIndex hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [
      ExplicitAffineRelativeCollar.refinedVertexIndex_eq_facetCoordinateIndex
    ]
    congr 1
    exact congrFun (hvertex i) j

  calc
    EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.upperEndpointMap
          (endpointSpatialMap hp N L q eta)) =
      EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
        hp N L a
        (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap
          hp N L o) := by
            rw [hmap]
    _ = EquivariantPrismGlobalCancellation.signatureWeight
        hp N L a
        (EquivariantPrismGlobalCancellation.facetSignature hp N L o) :=
      EquivariantPrismNonhorizontalCancellation.realizedFacetWeight_occurrence
        hp N L a o
    _ = unsignedFacetIndex hp
        (localVertexMap hp N L a o.1) o.2 :=
      EquivariantPrismGlobalCancellation.signatureWeight_facetSignature
        hp N L a o
    _ = RefinedAffineMap.localIndex hp (N + L) F
        (endpointTopCell hp N L q eta) :=
      ExplicitAffineRelativeCollar.unsignedFacetIndex_eq_refinedLocalIndex
        hp (localVertexMap hp N L a o.1) o.2
        (N + L) F (endpointTopCell hp N L q eta)
        hvertex haffine

/-- The induced lower horizontal count is the stable lower approximation count. -/
theorem RelativeResult.lower_zeroCount_eq_endpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : RelativeResult hp N L H m) :
    R.lower.zeroCount =
      lowerEndpointRefinedCount hp N L R.prism.assignment := by
  classical
  unfold StableRegularApproximation.zeroCount RegularApproximation.zeroCount
  unfold RefinedAffineMap.zeroCount lowerEndpointRefinedCount
  rcases R.boundaryFixed with ⟨hlev, _, hfix, _⟩
  rw [hlev]
  rw [← Equiv.sum_comp
    (RelativeCollarMiddlePrismEndpoints.splitTopCellEquiv hp N L).symm]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro orbit horbit
  apply Finset.sum_congr rfl
  intro rho hrho
  let q : TopCell hp N := (orbit, rho)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta heta
  change
    RefinedAffineMap.coefficient hp (N + L)
          (endpointTopCell hp N L q eta) *
        RefinedAffineMap.localIndex hp (N + L) R.lower.map
          (endpointTopCell hp N L q eta) =
      RefinedAffineMap.coefficient hp N q *
        (RefinedAffineMap.subdivisionSign L eta *
          EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
            hp N L R.prism.assignment
            (EquivariantPrismNonhorizontalCancellation.lowerEndpointMap
              (endpointSpatialMap hp N L q eta)))

  rw [
    RelativeCollarMiddlePrismEndpoints.coefficient_endpointTopCell,
    lower_realizedFacetWeight_eq_localIndex
      hp N L R.prism.assignment R.lower.map q eta (hfix q eta)
  ]
  ring

/-- The induced upper horizontal count is the stable upper approximation count. -/
theorem RelativeResult.upper_zeroCount_eq_endpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : RelativeResult hp N L H m) :
    R.upper.zeroCount =
      upperEndpointRefinedCount hp N L R.prism.assignment := by
  classical
  unfold StableRegularApproximation.zeroCount RegularApproximation.zeroCount
  unfold RefinedAffineMap.zeroCount upperEndpointRefinedCount
  rcases R.boundaryFixed with ⟨_, hlev, _, hfix⟩
  rw [hlev]
  rw [← Equiv.sum_comp
    (RelativeCollarMiddlePrismEndpoints.splitTopCellEquiv hp N L).symm]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro orbit horbit
  apply Finset.sum_congr rfl
  intro rho hrho
  let q : TopCell hp N := (orbit, rho)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta heta
  change
    RefinedAffineMap.coefficient hp (N + L)
          (endpointTopCell hp N L q eta) *
        RefinedAffineMap.localIndex hp (N + L) R.upper.map
          (endpointTopCell hp N L q eta) =
      RefinedAffineMap.coefficient hp N q *
        (RefinedAffineMap.subdivisionSign L eta *
          EquivariantPrismNonhorizontalCancellation.realizedFacetWeight
            hp N L R.prism.assignment
            (EquivariantPrismNonhorizontalCancellation.upperEndpointMap
              (endpointSpatialMap hp N L q eta)))

  rw [
    RelativeCollarMiddlePrismEndpoints.coefficient_endpointTopCell,
    upper_realizedFacetWeight_eq_localIndex
      hp N L R.prism.assignment R.upper.map q eta (hfix q eta)
  ]
  ring

/-- The two constructed stable endpoint approximations have equal positive-ray counts. -/
theorem RelativeResult.stable_zeroCount_eq
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) (R : RelativeResult hp N L H m) :
    R.lower.zeroCount = R.upper.zeroCount := by
  rw [R.lower_zeroCount_eq_endpointRefinedCount hp N L H m,
    R.upper_zeroCount_eq_endpointRefinedCount hp N L H m]
  exact EquivariantPrismHorizontalEndpointIdentification.Result.lowerEndpointRefinedCount_eq_upperEndpointRefinedCount
    hp N L H m R.prism

end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
