/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericityPolynomials
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Explicit affine relative collars and boundary-restricted genericity polynomials

This module defines the affine-cell interface used by the relative-cobordism construction.

A `RelativeAffineCellSystem` is finite proof-carrying data for a genuine simplicial cylinder:
its top cells are prime-orbit representatives with ordered geometric vertices, injective affine
charts, and coefficients.  Prime equivariance is reconstructed from symmetry-decorated local
vertex occurrences rather than by imposing an action on the chosen orbit representatives.  A `FoxNeuwirthRelativeAffineCollar` adds the exact signed facet-incidence formula
for independently subdivided lower and upper boundaries.

The second half of the file constructs the global point-coordinate orbit quotient directly from
those explicit cells.  Horizontal parameter orbits are frozen.  All other interior and spatial-side
orbits remain movable.  Facet-determinant and codimension-two-minor polynomials are then restricted
to the movable polynomial ring.  Evaluation of a restricted polynomial is proved to be evaluation
of the corresponding determinant after replacing only movable data.

Existence of the relative barycentric cylinder and nontriviality of the restricted polynomials
are handled by the dedicated geometric and boundary-aware algebraic modules. Purely horizontal
codimension-two minors are governed by stable endpoint transversality rather than the movable
genericity family.
-/

namespace NRR

open scoped BigOperators
open Geometry
open FoxNeuwirthOrderComplex
open MvPolynomial
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar

open EquivariantCoordinateHomotopy
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open AffinePositiveRayBoundary

variable {p : Nat}

/-- A cylinder point belongs to one of the two fixed horizontal boundary layers. -/
def IsHorizontalPoint (z : CylinderPoint p) : Prop :=
  z.time.1 = 0 ∨ z.time.1 = 1

/-! ## Genuine finite affine-cell data -/

/-- A finite family of nondegenerate affine `p`-simplex representatives in the realization
cylinder.  The representatives are already taken modulo prime symmetry; equivariant global vertex
parameters are reconstructed below by adjoining a symmetry decoration to every local occurrence.
The four level fields record the two fixed endpoint triangulations, a common interior level, and a
time-refinement level. -/
structure RelativeAffineCellSystem
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat) where
  lower_le_common : N₀ ≤ M
  upper_le_common : N₁ ≤ M

  /-- The finite type of affine cells forming the relative collar. -/
  Cell : Type
  cell_nonempty : Nonempty Cell
  instCellFintype : Fintype Cell
  instCellDecidableEq : DecidableEq Cell

  /-- The coefficient of each collar cell in the prime residue field. -/
  coefficient : Cell → ZMod p
  /-- The cylinder point assigned to each vertex of a collar cell. -/
  vertex : Cell → Fin (p + 1) → CylinderPoint p
  /-- The affine simplex chart parametrizing each collar cell. -/
  chart : Cell → Delta p → CylinderPoint p

  chart_vertex : ∀ q i, chart q (SphereOddDegree.FiniteSimplex.vertex i) = vertex q i
  chart_spatial_affine : ∀ q w c,
    (chart q w).spatial c =
      ∑ i : Fin (p + 1), w i * (vertex q i).spatial c
  chart_time_affine : ∀ q w,
    (chart q w).time.1 =
      ∑ i : Fin (p + 1), w i * (vertex q i).time.1
  chart_injective : ∀ q, Function.Injective (chart q)
  vertex_injective : ∀ q, Function.Injective (vertex q)
  vertex_orbit_injective : ∀ q (g : PrimeSymmetry p) i j,
    g • vertex q i = vertex q j → g = 1 ∧ i = j

attribute [instance]
  RelativeAffineCellSystem.instCellFintype
  RelativeAffineCellSystem.instCellDecidableEq

namespace RelativeAffineCellSystem

variable {hp : Nat.Prime p} {N₀ N₁ M L : Nat}
variable {hp : Nat.Prime p}
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- One local vertex occurrence of one explicit relative collar cell. -/
abbrev VertexSlot := C.Cell × Fin (p + 1)

instance vertexSlotFintype : Fintype C.VertexSlot := inferInstance
instance vertexSlotDecidableEq : DecidableEq C.VertexSlot := inferInstance

/-- One local facet occurrence, indexed by its omitted vertex. -/
abbrev FacetOccurrence := C.Cell × Fin (p + 1)

instance facetOccurrenceFintype : Fintype C.FacetOccurrence := inferInstance
instance facetOccurrenceDecidableEq : DecidableEq C.FacetOccurrence := inferInstance

/-- Geometric point at a local cell vertex occurrence. -/
def slotPoint (s : C.VertexSlot) : CylinderPoint p :=
  C.vertex s.1 s.2

/-- Ordered geometric vertex tuple of the facet obtained by omitting `o.2`. -/
def facetSignature (o : C.FacetOccurrence) : Fin p → CylinderPoint p :=
  fun i => C.vertex o.1 (o.2.succAbove i)

/-- Two facet occurrences represent the same oriented quotient facet when one ordered
geometric signature is the simultaneous prime translate of the other.  This is the facet-orbit
relation required by the Fox--Neuwirth orbit cycle: spatial side faces cancel after passage to the
prime quotient, not necessarily as identical facets of the chosen top-cell representatives. -/
noncomputable def facetSetoid : Setoid C.FacetOccurrence where
  r a b := ∃ g : PrimeSymmetry p,
    (fun i => g • C.facetSignature a i) = C.facetSignature b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by funext i; simp⟩
    · intro a b hab
      rcases hab with ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      funext i
      have hi := congrFun hg i
      rw [← hi]
      simp
    · intro a b c hab hbc
      rcases hab with ⟨g, hg⟩
      rcases hbc with ⟨h, hh⟩
      refine ⟨h * g, ?_⟩
      funext i
      rw [mul_smul, congrFun hg i, congrFun hh i]

/-- Finite ordered prime-orbit facets of the explicit relative collar. -/
abbrev Facet := Quotient C.facetSetoid

noncomputable instance facetFintype : Fintype C.Facet := Fintype.ofFinite _
noncomputable instance facetDecidableEq : DecidableEq C.Facet := Classical.decEq _

/-- Quotient facet represented by a local occurrence. -/
noncomputable def facetClass (o : C.FacetOccurrence) : C.Facet :=
  Quotient.mk _ o

/-- Alternating boundary sign attached to an omitted local vertex. -/
def alternatingSign (k : Fin (p + 1)) : ZMod p :=
  (-1 : ZMod p) ^ k.1

/-- Total signed incidence coefficient of one ordered prime-orbit facet. -/
noncomputable def facetIncidence (s : C.Facet) : ZMod p :=
  ∑ o : C.FacetOccurrence,
    if C.facetClass o = s then C.coefficient o.1 * alternatingSign o.2 else 0

/-- A local facet occurrence lies in the fixed lower horizontal boundary. -/
def IsLowerFacetOccurrence (o : C.FacetOccurrence) : Prop :=
  ∀ i : Fin p, (C.facetSignature o i).time.1 = 0

/-- A local facet occurrence lies in the fixed upper horizontal boundary. -/
def IsUpperFacetOccurrence (o : C.FacetOccurrence) : Prop :=
  ∀ i : Fin p, (C.facetSignature o i).time.1 = 1

/-- Lower-horizontal status is well-defined on ordered quotient-facet classes because
prime symmetry preserves the interval coordinate. -/
noncomputable def IsLowerFacet : C.Facet → Prop :=
  Quotient.lift C.IsLowerFacetOccurrence (by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    apply propext
    have htime : ∀ i : Fin p,
        (C.facetSignature a i).time.1 = (C.facetSignature b i).time.1 := by
      intro i
      have hi := congrArg (fun z : CylinderPoint p => z.time.1) (congrFun hg i)
      simpa using hi
    constructor
    · intro ha i
      rw [← htime i]
      exact ha i
    · intro hb i
      rw [htime i]
      exact hb i)

/-- Upper-horizontal status is well-defined on ordered quotient-facet classes because prime
symmetry preserves the interval coordinate. -/
noncomputable def IsUpperFacet : C.Facet → Prop :=
  Quotient.lift C.IsUpperFacetOccurrence (by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    apply propext
    have htime : ∀ i : Fin p,
        (C.facetSignature a i).time.1 = (C.facetSignature b i).time.1 := by
      intro i
      have hi := congrArg (fun z : CylinderPoint p => z.time.1) (congrFun hg i)
      simpa using hi
    constructor
    · intro ha i
      rw [← htime i]
      exact ha i
    · intro hb i
      rw [htime i]
      exact hb i)

/-- A geometric facet is horizontal when it belongs to either fixed endpoint boundary. -/
def IsHorizontalFacet (s : C.Facet) : Prop :=
  C.IsLowerFacet s ∨ C.IsUpperFacet s

end RelativeAffineCellSystem

/-- A proof-carrying relative affine collar.  The boundary coefficient fields encode the exact
upper-minus-lower horizontal boundary formula after all internal and side signatures are collected.
The structure does not assume pairwise cancellation: an arbitrary number of occurrences may share
a signature. -/
structure FoxNeuwirthRelativeAffineCollar
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat) where
  /-- The affine cell system underlying the relative collar. -/
  cells : RelativeAffineCellSystem hp N₀ N₁ M L
  /-- The coefficient assigned to each lower boundary facet. -/
  lowerBoundaryCoefficient : cells.Facet → ZMod p
  /-- The coefficient assigned to each upper boundary facet. -/
  upperBoundaryCoefficient : cells.Facet → ZMod p
  lower_zero_of_not_lower : ∀ s, ¬ cells.IsLowerFacet s → lowerBoundaryCoefficient s = 0
  upper_zero_of_not_upper : ∀ s, ¬ cells.IsUpperFacet s → upperBoundaryCoefficient s = 0
  incidence_eq_boundary : ∀ s,
    cells.facetIncidence s = upperBoundaryCoefficient s - lowerBoundaryCoefficient s

namespace FoxNeuwirthRelativeAffineCollar

variable {hp : Nat.Prime p} {N₀ N₁ M L : Nat}
variable (C : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L)

/-- Every nonhorizontal geometric facet has zero total signed incidence. -/
theorem nonhorizontal_incidence_zero
    (s : C.cells.Facet) (hs : ¬ C.cells.IsHorizontalFacet s) :
    C.cells.facetIncidence s = 0 := by
  have hlower : ¬ C.cells.IsLowerFacet s := by
    intro h
    exact hs (Or.inl h)
  have hupper : ¬ C.cells.IsUpperFacet s := by
    intro h
    exact hs (Or.inr h)
  rw [C.incidence_eq_boundary s,
    C.lower_zero_of_not_lower s hlower,
    C.upper_zero_of_not_upper s hupper]
  simp

end FoxNeuwirthRelativeAffineCollar

/-! ## Exact endpoint identification -/

/-- Embed a realization point in the lower horizontal boundary of the cylinder. -/
def lowerCylinderPoint (x : Realization p) : CylinderPoint p :=
  ⟨x, ⟨0, by simp⟩⟩

/-- Embed a realization point in the upper horizontal boundary of the cylinder. -/
def upperCylinderPoint (x : Realization p) : CylinderPoint p :=
  ⟨x, ⟨1, by simp⟩⟩

@[simp] theorem lowerCylinderPoint_time (x : Realization p) :
    (lowerCylinderPoint x).time.1 = 0 := rfl

@[simp] theorem upperCylinderPoint_time (x : Realization p) :
    (upperCylinderPoint x).time.1 = 1 := rfl

/-- A relative affine collar whose horizontal boundary chain is exactly the independently refined
Fox--Neuwirth orbit cycle.  The endpoint maps need not be injective: several refined top cells may
represent the same geometric prime-orbit facet, and their coefficients are then collected by the
pairing identities.  This is the chain-level identification required by Stokes and avoids imposing
an artificial choice of a unique quotient-facet representative. -/
structure EndpointIdentifiedRelativeAffineCollar
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat)
    extends FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L where
  /-- Identify each lower refined top cell with its collar boundary facet. -/
  lowerFacet : RefinedAffineMap.TopCell hp N₀ → cells.Facet
  /-- Identify each upper refined top cell with its collar boundary facet. -/
  upperFacet : RefinedAffineMap.TopCell hp N₁ → cells.Facet

  lowerFacet_isLower : ∀ q, cells.IsLowerFacet (lowerFacet q)
  upperFacet_isUpper : ∀ q, cells.IsUpperFacet (upperFacet q)
  lowerFacet_exhaustive : ∀ s, cells.IsLowerFacet s → ∃ q, lowerFacet q = s
  upperFacet_exhaustive : ∀ s, cells.IsUpperFacet s → ∃ q, upperFacet q = s

  lowerBoundaryPairing_eq : ∀ W : cells.Facet → ZMod p,
    (∑ s : cells.Facet, lowerBoundaryCoefficient s * W s) =
      ∑ q : RefinedAffineMap.TopCell hp N₀,
        RefinedAffineMap.coefficient hp N₀ q * W (lowerFacet q)
  upperBoundaryPairing_eq : ∀ W : cells.Facet → ZMod p,
    (∑ s : cells.Facet, upperBoundaryCoefficient s * W s) =
      ∑ q : RefinedAffineMap.TopCell hp N₁,
        RefinedAffineMap.coefficient hp N₁ q * W (upperFacet q)

  lowerFacetOccurrenceVertex_eq : ∀ q o,
    cells.facetClass o = lowerFacet q →
      ∃ g : PrimeSymmetry p, ∀ i, cells.facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N₀ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))
  upperFacetOccurrenceVertex_eq : ∀ q o,
    cells.facetClass o = upperFacet q →
      ∃ g : PrimeSymmetry p, ∀ i, cells.facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N₁ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))

namespace EndpointIdentifiedRelativeAffineCollar

variable {hp : Nat.Prime p} {N₀ N₁ M L : Nat}
variable (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M L)

/-- Every lower horizontal quotient facet is represented by at least one level-`N₀` refined orbit
cell.  Uniqueness is intentionally not required; the endpoint chain pairing collects repeated
geometric representatives with their signed coefficients. -/
theorem exists_lowerTopCell
    (s : C.cells.Facet) (hs : C.cells.IsLowerFacet s) :
    ∃ q : RefinedAffineMap.TopCell hp N₀, C.lowerFacet q = s :=
  C.lowerFacet_exhaustive s hs

/-- Every upper horizontal quotient facet is represented by at least one level-`N₁` refined orbit
cell. -/
theorem exists_upperTopCell
    (s : C.cells.Facet) (hs : C.cells.IsUpperFacet s) :
    ∃ q : RefinedAffineMap.TopCell hp N₁, C.upperFacet q = s :=
  C.upperFacet_exhaustive s hs

end EndpointIdentifiedRelativeAffineCollar

/-- Existence proposition for the genuine relative affine collar.  In contrast with the previous
raw interface, this proposition cannot be inhabited by an empty cell family or by a collar whose
horizontal boundary is unrelated to the supplied Fox--Neuwirth subdivision levels. -/
def RelativeAffineCollarExists
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat) : Prop :=
  Nonempty (EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M L)

/-! ## Global vertices and boundary-frozen parameters -/

namespace Parameters

variable {hp : Nat.Prime p} {N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Symmetry-decorated local vertex occurrences. -/
abbrev CoverVertexSlot := PrimeSymmetry p × C.VertexSlot

noncomputable instance coverVertexSlotFintype : Fintype (CoverVertexSlot hp C) := inferInstance
instance coverVertexSlotDecidableEq : DecidableEq (CoverVertexSlot hp C) := inferInstance

/-- Geometric point represented by a decorated local occurrence. -/
def coverPoint (s : CoverVertexSlot hp C) : CylinderPoint p :=
  s.1 • C.slotPoint s.2

/-- Equality of geometric cylinder points identifies duplicate local occurrences. -/
noncomputable def coverVertexSetoid : Setoid (CoverVertexSlot hp C) where
  r a b := coverPoint hp C a = coverPoint hp C b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Finite global vertices of the explicit relative affine collar. -/
abbrev GlobalVertex := Quotient (coverVertexSetoid hp C)

noncomputable instance globalVertexFintype : Fintype (GlobalVertex hp C) :=
  Fintype.ofFinite _

noncomputable instance globalVertexDecidableEq : DecidableEq (GlobalVertex hp C) :=
  Classical.decEq _

/-- Left multiplication on the symmetry decoration. -/
def actCoverVertex
    (g : PrimeSymmetry p) (s : CoverVertexSlot hp C) : CoverVertexSlot hp C :=
  (g * s.1, s.2)

@[simp] theorem coverPoint_actCoverVertex
    (g : PrimeSymmetry p) (s : CoverVertexSlot hp C) :
    coverPoint hp C (actCoverVertex hp C g s) = g • coverPoint hp C s := by
  simp [coverPoint, actCoverVertex, mul_smul]

/-- Prime symmetry acts on global relative-collar vertices. -/
noncomputable instance globalVertexAction :
    MulAction (PrimeSymmetry p) (GlobalVertex hp C) where
  smul g := Quotient.map (actCoverVertex hp C g) (by
    intro a b hab
    change coverPoint hp C (actCoverVertex hp C g a) =
      coverPoint hp C (actCoverVertex hp C g b)
    simpa using congrArg (fun z : CylinderPoint p => g • z) hab)
  one_smul x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp C (actCoverVertex hp C 1 s) = coverPoint hp C s
    simp
  mul_smul g h x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp C (actCoverVertex hp C (g * h) s) =
      coverPoint hp C (actCoverVertex hp C g (actCoverVertex hp C h s))
    simp [mul_smul]

/-- Actual geometric point represented by a global vertex. -/
noncomputable def globalPoint : GlobalVertex hp C → CylinderPoint p :=
  Quotient.lift (coverPoint hp C) (by
    intro a b hab
    exact hab)

@[simp] theorem globalPoint_mk (s : CoverVertexSlot hp C) :
    globalPoint hp C (Quotient.mk _ s) = coverPoint hp C s := rfl

@[simp] theorem globalPoint_smul
    (g : PrimeSymmetry p) (x : GlobalVertex hp C) :
    globalPoint hp C (g • x) = g • globalPoint hp C x := by
  refine Quotient.inductionOn x ?_
  intro s
  change coverPoint hp C (actCoverVertex hp C g s) = g • coverPoint hp C s
  exact coverPoint_actCoverVertex hp C g s

/-- Global vertex represented by an undecorated local slot. -/
noncomputable def sampleVertex (s : C.VertexSlot) : GlobalVertex hp C :=
  Quotient.mk _ ((1 : PrimeSymmetry p), s)

@[simp] theorem globalPoint_sampleVertex (s : C.VertexSlot) :
    globalPoint hp C (sampleVertex hp C s) = C.slotPoint s := by
  change coverPoint hp C ((1 : PrimeSymmetry p), s) = C.slotPoint s
  simp [coverPoint]

/-- Geometrically equal local slots determine the same global sampled vertex. -/
theorem sampleVertex_eq_of_slotPoint_eq
    {s t : C.VertexSlot} (h : C.slotPoint s = C.slotPoint t) :
    sampleVertex hp C s = sampleVertex hp C t := by
  apply Quotient.sound
  change coverPoint hp C ((1 : PrimeSymmetry p), s) =
    coverPoint hp C ((1 : PrimeSymmetry p), t)
  simpa [coverPoint] using h

/-- Point-coordinate sites before quotienting by diagonal prime symmetry. -/
abbrev ScalarSite := GlobalVertex hp C × Fin p

/-- One scalar parameter per diagonal prime orbit. -/
abbrev Parameter :=
  MulAction.orbitRel.Quotient (PrimeSymmetry p) (ScalarSite hp C)

noncomputable instance parameterFintype : Fintype (Parameter hp C) := Fintype.ofFinite _
noncomputable instance parameterDecidableEq : DecidableEq (Parameter hp C) := Classical.decEq _

/-- A global vertex is frozen precisely on one of the two horizontal boundaries. -/
def IsFrozenVertex (x : GlobalVertex hp C) : Prop :=
  IsHorizontalPoint (globalPoint hp C x)

@[simp] theorem isFrozenVertex_smul
    (g : PrimeSymmetry p) (x : GlobalVertex hp C) :
    IsFrozenVertex hp C (g • x) ↔ IsFrozenVertex hp C x := by
  simp [IsFrozenVertex, IsHorizontalPoint]

/-- Frozen status is well-defined on diagonal parameter orbits. -/
noncomputable def IsFrozenParameter : Parameter hp C → Prop :=
  Quotient.lift
    (fun s : ScalarSite hp C => IsFrozenVertex hp C s.1)
    (by
      intro a b hab
      change MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C) a b at hab
      rw [MulAction.orbitRel_apply] at hab
      rcases hab with ⟨g, rfl⟩
      simpa using propext (isFrozenVertex_smul hp C g b.1))

/-- Frozen horizontal scalar parameter orbits. -/
abbrev FrozenParameter := {q : Parameter hp C // IsFrozenParameter hp C q}

/-- Movable interior and spatial-side scalar parameter orbits. -/
abbrev MovableParameter := {q : Parameter hp C // ¬ IsFrozenParameter hp C q}

noncomputable instance frozenParameterFintype : Fintype (FrozenParameter hp C) :=
  Fintype.ofFinite _

noncomputable instance movableParameterFintype : Fintype (MovableParameter hp C) :=
  Fintype.ofFinite _

/-- A full compatible equivariant scalar assignment. -/
abbrev Assignment := Parameter hp C → Real

/-- Replace only movable values, retaining the horizontal boundary assignment literally. -/
noncomputable def replaceMovable
    (base : Assignment hp C) (move : MovableParameter hp C → Real) : Assignment hp C := by
  classical
  exact fun q => if h : IsFrozenParameter hp C q then base q else move ⟨q, h⟩

@[simp] theorem replaceMovable_eq_base
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    {q : Parameter hp C} (hq : IsFrozenParameter hp C q) :
    replaceMovable hp C base move q = base q := by
  simp [replaceMovable, hq]

@[simp] theorem replaceMovable_eq_move
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (q : MovableParameter hp C) :
    replaceMovable hp C base move q.1 = move q := by
  simp [replaceMovable, q.2]

/-- Full polynomial ring before fixing the horizontal boundary. -/
abbrev FullPolynomialRing := MvPolynomial (Parameter hp C) Real

/-- Polynomial ring in movable parameter orbits only. -/
abbrev MovablePolynomialRing := MvPolynomial (MovableParameter hp C) Real

/-- Substitute frozen variables by their base constants and retain movable variables. -/
noncomputable def relativeVariable
    (base : Assignment hp C) (q : Parameter hp C) : MovablePolynomialRing hp C := by
  classical
  exact if h : IsFrozenParameter hp C q then MvPolynomial.C (base q) else X ⟨q, h⟩

/-- Restriction homomorphism to the boundary-relative movable polynomial ring. -/
noncomputable def restrictPolynomial
    (base : Assignment hp C) : FullPolynomialRing hp C →+* MovablePolynomialRing hp C :=
  MvPolynomial.eval₂Hom MvPolynomial.C (relativeVariable hp C base)

@[simp] theorem eval_relativeVariable
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (q : Parameter hp C) :
    MvPolynomial.eval move (relativeVariable hp C base q) =
      replaceMovable hp C base move q := by
  by_cases hq : IsFrozenParameter hp C q
  · simp [relativeVariable, replaceMovable, hq]
  · simp [relativeVariable, replaceMovable, hq]

/-- Evaluation after restriction equals evaluation at the reconstructed boundary-relative full
assignment. -/
theorem eval_restrictPolynomial
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (P : FullPolynomialRing hp C) :
    MvPolynomial.eval move (restrictPolynomial hp C base P) =
      MvPolynomial.eval (replaceMovable hp C base move) P := by
  change ((MvPolynomial.eval move).comp (restrictPolynomial hp C base)) P = _
  have hhom : (MvPolynomial.eval move).comp (restrictPolynomial hp C base) =
      MvPolynomial.eval (replaceMovable hp C base move) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [restrictPolynomial]
    · intro q
      simp only [RingHom.comp_apply, restrictPolynomial, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval_X]
      exact eval_relativeVariable hp C base move q
  rw [hhom]

/-- Scalar value reconstructed at a global vertex. -/
noncomputable def scalarValue
    (a : Assignment hp C) (x : GlobalVertex hp C) (j : Fin p) : Real :=
  a (Quotient.mk _ (x, j))

/-- Vector value reconstructed at a global vertex. -/
noncomputable def vectorValue
    (a : Assignment hp C) (x : GlobalVertex hp C) : Fin p → Real :=
  fun j => scalarValue hp C a x j

/-- Every assignment reconstructs a prime-equivariant vector assignment. -/
theorem vectorValue_smul
    (a : Assignment hp C) (g : PrimeSymmetry p) (x : GlobalVertex hp C) :
    vectorValue hp C a (g • x) = g • vectorValue hp C a x := by
  funext j
  rw [PrimeSymmetry.smul_coordinate_apply]
  let j₀ : Fin p := g⁻¹ • j
  have hsite :
      Quotient.mk (MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C))
          (g • x, j) =
        Quotient.mk (MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C))
          (x, j₀) := by
    apply Quotient.sound
    change MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C) (g • x, j) (x, j₀)
    rw [MulAction.orbitRel_apply]
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · simp [j₀]
  exact congrArg a hsite

/-- Scalar endpoint-adjusted sample attached to one point-coordinate site.  Interior sites
sample the supplied zero-free homotopy.  Sites on the two horizontal boundaries instead sample the
actual endpoint approximations whose refined counts are being compared. -/
noncomputable def endpointAdjustedSiteValue
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map)
    (s : ScalarSite hp C) : Real :=
  if _h₀ : (globalPoint hp C s.1).time.1 = 0 then
    A₀.map (globalPoint hp C s.1).spatial s.2
  else if _h₁ : (globalPoint hp C s.1).time.1 = 1 then
    A₁.map (globalPoint hp C s.1).spatial s.2
  else
    H.map (CylinderPoint.toProd (globalPoint hp C s.1)) s.2

/-- Endpoint-adjusted samples are constant on diagonal prime orbits. -/
theorem endpointAdjustedSiteValue_eq_of_orbitRel
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map)
    {a b : ScalarSite hp C}
    (hab : MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C) a b) :
    endpointAdjustedSiteValue hp C H A₀ A₁ a =
      endpointAdjustedSiteValue hp C H A₀ A₁ b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, hgab⟩
  subst a
  have htime : (globalPoint hp C (g • b).1).time.1 =
      (globalPoint hp C b.1).time.1 := by
    change (globalPoint hp C (g • b.1)).time.1 = _
    rw [globalPoint_smul]
    rfl
  simp only [endpointAdjustedSiteValue]
  rw [htime]
  split_ifs
  · have heq := A₀.equivariant g (globalPoint hp C b.1).spatial
    have hj := congrFun heq (g • b.2)
    simpa [PrimeSymmetry.smul_coordinate_apply, PrimeSymmetry.smul_label] using hj
  · have heq := A₁.equivariant g (globalPoint hp C b.1).spatial
    have hj := congrFun heq (g • b.2)
    simpa [PrimeSymmetry.smul_coordinate_apply, PrimeSymmetry.smul_label] using hj
  · have heq := H.equivariant g (globalPoint hp C b.1).spatial
      (globalPoint hp C b.1).time
    have hj := congrFun heq (g • b.2)
    simpa [CylinderPoint.toProd, PrimeSymmetry.smul_coordinate_apply,
      PrimeSymmetry.smul_label] using hj

/-- Distinguished compatible assignment which agrees with the two supplied endpoint
approximations on the horizontal boundary and with the zero-free homotopy at every other sampled
vertex. -/
noncomputable def endpointAdjustedAssignment
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map) : Assignment hp C :=
  fun q => Quotient.liftOn q (endpointAdjustedSiteValue hp C H A₀ A₁) (by
    intro a b hab
    exact endpointAdjustedSiteValue_eq_of_orbitRel hp C H A₀ A₁ hab)

/-- Reconstructing the endpoint-adjusted assignment on the lower horizontal boundary gives the
supplied lower approximation exactly. -/
theorem vectorValue_endpointAdjustedAssignment_lower
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx : (globalPoint hp C x).time.1 = 0) :
    vectorValue hp C (endpointAdjustedAssignment hp C H A₀ A₁) x =
      A₀.map (globalPoint hp C x).spatial := by
  funext j
  simp [vectorValue, scalarValue, endpointAdjustedAssignment,
    endpointAdjustedSiteValue, hx]

/-- Reconstructing the endpoint-adjusted assignment on the upper horizontal boundary gives the
supplied upper approximation exactly. -/
theorem vectorValue_endpointAdjustedAssignment_upper
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx : (globalPoint hp C x).time.1 = 1) :
    vectorValue hp C (endpointAdjustedAssignment hp C H A₀ A₁) x =
      A₁.map (globalPoint hp C x).spatial := by
  have hx₀ : (globalPoint hp C x).time.1 ≠ 0 := by
    rw [hx]
    norm_num
  funext j
  simp [vectorValue, scalarValue, endpointAdjustedAssignment,
    endpointAdjustedSiteValue, hx]

/-- Away from both horizontal boundaries, reconstructing the endpoint-adjusted assignment gives
the original homotopy sample. -/
theorem vectorValue_endpointAdjustedAssignment_interior
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.RegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.RegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx₀ : (globalPoint hp C x).time.1 ≠ 0)
    (hx₁ : (globalPoint hp C x).time.1 ≠ 1) :
    vectorValue hp C (endpointAdjustedAssignment hp C H A₀ A₁) x =
      H.map (CylinderPoint.toProd (globalPoint hp C x)) := by
  funext j
  simp [vectorValue, scalarValue, endpointAdjustedAssignment,
    endpointAdjustedSiteValue, hx₀, hx₁]

/-- Local values agree whenever two local slots represent the same geometric point. -/
theorem localValue_eq_of_slotPoint_eq
    (a : Assignment hp C) {s t : C.VertexSlot}
    (h : C.slotPoint s = C.slotPoint t) :
    vectorValue hp C a (sampleVertex hp C s) =
      vectorValue hp C a (sampleVertex hp C t) := by
  rw [sampleVertex_eq_of_slotPoint_eq hp C h]

/-- Replacing movable parameters leaves a horizontal local vertex unchanged. -/
theorem replaceMovable_horizontal_localValue
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (s : C.VertexSlot)
    (hs : IsHorizontalPoint (C.slotPoint s)) :
    vectorValue hp C (replaceMovable hp C base move) (sampleVertex hp C s) =
      vectorValue hp C base (sampleVertex hp C s) := by
  funext j
  apply replaceMovable_eq_base hp C
  change IsFrozenVertex hp C (sampleVertex hp C s)
  simpa [IsFrozenVertex] using hs

end Parameters

/-! ## Full and boundary-restricted determinant polynomials -/

namespace Polynomials

variable {hp : Nat.Prime p} {N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

open Parameters

/-- Coordinate variable attached to one global vertex and one output coordinate. -/
noncomputable def scalarPolynomial
    (x : GlobalVertex hp C) (j : Fin p) : FullPolynomialRing hp C :=
  X (Quotient.mk _ (x, j))

/-- Polynomial coordinate vector at a global vertex. -/
noncomputable def vectorPolynomial
    (x : GlobalVertex hp C) : Fin p → FullPolynomialRing hp C :=
  fun j => scalarPolynomial hp C x j

/-- Polynomial coordinate vector at one local explicit-cell vertex. -/
noncomputable def localVertexPolynomial
    (q : C.Cell) (i : Fin (p + 1)) : Fin p → FullPolynomialRing hp C :=
  vectorPolynomial hp C (sampleVertex hp C (q, i))

/-- Fixed deviation coordinate in the full polynomial ring. -/
noncomputable def deviationPolynomial
    (y : Fin p → FullPolynomialRing hp C) (r : Fin (p - 1)) :
    FullPolynomialRing hp C :=
  y (ReferenceAffineOrbitCount.coordinateLabel hp r) -
    y (ReferenceAffineOrbitCount.lastLabel hp)

/-- Real local vertex map reconstructed from an assignment. -/
noncomputable def localVertexMap
    (a : Assignment hp C) (q : C.Cell) : VertexMap p where
  value i := vectorValue hp C a (sampleVertex hp C (q, i))

/-- Evaluation at a full assignment as a ring homomorphism. -/
noncomputable def assignmentEvalHom
    (a : Assignment hp C) : FullPolynomialRing hp C →+* Real :=
  MvPolynomial.eval₂Hom (RingHom.id Real) a

@[simp] theorem eval_scalarPolynomial
    (a : Assignment hp C) (x : GlobalVertex hp C) (j : Fin p) :
    MvPolynomial.eval a (scalarPolynomial hp C x j) =
      Parameters.scalarValue hp C a x j := by
  simp [scalarPolynomial, Parameters.scalarValue]

@[simp] theorem eval_vectorPolynomial
    (a : Assignment hp C) (x : GlobalVertex hp C) (j : Fin p) :
    MvPolynomial.eval a (vectorPolynomial hp C x j) =
      Parameters.vectorValue hp C a x j := by
  simp [vectorPolynomial, Parameters.vectorValue]

@[simp] theorem eval_localVertexPolynomial
    (a : Assignment hp C) (q : C.Cell) (i : Fin (p + 1)) (j : Fin p) :
    MvPolynomial.eval a (localVertexPolynomial hp C q i j) =
      vectorValue hp C a (sampleVertex hp C (q, i)) j := by
  simp [localVertexPolynomial]

@[simp] theorem eval_deviationPolynomial
    (a : Assignment hp C)
    (y : Fin p → FullPolynomialRing hp C) (r : Fin (p - 1)) :
    MvPolynomial.eval a (deviationPolynomial hp C y r) =
      VertexMap.deviation hp (fun j => MvPolynomial.eval a (y j)) r := by
  simp [deviationPolynomial, VertexMap.deviation]

/-- Polynomial augmented deviation matrix on the facet omitting `k`. -/
noncomputable def facetMatrixPolynomial
    (q : C.Cell) (k : Fin (p + 1)) :
    Matrix (Fin p) (Fin p) (FullPolynomialRing hp C) :=
  fun r i => Fin.lastCases (MvPolynomial.C (1 : Real))
    (fun s => deviationPolynomial hp C
      (localVertexPolynomial hp C q (k.succAbove i)) s)
    (VertexMap.augmentedRowEquiv hp r)

/-- Full-variable facet determinant polynomial. -/
noncomputable def facetDeterminantPolynomial
    (q : C.Cell) (k : Fin (p + 1)) : FullPolynomialRing hp C :=
  Matrix.det (facetMatrixPolynomial hp C q k)

/-- Evaluation of the polynomial facet matrix gives the real facet matrix. -/
theorem map_facetMatrixPolynomial
    (a : Assignment hp C) (q : C.Cell) (k : Fin (p + 1)) :
    (assignmentEvalHom hp C a).mapMatrix (facetMatrixPolynomial hp C q k) =
      VertexMap.facetMatrix hp (localVertexMap hp C a q) k := by
  ext r i
  change assignmentEvalHom hp C a
      (Fin.lastCases (MvPolynomial.C (1 : Real))
        (fun s => deviationPolynomial hp C
          (localVertexPolynomial hp C q (k.succAbove i)) s)
        (VertexMap.augmentedRowEquiv hp r)) =
    Fin.lastCases (1 : Real)
      (fun s => VertexMap.deviation hp
        ((localVertexMap hp C a q).facetValue k i) s)
      (VertexMap.augmentedRowEquiv hp r)
  generalize hr : VertexMap.augmentedRowEquiv hp r = r'
  refine Fin.lastCases ?_ (fun s => ?_) r'
  · simp [assignmentEvalHom]
  · simp [VertexMap.facetValue, localVertexMap, assignmentEvalHom]

/-- Evaluation of the full facet polynomial is the actual local facet determinant. -/
theorem eval_facetDeterminantPolynomial
    (a : Assignment hp C) (q : C.Cell) (k : Fin (p + 1)) :
    MvPolynomial.eval a (facetDeterminantPolynomial hp C q k) =
      VertexMap.facetDeterminant hp (localVertexMap hp C a q) k := by
  change assignmentEvalHom hp C a
      (Matrix.det (facetMatrixPolynomial hp C q k)) = _
  rw [RingHom.map_det]
  rw [map_facetMatrixPolynomial]
  rfl

/-- Ordered codimension-two face type. -/
abbrev CodimTwoFace (p : Nat) :=
  EquivariantPrismGenericityPolynomials.CodimTwoFace p

/-- Retained local vertex after the two ordered omissions. -/
def codimTwoVertex
    (f : CodimTwoFace p) (i : Fin (p - 1)) : Fin (p + 1) :=
  EquivariantPrismGenericityPolynomials.codimTwoVertex hp f i

/-- Polynomial deviation matrix on an ordered codimension-two face. -/
noncomputable def codimTwoDeviationMatrixPolynomial
    (q : C.Cell) (f : CodimTwoFace p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) (FullPolynomialRing hp C) :=
  fun r i => deviationPolynomial hp C
    (localVertexPolynomial hp C q (codimTwoVertex hp f i)) r

/-- Full-variable codimension-two deviation minor. -/
noncomputable def codimTwoMinorPolynomial
    (q : C.Cell) (f : CodimTwoFace p) : FullPolynomialRing hp C :=
  Matrix.det (codimTwoDeviationMatrixPolynomial hp C q f)

/-- Corresponding real deviation matrix. -/
noncomputable def codimTwoDeviationMatrix
    (a : Assignment hp C) (q : C.Cell) (f : CodimTwoFace p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) Real :=
  fun r i => VertexMap.deviation hp
    (vectorValue hp C a (sampleVertex hp C (q, codimTwoVertex hp f i))) r

/-- Evaluation of the polynomial codimension-two matrix gives the real matrix. -/
theorem map_codimTwoDeviationMatrixPolynomial
    (a : Assignment hp C) (q : C.Cell) (f : CodimTwoFace p) :
    (assignmentEvalHom hp C a).mapMatrix
        (codimTwoDeviationMatrixPolynomial hp C q f) =
      codimTwoDeviationMatrix hp C a q f := by
  ext r i
  simp [codimTwoDeviationMatrixPolynomial, codimTwoDeviationMatrix, assignmentEvalHom]

/-- Evaluation of the full codimension-two polynomial is the actual determinant. -/
theorem eval_codimTwoMinorPolynomial
    (a : Assignment hp C) (q : C.Cell) (f : CodimTwoFace p) :
    MvPolynomial.eval a (codimTwoMinorPolynomial hp C q f) =
      Matrix.det (codimTwoDeviationMatrix hp C a q f) := by
  change assignmentEvalHom hp C a
      (Matrix.det (codimTwoDeviationMatrixPolynomial hp C q f)) = _
  rw [RingHom.map_det]
  rw [map_codimTwoDeviationMatrixPolynomial]

/-- Boundary-restricted facet determinant polynomial. -/
noncomputable def restrictedFacetDeterminantPolynomial
    (base : Assignment hp C) (q : C.Cell) (k : Fin (p + 1)) :
    MovablePolynomialRing hp C :=
  restrictPolynomial hp C base (facetDeterminantPolynomial hp C q k)

/-- Boundary-restricted codimension-two minor polynomial. -/
noncomputable def restrictedCodimTwoMinorPolynomial
    (base : Assignment hp C) (q : C.Cell) (f : CodimTwoFace p) :
    MovablePolynomialRing hp C :=
  restrictPolynomial hp C base (codimTwoMinorPolynomial hp C q f)

/-- Exact restricted evaluation identity for facet determinants. -/
theorem eval_restrictedFacetDeterminantPolynomial
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (q : C.Cell) (k : Fin (p + 1)) :
    MvPolynomial.eval move (restrictedFacetDeterminantPolynomial hp C base q k) =
      VertexMap.facetDeterminant hp
        (localVertexMap hp C (replaceMovable hp C base move) q) k := by
  rw [restrictedFacetDeterminantPolynomial, eval_restrictPolynomial]
  exact eval_facetDeterminantPolynomial hp C (replaceMovable hp C base move) q k

/-- Exact restricted evaluation identity for codimension-two minors. -/
theorem eval_restrictedCodimTwoMinorPolynomial
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (q : C.Cell) (f : CodimTwoFace p) :
    MvPolynomial.eval move (restrictedCodimTwoMinorPolynomial hp C base q f) =
      Matrix.det
        (codimTwoDeviationMatrix hp C (replaceMovable hp C base move) q f) := by
  rw [restrictedCodimTwoMinorPolynomial, eval_restrictPolynomial]
  exact eval_codimTwoMinorPolynomial hp C (replaceMovable hp C base move) q f

/-- An ordered codimension-two face is purely lower horizontal. -/
def IsLowerHorizontalCodimTwo
    (q : C.Cell) (f : CodimTwoFace p) : Prop :=
  ∀ i : Fin (p - 1), (C.vertex q (codimTwoVertex hp f i)).time.1 = 0

/-- An ordered codimension-two face is purely upper horizontal. -/
def IsUpperHorizontalCodimTwo
    (q : C.Cell) (f : CodimTwoFace p) : Prop :=
  ∀ i : Fin (p - 1), (C.vertex q (codimTwoVertex hp f i)).time.1 = 1

/-- Purely horizontal codimension-two faces are excluded from the movable full-minor family. -/
def IsPurelyHorizontalCodimTwo
    (q : C.Cell) (f : CodimTwoFace p) : Prop :=
  IsLowerHorizontalCodimTwo hp C q f ∨ IsUpperHorizontalCodimTwo hp C q f

/-- Movable codimension-two indices. -/
abbrev MovableCodimTwoIndex :=
  {qf : C.Cell × CodimTwoFace p //
    ¬ IsPurelyHorizontalCodimTwo hp C qf.1 qf.2}

noncomputable instance movableCodimTwoIndexFintype :
    Fintype (MovableCodimTwoIndex hp C) := Fintype.ofFinite _

noncomputable instance movableCodimTwoIndexDecidableEq :
    DecidableEq (MovableCodimTwoIndex hp C) := Classical.decEq _

/-- Relative genericity indices: all local facets, plus only non-purely-horizontal
codimension-two faces. -/
abbrev RelativeGenericityIndex :=
  (C.Cell × Fin (p + 1)) ⊕ MovableCodimTwoIndex hp C

noncomputable instance relativeGenericityIndexFintype :
    Fintype (RelativeGenericityIndex hp C) := inferInstance

noncomputable instance relativeGenericityIndexDecidableEq :
    DecidableEq (RelativeGenericityIndex hp C) := Classical.decEq _

/-- Combined boundary-restricted genericity polynomial family. -/
noncomputable def restrictedGenericityPolynomial
    (base : Assignment hp C) :
    RelativeGenericityIndex hp C → MovablePolynomialRing hp C
  | Sum.inl qk => restrictedFacetDeterminantPolynomial hp C base qk.1 qk.2
  | Sum.inr qf => restrictedCodimTwoMinorPolynomial hp C base qf.1.1 qf.1.2

/-- Real determinant family corresponding to a full boundary-relative assignment. -/
noncomputable def genericityValue
    (a : Assignment hp C) : RelativeGenericityIndex hp C → Real
  | Sum.inl qk => VertexMap.facetDeterminant hp (localVertexMap hp C a qk.1) qk.2
  | Sum.inr qf => Matrix.det (codimTwoDeviationMatrix hp C a qf.1.1 qf.1.2)

/-- Evaluation identity for the combined relative genericity family. -/
theorem eval_restrictedGenericityPolynomial
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (i : RelativeGenericityIndex hp C) :
    MvPolynomial.eval move (restrictedGenericityPolynomial hp C base i) =
      genericityValue hp C (replaceMovable hp C base move) i := by
  cases i with
  | inl qk =>
      exact eval_restrictedFacetDeterminantPolynomial hp C base move qk.1 qk.2
  | inr qf =>
      exact eval_restrictedCodimTwoMinorPolynomial hp C base move qf.1.1 qf.1.2

/-- Proof-carrying attachment of the complete restricted polynomial family to explicit affine
relative cells. -/
structure RelativePolynomialAttachment
    (base : Assignment hp C) where
  /-- The polynomial family together with its identification with the restricted determinants. -/
  polynomialData : {f : RelativeGenericityIndex hp C → MovablePolynomialRing hp C //
    f = restrictedGenericityPolynomial hp C base}
  evaluation : ∀ move i,
    MvPolynomial.eval move (polynomialData.1 i) =
      genericityValue hp C (replaceMovable hp C base move) i

namespace RelativePolynomialAttachment

variable {hp C} {base : Assignment hp C}

/-- The determinant and minor polynomials carried by the attachment. -/
def polynomial (A : RelativePolynomialAttachment hp C base) :
    RelativeGenericityIndex hp C → MovablePolynomialRing hp C :=
  A.polynomialData.1

theorem polynomial_eq (A : RelativePolynomialAttachment hp C base) :
    A.polynomial = restrictedGenericityPolynomial hp C base :=
  A.polynomialData.2

end RelativePolynomialAttachment

/-- Every explicit affine relative cell system carries the audited boundary-restricted determinant
and minor polynomial attachment. -/
noncomputable def relativePolynomialAttachment
    (base : Assignment hp C) : RelativePolynomialAttachment hp C base where
  polynomialData := ⟨restrictedGenericityPolynomial hp C base, rfl⟩
  evaluation := eval_restrictedGenericityPolynomial hp C base

/-- The polynomial attachment exists without any genericity or nontriviality assumption. -/
theorem relativePolynomialAttachment_nonempty
    (base : Assignment hp C) :
    Nonempty (RelativePolynomialAttachment hp C base) :=
  ⟨relativePolynomialAttachment hp C base⟩

end Polynomials

variable (hp : Nat.Prime p)

/-- Combined proof-carrying package produced once a genuine relative affine collar and a base
boundary assignment are available. -/
structure AffineRelativeCellAndPolynomialAttachment
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat) where
  /-- The relative affine collar carrying the polynomial attachment. -/
  collar : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L
  /-- The base vertex assignment from which movable coordinates are perturbed. -/
  base : Parameters.Assignment hp collar.cells
  /-- The polynomial identities attached to the collar and its base assignment. -/
  attachment : Polynomials.RelativePolynomialAttachment hp collar.cells base

/-- Polynomial attachment to any already-constructed genuine relative affine collar. -/
noncomputable def attachPolynomialsToCollar
    {N₀ N₁ M L : Nat}
    (C : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L)
    (base : Parameters.Assignment hp C.cells) :
    AffineRelativeCellAndPolynomialAttachment hp N₀ N₁ M L where
  collar := C
  base := base
  attachment := Polynomials.relativePolynomialAttachment hp C.cells base

end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
