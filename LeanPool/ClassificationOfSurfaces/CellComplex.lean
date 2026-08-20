/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Triangulation
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Rotate

/-!
# Finite surface cell complexes

This file owns the shared combinatorial API between the topological triangulation route and the
Gallier-Xu normal-form route. The definitions are still intentionally light, but the public names
and theorem boundaries match the Moise/PL blueprint.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The raw finite incidence data underlying a Gallier-Xu surface cell complex.

Validity and connectedness are derived from this data by `IsSurfaceValid` and `IsConnected`, rather
than stored as unconstrained propositions. Its faithful polygonal realization is constructed
separately from the boundary occurrences. -/
structure SurfaceCellComplex where
  /-- The type of faces in the cell complex. -/
  Face : Type
  /-- The type of oriented darts in the cell complex. -/
  Dart : Type
  /-- The type of vertices in the cell complex. -/
  Vertex : Type
  faceFintype : Fintype Face
  dartFintype : Fintype Dart
  vertexFintype : Fintype Vertex
  /-- Reversal of an oriented dart. -/
  inv : Dart ≃ Dart
  /-- The source vertex of an oriented dart. -/
  source : Dart → Vertex
  /-- The target vertex of an oriented dart. -/
  target : Dart → Vertex
  /-- The cyclic boundary word of each face. -/
  boundary : Face → List Dart
  inv_involutive : ∀ d, inv (inv d) = d
  inv_source : ∀ d, source (inv d) = target d
  inv_target : ∀ d, target (inv d) = source d

attribute [instance] SurfaceCellComplex.faceFintype
attribute [instance] SurfaceCellComplex.dartFintype
attribute [instance] SurfaceCellComplex.vertexFintype

namespace SurfaceCellComplex

/-- The number of faces in a finite surface cell complex. -/
def numFaces (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Face

/-- The number of oriented darts in a finite surface cell complex. -/
def numDarts (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Dart

/-- The number of vertices in a finite surface cell complex. -/
def numVertices (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Vertex

/-- The length of a face boundary word. -/
abbrev faceBoundaryLength (K : SurfaceCellComplex) (f : K.Face) : ℕ :=
  (K.boundary f).length

/-- A position in one of the stored, positively oriented face boundaries. -/
abbrev BoundaryOccurrence (K : SurfaceCellComplex) :=
  Σ f : K.Face, Fin (K.boundary f).length

instance boundaryOccurrenceFintype (K : SurfaceCellComplex) : Fintype K.BoundaryOccurrence :=
  inferInstance

/-- The dart stored at a boundary occurrence. -/
def BoundaryOccurrence.dart {K : SurfaceCellComplex} (o : K.BoundaryOccurrence) : K.Dart :=
  (K.boundary o.1).get o.2

/-- Two darts name the same unoriented edge. -/
def SameEdge (K : SurfaceCellComplex) (d e : K.Dart) : Prop :=
  e = d ∨ e = K.inv d

/-- A boundary position belongs to the unoriented edge named by `d`. -/
def Occurs (K : SurfaceCellComplex) (d : K.Dart) (o : K.BoundaryOccurrence) : Prop :=
  K.SameEdge d o.dart

/-- The unoriented edge named by `d` occurs at exactly one boundary position. -/
def OccursExactlyOnce (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  ∃ o, K.Occurs d o ∧ ∀ o', K.Occurs d o' → o' = o

/-- The unoriented edge named by `d` occurs at exactly two boundary positions. -/
def OccursExactlyTwice (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  ∃ o₁ o₂, o₁ ≠ o₂ ∧ K.Occurs d o₁ ∧ K.Occurs d o₂ ∧
    ∀ o, K.Occurs d o → o = o₁ ∨ o = o₂

/-- Boundary status derived from incidence: the edge orbit of `d` occurs exactly once. -/
def IsBoundaryDart (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  K.OccursExactlyOnce d

/-- Incidence validity for the stored face-boundary system.

There is at least one face, different faces have different cyclic boundary words, inverse darts are
distinct, and every unoriented edge occurs either once (a boundary edge) or twice (an inner edge).
Boundary status and occurrence counts are derived from explicit boundary positions, so repeated
darts such as the projective-plane word `a a` are retained. The stored vertex endpoints are an
enrichment of Gallier--Xu's boundary-word data and are deliberately not part of this predicate. -/
def IsSurfaceValid (K : SurfaceCellComplex) : Prop :=
  Nonempty K.Face ∧
    (∀ f g, (K.boundary f).IsRotated (K.boundary g) → f = g) ∧
    (∀ d, K.inv d ≠ d) ∧
    ∀ d, K.OccursExactlyOnce d ∨ K.OccursExactlyTwice d

/-- Inverting the chosen representative does not change its unoriented edge. -/
@[simp]
theorem sameEdge_inv_left_iff (K : SurfaceCellComplex) (d e : K.Dart) :
    K.SameEdge (K.inv d) e ↔ K.SameEdge d e := by
  simp only [SameEdge, K.inv_involutive]
  exact or_comm

/-- Inverting the chosen representative does not change which boundary positions it occupies. -/
@[simp]
theorem occurs_inv_iff (K : SurfaceCellComplex) (d : K.Dart) (o : K.BoundaryOccurrence) :
    K.Occurs (K.inv d) o ↔ K.Occurs d o :=
  K.sameEdge_inv_left_iff d o.dart

/-- Boundary status is invariant under reversing the representative dart. -/
@[simp]
theorem isBoundaryDart_inv_iff (K : SurfaceCellComplex) (d : K.Dart) :
    K.IsBoundaryDart (K.inv d) ↔ K.IsBoundaryDart d := by
  simp only [IsBoundaryDart, OccursExactlyOnce, K.occurs_inv_iff]

namespace IsSurfaceValid

/-- Inverse darts in a valid incidence system are distinct. -/
theorem inv_ne {K : SurfaceCellComplex} (h : K.IsSurfaceValid) (d : K.Dart) :
    K.inv d ≠ d :=
  h.2.2.1 d

/-- A non-boundary edge in a valid incidence system occurs exactly twice. -/
theorem occurs_twice_of_not_boundary {K : SurfaceCellComplex} (h : K.IsSurfaceValid)
    {d : K.Dart} (hd : ¬K.IsBoundaryDart d) : K.OccursExactlyTwice d :=
  (h.2.2.2 d).resolve_left hd

end IsSurfaceValid

/-- Two faces are adjacent when their boundaries use the same unoriented edge. -/
def FaceAdjacent (K : SurfaceCellComplex) (f g : K.Face) : Prop :=
  ∃ d ∈ K.boundary f, ∃ e ∈ K.boundary g, K.SameEdge d e

/-- Gallier-Xu connectivity of the face-edge incidence system. -/
def IsConnected (K : SurfaceCellComplex) : Prop :=
  Nonempty K.Face ∧ ∀ f g, Relation.ReflTransGen K.FaceAdjacent f g

/-- A signed occurrence of a named edge in a polygonal boundary word. -/
inductive SignedDart (α : Type*) where
  | pos : α → SignedDart α
  | neg : α → SignedDart α
deriving DecidableEq, Repr, Fintype

namespace SignedDart

/-- The underlying unoriented edge name of a signed dart. -/
def edge {α : Type*} : SignedDart α → α
  | pos a => a
  | neg a => a

/-- Reverse the orientation of a signed dart. -/
def flip {α : Type*} : SignedDart α → SignedDart α
  | pos a => neg a
  | neg a => pos a

@[simp] theorem edge_flip {α : Type*} (d : SignedDart α) : (flip d).edge = d.edge := by
  cases d <;> rfl

@[simp] theorem flip_flip {α : Type*} (d : SignedDart α) : flip (flip d) = d := by
  cases d <;> rfl

/-- Orientation reversal as an equivalence. -/
def flipEquiv (α : Type*) : SignedDart α ≃ SignedDart α where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

@[simp]
theorem flipEquiv_apply {α : Type*} (d : SignedDart α) : flipEquiv α d = flip d :=
  rfl

end SignedDart

/-- A single-face polygonal presentation with all edge names based at one vertex.

This constructor is intentionally simple. It is useful for normal-form examples and for the
Gallier-Xu boundary-word API. -/
abbrev oneFacePresentation (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) :
    SurfaceCellComplex where
  Face := PUnit
  Dart := SignedDart Edge
  Vertex := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  inv := SignedDart.flipEquiv Edge
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun _ => word
  inv_involutive := SignedDart.flip_flip
  inv_source := by
    intro d
    rfl
  inv_target := by
    intro d
    rfl

/-- Every one-face presentation is connected in the face-edge incidence sense. -/
theorem oneFacePresentation_isConnected (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (oneFacePresentation Edge word).IsConnected := by
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  intro f g
  cases f
  cases g
  exact Relation.ReflTransGen.refl

/-- Convert an oriented triangulation edge occurrence to a cell-complex signed dart. -/
def signedDartOfOrientedEdge {Edge : Type*} :
    OrientedEdge Edge → SignedDart Edge
  | OrientedEdge.pos e => SignedDart.pos e
  | OrientedEdge.neg e => SignedDart.neg e

theorem signedDartOfOrientedEdge_injective {Edge : Type*} :
    Function.Injective
      (signedDartOfOrientedEdge : OrientedEdge Edge → SignedDart Edge) := by
  intro d e h
  cases d <;> cases e <;> simp_all [signedDartOfOrientedEdge]

@[simp]
theorem signedDartOfOrientedEdge_edge {Edge : Type*} (d : OrientedEdge Edge) :
    (signedDartOfOrientedEdge d).edge = d.edge := by
  cases d <;> rfl

/-- The sphere presented as two monogons with oppositely oriented copies of one edge.

The nonempty boundary presentation is equivalent to Gallier--Xu's empty-word sphere and is
directly compatible with the polygonal occurrence adapter. -/
def sphere : SurfaceCellComplex where
  Face := Bool
  Dart := SignedDart PUnit
  Vertex := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  inv := SignedDart.flipEquiv PUnit
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun
    | false => [SignedDart.pos PUnit.unit]
    | true => [SignedDart.neg PUnit.unit]
  inv_involutive := SignedDart.flip_flip
  inv_source := by
    intro d
    rfl
  inv_target := by
    intro d
    rfl

/-- The two-monogon presentation of the sphere has valid incidence data. -/
theorem sphere_isSurfaceValid : sphere.IsSurfaceValid := by
  refine ⟨⟨false⟩, ?_, ?_, ?_⟩
  · intro f g hfg
    cases f <;> cases g
    · rfl
    · simp [sphere] at hfg
    · simp [sphere] at hfg
    · rfl
  · intro d
    cases d <;> intro hd <;> cases hd
  · intro d
    right
    let o₀ : sphere.BoundaryOccurrence :=
      ⟨false, ⟨0, by simp [sphere]⟩⟩
    let o₁ : sphere.BoundaryOccurrence :=
      ⟨true, ⟨0, by simp [sphere]⟩⟩
    refine ⟨o₀, o₁, ?_, ?_, ?_, ?_⟩
    · intro h
      have : false = true := congrArg (fun o : sphere.BoundaryOccurrence => o.1) h
      exact Bool.noConfusion this
    · cases d with
      | pos e =>
          cases e
          exact Or.inl rfl
      | neg e =>
          cases e
          exact Or.inr rfl
    · cases d with
      | pos e =>
          cases e
          exact Or.inr rfl
      | neg e =>
          cases e
          exact Or.inl rfl
    · rintro ⟨f, i⟩ _hi
      cases f
      · left
        change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
      · right
        change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl

/-- The two faces of the sphere presentation are connected through their common edge. -/
theorem sphere_isConnected : sphere.IsConnected := by
  refine ⟨⟨false⟩, ?_⟩
  intro f g
  cases f <;> cases g
  · exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    refine ⟨SignedDart.pos PUnit.unit, List.mem_cons_self,
      SignedDart.neg PUnit.unit, List.mem_cons_self, Or.inr rfl⟩
  · apply Relation.ReflTransGen.single
    refine ⟨SignedDart.neg PUnit.unit, List.mem_cons_self,
      SignedDart.pos PUnit.unit, List.mem_cons_self, Or.inr rfl⟩
  · exact Relation.ReflTransGen.refl

end SurfaceCellComplex

/-- Raw compatibility bridge from the ledgered triangulation record to stored cell-presentation
data.

This conversion does not prove `IsSurfaceValid` or `IsConnected`; in particular, those properties
do not follow from `FiniteSurfaceTriangulation.Valid`.  New geometric work should start from
`GeometricTriangulation`, and downstream cellulation work must separately certify the incidence
predicates. -/
abbrev FiniteSurfaceTriangulation.toCellComplex {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) : SurfaceCellComplex where
  Face := T.Triangle
  Dart := SurfaceCellComplex.SignedDart T.Edge
  Vertex := T.Vertex
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  inv := SurfaceCellComplex.SignedDart.flipEquiv T.Edge
  source := fun
    | SurfaceCellComplex.SignedDart.pos e => T.edgeSource e
    | SurfaceCellComplex.SignedDart.neg e => T.edgeTarget e
  target := fun
    | SurfaceCellComplex.SignedDart.pos e => T.edgeTarget e
    | SurfaceCellComplex.SignedDart.neg e => T.edgeSource e
  boundary := fun f => (T.triangleBoundary f).map SurfaceCellComplex.signedDartOfOrientedEdge
  inv_involutive := SurfaceCellComplex.SignedDart.flip_flip
  inv_source := by
    intro d
    cases d <;> rfl
  inv_target := by
    intro d
    cases d <;> rfl

@[simp]
theorem FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S)
    (d e : T.toCellComplex.Dart) :
    T.toCellComplex.SameEdge d e ↔ e.edge = d.edge := by
  change e = d ∨ e = SurfaceCellComplex.SignedDart.flip d ↔ e.edge = d.edge
  cases d <;> cases e <;>
    simp only [SurfaceCellComplex.SignedDart.flip,
      SurfaceCellComplex.SignedDart.edge, reduceCtorEq,
      false_or, or_false]
  all_goals
    constructor
    · intro h
      injection h
    · rintro rfl
      rfl

namespace FiniteSurfaceTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- Triangle-boundary positions are canonically the boundary occurrences of the converted cell
complex. -/
def boundaryPositionEquivCellOccurrence (T : FiniteSurfaceTriangulation S) :
    T.BoundaryPosition ≃ T.toCellComplex.BoundaryOccurrence :=
  Equiv.sigmaCongrRight fun _ =>
    (Fin.castOrderIso (by simp [toCellComplex])).toEquiv

@[simp]
theorem boundaryPositionEquivCellOccurrence_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).1 = o.1 :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).2.val = o.2.val :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_symm_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.toCellComplex.BoundaryOccurrence) :
    (T.boundaryPositionEquivCellOccurrence.symm o).1 = o.1 :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_symm_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.toCellComplex.BoundaryOccurrence) :
    (T.boundaryPositionEquivCellOccurrence.symm o).2.val = o.2.val :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_dart
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).dart =
      SurfaceCellComplex.signedDartOfOrientedEdge o.orientedEdge := by
  change
    ((T.triangleBoundary o.1).map
      SurfaceCellComplex.signedDartOfOrientedEdge).get
        ⟨o.2.val, by simp⟩ =
      SurfaceCellComplex.signedDartOfOrientedEdge
        ((T.triangleBoundary o.1).get o.2)
  simp

theorem sameEdge_boundaryPositionEquivCellOccurrence_iff
    (T : FiniteSurfaceTriangulation S)
    (d : T.toCellComplex.Dart) (o : T.BoundaryPosition) :
    T.toCellComplex.SameEdge d (T.boundaryPositionEquivCellOccurrence o).dart ↔
      o.edge = d.edge := by
  rw [boundaryPositionEquivCellOccurrence_dart,
    FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff]
  simp [BoundaryPosition.edge]

private theorem occurs_once_or_twice_of_incidenceCertificate
    {T : FiniteSurfaceTriangulation S} (h : T.IncidenceCertificate)
    (d : T.toCellComplex.Dart) :
    T.toCellComplex.OccursExactlyOnce d ∨ T.toCellComplex.OccursExactlyTwice d := by
  let e := d.edge
  obtain ⟨o₀, ho₀⟩ := h.edge_used e
  classical
  by_cases hunique : ∀ o : T.BoundaryPosition, o.edge = e → o = o₀
  · left
    refine ⟨T.boundaryPositionEquivCellOccurrence o₀, ?_, ?_⟩
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₀).mpr ho₀
    · intro occurrence hoccur
      let o := T.boundaryPositionEquivCellOccurrence.symm occurrence
      have hedge : o.edge = e := by
        apply (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o).mp
        simpa only [SurfaceCellComplex.Occurs, o,
          Equiv.apply_symm_apply] using hoccur
      have ho : o = o₀ := hunique o hedge
      calc
        occurrence = T.boundaryPositionEquivCellOccurrence o := by
          simpa only [o] using
            (T.boundaryPositionEquivCellOccurrence.apply_symm_apply occurrence).symm
        _ = T.boundaryPositionEquivCellOccurrence o₀ :=
          congrArg T.boundaryPositionEquivCellOccurrence ho
  · push Not at hunique
    obtain ⟨o₁, ho₁, ho₁_ne⟩ := hunique
    right
    refine ⟨T.boundaryPositionEquivCellOccurrence o₀,
      T.boundaryPositionEquivCellOccurrence o₁, ?_, ?_, ?_, ?_⟩
    · exact T.boundaryPositionEquivCellOccurrence.injective.ne ho₁_ne.symm
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₀).mpr ho₀
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₁).mpr ho₁
    · intro occurrence hoccur
      let o₂ := T.boundaryPositionEquivCellOccurrence.symm occurrence
      have ho₂ : o₂.edge = e := by
        apply (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₂).mp
        simpa only [SurfaceCellComplex.Occurs, o₂,
          Equiv.apply_symm_apply] using hoccur
      rcases h.edge_valence_le_two e o₀ o₁ o₂ ho₀ ho₁ ho₂ with
        h01 | h02 | h12
      · exact False.elim (ho₁_ne h01.symm)
      · left
        simpa [o₂] using congrArg T.boundaryPositionEquivCellOccurrence h02.symm
      · right
        simpa [o₂] using congrArg T.boundaryPositionEquivCellOccurrence h12.symm

/-- An incidence-certified finite triangulation produces valid cell-complex incidence data. -/
theorem toCellComplex_isSurfaceValid_of_incidenceCertificate
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toCellComplex.IsSurfaceValid := by
  refine ⟨h.triangle_nonempty, ?_, ?_, ?_⟩
  · intro f g hrotated
    apply h.boundary_rotated_injective f g
    obtain ⟨n, hn⟩ := hrotated
    refine ⟨n, ?_⟩
    apply SurfaceCellComplex.signedDartOfOrientedEdge_injective.list_map
    simpa [toCellComplex, List.map_rotate] using hn
  · intro d
    cases d <;> intro hd <;> cases hd
  · exact occurs_once_or_twice_of_incidenceCertificate h

private theorem triangleAdjacent_to_faceAdjacent
    (T : FiniteSurfaceTriangulation S) {f g : T.Triangle}
    (h : T.TriangleAdjacent f g) : T.toCellComplex.FaceAdjacent f g := by
  rcases h with ⟨df, hdf, dg, hdg, hedge⟩
  refine ⟨SurfaceCellComplex.signedDartOfOrientedEdge df, ?_,
    SurfaceCellComplex.signedDartOfOrientedEdge dg, ?_, ?_⟩
  · exact List.mem_map_of_mem hdf
  · exact List.mem_map_of_mem hdg
  · rw [FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff]
    simpa using hedge.symm

/-- Dual connectivity of a certified triangulation gives cell-complex face connectivity. -/
theorem toCellComplex_isConnected_of_incidenceCertificate
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toCellComplex.IsConnected := by
  refine ⟨h.triangle_nonempty, ?_⟩
  intro f g
  apply Relation.ReflTransGen.mono (fun _ _ ↦ T.triangleAdjacent_to_faceAdjacent)
  exact h.dual_connected f g

end FiniteSurfaceTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
