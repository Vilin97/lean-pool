/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation
import LeanPool.ClassificationOfSurfaces.Triangulation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin

/-!
# Finite cyclic presentations of triangulations

This file relabels the finite faces and unoriented edges of a surface triangulation by `Fin`.
Each oriented triangle boundary is transported to a cyclic word of signed finite edge names.
Incidence validity and dual connectivity then pass to the resulting
`FiniteCyclicPresentation`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

/-- Oriented triangulation edges and signed cell-complex darts carry the same data. -/
private def orientedEdgeSignedDartEquiv {Edge : Type*} :
    OrientedEdge Edge ≃ SignedDart Edge where
  toFun := signedDartOfOrientedEdge
  invFun
    | .pos e => .pos e
    | .neg e => .neg e
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro d
    cases d <;> rfl

private theorem orientedEdgeSignedDartEquiv_apply {Edge : Type*} (d : OrientedEdge Edge) :
    orientedEdgeSignedDartEquiv d = signedDartOfOrientedEdge d :=
  rfl

private theorem orientedEdgeSignedDartEquiv_edge {Edge : Type*} (d : OrientedEdge Edge) :
    (orientedEdgeSignedDartEquiv d).edge = d.edge :=
  signedDartOfOrientedEdge_edge d

end SurfaceCellComplex

namespace FiniteSurfaceTriangulation

open SurfaceCellComplex

variable {S : Type*} [TopologicalSpace S]

/-- Relabel an oriented triangulation edge by a signed `Fin` edge name. -/
noncomputable def finiteCyclicDartEquiv (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge ≃ SignedDart (Fin (Fintype.card T.Edge)) :=
  SurfaceCellComplex.orientedEdgeSignedDartEquiv.trans
    (SignedDart.mapEquiv (Fintype.equivFin T.Edge))

@[simp]
theorem edgeOfDart_finiteCyclicDartEquiv
    (T : FiniteSurfaceTriangulation S) (d : OrientedEdge T.Edge) :
    FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
      Fintype.equivFin T.Edge d.edge := by
  cases d <;> rfl

/-- Enumerate the faces and unoriented edges of a finite triangulation and retain its cyclic
signed triangle boundaries. -/
@[reducible]
noncomputable def toFiniteCyclicPresentation (T : FiniteSurfaceTriangulation S) :
    FiniteCyclicPresentation where
  edgeCount := Fintype.card T.Edge
  faces :=
    List.ofFn fun f : Fin (Fintype.card T.Triangle) =>
      (T.triangleBoundary ((Fintype.equivFin T.Triangle).symm f)).map
        T.finiteCyclicDartEquiv

theorem toFiniteCyclicPresentation_faces_length (T : FiniteSurfaceTriangulation S) :
    T.toFiniteCyclicPresentation.faces.length = Fintype.card T.Triangle := by
  simp [toFiniteCyclicPresentation]

/-- The original unoriented edge names are equivalent to the enumerated presentation edges. -/
noncomputable def finiteCyclicEdgeEquiv (T : FiniteSurfaceTriangulation S) :
    T.Edge ≃ T.toFiniteCyclicPresentation.Edge := by
  change T.Edge ≃ Fin (Fintype.card T.Edge)
  exact Fintype.equivFin T.Edge

theorem edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv
    (T : FiniteSurfaceTriangulation S) (d : OrientedEdge T.Edge) :
    FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
      T.finiteCyclicEdgeEquiv d.edge := by
  change FiniteCyclicPresentation.edgeOfDart (T.finiteCyclicDartEquiv d) =
    Fintype.equivFin T.Edge d.edge
  exact T.edgeOfDart_finiteCyclicDartEquiv d

/-- The original triangles are equivalent to positions in the presentation's face list. -/
noncomputable def finiteCyclicFaceEquiv (T : FiniteSurfaceTriangulation S) :
    T.Triangle ≃ T.toFiniteCyclicPresentation.Face :=
  (Fintype.equivFin T.Triangle).trans
    (Fin.castOrderIso T.toFiniteCyclicPresentation_faces_length.symm).toEquiv

@[simp]
theorem finiteCyclicFaceEquiv_apply_val (T : FiniteSurfaceTriangulation S)
    (f : T.Triangle) :
    (T.finiteCyclicFaceEquiv f).val = (Fintype.equivFin T.Triangle f).val :=
  rfl

@[simp]
theorem finiteCyclicFaceEquiv_symm_apply_val (T : FiniteSurfaceTriangulation S)
    (f : T.toFiniteCyclicPresentation.Face) :
    (Fintype.equivFin T.Triangle (T.finiteCyclicFaceEquiv.symm f)).val = f.val := by
  simp [finiteCyclicFaceEquiv]

/-- Reading an enumerated face gives exactly the relabeled original triangle boundary. -/
theorem toFiniteCyclicPresentation_boundary_faceEquiv
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) :
    T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f) =
      (T.triangleBoundary f).map T.finiteCyclicDartEquiv := by
  simp [FiniteCyclicPresentation.boundary, toFiniteCyclicPresentation,
    finiteCyclicFaceEquiv]

theorem toFiniteCyclicPresentation_boundary_faceEquiv_length
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) :
    (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).length =
      (T.triangleBoundary f).length := by
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
  simp

/-- Reading a position in an enumerated boundary is the same as reading the corresponding
position before relabeling and then relabeling its dart. -/
theorem toFiniteCyclicPresentation_boundary_faceEquiv_get
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle)
    (i : Fin
      (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).length) :
    (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).get i =
      T.finiteCyclicDartEquiv
        ((T.triangleBoundary f).get
          (Fin.cast (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f) i)) := by
  have hi : i.val < (T.triangleBoundary f).length := by
    rw [← T.toFiniteCyclicPresentation_boundary_faceEquiv_length f]
    exact i.isLt
  have hleft :
      (T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f))[i.val]? =
        some ((T.toFiniteCyclicPresentation.boundary
          (T.finiteCyclicFaceEquiv f)).get i) := by
    rw [List.getElem?_eq_getElem i.isLt]
    congr
  have hright : ((T.triangleBoundary f).map T.finiteCyclicDartEquiv)[i.val]? =
      some (T.finiteCyclicDartEquiv
        ((T.triangleBoundary f).get
          (Fin.cast (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f) i))) := by
    have himap : i.val < ((T.triangleBoundary f).map T.finiteCyclicDartEquiv).length := by
      simpa using hi
    rw [List.getElem?_eq_getElem himap]
    simp [List.get_eq_getElem]
  have hget := congrArg (fun boundary => boundary[i.val]?)
    (T.toFiniteCyclicPresentation_boundary_faceEquiv f)
  rw [hleft, hright] at hget
  exact Option.some.inj hget

/-- Original triangle-boundary positions are canonically the boundary occurrences of the
enumerated cyclic presentation. -/
noncomputable def finiteCyclicOccurrenceEquiv (T : FiniteSurfaceTriangulation S) :
    T.BoundaryPosition ≃
      (Σ f : T.toFiniteCyclicPresentation.Face,
        Fin (T.toFiniteCyclicPresentation.boundary f).length) :=
  Equiv.sigmaCongr T.finiteCyclicFaceEquiv fun f =>
    (Fin.castOrderIso
      (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f).symm).toEquiv

@[simp]
theorem finiteCyclicOccurrenceEquiv_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.finiteCyclicOccurrenceEquiv o).1 = T.finiteCyclicFaceEquiv o.1 :=
  rfl

theorem finiteCyclicOccurrenceEquiv_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.finiteCyclicOccurrenceEquiv o).2.val = o.2.val :=
  rfl

theorem finiteCyclicOccurrenceEquiv_dart
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.toFiniteCyclicPresentation.boundary
      (T.finiteCyclicOccurrenceEquiv o).1).get
        (T.finiteCyclicOccurrenceEquiv o).2 =
      T.finiteCyclicDartEquiv o.orientedEdge := by
  rcases o with ⟨f, i⟩
  change (T.toFiniteCyclicPresentation.boundary
      (T.finiteCyclicFaceEquiv f)).get
        (Fin.cast
          (T.toFiniteCyclicPresentation_boundary_faceEquiv_length f).symm i) =
    T.finiteCyclicDartEquiv ((T.triangleBoundary f).get i)
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv_get]
  congr

/-- Number of occurrences of an original unoriented edge in one stored triangle boundary. -/
noncomputable def boundaryEdgeCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) : ℕ := by
  classical
  exact ((T.triangleBoundary f).map OrientedEdge.edge).count e

/-- Total number of boundary positions occupied by an original unoriented edge. -/
noncomputable def edgeOccurrenceCount
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e).card

private noncomputable def boundaryIndexCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (T.triangleBoundary f).length)).filter
    fun i => ((T.triangleBoundary f).get i).edge = e).card

/-- Relabeling a face and an edge does not change the number of times that edge occurs in the
face boundary. -/
@[simp]
theorem toFiniteCyclicPresentation_faceEdgeMultiplicity
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) :
    T.toFiniteCyclicPresentation.faceEdgeMultiplicity
        (T.finiteCyclicFaceEquiv f) (T.finiteCyclicEdgeEquiv e) =
      T.boundaryEdgeCount f e := by
  classical
  unfold boundaryEdgeCount
  change
    ((T.toFiniteCyclicPresentation.boundary (T.finiteCyclicFaceEquiv f)).map
      FiniteCyclicPresentation.edgeOfDart).count (Fintype.equivFin T.Edge e) =
        ((T.triangleBoundary f).map OrientedEdge.edge).count e
  rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
  have hmap :
      ((T.triangleBoundary f).map T.finiteCyclicDartEquiv).map
          FiniteCyclicPresentation.edgeOfDart =
        ((T.triangleBoundary f).map OrientedEdge.edge).map
          T.finiteCyclicEdgeEquiv := by
    simp [List.map_map, finiteCyclicEdgeEquiv]
  rw [hmap]
  exact List.count_map_of_injective
    ((T.triangleBoundary f).map OrientedEdge.edge)
    T.finiteCyclicEdgeEquiv T.finiteCyclicEdgeEquiv.injective e

private theorem boundaryIndex_card_eq_boundaryEdgeCount
    (T : FiniteSurfaceTriangulation S) (f : T.Triangle) (e : T.Edge) :
    T.boundaryIndexCount f e = T.boundaryEdgeCount f e := by
  classical
  unfold boundaryIndexCount boundaryEdgeCount
  let v : List.Vector T.Edge (T.triangleBoundary f).length :=
    List.Vector.ofFn fun i => ((T.triangleBoundary f).get i).edge
  simpa [v, List.ofFn_comp'] using
    Fin.card_filter_univ_eq_vector_get_eq_count e v

private theorem sum_boundaryEdgeCount_eq_edgeOccurrenceCount
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) :
    (∑ f : T.Triangle, T.boundaryEdgeCount f e) = T.edgeOccurrenceCount e := by
  classical
  unfold edgeOccurrenceCount
  let allPositions : Finset T.BoundaryPosition :=
    (Finset.univ : Finset T.Triangle).sigma fun f =>
      (Finset.univ : Finset (Fin (T.triangleBoundary f).length))
  have hall : allPositions = Finset.univ := by
    ext o
    simp [allPositions]
  calc
    (∑ f : T.Triangle, T.boundaryEdgeCount f e) =
        ∑ f : T.Triangle,
          T.boundaryIndexCount f e := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact (T.boundaryIndex_card_eq_boundaryEdgeCount f e).symm
    _ = (allPositions.filter fun o => o.edge = e).card := by
      unfold boundaryIndexCount
      rw [show allPositions =
          (Finset.univ : Finset T.Triangle).sigma fun f =>
            (Finset.univ : Finset (Fin (T.triangleBoundary f).length)) by
        rfl]
      rw [← Finset.card_sigma]
      congr 1
      ext o
      simp only [List.get_eq_getElem, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_filter, true_and, Finset.univ_sigma_univ]
      change
        ((T.triangleBoundary o.1).get o.2).edge = e ↔
          ((T.triangleBoundary o.1).get o.2).edge = e
      rfl
    _ = ((Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e).card := by
      rw [hall]

/-- The total multiplicity of an enumerated edge is the cardinality of its original boundary
position fiber. -/
theorem toFiniteCyclicPresentation_edgeMultiplicity
    (T : FiniteSurfaceTriangulation S) (e : T.Edge) :
    T.toFiniteCyclicPresentation.edgeMultiplicity (T.finiteCyclicEdgeEquiv e) =
      T.edgeOccurrenceCount e := by
  classical
  unfold FiniteCyclicPresentation.edgeMultiplicity
  calc
    (∑ f : T.toFiniteCyclicPresentation.Face,
        T.toFiniteCyclicPresentation.faceEdgeMultiplicity f
          (T.finiteCyclicEdgeEquiv e)) =
        ∑ f : T.Triangle,
          T.toFiniteCyclicPresentation.faceEdgeMultiplicity
            (T.finiteCyclicFaceEquiv f) (T.finiteCyclicEdgeEquiv e) := by
      exact (Fintype.sum_equiv T.finiteCyclicFaceEquiv _ _ fun _ => rfl).symm
    _ = ∑ f : T.Triangle,
        T.boundaryEdgeCount f e := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact T.toFiniteCyclicPresentation_faceEdgeMultiplicity f e
    _ = T.edgeOccurrenceCount e :=
      T.sum_boundaryEdgeCount_eq_edgeOccurrenceCount e

private theorem edgeOccurrenceCount_eq_one_or_two
    {T : FiniteSurfaceTriangulation S} (h : T.IncidenceCertificate) (e : T.Edge) :
    T.edgeOccurrenceCount e = 1 ∨ T.edgeOccurrenceCount e = 2 := by
  classical
  unfold edgeOccurrenceCount
  let occurrences :=
    (Finset.univ : Finset T.BoundaryPosition).filter fun o => o.edge = e
  obtain ⟨o, ho⟩ := h.edge_used e
  have homem : o ∈ occurrences := by
    simp [occurrences, ho]
  have hpos : 0 < occurrences.card :=
    Finset.card_pos.mpr ⟨o, homem⟩
  have hle : occurrences.card ≤ 2 := by
    by_contra hnot
    have hgt : 2 < occurrences.card := by
      omega
    obtain ⟨o₀, o₁, o₂, ho₀, ho₁, ho₂, h₀₁, h₀₂, h₁₂⟩ :=
      Finset.two_lt_card_iff.mp hgt
    have hedge₀ : o₀.edge = e := (Finset.mem_filter.mp ho₀).2
    have hedge₁ : o₁.edge = e := (Finset.mem_filter.mp ho₁).2
    have hedge₂ : o₂.edge = e := (Finset.mem_filter.mp ho₂).2
    rcases h.edge_valence_le_two e o₀ o₁ o₂ hedge₀ hedge₁ hedge₂ with
      h₀₁' | h₀₂' | h₁₂'
    · exact h₀₁ h₀₁'
    · exact h₀₂ h₀₂'
    · exact h₁₂ h₁₂'
  change occurrences.card = 1 ∨ occurrences.card = 2
  omega

private theorem triangleAdjacent_to_finiteCyclicFaceAdjacent
    (T : FiniteSurfaceTriangulation S) {f g : T.Triangle}
    (h : T.TriangleAdjacent f g) :
    T.toFiniteCyclicPresentation.FaceAdjacent
      (T.finiteCyclicFaceEquiv f) (T.finiteCyclicFaceEquiv g) := by
  rcases h with ⟨df, hdf, dg, hdg, hedge⟩
  refine ⟨T.finiteCyclicEdgeEquiv df.edge, ?_, ?_⟩
  · rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    rw [List.map_map, List.mem_map]
    exact ⟨df, hdf, T.edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv df⟩
  · rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    rw [List.map_map, List.mem_map]
    refine ⟨dg, hdg, ?_⟩
    change FiniteCyclicPresentation.edgeOfDart
      (T.finiteCyclicDartEquiv dg) = T.finiteCyclicEdgeEquiv df.edge
    rw [T.edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv, hedge]

/-- An incidence certificate and nonempty stored face boundaries give a valid finite cyclic
presentation. The boundary hypothesis is separate because the legacy certificate permits an
otherwise vacuous empty boundary. -/
theorem toFiniteCyclicPresentation_isSurfaceValid
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate)
    (hboundary : ∀ f, T.triangleBoundary f ≠ []) :
    T.toFiniteCyclicPresentation.IsSurfaceValid := by
  classical
  refine ⟨Nonempty.map T.finiteCyclicFaceEquiv h.triangle_nonempty, ?_, ?_, ?_⟩
  · intro f
    rw [← T.finiteCyclicFaceEquiv.apply_symm_apply f]
    rw [T.toFiniteCyclicPresentation_boundary_faceEquiv]
    simpa using hboundary (T.finiteCyclicFaceEquiv.symm f)
  · intro f g hrot
    let f' := T.finiteCyclicFaceEquiv.symm f
    let g' := T.finiteCyclicFaceEquiv.symm g
    have hf : f = T.finiteCyclicFaceEquiv f' :=
      (T.finiteCyclicFaceEquiv.apply_symm_apply f).symm
    have hg : g = T.finiteCyclicFaceEquiv g' :=
      (T.finiteCyclicFaceEquiv.apply_symm_apply g).symm
    have hrot' :
        ((T.triangleBoundary f').map T.finiteCyclicDartEquiv).IsRotated
          ((T.triangleBoundary g').map T.finiteCyclicDartEquiv) := by
      rw [hf, hg, T.toFiniteCyclicPresentation_boundary_faceEquiv,
        T.toFiniteCyclicPresentation_boundary_faceEquiv] at hrot
      exact hrot
    have horiginal :
        (T.triangleBoundary f').IsRotated (T.triangleBoundary g') := by
      simpa only [List.map_map, Equiv.symm_comp_self, List.map_id] using
        hrot'.map T.finiteCyclicDartEquiv.symm
    have hfg : f' = g' := h.boundary_rotated_injective f' g' horiginal
    calc
      f = T.finiteCyclicFaceEquiv f' :=
        (T.finiteCyclicFaceEquiv.apply_symm_apply f).symm
      _ = T.finiteCyclicFaceEquiv g' := congrArg T.finiteCyclicFaceEquiv hfg
      _ = g := T.finiteCyclicFaceEquiv.apply_symm_apply g
  · intro e
    let e' := T.finiteCyclicEdgeEquiv.symm e
    have hmultiplicity :=
      T.toFiniteCyclicPresentation_edgeMultiplicity e'
    have hcard := edgeOccurrenceCount_eq_one_or_two h e'
    rw [T.finiteCyclicEdgeEquiv.apply_symm_apply e] at hmultiplicity
    exact hmultiplicity.symm ▸ hcard

/-- A dual-connected incidence certificate gives connectivity of the enumerated finite cyclic
presentation. -/
theorem toFiniteCyclicPresentation_isConnected
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toFiniteCyclicPresentation.IsConnected := by
  refine ⟨Nonempty.map T.finiteCyclicFaceEquiv h.triangle_nonempty, ?_⟩
  intro f g
  let f' := T.finiteCyclicFaceEquiv.symm f
  let g' := T.finiteCyclicFaceEquiv.symm g
  have hpath :
      Relation.ReflTransGen T.toFiniteCyclicPresentation.FaceAdjacent
        (T.finiteCyclicFaceEquiv f') (T.finiteCyclicFaceEquiv g') :=
    Relation.ReflTransGen.lift T.finiteCyclicFaceEquiv
      (fun _ _ hadj => T.triangleAdjacent_to_finiteCyclicFaceAdjacent hadj)
      f' g'
      (h.dual_connected f' g')
  simpa [f', g'] using hpath

end FiniteSurfaceTriangulation

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- The finite cyclic presentation underlying a geometric triangulation. -/
@[reducible] noncomputable def toFiniteCyclicPresentation (T : GeometricTriangulation S) :
    FiniteCyclicPresentation :=
  T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation

/-- Surface incidence makes the cyclic presentation of a geometric triangulation valid. -/
theorem toFiniteCyclicPresentation_isSurfaceValid
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsSurfaceValid := by
  apply T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_isSurfaceValid
    (T.incidenceCertificate_of_surfaceIncidence h)
  intro f
  unfold GeometricTriangulation.toFiniteSurfaceTriangulation at f ⊢
  change T.triangleBoundary f ≠ []
  exact List.ne_nil_of_length_pos (by rw [T.triangleBoundary_length]; decide)

/-- Surface incidence makes the cyclic presentation of a geometric triangulation connected. -/
theorem toFiniteCyclicPresentation_isConnected
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsConnected :=
  T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_isConnected
    (T.incidenceCertificate_of_surfaceIncidence h)

/-- A geometric surface triangulation therefore supplies the valid, connected finite signed
cyclic presentation needed by the normal-form lane. -/
theorem toFiniteCyclicPresentation_valid_and_connected
    (T : GeometricTriangulation S) (h : T.SurfaceIncidence) :
    T.toFiniteCyclicPresentation.IsSurfaceValid ∧
      T.toFiniteCyclicPresentation.IsConnected :=
  ⟨T.toFiniteCyclicPresentation_isSurfaceValid h,
    T.toFiniteCyclicPresentation_isConnected h⟩

end GeometricTriangulation

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The named finite cyclic presentation obtained by enumerating the Radó triangulation of a
compact connected Eval surface. -/
noncomputable def compactEvalSurfaceFiniteCyclicPresentation :
    FiniteCyclicPresentation :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation

/-- The finite cyclic presentation attached to a compact connected Eval surface is valid. -/
theorem compact_eval_surface_finiteCyclicPresentation_isSurfaceValid :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsSurfaceValid :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation_isSurfaceValid
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S)

/-- The finite cyclic presentation attached to a compact connected Eval surface is connected. -/
theorem compact_eval_surface_finiteCyclicPresentation_isConnected :
    (compactEvalSurfaceFiniteCyclicPresentation S).IsConnected :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteCyclicPresentation_isConnected
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S)

include S

/-- The Eval hypotheses therefore supply a valid, connected finite cyclic presentation, which is
the input expected by the Gallier--Xu normal-form lane. -/
theorem compact_eval_surface_has_valid_connected_finiteCyclicPresentation :
    ∃ P : FiniteCyclicPresentation, P.IsSurfaceValid ∧ P.IsConnected :=
  ⟨compactEvalSurfaceFiniteCyclicPresentation S,
    compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S,
    compact_eval_surface_finiteCyclicPresentation_isConnected S⟩

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
