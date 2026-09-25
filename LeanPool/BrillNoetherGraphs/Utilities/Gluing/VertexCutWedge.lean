/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.InducedSubgraph
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgePresentation
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeSameSidePresentation

/-!
# A one-vertex cut is a vertex wedge

Two finite vertex sets which cover a graph, meet in one vertex, and have no
edges between their noncommon parts give a literal vertex-wedge presentation
by their induced subgraphs.  This is the structural extraction lemma needed
to turn articulation/block data into divisor and transmission theorems.
-/

@[expose] public section

namespace Utilities

universe u

/-- Finite data exhibiting `K` as two induced pieces meeting only at `glue`.
The no-cross condition is stated in edge-multiplicity language and therefore
retains parallel edges automatically. -/
structure OneVertexCut (K : CFGraph.{u}) where
  /-- The left vertex set of the cut, meeting the right set precisely at the glue vertex. -/
  left : Finset K.V
  /-- The right vertex set of the cut; together with the left set it covers every vertex. -/
  right : Finset K.V
  /-- The unique overlap vertex at which the two induced subgraphs are wedged. -/
  glue : K.V
  glue_mem_left : glue ∈ left
  glue_mem_right : glue ∈ right
  vertex_cover : ∀ z : K.V, z ∈ left ∨ z ∈ right
  only_overlap : ∀ z : K.V, z ∈ left → z ∈ right → z = glue
  no_cross : ∀ a : K.V, a ∈ left → a ≠ glue →
    ∀ b : K.V, b ∈ right → b ≠ glue → numEdges K a b = 0

namespace OneVertexCut

variable {K : CFGraph.{u}} (cut : OneVertexCut K)

theorem left_nonempty : cut.left.Nonempty :=
  ⟨cut.glue, cut.glue_mem_left⟩

theorem right_nonempty : cut.right.Nonempty :=
  ⟨cut.glue, cut.glue_mem_right⟩

/-- The induced left factor. -/
noncomputable def leftGraph : CFGraph :=
  inducedSubgraph K cut.left cut.left_nonempty

/-- The induced right factor. -/
noncomputable def rightGraph : CFGraph :=
  inducedSubgraph K cut.right cut.right_nonempty

/-- The common vertex as a vertex of the left induced factor. -/
noncomputable def leftGlue : cut.leftGraph.V :=
  ⟨cut.glue, cut.glue_mem_left⟩

/-- The common vertex as a vertex of the right induced factor. -/
noncomputable def rightGlue : cut.rightGraph.V :=
  ⟨cut.glue, cut.glue_mem_right⟩

@[simp] theorem leftGlue_val : cut.leftGlue.val = cut.glue := rfl

@[simp] theorem rightGlue_val : cut.rightGlue.val = cut.glue := rfl

/-- A one-vertex cut canonically presents the ambient graph as the wedge of
its two induced factors. -/
noncomputable def presentation :
    VertexWedgePresentation K cut.leftGraph cut.rightGraph
      cut.leftGlue cut.rightGlue where
  leftMap := fun vertex => vertex.val
  rightMap := fun vertex => vertex.val
  left_injective := Subtype.val_injective
  right_injective := Subtype.val_injective
  marked_eq := rfl
  only_overlap := by
    intro a b hEqual
    have hRight : a.val ∈ cut.right := by
      rw [hEqual]
      exact b.property
    have hGlue : a.val = cut.glue :=
      cut.only_overlap a.val a.property hRight
    constructor
    · apply Subtype.ext
      exact hGlue
    · apply Subtype.ext
      exact hEqual.symm.trans hGlue
  vertex_cover := by
    intro z
    rcases cut.vertex_cover z with hLeft | hRight
    · exact Or.inl ⟨⟨z, hLeft⟩, rfl⟩
    · exact Or.inr ⟨⟨z, hRight⟩, rfl⟩
  num_edges_left := by
    intro a b
    exact num_edges_inducedSubgraph K cut.left cut.left_nonempty a b |>.symm
  num_edges_right := by
    intro a b
    exact num_edges_inducedSubgraph K cut.right cut.right_nonempty a b |>.symm
  num_edges_cross := by
    intro a b hBMarked
    by_cases hAMarked : a = cut.leftGlue
    · rw [if_pos hAMarked]
      subst a
      exact (num_edges_inducedSubgraph K cut.right cut.right_nonempty
        cut.rightGlue b).symm
    · rw [if_neg hAMarked]
      apply cut.no_cross a.val a.property
      · intro hValue
        apply hAMarked
        apply Subtype.ext
        exact hValue
      · exact b.property
      · intro hValue
        apply hBMarked
        apply Subtype.ext
        exact hValue

/-- The occurrence-safe graph isomorphism extracted from a one-vertex cut. -/
noncomputable def graphIso :
    CFGraphIso
      (vertexWedge cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue) K :=
  cut.presentation.graphIso

/-- Genus is additive across a one-vertex cut. -/
theorem genus_eq : genus K = genus cut.leftGraph + genus cut.rightGraph :=
  cut.presentation.genus_eq

/-- Connected induced factors give a connected ambient graph. -/
theorem graph_connected_of_factors
    (hLeft : graphConnected cut.leftGraph)
    (hRight : graphConnected cut.rightGraph) :
    graphConnected K :=
  cut.presentation.graph_connected_of_factors hLeft hRight

/-- Brill--Noether existence on the ambient graph is exactly existence on the
extracted wedge. -/
@[simp] theorem BNExists_iff (r d : ℤ) :
    BNExists K r d ↔
      BNExists
        (vertexWedge cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue)
        r d :=
  cut.presentation.BNExists_iff r d

/-- Rank-one pencils on the two induced factors glue on the ambient graph,
with their degrees adding. -/
theorem BNExists_rank_one_of_factors (dLeft dRight : ℤ)
    (hLeft : BNExists cut.leftGraph 1 dLeft)
    (hRight : BNExists cut.rightGraph 1 dRight) :
    BNExists K 1 (dLeft + dRight) := by
  apply (cut.BNExists_iff 1 (dLeft + dRight)).mpr
  exact BNExists_vertexWedge_rank_one cut.leftGraph cut.rightGraph
    cut.leftGlue cut.rightGlue dLeft dRight hLeft hRight

/-- Arbitrary-ASP transmission profiles on the two induced factors transport
to the ambient graph. -/
theorem transmissionExists_of_profile
    (u : cut.leftGraph.V) (v : cut.rightGraph.V) (tau : AspPerm)
    (D : CFDiv cut.leftGraph) (E : CFDiv cut.rightGraph)
    (hProfile : WedgeTransmissionProfile cut.leftGraph cut.rightGraph
      cut.leftGlue cut.rightGlue D E u v tau) :
    TransmissionExists K u.val v.val tau :=
  cut.presentation.transmissionExists_of_profile u v tau D E hProfile

/-- An arbitrary-ASP profile with both marks on the left induced factor
transports to the ambient graph. -/
theorem transmissionExists_sameLeft_of_profile
    (p q : cut.leftGraph.V) (tau : AspPerm)
    (D : CFDiv cut.leftGraph) (E : CFDiv cut.rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
      D E p q tau) :
    TransmissionExists K p.val q.val tau :=
  cut.presentation.transmissionExists_sameLeft_of_profile
    p q tau D E hProfile

/-- Explicit ambient witness supplied by a same-left profile across a
one-vertex cut. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
    (p q : cut.leftGraph.V) (tau : AspPerm)
    (D : CFDiv cut.leftGraph) (E : CFDiv cut.rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
      D E p q tau) :
    SatisfiesTransmission K p.val q.val tau
      (cut.graphIso.mapDiv
        (wedgeAddDivisor cut.leftGraph cut.rightGraph
          cut.leftGlue cut.rightGlue D E)) :=
  cut.presentation.satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
    p q tau D E hProfile

/-- An arbitrary-ASP profile with both marks on the right induced factor
transports to the ambient graph. -/
theorem transmissionExists_sameRight_of_profile
    (p q : cut.rightGraph.V) (tau : AspPerm)
    (D : CFDiv cut.leftGraph) (E : CFDiv cut.rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
      D E p q tau) :
    TransmissionExists K p.val q.val tau :=
  cut.presentation.transmissionExists_sameRight_of_profile
    p q tau D E hProfile

/-- Explicit ambient witness supplied by a same-right profile across a
one-vertex cut. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
    (p q : cut.rightGraph.V) (tau : AspPerm)
    (D : CFDiv cut.leftGraph) (E : CFDiv cut.rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
      D E p q tau) :
    SatisfiesTransmission K p.val q.val tau
      (cut.graphIso.mapDiv
        (wedgeAddDivisor cut.leftGraph cut.rightGraph
          cut.leftGlue cut.rightGlue D E)) :=
  cut.presentation.satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
    p q tau D E hProfile

end OneVertexCut

/-! ## Closed regression -/

/-- A three-vertex path split at its middle vertex. -/
private abbrev threeVertexPath : CFGraph where
  V := Fin 3
  edges := {(0, 1), (1, 2)}
  loopless := by decide
private def threeVertexPathCut : OneVertexCut threeVertexPath where
  left := ({0, 1} : Finset (Fin 3))
  right := ({1, 2} : Finset (Fin 3))
  glue := (1 : Fin 3)
  glue_mem_left := by decide
  glue_mem_right := by decide
  vertex_cover := by decide
  only_overlap := by decide
  no_cross := by decide

example :
    genus threeVertexPath =
      genus threeVertexPathCut.leftGraph +
        genus threeVertexPathCut.rightGraph :=
  threeVertexPathCut.genus_eq

end Utilities
