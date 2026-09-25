/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Presentations of a vertex wedge

`VertexWedgePresentation` records the data needed to recognize an ambient
graph as a wedge of two graphs at distinguished vertices.  It is deliberately
stated using edge multiplicities, so it can be used without choosing an
orientation of the raw edge multisets.
-/

namespace Utilities

universe u v w

/-- A presentation of `K` as the wedge of `G` and `H`, identifying `x` with
`y`. -/
structure VertexWedgePresentation (K : CFGraph.{w})
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) where
  leftMap : G.V → K.V
  rightMap : H.V → K.V
  left_injective : Function.Injective leftMap
  right_injective : Function.Injective rightMap
  marked_eq : leftMap x = rightMap y
  only_overlap : ∀ a b, leftMap a = rightMap b → a = x ∧ b = y
  vertex_cover : ∀ z, (∃ a, leftMap a = z) ∨ ∃ b, rightMap b = z
  num_edges_left : ∀ a b, numEdges K (leftMap a) (leftMap b) = numEdges G a b
  num_edges_right : ∀ a b, numEdges K (rightMap a) (rightMap b) = numEdges H a b
  num_edges_cross : ∀ a b, b ≠ y →
    numEdges K (leftMap a) (rightMap b) = if a = x then numEdges H y b else 0

namespace VertexWedgePresentation

variable {K : CFGraph.{w}} {G : CFGraph.{u}} {H : CFGraph.{v}}
  {x : G.V} {y : H.V}

/-- The concrete vertex wedge carries its tautological presentation.  Besides
being useful in compositions, this witnesses that the presentation fields do
not impose any unintended restrictions at the common vertex. -/
def canonical (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    VertexWedgePresentation (vertexWedge G H x y) G H x y where
  leftMap := Sum.inl
  rightMap := wedgeRightVertex G H x y
  left_injective := Sum.inl_injective
  right_injective := by
    intro a b hEqual
    by_cases ha : a = y
    · subst a
      rw [wedgeRightVertex_marked] at hEqual
      exact ((wedgeRightVertex_eq_left_iff G H x y b x).mp hEqual.symm).1.symm
    · by_cases hb : b = y
      · subst b
        rw [wedgeRightVertex_marked] at hEqual
        exact False.elim (by
          have hLeft :=
            (wedgeRightVertex_eq_left_iff G H x y a x).mp hEqual
          exact ha hLeft.1)
      · rw [wedgeRightVertex_unmarked G H x y a ha,
          wedgeRightVertex_unmarked G H x y b hb] at hEqual
        exact congrArg Subtype.val (Sum.inr.inj hEqual)
  marked_eq := (wedgeRightVertex_marked G H x y).symm
  only_overlap := by
    intro a b hEqual
    have hEnds := (wedgeRightVertex_eq_left_iff G H x y b a).mp hEqual.symm
    exact ⟨hEnds.2, hEnds.1⟩
  vertex_cover := by
    intro z
    rcases z with a | b
    · exact Or.inl ⟨a, rfl⟩
    · refine Or.inr ⟨b.1, ?_⟩
      change wedgeRightVertex G H x y b.1 =
        (Sum.inr b : Sum G.V { b : H.V // b ≠ y })
      exact wedgeRightVertex_unmarked G H x y b.1 b.2
  num_edges_left := num_edges_vertexWedge_left G H x y
  num_edges_right := num_edges_vertexWedge_rightVertex G H x y
  num_edges_cross := by
    intro a b hb
    rw [wedgeRightVertex_unmarked G H x y b hb]
    exact num_edges_vertexWedge_left_right G H x y a ⟨b, hb⟩

/-- The map from the concrete wedge vertex type into a presented ambient
graph. -/
def map (P : VertexWedgePresentation K G H x y) :
    (vertexWedge G H x y).V → K.V :=
  Sum.elim P.leftMap (fun b => P.rightMap b.1)

@[simp] theorem map_left (P : VertexWedgePresentation K G H x y) (a : G.V) :
    P.map (Sum.inl a) = P.leftMap a := rfl

@[simp] theorem map_right (P : VertexWedgePresentation K G H x y)
    (b : { b : H.V // b ≠ y }) :
    P.map (Sum.inr b) = P.rightMap b.1 := rfl

theorem map_injective (P : VertexWedgePresentation K G H x y) :
    Function.Injective P.map := by
  intro p q hpq
  cases p with
  | inl a =>
      cases q with
      | inl b => exact congrArg Sum.inl (P.left_injective hpq)
      | inr b =>
          obtain ⟨ha, hb⟩ := P.only_overlap a b.1 hpq
          exact False.elim (b.2 hb)
  | inr a =>
      cases q with
      | inl b =>
          obtain ⟨hb, ha⟩ := P.only_overlap b a.1 hpq.symm
          exact False.elim (a.2 ha)
      | inr b => exact congrArg Sum.inr (Subtype.ext (P.right_injective hpq))

theorem map_surjective (P : VertexWedgePresentation K G H x y) :
    Function.Surjective P.map := by
  intro z
  rcases P.vertex_cover z with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨Sum.inl a, ha⟩
  · by_cases hby : b = y
    · subst b
      exact ⟨Sum.inl x, P.marked_eq.trans hb⟩
    · exact ⟨Sum.inr ⟨b, hby⟩, hb⟩

/-- The vertex equivalence induced by a wedge presentation. -/
noncomputable def vertexEquiv (P : VertexWedgePresentation K G H x y) :
    (vertexWedge G H x y).V ≃ K.V :=
  Equiv.ofBijective P.map ⟨P.map_injective, P.map_surjective⟩

@[simp] theorem vertexEquiv_left (P : VertexWedgePresentation K G H x y) (a : G.V) :
    P.vertexEquiv (Sum.inl a) = P.leftMap a := rfl

@[simp] theorem vertexEquiv_right (P : VertexWedgePresentation K G H x y)
    (b : { b : H.V // b ≠ y }) :
    P.vertexEquiv (Sum.inr b) = P.rightMap b.1 := rfl

/-- The whole right-factor vertex map, including the identified vertex, is
carried to the advertised ambient map. -/
@[simp] theorem vertexEquiv_wedgeRightVertex
    (P : VertexWedgePresentation K G H x y) (b : H.V) :
    P.vertexEquiv (wedgeRightVertex G H x y b) = P.rightMap b := by
  by_cases hb : b = y
  · subst b
    simpa [wedgeRightVertex, vertexEquiv, map] using P.marked_eq
  · simp [wedgeRightVertex, hb, vertexEquiv, map]

/-- A wedge presentation determines an isomorphism from the concrete wedge to
the ambient graph. -/
noncomputable def graphIso (P : VertexWedgePresentation K G H x y) :
    CFGraphIso (vertexWedge G H x y) K where
  vertexEquiv := P.vertexEquiv
  map_num_edges := by
    intro p q
    cases p with
    | inl a =>
        cases q with
        | inl b => simpa [vertexEquiv, map] using P.num_edges_left a b
        | inr b => simpa [vertexEquiv, map] using P.num_edges_cross a b.1 b.2
    | inr a =>
        cases q with
        | inl b =>
            calc
              numEdges K (P.rightMap a.1) (P.leftMap b) =
                  numEdges K (P.leftMap b) (P.rightMap a.1) :=
                num_edges_symmetric K _ _
              _ = if b = x then numEdges H y a.1 else 0 :=
                P.num_edges_cross b a.1 a.2
              _ = numEdges (vertexWedge G H x y) (Sum.inl b) (Sum.inr a) :=
                (num_edges_vertexWedge_left_right G H x y b a).symm
              _ = numEdges (vertexWedge G H x y) (Sum.inr a) (Sum.inl b) :=
                num_edges_symmetric _ _ _
        | inr b => simpa [vertexEquiv, map] using P.num_edges_right a.1 b.1

@[simp] theorem graphIso_apply_left (P : VertexWedgePresentation K G H x y) (a : G.V) :
    P.graphIso.vertexEquiv (Sum.inl a) = P.leftMap a := rfl

@[simp] theorem graphIso_apply_right (P : VertexWedgePresentation K G H x y)
    (b : { b : H.V // b ≠ y }) :
    P.graphIso.vertexEquiv (Sum.inr b) = P.rightMap b.1 := rfl

@[simp] theorem graphIso_apply_wedgeRightVertex
    (P : VertexWedgePresentation K G H x y) (b : H.V) :
    P.graphIso.vertexEquiv (wedgeRightVertex G H x y b) = P.rightMap b :=
  P.vertexEquiv_wedgeRightVertex b

/-- The presented graph has the genus expected of the two factors. -/
theorem genus_eq (P : VertexWedgePresentation K G H x y) :
    genus K = genus G + genus H := by
  rw [P.graphIso.genus_eq, genus_vertexWedge]

/-- Connectivity of the presented graph is equivalent to connectivity of its
concrete wedge. -/
theorem graph_connected_iff (P : VertexWedgePresentation K G H x y) :
    graphConnected K ↔ graphConnected (vertexWedge G H x y) :=
  P.graphIso.graph_connected_iff

/-- Connected factors give a connected presented ambient graph. -/
theorem graph_connected_of_factors
    (P : VertexWedgePresentation K G H x y)
    (hG : graphConnected G) (hH : graphConnected H) :
    graphConnected K :=
  P.graphIso.graph_connected_map
    (graph_connected_vertexWedge G H x y hG hH)

/-- Brill--Noether existence on a presented graph is exactly existence on its
concrete wedge model, at every rank and degree. -/
@[simp] theorem BNExists_iff (P : VertexWedgePresentation K G H x y)
    (r d : ℤ) :
    BNExists K r d ↔ BNExists (vertexWedge G H x y) r d :=
  P.graphIso.BNExists_iff r d

end VertexWedgePresentation

end Utilities
