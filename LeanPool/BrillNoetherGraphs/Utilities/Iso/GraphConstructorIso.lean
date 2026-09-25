/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgePresentation

/-!
# Functoriality of basic graph constructors

The bridge and wedge constructors respect graph isomorphisms of their
factors, including the distinguished attachment vertices.  The wedge proof
uses its presentation interface so that the dependent subtype of unmarked
right vertices never has to be relabelled directly.
-/

@[expose] public section

namespace Utilities

universe u v w x

namespace CFGraphIso

variable {G : CFGraph.{u}} {G' : CFGraph.{v}}
  {H : CFGraph.{w}} {H' : CFGraph.{x}}
/-- Relabel both factors of a separating bridge. -/
def bridgeGraphCongr (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) :
    CFGraphIso (bridgeGraph G H a b)
      (bridgeGraph G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b)) where
  vertexEquiv := Equiv.sumCongr φ.vertexEquiv ψ.vertexEquiv
  map_num_edges := by
    rintro (x | x) (y | y)
    · change numEdges (bridgeGraph G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b))
        (Sum.inl (φ.vertexEquiv x)) (Sum.inl (φ.vertexEquiv y)) = _
      calc
        _ = numEdges G' (φ.vertexEquiv x) (φ.vertexEquiv y) :=
          num_edges_bridgeGraph_inl _ _ _ _ _ _
        _ = numEdges G x y := φ.map_num_edges x y
        _ = _ := (num_edges_bridgeGraph_inl G H a b x y).symm
    · change numEdges (bridgeGraph G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b))
        (Sum.inl (φ.vertexEquiv x)) (Sum.inr (ψ.vertexEquiv y)) = _
      rw [num_edges_bridgeGraph_inl_inr]
      simp
    · change numEdges (bridgeGraph G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b))
        (Sum.inr (ψ.vertexEquiv x)) (Sum.inl (φ.vertexEquiv y)) = _
      rw [num_edges_symmetric, num_edges_bridgeGraph_inl_inr, num_edges_symmetric]
      simp
    · change numEdges (bridgeGraph G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b))
        (Sum.inr (ψ.vertexEquiv x)) (Sum.inr (ψ.vertexEquiv y)) = _
      calc
        _ = numEdges H' (ψ.vertexEquiv x) (ψ.vertexEquiv y) :=
          num_edges_bridgeGraph_inr _ _ _ _ _ _
        _ = numEdges H x y := ψ.map_num_edges x y
        _ = _ := (num_edges_bridgeGraph_inr G H a b x y).symm

@[simp] theorem bridgeGraphCongr_apply_left
    (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) (x : G.V) :
    (bridgeGraphCongr φ ψ a b).vertexEquiv (Sum.inl x) =
      Sum.inl (φ.vertexEquiv x) := rfl

@[simp] theorem bridgeGraphCongr_apply_right
    (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) (y : H.V) :
    (bridgeGraphCongr φ ψ a b).vertexEquiv (Sum.inr y) =
      Sum.inr (ψ.vertexEquiv y) := rfl
/-- A presentation of the relabelled wedge by the original two factors. -/
noncomputable def vertexWedgeCongrPresentation
    (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) :
    VertexWedgePresentation
      (vertexWedge G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b)) G H a b where
  leftMap := fun x => Sum.inl (φ.vertexEquiv x)
  rightMap := fun y =>
    wedgeRightVertex G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b) (ψ.vertexEquiv y)
  left_injective := fun _ _ h => φ.vertexEquiv.injective (Sum.inl.inj h)
  right_injective := by
    intro x y h
    apply ψ.vertexEquiv.injective
    exact (VertexWedgePresentation.canonical G' H'
      (φ.vertexEquiv a) (ψ.vertexEquiv b)).right_injective h
  marked_eq := by simp
  only_overlap := by
    intro x y h
    have hEnds := (wedgeRightVertex_eq_left_iff G' H'
      (φ.vertexEquiv a) (ψ.vertexEquiv b) (ψ.vertexEquiv y)
      (φ.vertexEquiv x)).mp h.symm
    exact ⟨φ.vertexEquiv.injective hEnds.2,
      ψ.vertexEquiv.injective hEnds.1⟩
  vertex_cover := by
    rintro (x | x)
    · exact Or.inl ⟨φ.vertexEquiv.symm x, by simp⟩
    · refine Or.inr ⟨ψ.vertexEquiv.symm x.1, ?_⟩
      have hx : ψ.vertexEquiv (ψ.vertexEquiv.symm x.1) ≠ ψ.vertexEquiv b := by
        intro h
        exact x.2 (by simpa using h)
      rw [wedgeRightVertex_unmarked]
      apply congrArg Sum.inr
      apply Subtype.ext
      simp only [ne_eq, Equiv.apply_symm_apply]
      exact hx
  num_edges_left := by
    intro x y
    simpa using φ.map_num_edges x y
  num_edges_right := by
    intro x y
    simpa using ψ.map_num_edges x y
  num_edges_cross := by
    intro x y hy
    have hImage : ψ.vertexEquiv y ≠ ψ.vertexEquiv b := by
      intro h
      exact hy (ψ.vertexEquiv.injective h)
    rw [wedgeRightVertex_unmarked _ _ _ _ _ hImage]
    rw [num_edges_vertexWedge_left_right]
    simp [φ.vertexEquiv.apply_eq_iff_eq, ψ.map_num_edges]

/-- Relabel both factors of a vertex wedge. -/
noncomputable def vertexWedgeCongr (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) :
    CFGraphIso (vertexWedge G H a b)
      (vertexWedge G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b)) :=
  (vertexWedgeCongrPresentation φ ψ a b).graphIso

@[simp] theorem vertexWedgeCongr_apply_left
    (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) (x : G.V) :
    (vertexWedgeCongr φ ψ a b).vertexEquiv (Sum.inl x) =
      Sum.inl (φ.vertexEquiv x) := rfl

@[simp] theorem vertexWedgeCongr_apply_right
    (φ : CFGraphIso G G') (ψ : CFGraphIso H H')
    (a : G.V) (b : H.V) (y : H.V) :
    (vertexWedgeCongr φ ψ a b).vertexEquiv
      (wedgeRightVertex G H a b y) =
      wedgeRightVertex G' H' (φ.vertexEquiv a) (ψ.vertexEquiv b)
        (ψ.vertexEquiv y) :=
  (vertexWedgeCongrPresentation φ ψ a b).graphIso_apply_wedgeRightVertex y

end CFGraphIso

end Utilities
