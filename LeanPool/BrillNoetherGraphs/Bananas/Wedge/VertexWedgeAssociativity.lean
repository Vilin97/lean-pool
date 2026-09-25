/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphConstructorIso

/-!
# Associativity of vertex wedges

The concrete `vertexWedge` constructor retains every vertex of the left
factor and every vertex of the right factor except its attachment vertex.
Consequently, both bracketings of a three-factor wedge have the same three
classes of vertices.  This file records the resulting graph isomorphism.
-/

@[expose] public section

namespace Bananas

open Utilities

universe u v w
/-- Rebracket the concrete vertex types underlying a three-factor wedge. -/
def vertexWedgeAssocVertexEquiv
    (G : CFGraph.{u}) (H : CFGraph.{v}) (K : CFGraph.{w})
    (x : G.V) (y z : H.V) (t : K.V) :
    (vertexWedge (vertexWedge G H x y) K
      (wedgeRightVertex G H x y z) t).V ≃
      (vertexWedge G (vertexWedge H K z t) x (Sum.inl y)).V where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl a
    | Sum.inl (Sum.inr b) => Sum.inr ⟨Sum.inl b.1, by
        intro h
        exact b.2 (Sum.inl.inj h)⟩
    | Sum.inr c => Sum.inr ⟨Sum.inr ⟨c.1, c.2⟩, by simp⟩
  invFun
    | Sum.inl a => Sum.inl (Sum.inl a)
    | Sum.inr b =>
        match hb : b.1 with
        | Sum.inl q => Sum.inl (Sum.inr ⟨q, by
            intro h
            apply b.2
            exact hb.trans (congrArg Sum.inl h)⟩)
        | Sum.inr q => Sum.inr ⟨q.1, q.2⟩
  left_inv := by
    rintro (a | c)
    · rcases a with a | b
      · rfl
      · simp
    · simp
  right_inv := by
    rintro (a | ⟨b, hb⟩)
    · rfl
    · rcases b with q | q <;> simp

@[simp] theorem vertexWedgeAssocVertexEquiv_apply_first
    (G : CFGraph.{u}) (H : CFGraph.{v}) (K : CFGraph.{w})
    (x : G.V) (y z : H.V) (t : K.V) (a : G.V) :
    vertexWedgeAssocVertexEquiv G H K x y z t
      (Sum.inl (Sum.inl a)) = Sum.inl a := rfl

/-- The unglued middle-factor vertex viewed in the right-associated outer
wedge's unmarked right subtype. -/
def vertexWedgeAssocMiddleVertex
    (H : CFGraph.{v}) (K : CFGraph.{w}) (y z : H.V) (t : K.V)
    (b : { b : H.V // b ≠ y }) :
    { q : (vertexWedge H K z t).V // q ≠ Sum.inl y } :=
  ⟨Sum.inl b.1, fun h => b.2 (Sum.inl.inj h)⟩
/-- The unglued last-factor vertex viewed in the right-associated outer
wedge's unmarked right subtype. -/
def vertexWedgeAssocLastVertex
    (H : CFGraph.{v}) (K : CFGraph.{w}) (y z : H.V) (t : K.V)
    (c : { c : K.V // c ≠ t }) :
    { q : (vertexWedge H K z t).V // q ≠ Sum.inl y } :=
  ⟨Sum.inr ⟨c.1, c.2⟩, by simp⟩

@[simp] theorem vertexWedgeAssocMiddleVertex_val
    (H : CFGraph.{v}) (K : CFGraph.{w}) (y z : H.V) (t : K.V)
    (b : { b : H.V // b ≠ y }) :
    (vertexWedgeAssocMiddleVertex H K y z t b).1 = Sum.inl b.1 := rfl

@[simp] theorem vertexWedgeAssocLastVertex_val
    (H : CFGraph.{v}) (K : CFGraph.{w}) (y z : H.V) (t : K.V)
    (c : { c : K.V // c ≠ t }) :
    (vertexWedgeAssocLastVertex H K y z t c).1 = Sum.inr c := rfl

@[simp] theorem vertexWedgeAssocVertexEquiv_apply_middle
    (G : CFGraph.{u}) (H : CFGraph.{v}) (K : CFGraph.{w})
    (x : G.V) (y z : H.V) (t : K.V) (b : { b : H.V // b ≠ y }) :
    vertexWedgeAssocVertexEquiv G H K x y z t
      (Sum.inl (Sum.inr b)) =
        Sum.inr (vertexWedgeAssocMiddleVertex H K y z t b) := by
  exact congrArg Sum.inr (Subtype.ext (by rfl))

@[simp] theorem vertexWedgeAssocVertexEquiv_apply_last
    (G : CFGraph.{u}) (H : CFGraph.{v}) (K : CFGraph.{w})
    (x : G.V) (y z : H.V) (t : K.V) (c : { c : K.V // c ≠ t }) :
    vertexWedgeAssocVertexEquiv G H K x y z t (Sum.inr c) =
      Sum.inr (vertexWedgeAssocLastVertex H K y z t c) := by
  exact congrArg Sum.inr (Subtype.ext (by rfl))
/-- The symmetric orientation of `num_edges_vertexWedge_left_right`. -/
@[simp] theorem num_edges_vertexWedge_right_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : { b : H.V // b ≠ y }) (a : G.V) :
    numEdges (vertexWedge G H x y) (Sum.inr b) (Sum.inl a) =
      if a = x then numEdges H y b.1 else 0 := by
  rw [num_edges_symmetric]
  exact num_edges_vertexWedge_left_right G H x y a b

@[simp] theorem wedgeLeft_eq_wedgeRightVertex_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y b : H.V) (a : G.V) :
    (Sum.inl a : (vertexWedge G H x y).V) = wedgeRightVertex G H x y b ↔
      b = y ∧ a = x := by
  rw [eq_comm, wedgeRightVertex_eq_left_iff]

@[simp] theorem wedgeUnmarkedRight_eq_wedgeRightVertex_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (q : { q : H.V // q ≠ y }) (b : H.V) :
    (Sum.inr q : (vertexWedge G H x y).V) = wedgeRightVertex G H x y b ↔
      q.1 = b := by
  by_cases hb : b = y
  · subst b
    simp [q.2]
  · rw [wedgeRightVertex_unmarked G H x y b hb]
    simp [Subtype.ext_iff]
/-- Vertex-wedge associativity as an isomorphism of chip-firing graphs.

The middle graph is glued to `G` at `y` and to `K` at `z`; no hypothesis
that these two vertices are distinct is needed. -/
def vertexWedgeAssoc
    (G : CFGraph.{u}) (H : CFGraph.{v}) (K : CFGraph.{w})
    (x : G.V) (y z : H.V) (t : K.V) :
    CFGraphIso
      (vertexWedge (vertexWedge G H x y) K
        (wedgeRightVertex G H x y z) t)
      (vertexWedge G (vertexWedge H K z t) x (Sum.inl y)) where
  vertexEquiv := vertexWedgeAssocVertexEquiv G H K x y z t
  map_num_edges := by
    have hReverseTarget := num_edges_vertexWedge_right_left
      G (vertexWedge H K z t) x (Sum.inl y)
    have hReverseSource := num_edges_vertexWedge_right_left
      (vertexWedge G H x y) K (wedgeRightVertex G H x y z) t
    have hLeftTarget := num_edges_vertexWedge_left G (vertexWedge H K z t) x (Sum.inl y)
    have hLeftSource := num_edges_vertexWedge_left (vertexWedge G H x y) K
      (wedgeRightVertex G H x y z) t
    have hLeftFirst := num_edges_vertexWedge_left G H x y
    have hLeftSecond := num_edges_vertexWedge_left H K z t
    have hRightTarget := num_edges_vertexWedge_right G (vertexWedge H K z t) x (Sum.inl y)
    have hRightSource := num_edges_vertexWedge_right (vertexWedge G H x y) K
      (wedgeRightVertex G H x y z) t
    have hRightFirst := num_edges_vertexWedge_right G H x y
    have hRightSecond := num_edges_vertexWedge_right H K z t
    have hCrossTarget := num_edges_vertexWedge_left_right G (vertexWedge H K z t) x (Sum.inl y)
    have hCrossSource := num_edges_vertexWedge_left_right (vertexWedge G H x y) K
      (wedgeRightVertex G H x y z) t
    have hCrossFirst := num_edges_vertexWedge_left_right G H x y
    have hCrossSecond := num_edges_vertexWedge_left_right H K z t
    intro a b
    rcases a with a | c
    · rcases a with a | q
      · rcases b with b | d
        · rcases b with b | r
          · rw [vertexWedgeAssocVertexEquiv_apply_first,
              vertexWedgeAssocVertexEquiv_apply_first]
            simp only [hLeftTarget, hLeftSource, hLeftFirst, hLeftSecond, hRightTarget,
              hRightSource, hRightFirst, hRightSecond, hCrossTarget, hCrossSource, hCrossFirst,
              hCrossSecond]
          · rw [vertexWedgeAssocVertexEquiv_apply_first,
              vertexWedgeAssocVertexEquiv_apply_middle]
            simp only [vertexWedgeAssocMiddleVertex, hLeftTarget, hLeftSource, hLeftFirst,
              hLeftSecond, hRightTarget, hRightSource, hRightFirst, hRightSecond, hCrossTarget,
              hCrossSource, hCrossFirst, hCrossSecond, ite_true, ite_false]
        · rw [vertexWedgeAssocVertexEquiv_apply_first,
            vertexWedgeAssocVertexEquiv_apply_last]
          simp only [hCrossTarget,
              hCrossSource,
              hCrossFirst,
              hCrossSecond]
          rw [vertexWedgeAssocLastVertex_val]
          rw [hCrossSecond y d]
          by_cases hzy : z = y
          · subst z
            rw [wedgeRightVertex_marked G H x y]
            by_cases hax : a = x
            · subst a
              simp only [hLeftTarget, hLeftSource, hLeftFirst, hLeftSecond, hRightTarget,
                hRightSource, hRightFirst, hRightSecond, hCrossTarget, hCrossSource,
                hCrossFirst, hCrossSecond, ite_true, ite_false]
            · have hsum : (Sum.inl a : (vertexWedge G H x y).V) ≠ Sum.inl x :=
                fun h => hax (Sum.inl.inj h)
              simp [hax, hsum]
          · have hyz : y ≠ z := Ne.symm hzy
            rw [wedgeRightVertex_unmarked G H x y z hzy]
            simp [hyz]
      · rcases b with b | d
        · rcases b with b | r
          · rw [vertexWedgeAssocVertexEquiv_apply_middle,
              vertexWedgeAssocVertexEquiv_apply_first]
            rw [num_edges_symmetric (vertexWedge G (vertexWedge H K z t) x (Sum.inl y)),
              num_edges_symmetric (vertexWedge (vertexWedge G H x y) K
                (wedgeRightVertex G H x y z) t)]
            simp only [vertexWedgeAssocMiddleVertex, hLeftTarget, hLeftSource, hLeftFirst,
              hLeftSecond, hRightTarget, hRightSource, hRightFirst, hRightSecond, hCrossTarget,
              hCrossSource, hCrossFirst, hCrossSecond, ite_true, ite_false]
          · rw [vertexWedgeAssocVertexEquiv_apply_middle,
              vertexWedgeAssocVertexEquiv_apply_middle]
            simp only [vertexWedgeAssocMiddleVertex, hLeftTarget, hLeftSource, hLeftFirst,
              hLeftSecond, hRightTarget, hRightSource, hRightFirst, hRightSecond, hCrossTarget,
              hCrossSource, hCrossFirst, hCrossSecond, ite_true, ite_false]
        · rw [vertexWedgeAssocVertexEquiv_apply_middle,
            vertexWedgeAssocVertexEquiv_apply_last]
          simp only [hRightTarget, hRightSource, hCrossTarget, hCrossSource]
          rw [vertexWedgeAssocMiddleVertex_val, vertexWedgeAssocLastVertex_val]
          rw [hCrossSecond q.1 d]
          by_cases hzy : z = y
          · subst z
            rw [wedgeRightVertex_marked G H x y]
            simp [q.2]
          · rw [wedgeRightVertex_unmarked G H x y z hzy]
            by_cases hqz : q.1 = z
            · have hsum : (Sum.inr q : (vertexWedge G H x y).V) =
                  Sum.inr ⟨z, hzy⟩ := congrArg Sum.inr (Subtype.ext hqz)
              simp [hqz, hsum]
            · have hsum : (Sum.inr q : (vertexWedge G H x y).V) ≠
                  Sum.inr ⟨z, hzy⟩ := fun h =>
                hqz (congrArg Subtype.val (Sum.inr.inj h))
              rw [ite_eq_right hqz]
              split
              · rename_i h
                exact (hsum h).elim
              · rfl
    · rcases b with b | d
      · rcases b with b | r
        · rw [vertexWedgeAssocVertexEquiv_apply_last,
            vertexWedgeAssocVertexEquiv_apply_first]
          simp only [hReverseTarget, hReverseSource]
          rw [vertexWedgeAssocLastVertex_val]
          rw [hCrossSecond y c]
          by_cases hzy : z = y
          · subst z
            rw [wedgeRightVertex_marked G H x y]
            by_cases hbx : b = x
            · subst b
              simp only [hLeftTarget, hLeftSource, hLeftFirst, hLeftSecond, hRightTarget,
                hRightSource, hRightFirst, hRightSecond, hCrossTarget, hCrossSource,
                hCrossFirst, hCrossSecond, ite_true, ite_false]
            · have hsum : (Sum.inl b : (vertexWedge G H x y).V) ≠ Sum.inl x :=
                fun h => hbx (Sum.inl.inj h)
              simp [hbx, hsum]
          · have hyz : y ≠ z := Ne.symm hzy
            rw [wedgeRightVertex_unmarked G H x y z hzy]
            simp [hyz]
        · rw [vertexWedgeAssocVertexEquiv_apply_last,
            vertexWedgeAssocVertexEquiv_apply_middle]
          simp only [hRightTarget, hRightSource, hReverseTarget, hReverseSource]
          rw [vertexWedgeAssocLastVertex_val, vertexWedgeAssocMiddleVertex_val]
          rw [num_edges_vertexWedge_right_left H K z t c r.1]
          by_cases hzy : z = y
          · subst z
            rw [wedgeRightVertex_marked G H x y]
            simp [r.2]
          · rw [wedgeRightVertex_unmarked G H x y z hzy]
            by_cases hrz : r.1 = z
            · have hsum : (Sum.inr r : (vertexWedge G H x y).V) =
                  Sum.inr ⟨z, hzy⟩ := congrArg Sum.inr (Subtype.ext hrz)
              simp [hrz, hsum]
            · have hsum : (Sum.inr r : (vertexWedge G H x y).V) ≠
                  Sum.inr ⟨z, hzy⟩ := fun h =>
                hrz (congrArg Subtype.val (Sum.inr.inj h))
              rw [ite_eq_right hrz]
              split
              · rename_i h
                exact (hsum h).elim
              · rfl
      · rw [vertexWedgeAssocVertexEquiv_apply_last,
          vertexWedgeAssocVertexEquiv_apply_last]
        simp only [vertexWedgeAssocLastVertex, hLeftTarget, hLeftSource, hLeftFirst,
          hLeftSecond, hRightTarget, hRightSource, hRightFirst, hRightSecond, hCrossTarget,
          hCrossSource, hCrossFirst, hCrossSecond, ite_true, ite_false]

/-- Brill--Noether generality is invariant under graph isomorphism. -/
theorem brillNoetherGeneral_iff_graphIso
    {G H : CFGraph} (equivalence : CFGraphIso G H) :
    BrillNoetherGeneral H ↔ BrillNoetherGeneral G := by
  constructor
  · intro hH r d hr hExists
    have h := hH r d hr ((equivalence.BNExists_iff r d).mpr hExists)
    simpa [bnNumber, rectangleWidth, equivalence.genus_eq] using h
  · intro hG r d hr hExists
    have h := hG r d hr ((equivalence.BNExists_iff r d).mp hExists)
    simpa [bnNumber, rectangleWidth, equivalence.genus_eq] using h

/-- Brill--Noether generality does not depend on the bracketing of a
three-factor vertex wedge. -/
theorem brillNoetherGeneral_vertexWedge_assoc_iff
    (G H K : CFGraph) (x : G.V) (y z : H.V) (t : K.V) :
    BrillNoetherGeneral
        (vertexWedge G (vertexWedge H K z t) x (Sum.inl y)) ↔
      BrillNoetherGeneral
        (vertexWedge (vertexWedge G H x y) K
          (wedgeRightVertex G H x y z) t) :=
  brillNoetherGeneral_iff_graphIso (vertexWedgeAssoc G H K x y z t)

end Bananas
