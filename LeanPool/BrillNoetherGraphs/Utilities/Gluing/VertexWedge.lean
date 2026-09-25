/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne

/-!
# Wedges of chip-firing graphs

`vertexWedge G H x y` is the graph obtained by identifying the selected
vertices `x : G.V` and `y : H.V`.  We represent the identified vertex by
`Sum.inl x`; the other vertices of `H` are stored in the right summand.

The point of this concrete presentation is that it has literal zero-extension
maps for divisors and firing scripts.  Later vertex-gluing arguments can use
these maps without choosing a quotient representative.
-/

@[expose] public section

open Multiset Finset

namespace Utilities

universe u v

/-- Map the vertices of the right factor into a wedge, sending its marked
vertex to the marked vertex on the left. -/
def wedgeRightVertex (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) : H.V → Sum G.V { b : H.V // b ≠ y } :=
  fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩

@[simp] theorem wedgeRightVertex_marked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    wedgeRightVertex G H x y y = Sum.inl x := by
  simp [wedgeRightVertex]

@[simp] theorem wedgeRightVertex_unmarked
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : H.V) (hb : b ≠ y) :
    wedgeRightVertex G H x y b = Sum.inr ⟨b, hb⟩ := by
  simp [wedgeRightVertex, hb]

/-- The only right-factor vertex represented by a left vertex of the wedge is
the marked vertex. -/
theorem wedgeRightVertex_eq_left_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : H.V) (a : G.V) :
    wedgeRightVertex G H x y b = Sum.inl a ↔ b = y ∧ a = x := by
  by_cases hb : b = y
  · subst b
    simp [wedgeRightVertex, eq_comm]
  · simp [wedgeRightVertex, hb]

/-- Identifying `x` and `y` in the disjoint union of `G` and `H`. -/
abbrev vertexWedge (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) : CFGraph.{max u v} where
  V := Sum G.V { b : H.V // b ≠ y }
  edges :=
    G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2)) +
      H.edges.map (fun e =>
        (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2))
  loopless := by
    intro z hz
    simp only [Multiset.mem_add] at hz
    rcases hz with hG | hH
    · rw [Multiset.mem_map] at hG
      obtain ⟨e, he, hEq⟩ := hG
      rcases e with ⟨a, b⟩
      cases z with
      | inl z =>
          simp only [Prod.mk.injEq, Sum.inl.injEq] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          exact G.loopless _ he
      | inr z => simp at hEq
    · rw [Multiset.mem_map] at hH
      obtain ⟨e, he, hEq⟩ := hH
      rcases e with ⟨a, b⟩
      have hfst : wedgeRightVertex G H x y a = z := by
        simpa using congrArg Prod.fst hEq
      have hsnd : wedgeRightVertex G H x y b = z := by
        simpa using congrArg Prod.snd hEq
      have hmap : wedgeRightVertex G H x y a = wedgeRightVertex G H x y b :=
        hfst.trans hsnd.symm
      have hab : a = b := by
        by_cases ha : a = y
        · subst a
          simp only [ne_eq, wedgeRightVertex, ↓reduceDIte, left_eq_dite_iff, reduceCtorEq,
            imp_false, Decidable.not_not] at hmap
          exact hmap.symm
        · by_cases hb : b = y
          · subst b
            simp [wedgeRightVertex, ha] at hmap
          · simp only [ne_eq, wedgeRightVertex, ha, ↓reduceDIte, hb, Sum.inr.injEq,
              Subtype.mk.injEq] at hmap
            exact hmap
      exact H.loopless _ (hab ▸ he)

@[simp] theorem vertexWedge_edges
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    (vertexWedge G H x y).edges =
      G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e =>
          (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2)) := rfl

/-- The left factor is included literally in the wedge. -/
def wedgeLeftVertex (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) : G.V → (vertexWedge G H x y).V := Sum.inl

@[simp] theorem wedgeLeftVertex_apply
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (a : G.V) :
    wedgeLeftVertex G H x y a = Sum.inl a := rfl

/-- A divisor on the wedge obtained by adding a left divisor and a right
divisor, with the right marked chip placed at the common vertex. -/
def wedgeAddDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (D : CFDiv G) (E : CFDiv H) :
    CFDiv (vertexWedge G H x y) :=
  Sum.elim (fun a => D a + if a = x then E y else 0) (fun b => E b.1)

/-- Extend a left divisor by zero away from the common vertex. -/
def wedgeLiftLeftDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (D : CFDiv G) : CFDiv (vertexWedge G H x y) :=
  wedgeAddDivisor G H x y D 0

/-- Extend a right divisor by zero away from the common vertex, placing its
marked coefficient at the common vertex. -/
def wedgeLiftRightDivisor (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (E : CFDiv H) : CFDiv (vertexWedge G H x y) :=
  wedgeAddDivisor G H x y 0 E

@[simp] theorem wedgeLiftLeftDivisor_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (a : G.V) :
    wedgeLiftLeftDivisor G H x y D (Sum.inl a) = D a := by
  simp [wedgeLiftLeftDivisor, wedgeAddDivisor]

@[simp] theorem wedgeLiftLeftDivisor_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (b : { b : H.V // b ≠ y }) :
    wedgeLiftLeftDivisor G H x y D (Sum.inr b) = 0 := rfl

@[simp] theorem wedgeLiftRightDivisor_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (E : CFDiv H) (a : G.V) :
    wedgeLiftRightDivisor G H x y E (Sum.inl a) = if a = x then E y else 0 := by
  simp [wedgeLiftRightDivisor, wedgeAddDivisor]

@[simp] theorem wedgeLiftRightDivisor_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (E : CFDiv H) (b : { b : H.V // b ≠ y }) :
    wedgeLiftRightDivisor G H x y E (Sum.inr b) = E b.1 := rfl

@[simp] theorem wedgeAddDivisor_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (a : G.V) :
    wedgeAddDivisor G H x y D E (Sum.inl a) = D a + if a = x then E y else 0 := rfl

@[simp] theorem wedgeAddDivisor_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (b : { b : H.V // b ≠ y }) :
    wedgeAddDivisor G H x y D E (Sum.inr b) = E b.1 := rfl

/-- Splitting a finite sum into the marked vertex and its complement. -/
theorem sum_unmarked_add_marked
    (H : CFGraph.{v}) (y : H.V) (f : H.V → ℤ) :
    (∑ b : { b : H.V // b ≠ y }, f b.1) + f y = ∑ b : H.V, f b := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun b : H.V => b = y) f
  have hDefault : ((default : { b : H.V // b = y }) : H.V) = y :=
    (default : { b : H.V // b = y }).property
  simpa [hDefault, add_comm] using h

/-- If the marked summand vanishes, summing over the unmarked subtype is the
same as summing over the whole factor. -/
theorem sum_unmarked_eq_sum_of_marked_zero
    (H : CFGraph.{v}) (y : H.V) (f : H.V → ℤ) (hy : f y = 0) :
    (∑ b : { b : H.V // b ≠ y }, f b.1) = ∑ b : H.V, f b := by
  have h := sum_unmarked_add_marked H y f
  rw [hy] at h
  simpa using h

-- `backward.isDefEq.respectTransparency` defaults to `true` as of Mathlib
-- v4.33 (see the comment on `prin_wedgeScript` below for the mechanism);
-- without disabling it here, `rw [Fintype.sum_sum_type]` can't identify
-- `(vertexWedge G H x y).V` with `Sum G.V {..}` when rebuilding the summand.
/-- Degrees add when the marked coefficients are placed at the common vertex. -/
@[simp] theorem deg_wedgeAddDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) :
    deg (wedgeAddDivisor G H x y D E) = deg D + deg E := by
  classical
  change (∑ z : Sum G.V { b : H.V // b ≠ y }, wedgeAddDivisor G H x y D E z) =
    (∑ a : G.V, D a) + ∑ b : H.V, E b
  rw [Fintype.sum_sum_type]
  simp only [wedgeAddDivisor_left, wedgeAddDivisor_right]
  rw [Finset.sum_add_distrib]
  have hMarked : ∑ a : G.V, (if a = x then E y else 0) = E y := by
    simp
  rw [hMarked]
  have hSplit := sum_unmarked_add_marked H y E
  linarith

@[simp] theorem deg_wedgeLiftLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (D : CFDiv G) :
    deg (wedgeLiftLeftDivisor G H x y D) = deg D := by
  change deg (wedgeAddDivisor G H x y D 0) = deg D
  rw [deg_wedgeAddDivisor]
  simp

@[simp] theorem deg_wedgeLiftRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (E : CFDiv H) :
    deg (wedgeLiftRightDivisor G H x y E) = deg E := by
  change deg (wedgeAddDivisor G H x y 0 E) = deg E
  rw [deg_wedgeAddDivisor]
  simp

/-- Effectivity is preserved when two effective divisors are glued. -/
theorem effective_wedgeAddDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H)
    (hD : effective D) (hE : effective E) :
    effective (wedgeAddDivisor G H x y D E) := by
  intro z
  cases z with
  | inl a =>
      rw [wedgeAddDivisor_left]
      by_cases ha : a = x
      · subst a
        simpa using add_nonneg (hD x) (hE y)
      · simpa [ha] using hD a
  | inr b =>
      rw [wedgeAddDivisor_right]
      exact hE b.1

@[simp] theorem effective_wedgeLiftLeftDivisor_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (D : CFDiv G) :
    effective (wedgeLiftLeftDivisor G H x y D) ↔ effective D := by
  constructor
  · intro h a
    simpa using h (Sum.inl a)
  · intro h
    exact effective_wedgeAddDivisor G H x y D 0 h (fun _ => le_rfl)

@[simp] theorem effective_wedgeLiftRightDivisor_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (E : CFDiv H) :
    effective (wedgeLiftRightDivisor G H x y E) ↔ effective E := by
  constructor
  · intro h b
    by_cases hb : b = y
    · subst b
      simpa using h (Sum.inl x)
    · simpa [wedgeRightVertex, hb] using h (Sum.inr ⟨b, hb⟩)
  · intro h
    exact effective_wedgeAddDivisor G H x y 0 E (fun _ => le_rfl) h

/-- Glue firing scripts by requiring their values to agree at the identified
vertex. -/
def wedgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firingScript G) (τ : firingScript H)
    (_hxy : σ x = τ y) : firingScript (vertexWedge G H x y) :=
  Sum.elim σ (fun b => τ b.1)

@[simp] theorem wedgeScript_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript G) (τ : firingScript H) (hxy : σ x = τ y) (a : G.V) :
    wedgeScript G H x y σ τ hxy (Sum.inl a) = σ a := rfl

@[simp] theorem wedgeScript_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript G) (τ : firingScript H) (hxy : σ x = τ y)
    (b : { b : H.V // b ≠ y }) :
    wedgeScript G H x y σ τ hxy (Sum.inr b) = τ b.1 := rfl

/- The raw edge construction preserves the two input edge multisets.  The
following cardinality lemma is deliberately stated before the more refined
edge-multiplicity transport lemmas, which will use the same maps. -/
@[simp] theorem vertexWedge_edge_card
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    (vertexWedge G H x y).edges.card = G.edges.card + H.edges.card := by
  simp [vertexWedge]

/-- Identifying one vertex reduces the total vertex count by one. -/
@[simp] theorem vertexWedge_vertex_card
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    Fintype.card (vertexWedge G H x y).V =
      Fintype.card G.V + Fintype.card H.V - 1 := by
  classical
  change Fintype.card (Sum G.V { b : H.V // b ≠ y }) = _
  have hH : 1 ≤ Fintype.card H.V := Fintype.card_pos_iff.mpr inferInstance
  rw [Fintype.card_sum, Fintype.card_subtype_compl (fun b : H.V => b = y),
    Fintype.card_subtype_eq y]
  omega

/-- Vertex identification creates no cycle: genera add across a wedge. -/
@[simp] theorem genus_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    genus (vertexWedge G H x y) = genus G + genus H := by
  unfold genus
  rw [vertexWedge_edge_card, vertexWedge_vertex_card]
  have hH : 1 ≤ Fintype.card H.V := Fintype.card_pos_iff.mpr inferInstance
  push_cast
  omega

/-- Edge multiplicities between two vertices of the left factor are unchanged
by wedging on the right factor. -/
@[simp] theorem num_edges_vertexWedge_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a b : G.V) :
    numEdges (vertexWedge G H x y) (Sum.inl a) (Sum.inl b) =
      numEdges G a b := by
  unfold numEdges
  rw [vertexWedge_edges]
  change
    (Multiset.filter
      (fun e : (Sum G.V { b : H.V // b ≠ y } × Sum G.V { b : H.V // b ≠ y }) =>
        e = (Sum.inl a, Sum.inl b) ∨ e = (Sum.inl b, Sum.inl a))
      (G.edges.map (fun e : G.V × G.V => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e : H.V × H.V =>
          (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2)))).card =
      (G.edges.filter (fun e => e = (a, b) ∨ e = (b, a))).card
  have hRight :
      (H.edges.map (fun e =>
        (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2))).filter
          (fun e => e = (Sum.inl a, Sum.inl b) ∨ e = (Sum.inl b, Sum.inl a)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro e he hmem
    rw [Multiset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    rcases p with ⟨c, d⟩
    rcases hmem with hmem | hmem
    · have hc := (wedgeRightVertex_eq_left_iff G H x y c a).mp
        (congrArg Prod.fst hmem)
      have hd := (wedgeRightVertex_eq_left_iff G H x y d b).mp
        (congrArg Prod.snd hmem)
      exact H.loopless y (by simpa [hc.1, hd.1] using hp)
    · have hc := (wedgeRightVertex_eq_left_iff G H x y c b).mp
        (congrArg Prod.fst hmem)
      have hd := (wedgeRightVertex_eq_left_iff G H x y d a).mp
        (congrArg Prod.snd hmem)
      exact H.loopless y (by simpa [hc.1, hd.1] using hp)
  rw [Multiset.filter_add, Multiset.card_add, hRight]
  simp only [Multiset.card_zero, add_zero]
  simp only [Multiset.filter_map]
  rw [Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro e _he
  rcases e with ⟨c, d⟩
  simp

/-- Edge multiplicities between unmarked vertices of the right factor are
unchanged by the wedge. -/
@[simp] theorem num_edges_vertexWedge_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a b : { z : H.V // z ≠ y }) :
    numEdges (vertexWedge G H x y) (Sum.inr a) (Sum.inr b) =
      numEdges H a.1 b.1 := by
  unfold numEdges
  rw [vertexWedge_edges]
  change
    (Multiset.filter
      (fun e : (Sum G.V { z : H.V // z ≠ y } × Sum G.V { z : H.V // z ≠ y }) =>
        e = (Sum.inr a, Sum.inr b) ∨ e = (Sum.inr b, Sum.inr a))
      (G.edges.map (fun e : G.V × G.V => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e : H.V × H.V =>
          (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2)))).card =
      (H.edges.filter (fun e => e = (a.1, b.1) ∨ e = (b.1, a.1))).card
  have hLeft :
      (G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2))).filter
          (fun e => e = (Sum.inr a, Sum.inr b) ∨ e = (Sum.inr b, Sum.inr a)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro e he hmem
    rw [Multiset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    rcases hmem with hmem | hmem
    · have h : (Sum.inl p.1 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr a :=
        congrArg Prod.fst hmem
      cases h
    · have h : (Sum.inl p.1 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b :=
        congrArg Prod.fst hmem
      cases h
  rw [Multiset.filter_add, Multiset.card_add, hLeft]
  simp only [Multiset.card_zero, zero_add, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro e _he
  rcases e with ⟨c, d⟩
  have hya : y ≠ a.1 := Ne.symm a.2
  have hyb : y ≠ b.1 := Ne.symm b.2
  by_cases hc : c = y
  · subst c
    simp [wedgeRightVertex, hya, hyb]
  · by_cases hd : d = y
    · subst d
      simp [wedgeRightVertex, hc, hya, hyb]
    · simp only [ne_eq, wedgeRightVertex, Function.comp_apply, hc, ↓reduceDIte, hd, Prod.mk.injEq,
        Sum.inr.injEq]
      simp only [Subtype.ext_iff]

/-- The edges from the common vertex to an unmarked right vertex are exactly
the edges from the right marked vertex before identification. -/
@[simp] theorem num_edges_vertexWedge_marked_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : { z : H.V // z ≠ y }) :
    numEdges (vertexWedge G H x y) (Sum.inl x) (Sum.inr b) =
      numEdges H y b.1 := by
  unfold numEdges
  rw [vertexWedge_edges]
  change
    (Multiset.filter
      (fun e : (Sum G.V { z : H.V // z ≠ y } × Sum G.V { z : H.V // z ≠ y }) =>
        e = (Sum.inl x, Sum.inr b) ∨ e = (Sum.inr b, Sum.inl x))
      (G.edges.map (fun e : G.V × G.V => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e : H.V × H.V =>
          (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2)))).card =
      (H.edges.filter (fun e => e = (y, b.1) ∨ e = (b.1, y))).card
  have hLeft :
      (G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2))).filter
          (fun e => e = (Sum.inl x, Sum.inr b) ∨ e = (Sum.inr b, Sum.inl x)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro e he hmem
    rw [Multiset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    rcases hmem with hmem | hmem
    · have h : (Sum.inl p.2 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b :=
        congrArg Prod.snd hmem
      cases h
    · have h : (Sum.inl p.1 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b :=
        congrArg Prod.fst hmem
      cases h
  rw [Multiset.filter_add, Multiset.card_add, hLeft]
  simp only [Multiset.card_zero, zero_add, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro e _he
  rcases e with ⟨c, d⟩
  have hyb : y ≠ b.1 := Ne.symm b.2
  by_cases hc : c = y
  · subst c
    by_cases hd : d = y
    · subst d
      simp [wedgeRightVertex, hyb]
    · simp only [ne_eq, wedgeRightVertex, Function.comp_apply, ↓reduceDIte, hd, Prod.mk.injEq,
        Sum.inr.injEq, true_and, reduceCtorEq, and_self, or_false, hyb]
      simp only [Subtype.ext_iff]
  · by_cases hd : d = y
    · subst d
      simp only [ne_eq, wedgeRightVertex, Function.comp_apply, hc, ↓reduceDIte, Prod.mk.injEq,
        reduceCtorEq, and_self, Sum.inr.injEq, and_true, false_or, hyb]
      simp only [Subtype.ext_iff]
    · simp [wedgeRightVertex, hc, hd]

/-- A left vertex other than the common vertex has no incident edge in the
unmarked part of the right factor. -/
@[simp] theorem num_edges_vertexWedge_left_right_of_ne
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a : G.V) (b : { z : H.V // z ≠ y }) (hax : a ≠ x) :
    numEdges (vertexWedge G H x y) (Sum.inl a) (Sum.inr b) = 0 := by
  unfold numEdges
  rw [vertexWedge_edges]
  change
    (Multiset.filter
      (fun e : (Sum G.V { z : H.V // z ≠ y } × Sum G.V { z : H.V // z ≠ y }) =>
        e = (Sum.inl a, Sum.inr b) ∨ e = (Sum.inr b, Sum.inl a))
      (G.edges.map (fun e : G.V × G.V => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e : H.V × H.V =>
          (wedgeRightVertex G H x y e.1, wedgeRightVertex G H x y e.2)))).card = 0
  apply Multiset.card_eq_zero.mpr
  apply Multiset.filter_eq_nil.mpr
  intro e he hmem
  rw [Multiset.mem_add] at he
  rcases he with he | he
  · rw [Multiset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    rcases hmem with hmem | hmem
    · have h : (Sum.inl p.2 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b :=
        congrArg Prod.snd hmem
      cases h
    · have h : (Sum.inl p.1 : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b :=
        congrArg Prod.fst hmem
      cases h
  · rw [Multiset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    rcases p with ⟨c, d⟩
    rcases hmem with hmem | hmem
    · have hc := (wedgeRightVertex_eq_left_iff G H x y c a).mp
        (congrArg Prod.fst hmem)
      exact hax hc.2
    · have hd := (wedgeRightVertex_eq_left_iff G H x y d a).mp
        (congrArg Prod.snd hmem)
      exact hax hd.2

/-- Cross-edge multiplicities are concentrated at the common left vertex. -/
@[simp] theorem num_edges_vertexWedge_left_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a : G.V) (b : { z : H.V // z ≠ y }) :
    numEdges (vertexWedge G H x y) (Sum.inl a) (Sum.inr b) =
      if a = x then numEdges H y b.1 else 0 := by
  by_cases hax : a = x
  · subst a
    simp
  · simp [hax, num_edges_vertexWedge_left_right_of_ne G H x y a b hax]

-- See the comment on `prin_wedgeScript` below for why this override is
-- needed (Mathlib v4.33 no longer bumps instance-implicit unification to
-- `default` transparency, so `rw [num_edges_symmetric]` can't unfold the
-- semireducible `vertexWedge` to match its argument types here).
/-- Identifying the marked vertices preserves every edge multiplicity from
the right factor (including those incident to the marked vertex). -/
@[simp] theorem num_edges_vertexWedge_rightVertex
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a b : H.V) :
    numEdges (vertexWedge G H x y)
      (wedgeRightVertex G H x y a) (wedgeRightVertex G H x y b) =
      numEdges H a b := by
  by_cases ha : a = y
  · subst a
    by_cases hb : b = y
    · subst b
      simp [wedgeRightVertex]
    · rw [wedgeRightVertex_marked G H x y,
        wedgeRightVertex_unmarked G H x y b hb]
      exact num_edges_vertexWedge_marked_right G H x y ⟨b, hb⟩
  · by_cases hb : b = y
    · subst b
      calc
        numEdges (vertexWedge G H x y)
            (wedgeRightVertex G H x y a) (wedgeRightVertex G H x y y) =
            numEdges (vertexWedge G H x y) (Sum.inl x) (Sum.inr ⟨a, ha⟩) := by
              rw [num_edges_symmetric]
              simp [wedgeRightVertex, ha]
        _ = numEdges H y a :=
          num_edges_vertexWedge_marked_right G H x y ⟨a, ha⟩
        _ = numEdges H a y := num_edges_symmetric H y a
    · rw [wedgeRightVertex_unmarked G H x y a ha,
        wedgeRightVertex_unmarked G H x y b hb]
      exact num_edges_vertexWedge_right G H x y ⟨a, ha⟩ ⟨b, hb⟩

-- Mathlib v4.33 flips `backward.isDefEq.respectTransparency` to `true` by
-- default (see `Init/MetaTypes.lean`), so instance-implicit unification no
-- longer bumps to `default` transparency and can't see through the
-- semireducible `vertexWedge` to identify `(vertexWedge G H x y).V` with
-- `Sum G.V {..}`. Lean core itself works around this the same way in several
-- library files (e.g. `Init/Data/List/Lemmas.lean`): disable the flag locally
-- for this declaration.
/-- Compatible firing scripts glue to the sum of their principal divisors. -/
theorem prin_wedgeScript
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript G) (τ : firingScript H) (hxy : σ x = τ y) :
    prin (vertexWedge G H x y) (wedgeScript G H x y σ τ hxy) =
      wedgeAddDivisor G H x y (prin G σ) (prin H τ) := by
  funext z
  cases z with
  | inl a =>
      change
        (∑ w : Sum G.V { b : H.V // b ≠ y },
          (wedgeScript G H x y σ τ hxy w - σ a) *
            (numEdges (vertexWedge G H x y) (Sum.inl a) w : ℤ)) =
          wedgeAddDivisor G H x y (prin G σ) (prin H τ) (Sum.inl a)
      rw [Fintype.sum_sum_type]
      simp only [wedgeScript_left, wedgeScript_right,
        num_edges_vertexWedge_left, num_edges_vertexWedge_left_right]
      by_cases hax : a = x
      · subst a
        rw [hxy]
        simp only [if_pos]
        have hMarked :
            (τ y - τ y) * (numEdges H y y : ℤ) = 0 := by simp
        have hRight := sum_unmarked_eq_sum_of_marked_zero H y
          (fun b => (τ b - τ y) * (numEdges H y b : ℤ)) hMarked
        rw [hRight]
        rw [wedgeAddDivisor_left]
        simp only [prin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ↓reduceIte, add_left_inj]
        rw [hxy]
      · simp only [ne_eq, hax, ↓reduceIte, CharP.cast_eq_zero, mul_zero, sum_const_zero, add_zero,
          wedgeAddDivisor_left]
        rfl
  | inr b =>
      change
        (∑ w : Sum G.V { c : H.V // c ≠ y },
          (wedgeScript G H x y σ τ hxy w - τ b.1) *
            (numEdges (vertexWedge G H x y) (Sum.inr b) w : ℤ)) =
          wedgeAddDivisor G H x y (prin G σ) (prin H τ) (Sum.inr b)
      rw [Fintype.sum_sum_type]
      simp only [wedgeScript_left, wedgeScript_right,
        num_edges_vertexWedge_right, num_edges_symmetric]
      simp_rw [num_edges_vertexWedge_left_right]
      have hLeft :
          (∑ a : G.V, (σ a - τ b.1) *
            ((if a = x then numEdges H y b.1 else 0 : ℕ) : ℤ)) =
            (τ y - τ b.1) * (numEdges H b.1 y : ℤ) := by
        simp_rw [Nat.cast_ite, mul_ite]
        simp_rw [Nat.cast_zero, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ x]
        rw [hxy, num_edges_symmetric H y b.1]
        simp
      rw [hLeft]
      have hMarked :
          (τ y - τ b.1) * (numEdges H b.1 y : ℤ) =
            (τ y - τ b.1) * (numEdges H b.1 y : ℤ) := rfl
      have hRight := sum_unmarked_add_marked H y
        (fun c => (τ c - τ b.1) * (numEdges H b.1 c : ℤ))
      rw [add_comm, hRight]
      rw [wedgeAddDivisor_right]
      rfl

/-- A constant firing script has zero principal divisor. -/
@[simp] theorem prin_const_script (G : CFGraph.{u}) (c : ℤ) :
    prin G (fun _ => c) = 0 := by
  funext v
  simp [prin]

/-- Add a constant to a firing script.  This changes no principal divisor. -/
def shiftScript (G : CFGraph.{u}) (σ : firingScript G) (c : ℤ) :
    firingScript G := fun v => σ v + c

@[simp] theorem shiftScript_apply
    (G : CFGraph.{u}) (σ : firingScript G) (c : ℤ) (v : G.V) :
    shiftScript G σ c v = σ v + c := rfl

@[simp] theorem prin_shiftScript
    (G : CFGraph.{u}) (σ : firingScript G) (c : ℤ) :
    prin G (shiftScript G σ c) = prin G σ := by
  funext v
  change (∑ u : G.V, ((σ u + c) - (σ v + c)) * (numEdges G v u : ℤ)) =
    ∑ u : G.V, (σ u - σ v) * (numEdges G v u : ℤ)
  apply Finset.sum_congr rfl
  intro u _hu
  ring

/-- Compatible principal witnesses transport linear equivalence to a wedge. -/
theorem linear_equiv_wedgeAddDivisor_of_prin
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D D' : CFDiv G) (E E' : CFDiv H)
    (σ : firingScript G) (τ : firingScript H) (hxy : σ x = τ y)
    (hG : prin G σ = D' - D) (hH : prin H τ = E' - E) :
    linearEquiv (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) (wedgeAddDivisor G H x y D' E') := by
  apply (principal_iff_eq_prin (vertexWedge G H x y)
    (wedgeAddDivisor G H x y D' E' - wedgeAddDivisor G H x y D E)).mpr
  refine ⟨wedgeScript G H x y σ τ hxy, ?_⟩
  rw [prin_wedgeScript, hG, hH]
  funext z
  cases z with
  | inl a =>
      change (D' a + if a = x then E' y else 0) -
        (D a + if a = x then E y else 0) =
          D' a - D a + if a = x then E' y - E y else 0
      by_cases ha : a = x
      · simp only [ha, ↓reduceIte]
        ring
      · simp [ha]
  | inr b =>
      change E' b.1 - E b.1 = E' b.1 - E b.1
      rfl

/-- Linear equivalence on both factors transports to the wedge.  The proof
normalizes the right firing script by a constant so that the two scripts agree
at the identified vertex. -/
theorem linear_equiv_wedgeAddDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D D' : CFDiv G) (E E' : CFDiv H)
    (hG : linearEquiv G D D') (hH : linearEquiv H E E') :
    linearEquiv (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) (wedgeAddDivisor G H x y D' E') := by
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (D' - D)).mp hG
  obtain ⟨τ, hτ⟩ := (principal_iff_eq_prin H (E' - E)).mp hH
  let c : ℤ := σ x - τ y
  apply linear_equiv_wedgeAddDivisor_of_prin G H x y D D' E E' σ
    (shiftScript H τ c)
  · simp [shiftScript, c]
  · exact hσ.symm
  · simpa using hτ.symm

/-- A compatible pair of effective representatives makes the glued divisor
winnable. -/
theorem winnable_wedgeAddDivisor_of_prin
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D D' : CFDiv G) (E E' : CFDiv H)
    (σ : firingScript G) (τ : firingScript H) (hxy : σ x = τ y)
    (hG : prin G σ = D' - D) (hH : prin H τ = E' - E)
    (hD' : effective D') (hE' : effective E') :
    winnable (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) := by
  refine ⟨wedgeAddDivisor G H x y D' E',
    effective_wedgeAddDivisor G H x y D' E' hD' hE', ?_⟩
  exact linear_equiv_wedgeAddDivisor_of_prin G H x y D D' E E' σ τ hxy hG hH

/-- Winnability transports from the two factors to their vertex wedge. -/
theorem winnable_wedgeAddDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H)
    (hD : winnable G D) (hE : winnable H E) :
    winnable (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) := by
  obtain ⟨D', hD', hDE⟩ := hD
  obtain ⟨E', hE', hEE⟩ := hE
  exact ⟨wedgeAddDivisor G H x y D' E',
    effective_wedgeAddDivisor G H x y D' E' hD' hE',
    linear_equiv_wedgeAddDivisor G H x y D D' E E' hDE hEE⟩

/-- Adding an effective divisor preserves winnability. -/
theorem winnable_add_effective_divisor
    (G : CFGraph.{u}) (D E : CFDiv G)
    (hD : winnable G D) (hE : effective E) : winnable G (D + E) := by
  obtain ⟨D', hD', hDD'⟩ := hD
  refine ⟨D' + E, fun v => add_nonneg (hD' v) (hE v), ?_⟩
  apply (principal_iff_eq_prin G ((D' + E) - (D + E))).mpr
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (D' - D)).mp hDD'
  refine ⟨σ, ?_⟩
  rw [← hσ]
  abel

/-- A rank-one divisor is winnable. -/
theorem winnable_of_rank_ge_one
    (G : CFGraph.{u}) (D : CFDiv G) (hD : rank G D ≥ 1) : winnable G D := by
  classical
  let q : G.V := Classical.choice (inferInstance : Nonempty G.V)
  have hSub : winnable G (D - oneChip (G := G) q) :=
    (rank_ge_one_iff_winnable_sub_one_chip G D).mp hD q
  have hOne : effective (oneChip (G := G) q) := by
    intro v
    by_cases hv : v = q
    · simp [oneChip, hv]
    · simp [oneChip, hv]
  have hWin := winnable_add_effective_divisor G
    (D - oneChip (G := G) q) (oneChip (G := G) q) hSub hOne
  convert hWin using 1
  abel

/-- Rank-one divisors on the two factors glue to a rank-one divisor on their
vertex wedge, without the degree correction needed for a bridge. -/
theorem rank_vertexWedge_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H)
    (hD : rank G D ≥ 1) (hE : rank H E ≥ 1) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro z
  cases z with
  | inl a =>
      have hDa : winnable G (D - oneChip a) :=
        (rank_ge_one_iff_winnable_sub_one_chip G D).mp hD a
      have hEw : winnable H E := winnable_of_rank_ge_one H E hE
      have hWin := winnable_wedgeAddDivisor G H x y (D - oneChip a) E hDa hEw
      have hEq :
          wedgeAddDivisor G H x y D E - oneChip (Sum.inl a) =
            wedgeAddDivisor G H x y (D - oneChip a) E := by
        funext w
        cases w with
        | inl v =>
            change wedgeAddDivisor G H x y D E (Sum.inl v) -
              oneChip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inl v) =
              wedgeAddDivisor G H x y (D - oneChip a) E (Sum.inl v)
            rw [wedgeAddDivisor_left, wedgeAddDivisor_left]
            change (D v + if v = x then E y else 0) -
              (if (Sum.inl v : Sum G.V { z : H.V // z ≠ y }) = Sum.inl a then 1 else 0) =
              (D v - (if v = a then 1 else 0)) + if v = x then E y else 0
            simp only [Sum.inl.injEq]
            ring
        | inr b =>
            change wedgeAddDivisor G H x y D E (Sum.inr b) -
              oneChip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inr b) =
              wedgeAddDivisor G H x y (D - oneChip a) E (Sum.inr b)
            rw [wedgeAddDivisor_right, wedgeAddDivisor_right]
            simp [oneChip]
      rw [hEq]
      exact hWin
  | inr b =>
      have hEb : winnable H (E - oneChip b.1) :=
        (rank_ge_one_iff_winnable_sub_one_chip H E).mp hE b.1
      have hDw : winnable G D := winnable_of_rank_ge_one G D hD
      have hWin := winnable_wedgeAddDivisor G H x y D (E - oneChip b.1) hDw hEb
      have hEq :
          wedgeAddDivisor G H x y D E - oneChip (Sum.inr b) =
            wedgeAddDivisor G H x y D (E - oneChip b.1) := by
        funext w
        cases w with
        | inl v =>
            change wedgeAddDivisor G H x y D E (Sum.inl v) -
              oneChip (G := vertexWedge G H x y) (Sum.inr b) (Sum.inl v) =
              wedgeAddDivisor G H x y D (E - oneChip b.1) (Sum.inl v)
            rw [wedgeAddDivisor_left, wedgeAddDivisor_left]
            change (D v + if v = x then E y else 0) -
              (if (Sum.inl v : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b then 1 else 0) =
              D v + if v = x then E y - (if y = b.1 then 1 else 0) else 0
            simp [Ne.symm b.2]
        | inr q =>
            change wedgeAddDivisor G H x y D E (Sum.inr q) -
              oneChip (G := vertexWedge G H x y) (Sum.inr b) (Sum.inr q) =
              wedgeAddDivisor G H x y D (E - oneChip b.1) (Sum.inr q)
            rw [wedgeAddDivisor_right, wedgeAddDivisor_right]
            change E q.1 -
              (if (Sum.inr q : Sum G.V { z : H.V // z ≠ y }) = Sum.inr b then 1 else 0) =
              E q.1 - (if q.1 = b.1 then 1 else 0)
            simp only [Sum.inr.injEq]
            simp [Subtype.ext_iff]
      rw [hEq]
      exact hWin

/-- Rank-one Brill--Noether witnesses glue across a vertex sum with degrees
adding exactly. -/
theorem BNExists_vertexWedge_rank_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (d₁ d₂ : ℤ)
    (hG : BNExists G 1 d₁) (hH : BNExists H 1 d₂) :
    BNExists (vertexWedge G H x y) 1 (d₁ + d₂) := by
  obtain ⟨D, hDegD, hRankD⟩ := hG
  obtain ⟨E, hDegE, hRankE⟩ := hH
  refine ⟨wedgeAddDivisor G H x y D E, ?_,
    rank_vertexWedge_ge_one G H x y D E hRankD hRankE⟩
  rw [deg_wedgeAddDivisor, hDegD, hDegE]

/-- Restrict a wedge firing script to the left factor. -/
def restrictLeftWedgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firingScript (vertexWedge G H x y)) :
    firingScript G := fun a => σ (Sum.inl a)

/-- Restrict a wedge firing script to the right factor, reading the common
vertex at `y`. -/
def restrictRightWedgeScript (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) (σ : firingScript (vertexWedge G H x y)) :
    firingScript H := fun b => σ (wedgeRightVertex G H x y b)

@[simp] theorem restrictLeftWedgeScript_apply
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript (vertexWedge G H x y)) (a : G.V) :
    restrictLeftWedgeScript G H x y σ a = σ (Sum.inl a) := rfl

@[simp] theorem restrictRightWedgeScript_apply
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript (vertexWedge G H x y)) (b : H.V) :
    restrictRightWedgeScript G H x y σ b = σ (wedgeRightVertex G H x y b) := rfl

@[simp] theorem restrictWedgeScripts_agree
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript (vertexWedge G H x y)) :
    restrictLeftWedgeScript G H x y σ x = restrictRightWedgeScript G H x y σ y := by
  simp [restrictLeftWedgeScript, restrictRightWedgeScript]

@[simp] theorem wedgeScript_restrictWedgeScripts
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (σ : firingScript (vertexWedge G H x y)) :
    wedgeScript G H x y (restrictLeftWedgeScript G H x y σ)
      (restrictRightWedgeScript G H x y σ) (restrictWedgeScripts_agree G H x y σ) = σ := by
  funext z
  cases z with
  | inl a => rfl
  | inr b =>
      change σ (wedgeRightVertex G H x y b.1) = σ (Sum.inr b)
      rw [wedgeRightVertex_unmarked G H x y b.1 b.2]

/-- Add a prescribed integral number of chips at a vertex. -/
def chipShift (G : CFGraph.{u}) (D : CFDiv G) (v : G.V) (t : ℤ) : CFDiv G :=
  D + t • oneChip v

@[simp] theorem chipShift_apply
    (G : CFGraph.{u}) (D : CFDiv G) (v w : G.V) (t : ℤ) :
    chipShift G D v t w = D w + if w = v then t else 0 := by
  simp [chipShift, oneChip]

/-- Principal shifts of a divisor remain linearly equivalent after adding the
same chip shift to both representatives. -/
theorem linear_equiv_chipShift_of_prin
    (G : CFGraph.{u}) (D : CFDiv G) (σ : firingScript G) (v : G.V) (t : ℤ) :
    linearEquiv G (chipShift G D v t) (chipShift G (D + prin G σ) v t) := by
  apply (principal_iff_eq_prin G
    (chipShift G (D + prin G σ) v t - chipShift G D v t)).mpr
  refine ⟨σ, ?_⟩
  funext w
  simp [chipShift]

/-- Opposite chip shifts at the identified vertices cancel in a wedge sum. -/
theorem wedgeAddDivisor_chipShift_cancel
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (t : ℤ) :
    wedgeAddDivisor G H x y (chipShift G D x t) (chipShift H E y (-t)) =
      wedgeAddDivisor G H x y D E := by
  funext z
  cases z with
  | inl a =>
      rw [wedgeAddDivisor_left, wedgeAddDivisor_left]
      simp only [chipShift, zsmul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq,
        neg_smul, Pi.neg_apply, one_chip_apply_v, mul_one]
      by_cases ha : a = x
      · simp only [ha, one_chip_apply_v, mul_one, ↓reduceIte]
        ring
      · simp [ha]
  | inr b =>
      rw [wedgeAddDivisor_right, wedgeAddDivisor_right]
      simp [chipShift, b.2]

/-- Exact winnability convolution across a vertex wedge.  The integer `t`
records how much of the common coefficient is allocated to the left factor. -/
theorem winnable_vertexWedge_iff_exists_chipShift
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) :
    winnable (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ↔
      ∃ t : ℤ, winnable G (chipShift G D x t) ∧
        winnable H (chipShift H E y (-t)) := by
  constructor
  · intro hWin
    obtain ⟨F, hFEffective, hFEquiv⟩ := hWin
    obtain ⟨σ, hσ⟩ :=
      (principal_iff_eq_prin (vertexWedge G H x y)
        (F - wedgeAddDivisor G H x y D E)).mp hFEquiv
    let σG : firingScript G := restrictLeftWedgeScript G H x y σ
    let σH : firingScript H := restrictRightWedgeScript G H x y σ
    let DG : CFDiv G := D + prin G σG
    let EH : CFDiv H := E + prin H σH
    have hPrin : prin (vertexWedge G H x y) σ =
        wedgeAddDivisor G H x y (prin G σG) (prin H σH) := by
      rw [← wedgeScript_restrictWedgeScripts G H x y σ]
      exact prin_wedgeScript G H x y σG σH (restrictWedgeScripts_agree G H x y σ)
    have hF : F = wedgeAddDivisor G H x y DG EH := by
      have hAdd : F = wedgeAddDivisor G H x y D E +
          prin (vertexWedge G H x y) σ := by
        rw [← hσ]
        abel
      rw [hAdd, hPrin]
      funext z
      cases z with
      | inl a =>
          change (D a + if a = x then E y else 0) +
              (prin G σG a + if a = x then prin H σH y else 0) =
            (D a + prin G σG a) +
              if a = x then E y + prin H σH y else 0
          by_cases ha : a = x
          · simp only [ha, ↓reduceIte]
            ring
          · simp [ha]
      | inr b => rfl
    let t : ℤ := -(DG x)
    refine ⟨t, ?_, ?_⟩
    · refine ⟨chipShift G DG x t, ?_,
        linear_equiv_chipShift_of_prin G D σG x t⟩
      intro a
      by_cases hax : a = x
      · subst a
        simp [chipShift, t]
      · have h := hFEffective (Sum.inl a)
        rw [hF, wedgeAddDivisor_left] at h
        simpa [chipShift, hax] using h
    · refine ⟨chipShift H EH y (-t), ?_,
        linear_equiv_chipShift_of_prin H E σH y (-t)⟩
      intro b
      by_cases hby : b = y
      · subst b
        have h := hFEffective (Sum.inl x)
        rw [hF, wedgeAddDivisor_left] at h
        rw [chipShift_apply]
        simp only [if_pos]
        change 0 ≤ EH y + -t
        dsimp [t]
        simp only [neg_neg]
        simp only [if_pos] at h
        linarith
      · have h := hFEffective (Sum.inr ⟨b, hby⟩)
        rw [hF, wedgeAddDivisor_right] at h
        simpa [chipShift, hby] using h
  · rintro ⟨t, hD, hE⟩
    have hWin := winnable_wedgeAddDivisor G H x y
      (chipShift G D x t) (chipShift H E y (-t)) hD hE
    rw [wedgeAddDivisor_chipShift_cancel] at hWin
    exact hWin

/-- Wedging two connected graphs at a vertex produces a connected graph. -/
theorem graph_connected_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graphConnected G) (hH : graphConnected H) :
    graphConnected (vertexWedge G H x y) := by
  intro S hS
  change Finset (Sum G.V { b : H.V // b ≠ y }) at S
  let SL : Finset G.V := Finset.univ.filter (fun a => Sum.inl a ∈ S)
  let SR : Finset H.V := Finset.univ.filter
    (fun b => wedgeRightVertex G H x y b ∈ S)
  have hLeftCross : ∀ a b : G.V,
      Sum.inl a ∈ S → Sum.inl b ∉ S →
        ∃ z ∈ S, ∃ w ∉ S,
          numEdges (vertexWedge G H x y) z w > 0 := by
    intro a b ha hb
    obtain ⟨p, hp, q, hq, hpq⟩ := hG SL
      ⟨a, b, by simpa [SL] using ha, by simpa [SL] using hb⟩
    exact ⟨Sum.inl p, by simpa [SL] using hp,
      Sum.inl q, by simpa [SL] using hq,
      by simpa using hpq⟩
  have hRightCross : ∀ a b : H.V,
      wedgeRightVertex G H x y a ∈ S → wedgeRightVertex G H x y b ∉ S →
        ∃ z ∈ S, ∃ w ∉ S,
          numEdges (vertexWedge G H x y) z w > 0 := by
    intro a b ha hb
    obtain ⟨p, hp, q, hq, hpq⟩ := hH SR
      ⟨a, b, by simpa [SR] using ha, by simpa [SR] using hb⟩
    exact ⟨wedgeRightVertex G H x y p, by simpa [SR] using hp,
      wedgeRightVertex G H x y q, by simpa [SR] using hq,
      by simpa using hpq⟩
  by_cases hx : Sum.inl x ∈ S
  · obtain ⟨_z, w, _hz, hw⟩ := hS
    cases w with
    | inl b => exact hLeftCross x b hx hw
    | inr b =>
        have hbw : wedgeRightVertex G H x y b.1 ∉ S := by
          rw [wedgeRightVertex_unmarked G H x y b.1 b.2]
          exact hw
        exact hRightCross y b.1 (by simpa using hx) hbw
  · obtain ⟨z, _w, hz, _hw⟩ := hS
    cases z with
    | inl a => exact hLeftCross a x hz hx
    | inr a =>
        have hza : wedgeRightVertex G H x y a.1 ∈ S := by
          rw [wedgeRightVertex_unmarked G H x y a.1 a.2]
          exact hz
        exact hRightCross a.1 y hza (by simpa using hx)

end Utilities
