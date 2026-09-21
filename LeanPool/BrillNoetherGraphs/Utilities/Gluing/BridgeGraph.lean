/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Basic

/-!
# Joining two graphs by a bridge

This module forms the disjoint union of two chip-firing graphs on a sum vertex
type and adds one edge between specified vertices in the two factors. The
construction is useful for reducing divisor questions across separating edges.
-/

open Multiset Finset

namespace Utilities

universe u v

/-- The graph obtained from `G` and `H` by joining `x` to `y` with one edge.
The factor vertex types are kept as the two summands of the new vertex type. -/
abbrev bridgeGraph (G : CFGraph.{u}) (H : CFGraph.{v})
    (x : G.V) (y : H.V) : CFGraph.{max u v} where
  V := Sum G.V H.V
  edges :=
    (Sum.inl x, Sum.inr y) ::ₘ
      (G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2)) +
        H.edges.map (fun e => (Sum.inr e.1, Sum.inr e.2)))
  loopless := by
    intro z hz
    simp only [Multiset.mem_cons, Multiset.mem_add] at hz
    rcases hz with hBridge | hFactor
    · cases z <;> simp at hBridge
    · rcases hFactor with hLeft | hRight
      · rw [Multiset.mem_map] at hLeft
        obtain ⟨e, he, hEq⟩ := hLeft
        rcases e with ⟨a, b⟩
        cases z with
        | inl z =>
            simp only [Prod.mk.injEq, Sum.inl.injEq] at hEq
            rcases hEq with ⟨rfl, rfl⟩
            exact G.loopless _ he
        | inr z => simp at hEq
      · rw [Multiset.mem_map] at hRight
        obtain ⟨e, he, hEq⟩ := hRight
        rcases e with ⟨a, b⟩
        cases z with
        | inl z => simp at hEq
        | inr z =>
            simp only [Prod.mk.injEq, Sum.inr.injEq] at hEq
            rcases hEq with ⟨rfl, rfl⟩
            exact H.loopless _ he

@[simp] theorem bridgeGraph_edges
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    (bridgeGraph G H x y).edges =
      (Sum.inl x, Sum.inr y) ::ₘ
        (G.edges.map (fun e => (Sum.inl e.1, Sum.inl e.2)) +
          H.edges.map (fun e => (Sum.inr e.1, Sum.inr e.2))) := rfl

/-- Joining two factors by one bridge adds their edge counts and one. -/
@[simp] theorem bridgeGraph_edge_card
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    (bridgeGraph G H x y).edges.card = G.edges.card + H.edges.card + 1 := by
  simp [bridgeGraph, Nat.add_assoc]

/-- The sum vertex type has the sum of the two factor vertex counts. -/
@[simp] theorem bridgeGraph_vertex_card
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    Fintype.card (bridgeGraph G H x y).V =
      Fintype.card G.V + Fintype.card H.V := by
  exact Fintype.card_sum

/-- A bridge joining two components creates no new cycle. -/
@[simp] theorem genus_bridgeGraph
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    genus (bridgeGraph G H x y) = genus G + genus H := by
  simp only [genus, bridgeGraph, Multiset.card_cons, Multiset.card_add,
    Multiset.card_map, Fintype.card_sum]
  push_cast
  ring

/-- Edge multiplicities within the left factor are unchanged. -/
@[simp] theorem num_edges_bridgeGraph_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a b : G.V) :
    num_edges (bridgeGraph G H x y) (Sum.inl a) (Sum.inl b) =
      num_edges G a b := by
  simp only [num_edges, bridgeGraph, Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false, or_self,
    not_false_eq_true, Multiset.filter_cons_of_neg, filter_add, Multiset.filter_map,
    Function.comp_apply, and_self, Multiset.filter_false, Multiset.map_zero, Multiset.add_zero,
    Multiset.card_map]
  -- `Multiset.card` became universe-polymorphic in Mathlib v4.33, so
  -- `apply congrArg Multiset.card` can no longer unify its conclusion's
  -- universe metavariable against the goal; `congr 1` sidesteps that.
  congr 1
  apply Multiset.filter_congr
  intro e _he
  rcases e with ⟨p, q⟩
  simp
/-- Edge multiplicities within the right factor are unchanged. -/
@[simp] theorem num_edges_bridgeGraph_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a b : H.V) :
    num_edges (bridgeGraph G H x y) (Sum.inr a) (Sum.inr b) =
      num_edges H a b := by
  simp only [num_edges, bridgeGraph, Prod.mk.injEq, reduceCtorEq, Sum.inr.injEq, false_and, or_self,
    not_false_eq_true, Multiset.filter_cons_of_neg, filter_add, Multiset.filter_map,
    Function.comp_apply, and_self, Multiset.filter_false, Multiset.map_zero, Multiset.zero_add,
    Multiset.card_map]
  -- `Multiset.card` became universe-polymorphic in Mathlib v4.33, so
  -- `apply congrArg Multiset.card` can no longer unify its conclusion's
  -- universe metavariable against the goal; `congr 1` sidesteps that.
  congr 1
  apply Multiset.filter_congr
  intro e _he
  rcases e with ⟨p, q⟩
  simp
/-- The bridge is the only edge between the two factors. -/
@[simp] theorem num_edges_bridgeGraph_inl_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (a : G.V) (b : H.V) :
    num_edges (bridgeGraph G H x y) (Sum.inl a) (Sum.inr b) =
      if a = x ∧ b = y then 1 else 0 := by
  by_cases h : a = x ∧ b = y
  · rcases h with ⟨rfl, rfl⟩
    simp [num_edges, bridgeGraph, Multiset.filter_map]
  · have hReverse : ¬ (x = a ∧ y = b) := by
      rintro ⟨hxa, hyb⟩
      exact h ⟨hxa.symm, hyb.symm⟩
    simp [num_edges, bridgeGraph, Multiset.filter_add,
      Multiset.filter_map, h, hReverse]

/-- The distinguished endpoints are joined by exactly one cross edge. -/
@[simp] theorem num_edges_bridgeGraph_endpoints
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    num_edges (bridgeGraph G H x y) (Sum.inl x) (Sum.inr y) = 1 := by
  simp

-- See the comment above `num_edges_bridgeGraph_inl` for why this override is
-- needed (Mathlib v4.33): `rw [num_edges_symmetric]` below needs to unify
-- `Sum.inr y : G.V ⊕ H.V` against `(bridgeGraph G H x y).V`.
/-- Joining two connected graphs by a bridge produces a connected graph. -/
theorem graph_connected_bridgeGraph
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graph_connected G) (hH : graph_connected H) :
    graph_connected (bridgeGraph G H x y) := by
  intro S hS
  change Finset (Sum G.V H.V) at S
  let SL : Finset G.V := Finset.univ.filter (fun a => Sum.inl a ∈ S)
  let SR : Finset H.V := Finset.univ.filter (fun b => Sum.inr b ∈ S)
  have hLeftCross : ∀ a b : G.V,
      Sum.inl a ∈ S → Sum.inl b ∉ S →
        ∃ z ∈ S, ∃ w ∉ S,
          num_edges (bridgeGraph G H x y) z w > 0 := by
    intro a b ha hb
    have hCut : ∃ p q : G.V, p ∈ SL ∧ q ∉ SL := by
      exact ⟨a, b, by simpa [SL] using ha, by simpa [SL] using hb⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hG SL hCut
    exact ⟨Sum.inl p, by simpa [SL] using hp,
      Sum.inl q, by simpa [SL] using hq, by simpa using hpq⟩
  have hRightCross : ∀ a b : H.V,
      Sum.inr a ∈ S → Sum.inr b ∉ S →
        ∃ z ∈ S, ∃ w ∉ S,
          num_edges (bridgeGraph G H x y) z w > 0 := by
    intro a b ha hb
    have hCut : ∃ p q : H.V, p ∈ SR ∧ q ∉ SR := by
      exact ⟨a, b, by simpa [SR] using ha, by simpa [SR] using hb⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hH SR hCut
    exact ⟨Sum.inr p, by simpa [SR] using hp,
      Sum.inr q, by simpa [SR] using hq, by simpa using hpq⟩
  by_cases hx : Sum.inl x ∈ S
  · by_cases hy : Sum.inr y ∈ S
    · obtain ⟨_z, w, _hz, hw⟩ := hS
      cases w with
      | inl b => exact hLeftCross x b hx hw
      | inr b => exact hRightCross y b hy hw
    · exact ⟨Sum.inl x, hx, Sum.inr y, hy, by simp⟩
  · by_cases hy : Sum.inr y ∈ S
    · refine ⟨Sum.inr y, hy, Sum.inl x, hx, ?_⟩
      rw [num_edges_symmetric]
      simp
    · obtain ⟨z, _w, hz, _hw⟩ := hS
      cases z with
      | inl a => exact hLeftCross a x hz hx
      | inr a => exact hRightCross a y hz hy

end Utilities
