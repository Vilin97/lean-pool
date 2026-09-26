/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # External degrees in three-vertex stars -/

public section

namespace ACMax

open Classical in
/-- A degree-four center has two neighbors outside a three-vertex star. -/
theorem star_center_external_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h a b : V) (ha : G.Adj h a) (hb : G.Adj h b)
    (hab : a ≠ b) (hd : G.degree h = 4) :
    (G.neighborFinset h \ ({h, a, b} : Finset V)).card = 2 := by
  classical
  have hinter : G.neighborFinset h ∩ {h, a, b} = {a, b} := by
    ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl⟩
      · exact (G.irrefl hx).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨ha, Or.inr (Or.inl rfl)⟩
      · exact ⟨hb, Or.inr (Or.inr rfl)⟩
  have hcard := Finset.card_inter_add_card_sdiff (G.neighborFinset h) {h, a, b}
  rw [hinter, Finset.card_pair hab, G.card_neighborFinset_eq_degree, hd] at hcard
  omega

open Classical in
/-- A degree-three leaf has two neighbors outside an induced three-vertex star. -/
theorem star_leaf_external_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h a b : V) (ha : G.Adj h a) (hab : ¬G.Adj a b)
    (hd : G.degree a = 3) :
    (G.neighborFinset a \ ({h, a, b} : Finset V)).card = 2 := by
  classical
  have hinter : G.neighborFinset a ∩ {h, a, b} = {h} := by
    ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl⟩
      · rfl
      · exact (G.irrefl hx).elim
      · exact (hab hx).elim
    · rintro rfl
      exact ⟨ha.symm, Or.inl rfl⟩
  have hcard := Finset.card_inter_add_card_sdiff (G.neighborFinset a) {h, a, b}
  rw [hinter, Finset.card_singleton, G.card_neighborFinset_eq_degree, hd] at hcard
  omega

open Finset

open Classical in
/-- Vertices of degree at least four each contribute at least one unit of excess. -/
theorem card_le_sum_excess {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hdeg : ∀ x ∈ S, 4 ≤ G.degree x) :
    S.card ≤ ∑ x ∈ S, (G.degree x - 3) := by
  classical
  calc
    S.card = ∑ _x ∈ S, 1 := by simp
    _ ≤ ∑ x ∈ S, (G.degree x - 3) :=
      Finset.sum_le_sum fun x hx => by have := hdeg x hx; omega

end ACMax
