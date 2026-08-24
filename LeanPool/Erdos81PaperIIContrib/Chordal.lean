/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Chordal graphs and induced subgraphs

A simple graph is chordal when every cycle of length at least four has a chord. This file also
defines simplicial vertices and vertex separators, and proves that chordality is inherited along
induced graph embeddings and by induced subgraphs.

## Main definitions

* `SimpleGraph.IsChordal`
* `SimpleGraph.IsSimplicial`
* `SimpleGraph.Separates`
* `SimpleGraph.IsMinimalSeparator`

## Main results

* `SimpleGraph.IsChordal.comap`
* `SimpleGraph.IsChordal.induce`
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A graph is chordal if every cycle of length at least four has a chord. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-- A vertex is simplicial if its neighborhood is a clique. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop := G.IsClique (G.neighborSet v)

/-- `S` separates `a` from `b` if neither endpoint lies in `S` and every walk between them
meets `S`. -/
def Separates (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) a b

/-- `S` is a minimal `a`–`b` separator if it separates the endpoints and no proper subset does. -/
def IsMinimalSeparator (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  G.Separates S a b ∧ ∀ T ⊂ S, ¬ G.Separates T a b

/-- Chordality pulls back along an induced graph embedding. -/
theorem IsChordal.comap {W : Type*} (hG : G.IsChordal) (f : W ↪ V)
    (H : SimpleGraph W) (hf : ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b)) : H.IsChordal := by
  intro v c hc hlen
  let φ : H →g G := ⟨f, fun {a b} h => (hf a b).1 h⟩
  have hinj : Function.Injective φ := f.injective
  obtain ⟨x, y, hx, hy, hadj, hchord⟩ :=
    hG (c.map φ) (hc.map hinj) (by rwa [Walk.length_map])
  rw [Walk.support_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  refine ⟨x', y', hx', hy', (hf x' y').2 hadj, fun hmem => hchord ?_⟩
  rw [Walk.edges_map]
  exact List.mem_map.2 ⟨s(x', y'), hmem, rfl⟩

/-- Every induced subgraph of a chordal graph is chordal. -/
theorem IsChordal.induce (hG : G.IsChordal) (W : Set V) : (G.induce W).IsChordal :=
  hG.comap (Function.Embedding.subtype (· ∈ W)) _ (by simp)

end SimpleGraph
