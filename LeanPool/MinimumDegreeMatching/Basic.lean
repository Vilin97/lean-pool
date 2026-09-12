/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.MinimumDegreeMatching.Spread

/-!
# Perfect and near-perfect matchings from high minimum degree

A finite simple graph whose minimum degree is at least half the number of vertices contains
a perfect matching when its order is even and a near-perfect matching when its order is odd.
The results are stated in the idiomatic `SimpleGraph.Subgraph` matching vocabulary.

## Main results

* `SimpleGraph.exists_isPerfectMatching_of_minDegree`: if `V` has an even number of vertices
  and `|V| ≤ 2 · δ(G)`, then `G` has a perfect matching (`Subgraph.IsPerfectMatching`).
* `SimpleGraph.exists_isMatching_compl_singleton_of_minDegree`: if `V` has an odd number of
  vertices and `|V| ≤ 2 · δ(G) + 1`, then `G` has a matching covering all but exactly one
  vertex, i.e. a matching `M` whose vertex set is the complement `{w}ᶜ` of a single vertex
  `w` (a *near-perfect* matching).

## Implementation notes

The even case reuses the finite-set augmentation theorem from `Spread`. The odd case is
reduced to it by adjoining a universal apex vertex and deleting that vertex from the resulting
perfect matching. Both public formulations therefore share one proof of the degree criterion.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- **Dirac-type perfect matching (even case).**  A finite simple graph on an even number of
vertices whose minimum degree satisfies `|V| ≤ 2 · δ(G)` has a perfect matching. -/
theorem exists_isPerfectMatching_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : Even (Fintype.card V)) (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  exact exists_isPerfectMatching_of_card_le_minDegree heven (by omega)

/-- Adjoin one universal (apex) vertex `none` to `G`. -/
private def apexGraph (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm.symm := by
    rintro (_ | a) (_ | b) h <;> first | exact h | trivial | exact G.adj_symm h
  loopless := by
    refine ⟨fun x hx => ?_⟩
    cases x with
    | none => exact hx
    | some a => exact G.irrefl hx

open Classical in
/-- Every vertex of the apex graph has degree at least `δ(G) + 1`. -/
private lemma apex_degree_ge (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (x : Option V) : G.minDegree + 1 ≤ (apexGraph G).degree x := by
  classical
  rw [← card_neighborFinset_eq_degree]
  cases x with
  | none =>
    have hsub : (Finset.univ.map Function.Embedding.some) ⊆ (apexGraph G).neighborFinset none := by
      intro y hy
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.some_apply] at hy
      obtain ⟨a, rfl⟩ := hy
      rw [mem_neighborFinset]; trivial
    calc G.minDegree + 1 ≤ Fintype.card V := by have := G.minDegree_lt_card; omega
      _ = (Finset.univ.map Function.Embedding.some : Finset (Option V)).card := by
            rw [Finset.card_map, Finset.card_univ]
      _ ≤ ((apexGraph G).neighborFinset none).card := Finset.card_le_card hsub
  | some a =>
    have hsub : insert none ((G.neighborFinset a).map Function.Embedding.some)
        ⊆ (apexGraph G).neighborFinset (some a) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_map, mem_neighborFinset,
        Function.Embedding.some_apply] at hy
      rw [mem_neighborFinset]
      rcases hy with rfl | ⟨b, hb, rfl⟩
      · trivial
      · exact hb
    calc G.minDegree + 1 ≤ G.degree a + 1 := by have := G.minDegree_le_degree a; omega
      _ = (insert none ((G.neighborFinset a).map Function.Embedding.some)).card := by
            rw [Finset.card_insert_of_notMem (by simp), Finset.card_map,
              card_neighborFinset_eq_degree]
      _ ≤ ((apexGraph G).neighborFinset (some a)).card := Finset.card_le_card hsub

open Classical in
/-- **Near-perfect matching from high minimum degree.**  If `|V| ≤ 2·δ(G) + 1`, then `G`
has a matching covering all but at most one vertex. -/
private theorem exists_near_perfect_matching (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ≤ 2 * G.minDegree + 1) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Fintype.card V ≤ M.verts.toFinset.card + 1 := by
  classical
  rcases Nat.even_or_odd (Fintype.card V) with hev | hodd
  · -- even vertex count: a perfect matching
    have hle : Fintype.card V ≤ 2 * G.minDegree := by rcases hev with ⟨t, ht⟩; omega
    obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_minDegree G hev hle
    refine ⟨M, hM.1, ?_⟩
    rw [← Set.ncard_eq_toFinset_card']
    have huniv : M.verts = Set.univ := Set.eq_univ_iff_forall.mpr hM.2
    rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  · -- odd vertex count: apex + perfect matching, then drop the apex
    have hpos : 0 < Fintype.card V := by rcases hodd with ⟨k, hk⟩; omega
    have : Nonempty V := Fintype.card_pos_iff.mp hpos
    have hev' : Even (Fintype.card (Option V)) := by
      rw [Fintype.card_option]; rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have hcard' : Fintype.card (Option V) ≤ 2 * (apexGraph G).minDegree := by
      rw [Fintype.card_option]
      have hmin : G.minDegree + 1 ≤ (apexGraph G).minDegree :=
        le_minDegree_of_forall_le_degree _ _ (apex_degree_ge G)
      omega
    obtain ⟨M', hM'⟩ := exists_isPerfectMatching_of_minDegree (apexGraph G) hev' hcard'
    have hnone : none ∈ M'.verts := hM'.2 none
    obtain ⟨w, hw, huniq⟩ := hM'.1 hnone
    obtain ⟨b₀, rfl⟩ : ∃ b₀, w = some b₀ := by
      cases w with
      | none => exact absurd (M'.adj_sub hw) (by simp [apexGraph])
      | some b => exact ⟨b, rfl⟩
    let M : G.Subgraph :=
      { verts := {a | ∃ b, M'.Adj (some a) (some b)}
        Adj := fun a b => M'.Adj (some a) (some b)
        adj_sub := fun {a b} hab => M'.adj_sub hab
        edge_vert := fun {a b} hab => ⟨b, hab⟩
        symm.symm := fun {a b} hab => M'.adj_symm hab }
    have hMatch : M.IsMatching := by
      intro a ha
      obtain ⟨b, hb⟩ := ha
      refine ⟨b, hb, ?_⟩
      intro b' hb'
      have hsa : some a ∈ M'.verts := M'.edge_vert hb
      obtain ⟨z, hz, huz⟩ := hM'.1 hsa
      exact Option.some_injective _ ((huz (some b') hb').trans (huz (some b) hb).symm)
    refine ⟨M, hMatch, ?_⟩
    rw [← Set.ncard_eq_toFinset_card']
    have hverts : ∀ a : V, a ≠ b₀ → a ∈ M.verts := by
      intro a hab
      have hsa : some a ∈ M'.verts := hM'.2 (some a)
      obtain ⟨z, hz, huz⟩ := hM'.1 hsa
      cases z with
      | none =>
        exact absurd (huniq (some a) (M'.adj_symm hz))
          (fun hc => hab (Option.some_injective _ hc))
      | some c => exact ⟨c, hz⟩
    have hsub : (Set.univ \ {b₀} : Set V) ⊆ M.verts := by
      intro a ha; exact hverts a (by simpa using ha.2)
    have h1 : (Set.univ \ {b₀} : Set V).ncard ≤ M.verts.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (Set.univ \ {b₀} : Set V).ncard = Fintype.card V - 1 := by
      rw [Set.ncard_sdiff (by simp), Set.ncard_univ, Set.ncard_singleton,
        Nat.card_eq_fintype_card]
    omega

open Classical in
/-- **Dirac-type near-perfect matching (odd case).**  A finite simple graph on an odd number
of vertices whose minimum degree satisfies `|V| ≤ 2 · δ(G) + 1` has a matching covering all
but exactly one vertex: there is a vertex `w` and a matching `M` with vertex set `{w}ᶜ`. -/
theorem exists_isMatching_compl_singleton_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : Odd (Fintype.card V)) (hδ : Fintype.card V ≤ 2 * G.minDegree + 1) :
    ∃ (M : G.Subgraph) (w : V), M.IsMatching ∧ M.verts = {w}ᶜ := by
  classical
  obtain ⟨M, hM, hcard⟩ := exists_near_perfect_matching G hδ
  have heven : Even M.verts.toFinset.card := hM.even_card
  have hle : M.verts.toFinset.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ M.verts.toFinset
  have hcompl : M.verts.toFinsetᶜ.card = 1 := by
    rw [Finset.card_compl, Set.toFinset_card]
    rw [Set.toFinset_card] at hle hcard heven
    rcases hodd with ⟨k, hk⟩
    rcases heven with ⟨t, ht⟩
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨M, w, hM, ?_⟩
  ext x
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro hx rfl
    have hxc : x ∈ M.verts.toFinsetᶜ := by rw [hw]; simp
    simp only [Finset.mem_compl, Set.mem_toFinset] at hxc
    exact hxc hx
  · intro hx
    by_contra hxv
    have hxc : x ∈ M.verts.toFinsetᶜ := by
      simp only [Finset.mem_compl, Set.mem_toFinset]; exact hxv
    rw [hw, Finset.mem_singleton] at hxc
    exact hx hxc

end SimpleGraph
