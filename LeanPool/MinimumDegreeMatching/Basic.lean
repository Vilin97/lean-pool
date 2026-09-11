/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

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

The proofs go through Mathlib's Tutte theorem (`SimpleGraph.tutte`).  For an even vertex
count, a minimum degree of at least `|V| / 2` rules out any Tutte violator (bounding the
number of connected components of `G − u` by `|u|`), hence a perfect matching exists.  The
odd case is reduced to the even case by adjoining a universal apex vertex and deleting it
from the resulting perfect matching.

This file is self-contained and depends only on Mathlib; it is intended to be ready for
upstreaming to `Mathlib/Combinatorics/SimpleGraph/`.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- The neighbourhood cardinality as an `ncard` equals the degree. -/
private theorem neighborSet_ncard_eq_degree (H : SimpleGraph V) (v : V) :
    (H.neighborSet v).ncard = H.degree v := by
  classical
  rw [Set.ncard_eq_toFinset_card', ← card_neighborFinset_eq_degree]
  congr 1

omit [Fintype V] in
open Classical in
/-- A connected component's support contains a vertex together with all of its
neighbours, hence has at least `deg v + 1` elements. -/
private theorem comp_supp_card_ge [Finite V] (H : SimpleGraph V) (v : V) :
    (H.neighborSet v).ncard + 1 ≤ (H.connectedComponentMk v).supp.ncard := by
  let _instFintypeV : Fintype V := Fintype.ofFinite V
  classical
  rw [neighborSet_ncard_eq_degree]
  have hsub : (insert v (H.neighborFinset v) : Finset V) ⊆
      (H.connectedComponentMk v).supp.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, mem_neighborFinset] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | hx
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr
        (ConnectedComponent.eq.mpr (Adj.reachable hx.symm))
  have hcard : (insert v (H.neighborFinset v)).card = H.degree v + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  calc H.degree v + 1 = (insert v (H.neighborFinset v)).card := hcard.symm
    _ ≤ (H.connectedComponentMk v).supp.toFinset.card := Finset.card_le_card hsub
    _ = (H.connectedComponentMk v).supp.ncard := by rw [Set.ncard_eq_toFinset_card']

open Classical in
/-- If every vertex of `H` has degree at least `d`, the number of connected components
times `d + 1` is at most `|V|`. -/
private theorem num_components_le (H : SimpleGraph V) (d : ℕ)
    (hd : ∀ v : V, d ≤ (H.neighborSet v).ncard) :
    Fintype.card H.ConnectedComponent * (d + 1) ≤ Fintype.card V := by
  classical
  have sum_supp_card :
      ∑ c : H.ConnectedComponent, c.supp.toFinset.card = Fintype.card V := by
    rw [← Finset.card_univ, ← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
      exact ⟨fun _ => trivial,
        fun _ => ⟨H.connectedComponentMk v, (ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩⟩
    · intro c₁ _ c₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      rw [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] at h1 h2
      exact hne (h1 ▸ h2)
  rw [← sum_supp_card]
  have hge : ∀ c : H.ConnectedComponent, d + 1 ≤ c.supp.toFinset.card := by
    intro c
    rw [← Set.ncard_eq_toFinset_card']
    obtain ⟨v, hv⟩ := c.exists_rep
    have h := comp_supp_card_ge H v
    have hvc : H.connectedComponentMk v = c := hv
    rw [hvc] at h
    have := hd v
    omega
  calc Fintype.card H.ConnectedComponent * (d + 1)
      = ∑ _c : H.ConnectedComponent, (d + 1) := by
        rw [Finset.sum_const, Finset.card_univ]; ring
    _ ≤ ∑ c : H.ConnectedComponent, c.supp.toFinset.card :=
        Finset.sum_le_sum (fun c _ => hge c)

open Classical in
/-- The number of odd components is at most the total number of components. -/
private theorem oddComponents_ncard_le (H : SimpleGraph V) :
    H.oddComponents.ncard ≤ Fintype.card H.ConnectedComponent := by
  calc H.oddComponents.ncard ≤ (Set.univ : Set H.ConnectedComponent).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = Nat.card H.ConnectedComponent := Set.ncard_univ _
    _ = Fintype.card H.ConnectedComponent := Nat.card_eq_fintype_card

open Classical in
/-- Degree in the induced subgraph on `V \ u` is at least `δ(G) − |u|`. -/
private theorem induced_degree_ge (G : SimpleGraph V) [DecidableRel G.Adj] (u : Finset V)
    (w : ((⊤ : G.Subgraph).deleteVerts (↑u : Set V)).verts) :
    G.minDegree - u.card ≤
      (((⊤ : G.Subgraph).deleteVerts (↑u : Set V)).coe.neighborSet w).ncard := by
  classical
  have hwu : (w : V) ∉ u := by
    have := w.2
    simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe] at this
    exact this
  have hinj : (((⊤ : G.Subgraph).deleteVerts (↑u:Set V)).coe.neighborSet w).ncard
      = ((G.neighborFinset (w : V)) \ u).card := by
    rw [Set.ncard_eq_toFinset_card']
    apply Finset.card_bij (fun (b : ((⊤ : G.Subgraph).deleteVerts (↑u:Set V)).verts)
        (_ : b ∈ _) => (b : V))
    · intro b hb
      rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.coe_adj] at hb
      simp only [SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj,
        SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and, Finset.mem_coe] at hb
      simp only [Finset.mem_sdiff, mem_neighborFinset]
      exact ⟨hb.2.2, hb.2.1⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro c hc
      simp only [Finset.mem_sdiff, mem_neighborFinset] at hc
      have hcv : c ∈ ((⊤ : G.Subgraph).deleteVerts (↑u:Set V)).verts := by
        simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
          Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
        exact hc.2
      refine ⟨⟨c, hcv⟩, ?_, rfl⟩
      rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.coe_adj]
      simp only [SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj,
        SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and, Finset.mem_coe]
      exact ⟨hwu, hc.2, hc.1⟩
  rw [hinj]
  have h1 : G.minDegree ≤ (G.neighborFinset (w:V)).card := by
    rw [card_neighborFinset_eq_degree]; exact G.minDegree_le_degree _
  have h2 : (G.neighborFinset (w:V)).card ≤ ((G.neighborFinset (w:V)) \ u).card + u.card :=
    Finset.card_le_card_sdiff_add_card
  omega

/-- Pure-`ℕ` arithmetic core behind the Tutte-count bound: from a component-count bound,
a trivial component bound, the parity fact and the size relations, the number of odd
components is at most `m`. -/
private lemma arith_core {O K W n d m : ℕ}
    (hOK : O ≤ K) (hK : K * (d - m + 1) ≤ W) (hK0 : K ≤ W)
    (hVn : W = n - m) (hmn : m ≤ n) (hn2d : n ≤ 2 * d)
    (hev : Even n) (hpar : Odd O ↔ Odd W) : O ≤ m := by
  by_cases hm0 : m = 0
  · subst hm0
    have hK1 : K ≤ 1 := by
      by_contra hc
      push Not at hc
      have h2 : 2 * (d - 0 + 1) ≤ K * (d - 0 + 1) := Nat.mul_le_mul_right _ hc
      omega
    have hOle1 : O ≤ 1 := le_trans hOK hK1
    have hevV : Even W := by rw [hVn]; simpa using hev
    have hnodd : ¬ Odd O := by rw [hpar]; exact Nat.not_odd_iff_even.mpr hevV
    have hevO : Even O := Nat.not_odd_iff_even.mp hnodd
    rcases hevO with ⟨t, ht⟩
    omega
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    by_cases hmd : d ≤ m
    · omega
    · push Not at hmd
      obtain ⟨a, hda, ha1⟩ : ∃ a, d = m + a ∧ 1 ≤ a := ⟨d - m, by omega, by omega⟩
      by_contra hcon
      push Not at hcon
      have hKm : m + 1 ≤ K := by omega
      have hK' : K * (d - m + 1) ≤ n - m := by rw [← hVn]; exact hK
      have h3 : (m + 1) * (a + 1) ≤ n - m := by
        have := le_trans (Nat.mul_le_mul_right (d - m + 1) hKm) hK'
        have hae : d - m + 1 = a + 1 := by omega
        rwa [hae] at this
      have hb : n - m ≤ m + 2 * a := by omega
      have hexp : (m + 1) * (a + 1) = m * a + m + a + 1 := by ring
      rw [hexp] at h3
      have hma : a ≤ m * a := Nat.le_mul_of_pos_left a (by omega)
      omega

open Classical in
/-- **No Tutte violator at high minimum degree (even case).**  A finite graph with an even
number of vertices and `|V| ≤ 2·δ(G)` has no Tutte violator. -/
private theorem no_tutte_violator_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : Even (Fintype.card V)) (hcard : Fintype.card V ≤ 2 * G.minDegree)
    (u : Set V) : ¬ G.IsTutteViolator u := by
  classical
  simp only [SimpleGraph.IsTutteViolator, not_lt]
  obtain ⟨uF, huF⟩ : ∃ uF : Finset V, (↑uF : Set V) = u := ⟨u.toFinset, Set.coe_toFinset u⟩
  rw [← huF, Set.ncard_coe_finset]
  have hcardV : Fintype.card ((⊤ : G.Subgraph).deleteVerts (↑uF : Set V)).verts
      = Fintype.card V - uF.card := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top]
    have h : (Set.univ \ (↑uF : Set V)) = ((univ \ uF : Finset V) : Set V) := by simp
    rw [h]
    simp only [SetLike.coe_sort_coe, Fintype.card_coe]
    rw [Finset.card_univ_sdiff]
  have hK := num_components_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set V)).coe
    (G.minDegree - uF.card) (fun w => induced_degree_ge G uF w)
  have hK0 := num_components_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set V)).coe 0
    (fun _ => Nat.zero_le _)
  simp only [zero_add, mul_one] at hK0
  have hOK := oddComponents_ncard_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set V)).coe
  have hpar := SimpleGraph.odd_ncard_oddComponents
    ((⊤ : G.Subgraph).deleteVerts (↑uF : Set V)).coe
  rw [Nat.card_eq_fintype_card] at hpar
  have hnm : uF.card ≤ Fintype.card V := by simpa using Finset.card_le_univ uF
  exact arith_core hOK hK hK0 hcardV hnm hcard hev hpar

open Classical in
/-- **Dirac-type perfect matching (even case).**  A finite simple graph on an even number of
vertices whose minimum degree satisfies `|V| ≤ 2 · δ(G)` has a perfect matching. -/
theorem exists_isPerfectMatching_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : Even (Fintype.card V)) (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  SimpleGraph.tutte.mpr (fun u => no_tutte_violator_of_minDegree G heven hδ u)

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
