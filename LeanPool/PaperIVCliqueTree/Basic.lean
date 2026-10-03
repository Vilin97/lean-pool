/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Erdos81PaperIIContrib.Chordal
import Mathlib.ModelTheory.Graph

/-!
# Clique trees (rooted clique forests) of a finite graph

This file introduces a reusable, Mathlib-style structure for **clique trees**: tree decompositions
whose bags are cliques of the ambient graph, presented in *rooted* form.  A rooted presentation is
carried by a partial `parent` function together with a strictly decreasing `rank`, which makes the
whole ancestor calculus available by well-founded recursion and turns the running-intersection
property into a single local *climb* condition.

The structure is deliberately independent of chordality: this file develops the general API, and
the companion files construct clique trees of chordal graphs (from a perfect elimination order,
and with maximal-clique bags).

## Main definitions

* `SimpleGraph.CliqueTree` — a rooted clique forest for `G`: clique bags, a parent function with
  strictly decreasing rank, a distinguished top node `top v` for every vertex, edge covering, and
  the local climb condition.
* `SimpleGraph.CliqueTree.IsAncestor` — reflexive-transitive closure of `parent`.
* `SimpleGraph.CliqueTree.IsLeaf` — a node that is nobody's parent.
* `SimpleGraph.CliqueTree.privateVerts` — vertices occurring in exactly one bag.
* `SimpleGraph.CliqueTree.branch` — the set of vertices covered by the subtree below a node.
* `SimpleGraph.CliqueTree.edgeBag` — the canonical bag assigned to an edge.

## Main results

* `SimpleGraph.CliqueTree.mem_bag_of_isAncestor` — **intersection property**: the nodes whose bag
  contains a fixed vertex form a connected (upward closed until `top v`) part of the forest.
* `SimpleGraph.CliqueTree.branch_separator` — **branch separation**: for a tree edge `i → j`, the
  intersection `bag i ∩ bag j` separates the branch below `i` from the rest of the graph.
* `SimpleGraph.CliqueTree.isSimplicial_of_mem_privateVerts` — a vertex lying in a single bag is
  simplicial.
* `SimpleGraph.CliqueTree.exists_bag_ne_of_isLeaf` — **leaf elimination**: after deleting a leaf,
  every edge not incident to a private vertex of that leaf is still covered.
* `SimpleGraph.CliqueTree.existsUnique_edgeBag` — **unique edge assignment**: every edge belongs to
  a unique deepest bag.
* `SimpleGraph.CliqueTree.card_edgeFinset_eq_sum_fiber` — **accounting**: the edges of `G` are
  partitioned by their assigned bags.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A **clique tree** (rooted clique forest) of `G` indexed by `ι`.

`bag i` are cliques of `G` covering all vertices and all edges; `parent` organises the nodes into
a rooted forest (made acyclic by the strictly decreasing `rank`); `top v` is the highest node whose
bag contains `v`, and `mem_bag_parent` is the local form of the running-intersection property: a
bag containing `v` which is not `top v` passes `v` on to its parent. -/
structure CliqueTree (G : SimpleGraph V) (ι : Type*) where
  /-- The bag (clique) attached to a node. -/
  bag : ι → Finset V
  /-- The parent of a node, `none` at a root. -/
  parent : ι → Option ι
  /-- A rank witnessing acyclicity; it also distinguishes nodes. -/
  rank : ι → ℕ
  /-- The top node of a vertex: the highest bag containing it. -/
  top : V → ι
  /-- Distinct nodes have distinct ranks. -/
  rank_injective : Function.Injective rank
  /-- The rank strictly decreases towards the root. -/
  rank_parent_lt : ∀ {i j}, parent i = some j → rank j < rank i
  /-- Every bag is a clique. -/
  bag_isClique : ∀ i, G.IsClique (bag i : Set V)
  /-- Every vertex lies in its own top bag. -/
  mem_bag_top : ∀ v, v ∈ bag (top v)
  /-- Every edge lies in some bag. -/
  exists_bag_of_adj : ∀ {u v}, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- Local running-intersection property. -/
  mem_bag_parent : ∀ {i v}, v ∈ bag i → i ≠ top v → ∃ j, parent i = some j ∧ v ∈ bag j

namespace CliqueTree

variable {ι : Type*} (T : CliqueTree G ι)

/-- Every vertex lies in some bag. -/
theorem exists_mem_bag (v : V) : ∃ i, v ∈ T.bag i := ⟨T.top v, T.mem_bag_top v⟩

/-- `T.IsAncestor i j` means that `j` occurs on the chain of parents starting at `i`
(inclusively). -/
@[expose]
def IsAncestor (i j : ι) : Prop := Relation.ReflTransGen (fun a b => T.parent a = some b) i j

variable {T}

@[refl] theorem isAncestor_refl (i : ι) : T.IsAncestor i i := Relation.ReflTransGen.refl

theorem IsAncestor.trans {i j k : ι} (h₁ : T.IsAncestor i j) (h₂ : T.IsAncestor j k) :
    T.IsAncestor i k := Relation.ReflTransGen.trans h₁ h₂

theorem isAncestor_parent {i j : ι} (h : T.parent i = some j) : T.IsAncestor i j :=
  Relation.ReflTransGen.single h

theorem IsAncestor.rank_le {i j : ι} (h : T.IsAncestor i j) : T.rank j ≤ T.rank i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (le_of_lt (T.rank_parent_lt hbc)) ih

/-- The ancestor relation is antisymmetric. -/
theorem IsAncestor.antisymm {i j : ι} (h₁ : T.IsAncestor i j) (h₂ : T.IsAncestor j i) : i = j :=
  T.rank_injective (le_antisymm h₂.rank_le h₁.rank_le)

/-- Ancestors of a fixed node are linearly ordered. -/
theorem IsAncestor.comparable {i j k : ι} (h₁ : T.IsAncestor i j) (h₂ : T.IsAncestor i k) :
    T.IsAncestor j k ∨ T.IsAncestor k j := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl h₂
  | @head a c hstep hchain ih =>
      rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨m, hm, hmk⟩
      · exact Or.inr (Relation.ReflTransGen.head hstep hchain)
      · have hmc : m = c := Option.some_inj.1 (hm.symm.trans hstep)
        exact ih (hmc ▸ hmk)

/-- Following parents from any bag containing `v` eventually reaches `T.top v`. -/
theorem isAncestor_top_of_mem_bag {i : ι} {v : V} (h : v ∈ T.bag i) :
    T.IsAncestor i (T.top v) := by
  generalize hn : T.rank i = n
  induction n using Nat.strong_induction_on generalizing i with
  | _ n ih =>
      by_cases hi : i = T.top v
      · subst hi; exact isAncestor_refl _
      · obtain ⟨j, hj, hvj⟩ := T.mem_bag_parent h hi
        exact Relation.ReflTransGen.head hj (ih _ (hn ▸ T.rank_parent_lt hj) hvj rfl)

/-- **Intersection property.** If `v` lies in the bag of `i`, then it lies in the bag of every node
between `i` and `T.top v`. -/
theorem mem_bag_of_isAncestor {i j : ι} {v : V} (hv : v ∈ T.bag i) (hij : T.IsAncestor i j)
    (hj : T.IsAncestor j (T.top v)) : v ∈ T.bag j := by
  revert hv
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | @head a c hstep hchain ih =>
      intro hva
      by_cases ha : a = T.top v
      · have hja : T.IsAncestor j a := by rw [ha]; exact hj
        have haj : T.IsAncestor a j := Relation.ReflTransGen.head hstep hchain
        have hEq : a = j := haj.antisymm hja
        exact hEq ▸ hva
      · obtain ⟨m, hm, hvm⟩ := T.mem_bag_parent hva ha
        have hmc : m = c := Option.some_inj.1 (hm.symm.trans hstep)
        exact ih (hmc ▸ hvm)

variable (T)

/-- A **leaf** of the clique forest: a node which is nobody's parent. -/
def IsLeaf (i : ι) : Prop := ∀ j, T.parent j ≠ some i

variable {T}

theorem eq_of_isAncestor_of_isLeaf {i k : ι} (hleaf : T.IsLeaf i) (h : T.IsAncestor k i) :
    k = i := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, _, hb⟩
  · rfl
  · exact absurd hb (hleaf b)

/-- A finite nonempty clique forest has a leaf. -/
theorem exists_isLeaf [Finite ι] [Nonempty ι] (T : CliqueTree G ι) : ∃ i, T.IsLeaf i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) T.rank Finset.univ_nonempty
  refine ⟨i, fun j hj => ?_⟩
  exact absurd (hi j (Finset.mem_univ j)) (not_le.2 (T.rank_parent_lt hj))

variable (T)

/-- The vertices occurring in exactly one bag, namely in the bag of `i`. -/
@[expose]
def privateVerts (i : ι) : Set V := {v | v ∈ T.bag i ∧ ∀ k, v ∈ T.bag k → k = i}

variable {T}

theorem mem_privateVerts_iff {i : ι} {v : V} :
    v ∈ T.privateVerts i ↔ v ∈ T.bag i ∧ ∀ k, v ∈ T.bag k → k = i := Iff.rfl

/-- A vertex lying in a single bag is simplicial: all of its neighbours are in that bag, which is
a clique. -/
theorem isSimplicial_of_mem_privateVerts {i : ι} {v : V} (hv : v ∈ T.privateVerts i) :
    G.IsSimplicial v := by
  intro a ha b hb hab
  obtain ⟨ka, hva, haa⟩ := T.exists_bag_of_adj (show G.Adj v a from ha)
  obtain ⟨kb, hvb, hbb⟩ := T.exists_bag_of_adj (show G.Adj v b from hb)
  have hka : ka = i := hv.2 ka hva
  have hkb : kb = i := hv.2 kb hvb
  exact T.bag_isClique i (by simpa [hka] using haa) (by simpa [hkb] using hbb) hab

/-- **Leaf elimination.** Every edge whose endpoints are not private to a leaf `i` is covered by a
bag different from `i`; hence deleting the leaf together with its private vertices leaves a covered
graph. -/
theorem exists_bag_ne_of_isLeaf {i : ι} (hleaf : T.IsLeaf i) {x y : V} (hadj : G.Adj x y)
    (hx : x ∉ T.privateVerts i) (hy : y ∉ T.privateVerts i) :
    ∃ k, k ≠ i ∧ x ∈ T.bag k ∧ y ∈ T.bag k := by
  obtain ⟨k₀, hxk, hyk⟩ := T.exists_bag_of_adj hadj
  by_cases hk : k₀ = i
  · subst hk
    have htop : ∀ z, z ∈ T.bag k₀ → z ∉ T.privateVerts k₀ → k₀ ≠ T.top z := by
      intro z hz hzp htop
      refine hzp ⟨hz, fun k hk => ?_⟩
      exact eq_of_isAncestor_of_isLeaf hleaf (htop ▸ isAncestor_top_of_mem_bag hk)
    obtain ⟨j, hj, hxj⟩ := T.mem_bag_parent hxk (htop x hxk hx)
    obtain ⟨j', hj', hyj⟩ := T.mem_bag_parent hyk (htop y hyk hy)
    refine ⟨j, fun hji => ?_, hxj, ?_⟩
    · exact absurd (hji ▸ T.rank_parent_lt hj) (lt_irrefl _)
    · rwa [Option.some_inj.1 (hj'.symm.trans hj)] at hyj
  · exact ⟨k₀, hk, hxk, hyk⟩

variable (T)

/-- The set of vertices covered by the subtree hanging below `i`. -/
@[expose]
def branch (i : ι) : Set V := {v | ∃ j, T.IsAncestor j i ∧ v ∈ T.bag j}

variable {T}

theorem mem_branch_self {i : ι} {v : V} (h : v ∈ T.bag i) : v ∈ T.branch i :=
  ⟨i, isAncestor_refl i, h⟩

/-- **Branch separation.** For a tree edge `i → j`, every `G`-edge leaving the branch below `i`
does so through the separator `bag i ∩ bag j`. -/
theorem branch_separator {i j : ι} (hp : T.parent i = some j) {x y : V} (hadj : G.Adj x y)
    (hx : x ∈ T.branch i) (hy : y ∉ T.branch i) : x ∈ T.bag i ∧ x ∈ T.bag j := by
  obtain ⟨m, hmi, hxm⟩ := hx
  obtain ⟨k, hxk, hyk⟩ := T.exists_bag_of_adj hadj
  have hki : ¬ T.IsAncestor k i := fun h => hy ⟨k, h, hyk⟩
  have htop : ¬ T.IsAncestor (T.top x) i := fun h =>
    hki ((isAncestor_top_of_mem_bag hxk).trans h)
  have hitop : T.IsAncestor i (T.top x) :=
    (hmi.comparable (isAncestor_top_of_mem_bag hxm)).resolve_right htop
  have hxi : x ∈ T.bag i := mem_bag_of_isAncestor hxm hmi hitop
  refine ⟨hxi, ?_⟩
  have hij : i ≠ T.top x := by
    rintro rfl
    exact htop (isAncestor_refl _)
  have hjtop : T.IsAncestor j (T.top x) := by
    rcases Relation.ReflTransGen.cases_head hitop with h | ⟨m', hm', hm'top⟩
    · exact absurd h hij
    · rwa [Option.some_inj.1 (hm'.symm.trans hp)] at hm'top
  exact mem_bag_of_isAncestor hxi (isAncestor_parent hp) hjtop

/-- The separator of a tree edge disconnects: no `G`-edge joins the branch below `i` (minus the
separator) to the outside of that branch. -/
theorem not_adj_of_branch_separator [DecidableEq V] {i j : ι} (hp : T.parent i = some j)
    {x y : V} (hx : x ∈ T.branch i) (hxs : x ∉ T.bag i ∩ T.bag j) (hy : y ∉ T.branch i) :
    ¬ G.Adj x y := by
  intro hadj
  obtain ⟨h₁, h₂⟩ := branch_separator hp hadj hx hy
  exact hxs (Finset.mem_inter.2 ⟨h₁, h₂⟩)

/-! ### Unique edge assignment and accounting -/

/-- The canonical bag of an edge: the deeper of the two top bags of its endpoints. -/
@[expose]
noncomputable def edgeBag (T : CliqueTree G ι) (e : Sym2 V) : ι :=
  Sym2.lift ⟨fun x y => if T.rank (T.top x) ≤ T.rank (T.top y) then T.top y else T.top x,
    by
      intro x y
      by_cases h : T.rank (T.top x) ≤ T.rank (T.top y)
      · by_cases h' : T.rank (T.top y) ≤ T.rank (T.top x)
        · have hxy : T.top x = T.top y := T.rank_injective (le_antisymm h h')
          simp [hxy]
        · simp [h, h']
      · have h' : T.rank (T.top y) ≤ T.rank (T.top x) := le_of_lt (not_le.1 h)
        simp [h, h']⟩ e

theorem edgeBag_mk (x y : V) :
    T.edgeBag s(x, y) =
      if T.rank (T.top x) ≤ T.rank (T.top y) then T.top y else T.top x := rfl

/-- **Unique edge assignment.** Every edge lies in a unique bag below all bags containing it. -/
theorem existsUnique_edgeBag {x y : V} (hadj : G.Adj x y) :
    ∃! i, x ∈ T.bag i ∧ y ∈ T.bag i ∧ ∀ k, x ∈ T.bag k → y ∈ T.bag k → T.IsAncestor k i := by
  obtain ⟨k₀, hxk, hyk⟩ := T.exists_bag_of_adj hadj
  have hcomp : T.IsAncestor (T.top x) (T.top y) ∨ T.IsAncestor (T.top y) (T.top x) :=
    (isAncestor_top_of_mem_bag hxk).comparable (isAncestor_top_of_mem_bag hyk)
  have key : ∀ {a b : V}, a ∈ T.bag k₀ → b ∈ T.bag k₀ →
      T.IsAncestor (T.top a) (T.top b) →
      (a ∈ T.bag (T.top a) ∧ b ∈ T.bag (T.top a) ∧
        ∀ k, a ∈ T.bag k → b ∈ T.bag k → T.IsAncestor k (T.top a)) := by
    intro a b hak hbk hab
    refine ⟨T.mem_bag_top a, ?_, fun k hka _ => isAncestor_top_of_mem_bag hka⟩
    exact mem_bag_of_isAncestor hbk (isAncestor_top_of_mem_bag hak) hab
  have huniq : ∀ i i', (x ∈ T.bag i ∧ y ∈ T.bag i ∧
      ∀ k, x ∈ T.bag k → y ∈ T.bag k → T.IsAncestor k i) →
      (x ∈ T.bag i' ∧ y ∈ T.bag i' ∧
      ∀ k, x ∈ T.bag k → y ∈ T.bag k → T.IsAncestor k i') → i = i' := by
    rintro i i' ⟨hxi, hyi, hi⟩ ⟨hxi', hyi', hi'⟩
    exact (hi' i hxi hyi).antisymm (hi i' hxi' hyi')
  rcases hcomp with h | h
  · obtain ⟨h₁, h₂, h₃⟩ := key hxk hyk h
    exact ⟨T.top x, ⟨h₁, h₂, h₃⟩, fun i hi => huniq i (T.top x) hi ⟨h₁, h₂, h₃⟩⟩
  · obtain ⟨h₁, h₂, h₃⟩ := key hyk hxk h
    exact ⟨T.top y, ⟨h₂, h₁, fun k hk hk' => h₃ k hk' hk⟩,
      fun i hi => huniq i (T.top y) hi ⟨h₂, h₁, fun k hk hk' => h₃ k hk' hk⟩⟩

/-- The canonical bag of an edge contains both of its endpoints. -/
theorem mem_bag_edgeBag {x y : V} (hadj : G.Adj x y) :
    x ∈ T.bag (T.edgeBag s(x, y)) ∧ y ∈ T.bag (T.edgeBag s(x, y)) := by
  obtain ⟨k₀, hxk, hyk⟩ := T.exists_bag_of_adj hadj
  have hax : T.IsAncestor k₀ (T.top x) := isAncestor_top_of_mem_bag hxk
  have hay : T.IsAncestor k₀ (T.top y) := isAncestor_top_of_mem_bag hyk
  rw [edgeBag_mk]
  by_cases h : T.rank (T.top x) ≤ T.rank (T.top y)
  · have hxy : T.IsAncestor (T.top y) (T.top x) := by
      rcases hax.comparable hay with h' | h'
      · have : T.top x = T.top y := T.rank_injective (le_antisymm h h'.rank_le)
        exact this ▸ isAncestor_refl _
      · exact h'
    rw [ite_eq_left h]
    exact ⟨mem_bag_of_isAncestor hxk hay hxy, T.mem_bag_top y⟩
  · have hyx : T.IsAncestor (T.top x) (T.top y) := by
      rcases hax.comparable hay with h'' | h''
      · exact h''
      · exact absurd h''.rank_le h
    rw [ite_eq_right h]
    exact ⟨T.mem_bag_top x, mem_bag_of_isAncestor hyk hax hyx⟩

/-- **Accounting.** The edges of `G` are partitioned according to their assigned bags. -/
theorem card_edgeFinset_eq_sum_fiber [Fintype V] [DecidableRel G.Adj]
    [Fintype ι] [DecidableEq ι] (T : CliqueTree G ι) :
    G.edgeFinset.card =
      ∑ i : ι, (G.edgeFinset.filter fun e => T.edgeBag e = i).card :=
  Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _

/-- Every edge assigned to `i` has both endpoints in `bag i`. -/
theorem subset_bag_of_mem_fiber [Fintype V] [DecidableRel G.Adj] [DecidableEq ι]
    (T : CliqueTree G ι) {i : ι} {e : Sym2 V}
    (he : e ∈ G.edgeFinset.filter fun e' => T.edgeBag e' = i) : ∀ v ∈ e, v ∈ T.bag i := by
  obtain ⟨he, hi⟩ := Finset.mem_filter.1 he
  induction e with
  | _ x y =>
      have hadj : G.Adj x y := by simpa using he
      obtain ⟨hx, hy⟩ := mem_bag_edgeBag (T := T) hadj
      rw [hi] at hx hy
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hx
      · exact hy

end CliqueTree

end SimpleGraph
