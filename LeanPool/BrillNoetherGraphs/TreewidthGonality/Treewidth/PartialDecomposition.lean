/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreeDecomposition

/-!
# Partial tree decompositions

A `PartialDecomposition H U` is a tree decomposition of the subgraph of `H`
induced on the finset `U`, carried on the **same** vertex type `V`: bags are
finsets of `V` contained in `U`, and the coverage/coherence axioms are asserted
only for vertices of `U`.

## Why this notion exists

`TreewidthGonality/Treewidth/TreeDecomposition.lean`'s `TreeDecomposition H` demands
`cover_vertex : ∀ v : V, ∃ t, v ∈ bag t` — *every* vertex of the ambient type.
The Bellenbaum--Diestel induction for Seymour--Thomas duality builds a decomposition of `G`
from a root bag `X` together with decompositions of the subgraphs
`G[C ∪ X]`, `C` a component of `G − X`.  Those pieces are not
`TreeDecomposition`s of anything on `V`, and making them so by moving to the
subtype `↥(↑(C ∪ X) : Set V)` would push every statement downstream (bags,
cardinalities, `Bramble` members, the separator of the Menger-free Lemma 2)
through a coercion tower that changes at each level of the recursion.  Hence
this relative notion, with `U = Finset.univ` recovering the absolute one via
`toTreeDecomposition`.

## Gluing

The paper glues the per-component decompositions by *identifying* their
`X`-nodes.  Here they are instead joined **pairwise**, keeping both copies of
the `X`-node (they carry the same bag `X`, so duplicating costs nothing) and
adding a bridge between them; `SeymourThomasInduction.lean` folds that binary
`join` over the components one at a time.  The payoff is that the joined tree
is `(T₁ ⊕g T₂) ⊔ SimpleGraph.edge _ _`, which is exactly the shape mathlib
supports: `SimpleGraph.Connected.sum_sup_edge` gives connectivity and
`SimpleGraph.isTree_iff_connected_and_card` converts an edge count into
`IsTree`, so acyclicity is never proved directly.

## Contents

* `PartialDecomposition`, `width`, `toTreeDecomposition`;
* `single` — the one-bag decomposition of `H` on `U = X`;
* `connected_induce_inl_image` / `..._inr_image` — transport of induced
  connectivity along the two summand inclusions;
* `join` — the binary gluing along a common root bag.
-/

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u} {H : SimpleGraph V}

/-- A **partial tree decomposition**: a tree decomposition of the subgraph of
`H` induced on `U`, stated on the ambient vertex type `V`.

`bag_subset` is what makes the notion relative; `cover_vertex`, `cover_edge`
and `coherent` are the three usual axioms restricted to `U`.  For `v ∉ U` no
bag contains `v` (by `bag_subset`), which is why `coherent` may be — and must
be — asserted only on `U`: `SimpleGraph.Connected` bundles `Nonempty`. -/
structure PartialDecomposition (H : SimpleGraph V) (U : Finset V) where
  /-- The nodes of the decomposition tree. -/
  Node : Type
  [nodeFintype : Fintype Node]
  [nodeDecidableEq : DecidableEq Node]
  /-- The decomposition tree. -/
  tree : SimpleGraph Node
  /-- `tree` really is a tree. -/
  isTree : tree.IsTree
  /-- The bag of vertices at each node. -/
  bag : Node → Finset V
  /-- Every bag lies inside `U`. -/
  bag_subset : ∀ t, bag t ⊆ U
  /-- Every vertex of `U` appears in some bag. -/
  cover_vertex : ∀ v ∈ U, ∃ t, v ∈ bag t
  /-- Every edge of `H` inside `U` has both endpoints in a common bag. -/
  cover_edge : ∀ v ∈ U, ∀ w ∈ U, H.Adj v w → ∃ t, v ∈ bag t ∧ w ∈ bag t
  /-- The nodes containing a fixed vertex of `U` form a connected subtree. -/
  coherent : ∀ v ∈ U, (tree.induce {t | v ∈ bag t}).Connected

attribute [instance] PartialDecomposition.nodeFintype
attribute [instance] PartialDecomposition.nodeDecidableEq

namespace PartialDecomposition

variable {U : Finset V}

/-- The **width** of a partial decomposition, defined exactly as for
`TreeDecomposition`. -/
def width (D : PartialDecomposition H U) : ℕ :=
  (Finset.univ.sup fun t : D.Node => (D.bag t).card) - 1

/-- Every bag has at most `width + 1` vertices. -/
theorem card_bag_le_width_succ (D : PartialDecomposition H U) (t : D.Node) :
    (D.bag t).card ≤ D.width + 1 := by
  have hsup : (D.bag t).card ≤ Finset.univ.sup fun s : D.Node => (D.bag s).card :=
    Finset.le_sup (f := fun s : D.Node => (D.bag s).card) (Finset.mem_univ t)
  unfold width
  omega

/-- A partial decomposition on all of `V` is a tree decomposition. -/
def toTreeDecomposition [Fintype V] (D : PartialDecomposition H Finset.univ) :
    TreeDecomposition H where
  Node := D.Node
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  cover_vertex := fun v => D.cover_vertex v (Finset.mem_univ v)
  cover_edge := fun v w h => D.cover_edge v (Finset.mem_univ v) w (Finset.mem_univ w) h
  coherent := fun v => D.coherent v (Finset.mem_univ v)

@[simp] theorem toTreeDecomposition_bag [Fintype V]
    (D : PartialDecomposition H Finset.univ) (t : D.Node) :
    (D.toTreeDecomposition).bag t = D.bag t := rfl

/-- The width of a decomposition of all of `V`, as a `TreeDecomposition`, is
the width of the partial decomposition. -/
theorem width_toTreeDecomposition [Fintype V] (D : PartialDecomposition H Finset.univ) :
    (D.toTreeDecomposition).width = D.width := rfl

/-! ### The one-bag decomposition -/

/-- The **one-bag partial decomposition**: a single node carrying the bag `X`,
a decomposition of `H` on `U = X`. -/
def single (H : SimpleGraph V) (X : Finset V) : PartialDecomposition H X where
  Node := Unit
  tree := ⊥
  isTree := SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => X
  bag_subset := fun _ => le_rfl
  cover_vertex := fun v hv => ⟨(), hv⟩
  cover_edge := fun v hv w hw _ => ⟨(), hv, hw⟩
  coherent := fun v hv => by
    have : Nonempty ↥{t : Unit | v ∈ X} := ⟨⟨(), hv⟩⟩
    exact SimpleGraph.Connected.of_subsingleton

@[simp] theorem single_bag (H : SimpleGraph V) (X : Finset V) (t : (single H X).Node) :
    (single H X).bag t = X := rfl

/-! ### Transport of induced connectivity along the summand inclusions

`join`'s coherence proof needs to know that a connected set of nodes on one
side stays connected after the two trees are summed and bridged.  There is no
mathlib lemma for this; it is a walk map (`SimpleGraph.Walk.map` along
`SimpleGraph.Embedding.sumInl`, then `Walk.mapLe`, then `Walk.induce`). -/

/-- A connected node set of the left summand stays connected in any graph above
the sum. -/
theorem connected_induce_inl_image {N₁ N₂ : Type} {T₁ : SimpleGraph N₁}
    {T₂ : SimpleGraph N₂} {e : SimpleGraph (N₁ ⊕ N₂)}
    (hle : T₁.sum T₂ ≤ e) {S : Set N₁} (h : (T₁.induce S).Connected) :
    (e.induce (Sum.inl '' S)).Connected := by
  refine h.map (G := T₁.induce S) (H := e.induce (Sum.inl '' S))
    { toFun := fun x => ⟨Sum.inl x.1, ⟨x.1, x.2, rfl⟩⟩
      map_rel' := fun {u v} huv => hle (SimpleGraph.sum_adj_inl.mpr huv) } ?_
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- A connected node set of the right summand stays connected in any graph above
the sum. -/
theorem connected_induce_inr_image {N₁ N₂ : Type} {T₁ : SimpleGraph N₁}
    {T₂ : SimpleGraph N₂} {e : SimpleGraph (N₁ ⊕ N₂)}
    (hle : T₁.sum T₂ ≤ e) {S : Set N₂} (h : (T₂.induce S).Connected) :
    (e.induce (Sum.inr '' S)).Connected := by
  refine h.map (G := T₂.induce S) (H := e.induce (Sum.inr '' S))
    { toFun := fun x => ⟨Sum.inr x.1, ⟨x.1, x.2, rfl⟩⟩
      map_rel' := fun {u v} huv => hle (SimpleGraph.sum_adj_inr.mpr huv) } ?_
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-! ### The binary join -/

section Join

variable [DecidableEq V] {U₁ U₂ X : Finset V}

/-- The tree of `join`: the two trees side by side, plus a bridge between the
two root nodes. -/
def joinTree {N₁ N₂ : Type} (T₁ : SimpleGraph N₁) (T₂ : SimpleGraph N₂)
    (r₁ : N₁) (r₂ : N₂) : SimpleGraph (N₁ ⊕ N₂) :=
  T₁.sum T₂ ⊔ SimpleGraph.edge (Sum.inl r₁) (Sum.inr r₂)

/-- `joinTree` of two trees is a tree.

Discharge plan: `SimpleGraph.isTree_iff_connected_and_card`.  Connectivity is
`SimpleGraph.Connected.sum_sup_edge`.  For the edge count, the two edge sets are
disjoint (`Sum.inl r₁` and `Sum.inr r₂` are non-adjacent in the sum by
`SimpleGraph.not_adj_sum_inl_inr`), `SimpleGraph.edgeSetSumEquiv` splits the
sum's edge set, and `SimpleGraph.IsTree.card_edgeFinset` gives
`|Eᵢ| + 1 = |Nᵢ|`, so `(|N₁| - 1) + (|N₂| - 1) + 1 + 1 = |N₁ ⊕ N₂|`.
Acyclicity is never proved directly. -/
theorem isTree_joinTree {N₁ N₂ : Type} [Fintype N₁] [Fintype N₂]
    [DecidableEq N₁] [DecidableEq N₂] {T₁ : SimpleGraph N₁} {T₂ : SimpleGraph N₂}
    (h₁ : T₁.IsTree) (h₂ : T₂.IsTree) (r₁ : N₁) (r₂ : N₂) :
    (joinTree T₁ T₂ r₁ r₂).IsTree := by
  classical
  have hne : (Sum.inl r₁ : N₁ ⊕ N₂) ≠ Sum.inr r₂ := by simp
  have hedgeSet :
      (SimpleGraph.edge (Sum.inl r₁) (Sum.inr r₂) : SimpleGraph (N₁ ⊕ N₂)).edgeSet
        = {s(Sum.inl r₁, Sum.inr r₂)} :=
    SimpleGraph.edgeSet_edge_of_ne hne
  have hnotmem : s(Sum.inl r₁, Sum.inr r₂) ∉ (T₁.sum T₂).edgeSet := by
    simp [SimpleGraph.mem_edgeSet]
  have hins : (joinTree T₁ T₂ r₁ r₂).edgeSet
      = insert s(Sum.inl r₁, Sum.inr r₂) (T₁.sum T₂).edgeSet := by
    rw [joinTree, SimpleGraph.edgeSet_sup, hedgeSet, Set.union_singleton]
  have hcard : Nat.card (joinTree T₁ T₂ r₁ r₂).edgeSet
      = Nat.card (T₁.sum T₂).edgeSet + 1 := by
    rw [hins, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_insert_of_notMem hnotmem (Set.toFinite _)]
  have hsum : Nat.card (T₁.sum T₂).edgeSet
      = Nat.card T₁.edgeSet + Nat.card T₂.edgeSet := by
    rw [Nat.card_congr SimpleGraph.edgeSetSumEquiv, Nat.card_sum]
  have e₁ := (SimpleGraph.isTree_iff_connected_and_card.mp h₁).2
  have e₂ := (SimpleGraph.isTree_iff_connected_and_card.mp h₂).2
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.Connected.sum_sup_edge h₁.connected h₂.connected, ?_⟩
  rw [hcard, hsum, Nat.card_sum]
  omega

/-- **The binary join.**  Two partial decompositions sharing the bag `X` at a
designated node are glued into a partial decomposition of the union, again with
bag `X` at a designated node (`Sum.inl r₁`).

`hcap` says the two ground sets meet only inside `X`, and `hsep` says `H` has no
edge between `U₁ \ X` and `U₂ \ X`; for the components of `H − X` both hold. -/
def join (D₁ : PartialDecomposition H U₁) (r₁ : D₁.Node) (h₁ : D₁.bag r₁ = X)
    (D₂ : PartialDecomposition H U₂) (r₂ : D₂.Node) (h₂ : D₂.bag r₂ = X)
    (hcap : ∀ v, v ∈ U₁ → v ∈ U₂ → v ∈ X)
    (hsep : ∀ v ∈ U₁, ∀ w ∈ U₂, v ∉ X → w ∉ X → ¬ H.Adj v w) :
    PartialDecomposition H (U₁ ∪ U₂) where
  Node := D₁.Node ⊕ D₂.Node
  tree := joinTree D₁.tree D₂.tree r₁ r₂
  isTree := isTree_joinTree D₁.isTree D₂.isTree r₁ r₂
  bag := Sum.elim D₁.bag D₂.bag
  bag_subset := by
    rintro (a | b) x hx
    · exact Finset.mem_union_left _ (D₁.bag_subset a hx)
    · exact Finset.mem_union_right _ (D₂.bag_subset b hx)
  cover_vertex := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨t, ht⟩ := D₁.cover_vertex v h
      exact ⟨Sum.inl t, ht⟩
    · obtain ⟨t, ht⟩ := D₂.cover_vertex v h
      exact ⟨Sum.inr t, ht⟩
  cover_edge := by
    have hX₁ : X ⊆ U₁ := by rw [← h₁]; exact D₁.bag_subset r₁
    have hX₂ : X ⊆ U₂ := by rw [← h₂]; exact D₂.bag_subset r₂
    intro v hv w hw hadj
    by_cases hv1 : v ∈ U₁
    · by_cases hw1 : w ∈ U₁
      · obtain ⟨t, ht⟩ := D₁.cover_edge v hv1 w hw1 hadj
        exact ⟨Sum.inl t, ht⟩
      · have hw2 : w ∈ U₂ := (Finset.mem_union.mp hw).resolve_left hw1
        have hwX : w ∉ X := fun h => hw1 (hX₁ h)
        have hvX : v ∈ X := by
          by_contra hvX
          exact hsep v hv1 w hw2 hvX hwX hadj
        obtain ⟨t, ht⟩ := D₂.cover_edge v (hX₂ hvX) w hw2 hadj
        exact ⟨Sum.inr t, ht⟩
    · have hv2 : v ∈ U₂ := (Finset.mem_union.mp hv).resolve_left hv1
      by_cases hw2 : w ∈ U₂
      · obtain ⟨t, ht⟩ := D₂.cover_edge v hv2 w hw2 hadj
        exact ⟨Sum.inr t, ht⟩
      · have hw1 : w ∈ U₁ := (Finset.mem_union.mp hw).resolve_right hw2
        have hwX : w ∉ X := fun h => hw2 (hX₂ h)
        have hvX : v ∉ X := fun h => hv1 (hX₁ h)
        exact absurd hadj.symm (hsep w hw1 v hv2 hwX hvX)
  coherent := by
    have hX₁ : X ⊆ U₁ := by rw [← h₁]; exact D₁.bag_subset r₁
    have hX₂ : X ⊆ U₂ := by rw [← h₂]; exact D₂.bag_subset r₂
    have hle : D₁.tree.sum D₂.tree ≤ joinTree D₁.tree D₂.tree r₁ r₂ := le_sup_left
    have hbridge : (joinTree D₁.tree D₂.tree r₁ r₂).Adj (Sum.inl r₁) (Sum.inr r₂) := by
      simp [joinTree, SimpleGraph.edge_adj]
    intro v hv
    have hset : {t : D₁.Node ⊕ D₂.Node | v ∈ Sum.elim D₁.bag D₂.bag t}
        = Sum.inl '' {t : D₁.Node | v ∈ D₁.bag t}
          ∪ Sum.inr '' {t : D₂.Node | v ∈ D₂.bag t} := by
      ext t
      cases t with
      | inl a => simp
      | inr b => simp
    rw [hset]
    by_cases hvX : v ∈ X
    · refine SimpleGraph.connected_induce_union
        (connected_induce_inl_image hle (D₁.coherent v (hX₁ hvX))).preconnected
        (connected_induce_inr_image hle (D₂.coherent v (hX₂ hvX))).preconnected
        (v := Sum.inl r₁) (w := Sum.inr r₂) ⟨r₁, ?_, rfl⟩ ⟨r₂, ?_, rfl⟩ hbridge
      · show v ∈ D₁.bag r₁
        rw [h₁]; exact hvX
      · show v ∈ D₂.bag r₂
        rw [h₂]; exact hvX
    · by_cases hv1 : v ∈ U₁
      · have hempty : Sum.inr '' {t : D₂.Node | v ∈ D₂.bag t} = (∅ : Set (D₁.Node ⊕ D₂.Node)) := by
          rw [Set.image_eq_empty]
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hmem => hvX (hcap v hv1 (D₂.bag_subset t hmem))
        rw [hempty, Set.union_empty]
        exact connected_induce_inl_image hle (D₁.coherent v hv1)
      · have hv2 : v ∈ U₂ := (Finset.mem_union.mp hv).resolve_left hv1
        have hempty : Sum.inl '' {t : D₁.Node | v ∈ D₁.bag t} = (∅ : Set (D₁.Node ⊕ D₂.Node)) := by
          rw [Set.image_eq_empty]
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hmem => hv1 (D₁.bag_subset t hmem)
        rw [hempty, Set.empty_union]
        exact connected_induce_inr_image hle (D₂.coherent v hv2)

/-- **The two-bag decomposition.**  Two nodes joined by an edge, carrying the
bags `X` and `Y`; a decomposition of `H` on `X ∪ Y` whenever every edge of `H`
inside `X ∪ Y` has both ends in `X` or both ends in `Y`.

This is the decomposition the paper uses in the branch where `𝔅 ∪ {C}` fails to
be a bramble (`X` and `Y := V(C) ∪ N(C)`). -/
def pairDecomp (H : SimpleGraph V) (X Y : Finset V)
    (hedge : ∀ v ∈ X ∪ Y, ∀ w ∈ X ∪ Y, H.Adj v w →
      (v ∈ X ∧ w ∈ X) ∨ (v ∈ Y ∧ w ∈ Y)) :
    PartialDecomposition H (X ∪ Y) where
  Node := Unit ⊕ Unit
  tree := joinTree ⊥ ⊥ () ()
  isTree := isTree_joinTree SimpleGraph.IsTree.of_subsingleton
    SimpleGraph.IsTree.of_subsingleton () ()
  bag := Sum.elim (fun _ => X) (fun _ => Y)
  bag_subset := by
    rintro (a | b)
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  cover_vertex := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact ⟨Sum.inl (), h⟩
    · exact ⟨Sum.inr (), h⟩
  cover_edge := by
    intro v hv w hw hadj
    rcases hedge v hv w hw hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Sum.inl (), h1, h2⟩
    · exact ⟨Sum.inr (), h1, h2⟩
  coherent := by
    have hle : (⊥ : SimpleGraph Unit).sum (⊥ : SimpleGraph Unit)
        ≤ joinTree (⊥ : SimpleGraph Unit) (⊥ : SimpleGraph Unit) () () := le_sup_left
    have hbridge : (joinTree (⊥ : SimpleGraph Unit) (⊥ : SimpleGraph Unit) () ()).Adj
        (Sum.inl ()) (Sum.inr ()) := by
      simp [joinTree, SimpleGraph.edge_adj]
    have hsub : ∀ (P : Prop) (hP : P), ((⊥ : SimpleGraph Unit).induce {_t : Unit | P}).Connected := by
      intro P hP
      have : Nonempty ↥{_t : Unit | P} := ⟨⟨(), hP⟩⟩
      exact SimpleGraph.Connected.of_subsingleton
    intro v hv
    have hset : {t : Unit ⊕ Unit | v ∈ Sum.elim (fun _ => X) (fun _ => Y) t}
        = Sum.inl '' {_t : Unit | v ∈ X} ∪ Sum.inr '' {_t : Unit | v ∈ Y} := by
      ext t
      cases t with
      | inl a => simp
      | inr b => simp
    rw [hset]
    by_cases hX : v ∈ X
    · by_cases hY : v ∈ Y
      · exact SimpleGraph.connected_induce_union
          (connected_induce_inl_image hle (hsub _ hX)).preconnected
          (connected_induce_inr_image hle (hsub _ hY)).preconnected
          (v := Sum.inl ()) (w := Sum.inr ()) ⟨(), hX, rfl⟩ ⟨(), hY, rfl⟩ hbridge
      · have hempty : Sum.inr '' {_t : Unit | v ∈ Y} = (∅ : Set (Unit ⊕ Unit)) := by
          rw [Set.image_eq_empty]
          ext t
          simp [hY]
        rw [hempty, Set.union_empty]
        exact connected_induce_inl_image hle (hsub _ hX)
    · have hY : v ∈ Y := (Finset.mem_union.mp hv).resolve_left hX
      have hempty : Sum.inl '' {_t : Unit | v ∈ X} = (∅ : Set (Unit ⊕ Unit)) := by
        rw [Set.image_eq_empty]
        ext t
        simp [hX]
      rw [hempty, Set.empty_union]
      exact connected_induce_inr_image hle (hsub _ hY)

@[simp] theorem pairDecomp_bag_inl (H : SimpleGraph V) (X Y : Finset V) (hedge)
    (t : Unit) : (pairDecomp H X Y hedge).bag (Sum.inl t) = X := rfl

@[simp] theorem pairDecomp_bag_inr (H : SimpleGraph V) (X Y : Finset V) (hedge)
    (t : Unit) : (pairDecomp H X Y hedge).bag (Sum.inr t) = Y := rfl

/-- Every bag of `pairDecomp` is `X` or `Y`. -/
theorem pairDecomp_bag_cases (H : SimpleGraph V) (X Y : Finset V) (hedge)
    (t : (pairDecomp H X Y hedge).Node) :
    (pairDecomp H X Y hedge).bag t = X ∨ (pairDecomp H X Y hedge).bag t = Y := by
  cases t with
  | inl a => exact Or.inl rfl
  | inr b => exact Or.inr rfl

@[simp] theorem join_bag_inl (D₁ : PartialDecomposition H U₁) (r₁ : D₁.Node)
    (h₁ : D₁.bag r₁ = X) (D₂ : PartialDecomposition H U₂) (r₂ : D₂.Node)
    (h₂ : D₂.bag r₂ = X) (hcap) (hsep) (t : D₁.Node) :
    (join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep).bag (Sum.inl t) = D₁.bag t := rfl

@[simp] theorem join_bag_inr (D₁ : PartialDecomposition H U₁) (r₁ : D₁.Node)
    (h₁ : D₁.bag r₁ = X) (D₂ : PartialDecomposition H U₂) (r₂ : D₂.Node)
    (h₂ : D₂.bag r₂ = X) (hcap) (hsep) (t : D₂.Node) :
    (join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep).bag (Sum.inr t) = D₂.bag t := rfl

/-- Every bag of a join is a bag of one of the two pieces. -/
theorem join_bag_cases (D₁ : PartialDecomposition H U₁) (r₁ : D₁.Node)
    (h₁ : D₁.bag r₁ = X) (D₂ : PartialDecomposition H U₂) (r₂ : D₂.Node)
    (h₂ : D₂.bag r₂ = X) (hcap) (hsep)
    (t : (join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep).Node) :
    (∃ a, (join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep).bag t = D₁.bag a) ∨
      (∃ b, (join D₁ r₁ h₁ D₂ r₂ h₂ hcap hsep).bag t = D₂.bag b) := by
  cases t with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr b => exact Or.inr ⟨b, rfl⟩

end Join

end PartialDecomposition

end Utilities.Treewidth
