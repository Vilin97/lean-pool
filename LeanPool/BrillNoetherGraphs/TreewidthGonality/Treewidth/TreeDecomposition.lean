/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Tactic

/-!
# Tree decompositions and treewidth

Mathlib has no treewidth as of 2026-08-25, so this module introduces it from
scratch, in the shape needed by the van Dobben de Bruyn--Gijswijt theorem
`treewidth ≤ gonality` (`TreewidthGonality/Gonality/TreewidthGonality.lean`).

## The connectivity convention (binds every downstream module)

Two conventions were available for "the vertex set `S` induces a connected
subgraph of `H`": `SimpleGraph.Subgraph` connectivity, and the induced graph
on the coercion of `S` to a `Set`.  **This library uses the induced-graph
form throughout**:

```
(H.induce (↑S : Set V)).Connected
```

for `S : Finset V`, and likewise for subsets of the tree's node type.  Reasons:

* `SimpleGraph.induce` produces an honest `SimpleGraph ↥s`, so the whole
  `SimpleGraph.Connected`/`Walk`/`Reachable` API applies verbatim with no
  `Subgraph.verts` side conditions;
* `SimpleGraph.Connected` already bundles `Nonempty`, which is exactly the
  nonemptiness condition brambles need, so one field does two jobs;
* the coercion `↑S : Set V` keeps the `Finset` bookkeeping (cardinalities,
  `Finset.filter`) available on the other side of the statement.

`TreewidthGonality/Treewidth/Bramble.lean` and `TreewidthGonality/Gonality/BrambleGonality.lean`
use the same form.  Do not mix in `Subgraph.Connected` without converting.

## Multigraph note

Treewidth is defined for a `SimpleGraph`.  For a chip-firing multigraph `G` the
intended instantiation is `underlyingSimpleGraph G`: parallel edges and loops do
not change treewidth, so nothing is lost.

## Contents

* `TreeDecomposition H` — a bundled tree decomposition: a finite tree together
  with bags satisfying vertex coverage, edge coverage, and coherence.
* `TreeDecomposition.width`, `treewidth` (an `sInf` over `ℕ`).
* `trivialDecomposition` — the one-bag decomposition, which makes the set of
  achievable widths nonempty; `treewidth_le_card_sub_one`.
-/

@[expose] public section

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u}

/-- A **tree decomposition** of a simple graph `H`: a finite tree `tree` on a
node type `Node`, together with a `bag` of vertices at each node, such that

* `cover_vertex` — every vertex lies in some bag;
* `cover_edge` — the two endpoints of every edge lie in a common bag;
* `coherent` — for each vertex `v` the set of nodes whose bag contains `v`
  induces a connected (in particular nonempty) subtree.

`coherent` implies `cover_vertex` (connectedness bundles nonemptiness), but both
are kept: `cover_vertex` is the field callers actually use, and stating it
separately keeps the definition readable. -/
structure TreeDecomposition (H : SimpleGraph V) where
  /-- The nodes of the decomposition tree. -/
  Node : Type
  [nodeFintype : Fintype Node]
  [nodeDecidableEq : DecidableEq Node]
  /-- The decomposition tree. -/
  tree : SimpleGraph Node
  /-- `tree` really is a tree: connected and acyclic. -/
  isTree : tree.IsTree
  /-- The bag of vertices sitting at each node. -/
  bag : Node → Finset V
  /-- Every vertex appears in some bag. -/
  cover_vertex : ∀ v : V, ∃ t, v ∈ bag t
  /-- Every edge has both endpoints in a common bag. -/
  cover_edge : ∀ v w : V, H.Adj v w → ∃ t, v ∈ bag t ∧ w ∈ bag t
  /-- The nodes containing a fixed vertex form a connected subtree. -/
  coherent : ∀ v : V, (tree.induce {t | v ∈ bag t}).Connected

attribute [instance] TreeDecomposition.nodeFintype TreeDecomposition.nodeDecidableEq

namespace TreeDecomposition

variable {H : SimpleGraph V}

/-- The **width** of a tree decomposition: one less than the largest bag size.
The subtraction is truncated `ℕ` subtraction, which is harmless: `sup (card - 1)`
and `sup card - 1` agree in every case, including the degenerate all-bags-empty
one. -/
def width (D : TreeDecomposition H) : ℕ :=
  (Finset.univ.sup fun t : D.Node => (D.bag t).card) - 1

/-- Every bag has at most `width + 1` vertices. -/
theorem card_bag_le_width_succ (D : TreeDecomposition H) (t : D.Node) :
    (D.bag t).card ≤ D.width + 1 := by
  have hsup : (D.bag t).card ≤ Finset.univ.sup fun s : D.Node => (D.bag s).card :=
    Finset.le_sup (f := fun s : D.Node => (D.bag s).card) (Finset.mem_univ t)
  unfold width
  omega

/-- Every bag has at most `Fintype.card V` vertices. -/
theorem card_bag_le_card [Fintype V] (D : TreeDecomposition H) (t : D.Node) :
    (D.bag t).card ≤ Fintype.card V :=
  Finset.card_le_univ _

end TreeDecomposition

/-- The set of widths realized by some tree decomposition of `H`. -/
def widthSet (H : SimpleGraph V) : Set ℕ :=
  {w : ℕ | ∃ D : TreeDecomposition H, D.width = w}

/-- The **treewidth** of `H`: the least width of a tree decomposition.

This is an `sInf` over `ℕ`, which is total; `widthSet_nonempty` (via
`trivialDecomposition`) is what makes the value meaningful rather than the
`sInf ∅ = 0` default. -/
noncomputable def treewidth (H : SimpleGraph V) : ℕ :=
  sInf (widthSet H)

/-- The **trivial tree decomposition**: a single node whose bag is all of `V`. -/
def trivialDecomposition [Fintype V] (H : SimpleGraph V) : TreeDecomposition H where
  Node := Unit
  tree := ⊥
  isTree := SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  cover_vertex := fun v => ⟨(), Finset.mem_univ v⟩
  cover_edge := fun v w _ => ⟨(), Finset.mem_univ v, Finset.mem_univ w⟩
  coherent := fun v => by
    have : Nonempty ↥{t : Unit | v ∈ (Finset.univ : Finset V)} :=
      ⟨⟨(), Finset.mem_univ v⟩⟩
    exact SimpleGraph.Connected.of_subsingleton

/-- Some tree decomposition exists, so `treewidth` is an infimum over a nonempty
set of naturals. -/
theorem widthSet_nonempty [Fintype V] (H : SimpleGraph V) : (widthSet H).Nonempty :=
  ⟨(trivialDecomposition H).width, trivialDecomposition H, rfl⟩

/-- Any tree decomposition bounds the treewidth. -/
theorem treewidth_le_width {H : SimpleGraph V} (D : TreeDecomposition H) :
    treewidth H ≤ D.width :=
  Nat.sInf_le ⟨D, rfl⟩

/-- The treewidth is realized by an actual decomposition. -/
theorem exists_treeDecomposition_width_eq_treewidth [Fintype V] (H : SimpleGraph V) :
    ∃ D : TreeDecomposition H, D.width = treewidth H :=
  Nat.sInf_mem (widthSet_nonempty H)

/-- `treewidth H ≤ |V| - 1`, from the one-bag decomposition. -/
theorem treewidth_le_card_sub_one [Fintype V] (H : SimpleGraph V) :
    treewidth H ≤ Fintype.card V - 1 := by
  refine le_trans (treewidth_le_width (trivialDecomposition H)) ?_
  unfold TreeDecomposition.width
  exact Nat.sub_le_sub_right
    (Finset.sup_le fun t _ => (trivialDecomposition H).card_bag_le_card t) 1

end Utilities.Treewidth
