/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Gonality.TreewidthGonality

/-!
# Highlights of the `TreewidthGonality` library

**A public interface, in one file.**  Every main theorem of this library is
restated below as an `example` whose type is written out in full and whose
proof is the real theorem.  There is not a single new definition or theorem
here.

* **For a reader.**  The complete statement of each headline result is visible
  here, with all of its binders and hypotheses.
* **For the build.** Because each `example` is checked by the kernel against
  the real declaration, a change to a statement is detected in this file.

The headline theorem of the library is **`treewidth ≤ gonality`** (van Dobben
de Bruyn–Gijswijt, arXiv:1407.7055), assembled from two independent halves:
the divisor-theoretic bound `bramble_order_le_gonality_succ`, and
Seymour–Thomas bramble/treewidth duality `exists_bramble_of_treewidth`.  Both
are unconditional; `#print axioms` on either reports exactly
`[propext, Classical.choice, Quot.sound]`. The Seymour–Thomas half follows the
Bellenbaum–Diestel proof.
-/

@[expose] public section

namespace TreewidthGonality.Highlights

open Utilities Utilities.Gonality Utilities.Treewidth

universe u

/-! ## The key definitions

Re-exported here so that the statements below read without qualification. -/

/-- The simple graph underlying a chip-firing multigraph: `v` and `w` are
adjacent when `numEdges G v w > 0`.  "The treewidth of a multigraph" means the
treewidth of this graph — parallel edges do not change it.
(`Utilities/Foundations/UnderlyingSimpleGraph.lean`) -/
alias underlyingSimpleGraph := Utilities.underlyingSimpleGraph

/-- **Divisorial gonality**: the least degree of an effective divisor of rank
at least one, as a natural number.
(`Utilities/Gonality/DivisorialGonality.lean`) -/
alias divisorialGonality := Utilities.Gonality.divisorialGonality

/-- A **bramble** of a simple graph: a family of vertex sets, each inducing a
connected subgraph, any two of which touch.
(`TreewidthGonality/Treewidth/Bramble.lean`) -/
alias Bramble := Utilities.Treewidth.Bramble

/-- The **order** of a bramble: the least size of a set meeting every member.
(`TreewidthGonality/Treewidth/Bramble.lean`) -/
alias brambleOrder := Utilities.Treewidth.Bramble.order

/-- **Treewidth**: the least width of a tree decomposition.
(`TreewidthGonality/Treewidth/TreeDecomposition.lean`) -/
alias treewidth := Utilities.Treewidth.treewidth

/-! ## The headline theorem -/

/-- **`treewidth ≤ gonality`** (van Dobben de Bruyn–Gijswijt, arXiv:1407.7055). -/
example (G : CFGraph) (h_conn : graphConnected G) :
    treewidth (underlyingSimpleGraph G) ≤ divisorialGonality G :=
  Utilities.Gonality.treewidth_le_gonality h_conn

/-- The same bound against the dependency's `ℤ`-valued `gonality`. -/
example (G : CFGraph) (h_conn : graphConnected G) :
    (treewidth (underlyingSimpleGraph G) : ℤ) ≤ gonality h_conn :=
  Utilities.Gonality.treewidth_le_gonality_int h_conn

/-! ## Its two halves -/

/-- **Theorem A**, the divisor-theoretic half: no bramble of a connected graph
has order exceeding its gonality plus one. -/
example (G : CFGraph) (h_conn : graphConnected G)
    (𝔅 : Bramble (underlyingSimpleGraph G)) :
    𝔅.order ≤ divisorialGonality G + 1 :=
  Utilities.Gonality.bramble_order_le_gonality_succ h_conn 𝔅

/-- **Seymour–Thomas duality**, the combinatorial half: every finite simple
graph carries a bramble of order exactly `treewidth + 1`. -/
example {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V) :
    ∃ 𝔅 : Bramble H, 𝔅.order = treewidth H + 1 :=
  Utilities.Treewidth.exists_bramble_of_treewidth H

end TreewidthGonality.Highlights
