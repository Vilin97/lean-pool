/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.CrosscutExists
import LeanPool.Schoenflies.CrosscutEncloses

/-!
# `lem:outer-chain`, with nothing assumed

`Schoenflies/OuterChain.lean` proves the outer-chain lemma from `Graph.Descent`, the middle
paragraph of the blueprint's proof, which it states and assumes. `Descent` splits into a
combinatorial half and a geometric half, and the two are proved in the two modules imported
here. This file is the one line that puts them together.

The split was worth making. The combinatorial half is a minimisation over walks with no
geometry in it at all; the geometric half is one plane graph, one cycle and one crosscut, with
no chain. Neither module has to know the other exists, and the geometric half turned out to be
**false as the assumed version stated it** — see the counterexample recorded in
`Schoenflies/OuterChain.lean` where that version used to stand. Had the gap been a `sorry`
instead of a named hypothesis, the falsity would have surfaced only when someone came back to
fill it in, and every consumer written in the meantime would have been built on sand.

## Blueprint

* `Graph.IsPlaneChain.outer_chain'` — **`lem:outer-chain`**: if `x` is in the outer face of
  every consecutive pair `Γ p ∪ Γ (p+1)`, it is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`. Same
  statement as `Graph.IsPlaneChain.outer_chain`, with its hypothesis discharged.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {n : ℕ} {x : Plane}

namespace IsPlaneChain

/-- **`lem:outer-chain`.** Let `Γ 0, …, Γ n` (`n ≥ 2`) be finite 2-connected polygonal plane
graphs inside one ambient plane graph, consecutive ones sharing at least two vertices and
nonconsecutive ones disjoint. If `x` is in the outer face of every consecutive pair, it is in
the outer face of the whole chain.

"In the outer face" is spelled as everywhere in this development: off the drawing, with an
unbounded face through it. -/
theorem outer_chain' (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) :=
  h.outer_chain_of_crosscutExists hout h.crosscutExists

end IsPlaneChain

end Graph
