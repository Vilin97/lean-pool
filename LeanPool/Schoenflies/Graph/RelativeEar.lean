/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.Component
import LeanPool.Schoenflies.Graph.Ear
import LeanPool.Schoenflies.Graph.Tree

/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-- **An edge of a subgraph has its ends in the subgraph**, even when the incidence is only
known in the big graph. This is what turns "every edge of the ear has an end outside `V(K)`"
into "no edge of the ear is an edge of `K`". -/
theorem mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

/-- **A subgraph with all the vertices and all the edges is the graph.** The termination
condition of the ear process. -/
theorem eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

/-! ### The relative ear -/

/-- **`lem:relative-ear`, the ear.** A 2-connected subgraph `K` of a loopless 2-connected `G`
that is missing a vertex or an edge has a *relative* ear: a path of `G` whose two distinct
endpoints lie in `K`, whose every other vertex lies **outside** `K`, and none of whose edges
belongs to `K`.

This is the blueprint's own construction, and the freshness of the interior is what
distinguishes it from `Graph.IsTwoConnected.ear_exists`. The first branch takes a component
`L` of `G - V(K)` and a path across it between two of its neighbours in `K`
(`Graph.IsTwoConnected.exists_path_through_component`); the two distinct vertices of `V(K)`
that construction needs are supplied by the counting clause of `K.IsTwoConnected`. The second
branch is the blueprint's "if all vertices are already present, add a missing edge as an ear
of length one", and it is the only place looplessness is used. -/
theorem IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    -- The subgraph's three vertices supply the two distinct targets the component needs.
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    -- Each edge of the ear has an end outside `V(K)`, so it is not an edge of `K`.
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · -- Every vertex is already present, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · -- A one-edge path visits nothing but its two ends, so freshness is vacuous.
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

/-- **One step of the relative ear decomposition.** The ear of
`Graph.IsTwoConnected.relative_ear_exists`, glued on with `Graph.IsTwoConnected.ear`: the
enlarged graph is again a 2-connected subgraph of `G` between `K` and `G`, and it has an edge
that `K` did not have.

The ear data is handed back alongside the enlarged graph, because a consumer of the geometric
version needs the *path*, not merely the fact that the subgraph grew. -/
theorem IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

@[simp]
theorem vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

theorem edgeSet_union_pathGraphOf (h : G.IsWalk a D b) :
    E(B.union (G.pathGraphOf a D)) = E(B) ∪ {e | e ∈ D} := by
  rw [edgeSet_union, pathGraphOf_edgeSet h]

/-! ### Iterating: the decomposition itself -/

/-- **`lem:relative-ear`.** A 2-connected subgraph `K` of a finite loopless 2-connected graph
`G` grows to `G` by repeatedly adding relative ears, stated as the induction principle a
consumer uses: whatever holds of `K` and survives the addition of one ear holds of `G`.

The step is given the whole ear — the path `D` of `G`, its two distinct ends in the current
subgraph `B`, and the fact that its other vertices are outside `B` — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`.

"Finiteness terminates the process" is the strong induction below on `(E(G) \ E(B)).ncard`:
every ear contributes an edge of `G` that `B` was missing, and the process can only be stuck
when `B` has all of `G`'s vertices and edges, which makes `B = G`. -/
theorem IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  -- One step, packaged with the strict drop of the measure.
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    -- A subgraph that is not the graph is missing a vertex or an edge.
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    -- The new edge is one the old subgraph was missing, and nothing was lost.
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  -- Strong induction on the number of edges of `G` the subgraph is still missing.
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · -- Nothing is missing, yet an ear was found: its edges were missing after all.
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end Graph
