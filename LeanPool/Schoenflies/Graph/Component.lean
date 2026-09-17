/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.Walk
import LeanPool.Schoenflies.Graph.TwoConnected

/-!
# Components and shortest paths

The two prerequisites of the relative ear decomposition (`lem:relative-ear`) that no earlier
module builds: the **component** of a vertex, and a **shortest** walk between two vertices.
Both are then spent on the geometric heart of that lemma — a component of `G - S` has two
distinct neighbours in `S`, and a path between two of them whose interior lies outside `S`.

## The component is a comprehension

`G.component u = {v | G.Reaches u v}`, exactly as `connectedComponentIn` collects the points
a space reaches. Nothing restricts the comprehension to `V(G)`: the empty walk already demands
a vertex of the graph (`Graph.IsWalk.nil`), so `G.Reaches u v` carries `v ∈ V(G)` with it, and
a clause `v ∈ V(G) ∧ …` would be redundant noise at every use site. When `u ∉ V(G)` the
component is empty, which is the convention that makes the covering statement
`Graph.iUnion_component` true with no side condition.

Reachability is an equivalence relation on `V(G)`, so the component is closed under `Reaches`,
two components are equal or disjoint, and the components cover `V(G)`. The one statement that
is not pure equivalence-relation bookkeeping is that the **induced** subgraph on a component
is connected: a walk between two vertices of a component never leaves it
(`Graph.IsWalk.walkVertices_subset_component`), so it is already a walk of the induced
subgraph, by `Graph.IsWalk.anti`.

## Shortest walks need no finiteness

The set of lengths of walks from `u` to `v` is a nonempty set of naturals, so it has a least
element — `Nat.find`, with no `Graph.Finite` hypothesis anywhere. That is worth noticing: the
blueprint says "in a finite graph", but finiteness is used there only to terminate the ear
*process*, never to find one shortest path.

A minimum-length walk is automatically a path (`Graph.IsWalk.isPath_of_minLength`). The proof
is the induction of `Graph.IsWalk.contains_path` run once more, with lengths attached: if the
step's source were revisited later, `Graph.IsPath.from_visited` would cut the tail down to a
strictly shorter walk with the same ends, and a path's edge list repeats nothing
(`Graph.IsPath.nodup`), so the cut piece really is no longer than what it came from
(`List.subperm_of_subset`).

## The two neighbours, without a contradiction

The blueprint argues by contradiction: "otherwise its unique neighbour would be a cut vertex".
Here the two neighbours are *constructed*, in the shape `Graph.IsTwoConnected.no_bridge`
already uses. A walk from the component out to a vertex of `S` crosses the boundary
(`Graph.IsWalk.crossing`), and the crossing edge's far end is in `S` — because a neighbour
outside `S` would still be in the component. That is the first neighbour `c`. For the second,
delete `c`: the big graph is still connected, so the same crossing argument runs inside
`G - c`, and its crossing edge's far end is a neighbour that is not `c`.

Two distinct vertices of `S` are needed, and used exactly once: the walk of the second step
must aim at a vertex of `S` other than `c`. In the application `S` is the vertex set of a
2-connected subgraph, which has three.

## Blueprint

* `Graph.component`, `Graph.induce_component_connected` — "a component `L` of `G - V(H₀)`" in
  the proof of `lem:relative-ear`.
* `Graph.exists_minLength_isPath` — "a shortest path through `L`", same proof.
* `Graph.IsTwoConnected.component_two_neighbors` — "if a component `L` of `G - V(H₀)` contains
  a vertex, it has at least two distinct neighbors in `H₀`; otherwise its unique neighbor
  would be a cut vertex of `G`".
* `Graph.IsTwoConnected.exists_path_through_component` — "a shortest path through `L` between
  two such neighbors is an ear": a path of `G` between two distinct vertices of `S`, whose
  every other vertex is outside `S`, which has at least one such vertex, and each of whose
  edges has an end outside `S`. The word *ear* is not used here and nothing about ears is
  assumed; this is the raw path that a consumer recognises as one.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

/-! ### Components -/

/-- The component of `u` in `G`: the vertices `u` reaches. A comprehension over the vertices,
not an indexed union of connected subgraphs; the membership test is `Graph.Reaches` itself,
which is why every closure property below is one line of the reachability API.

No `v ∈ V(G)` clause: `Graph.Reaches` already carries it, since the empty walk demands a
vertex of the graph. For `u ∉ V(G)` the component is empty. -/
def component (G : Graph α β) (u : α) : Set α := {v | G.Reaches u v}

theorem mem_component_iff : v ∈ G.component u ↔ G.Reaches u v := Iff.rfl

theorem component_subset_vertexSet : G.component u ⊆ V(G) := fun _ h ↦ Reaches.right_mem h

theorem mem_component_self (hu : u ∈ V(G)) : u ∈ G.component u := Reaches.refl hu

theorem component_nonempty (hu : u ∈ V(G)) : (G.component u).Nonempty :=
  ⟨u, mem_component_self hu⟩

/-- A vertex the graph does not have reaches nothing. -/
theorem component_eq_empty (hu : u ∉ V(G)) : G.component u = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ hu (Reaches.left_mem h)

/-- **A component is closed under reachability**, which is the property every consumer uses:
whatever a vertex of the component reaches is in the component. -/
theorem mem_component_of_reaches (hv : v ∈ G.component u) (h : G.Reaches v w) :
    w ∈ G.component u :=
  Reaches.trans hv h

/-- A component is closed under taking an edge. -/
theorem mem_component_of_isLink (hx : x ∈ G.component u) (hl : G.IsLink e x y) :
    y ∈ G.component u :=
  mem_component_of_reaches hx (Reaches.of_isLink hl)

theorem mem_component_comm : v ∈ G.component u ↔ u ∈ G.component v := reaches_comm

/-- A vertex of a component has the same component. -/
theorem component_eq_of_mem (hv : v ∈ G.component u) : G.component v = G.component u :=
  Set.ext fun _ ↦ ⟨fun h ↦ Reaches.trans hv h, fun h ↦ Reaches.trans (Reaches.symm hv) h⟩

/-- **Two components are equal or disjoint.** -/
theorem component_eq_or_disjoint (u v : α) :
    G.component u = G.component v ∨ Disjoint (G.component u) (G.component v) := by
  rcases em (∃ w, w ∈ G.component u ∧ w ∈ G.component v) with ⟨w, hu, hv⟩ | hne
  · exact Or.inl ((component_eq_of_mem hu).symm.trans (component_eq_of_mem hv))
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' ↦ hne ⟨w, hw, hw'⟩)

/-- **The components cover the vertex set.** -/
theorem iUnion_component (G : Graph α β) : ⋃ u ∈ V(G), G.component u = V(G) :=
  Set.Subset.antisymm (Set.iUnion₂_subset fun _ _ ↦ component_subset_vertexSet)
    fun _ hx ↦ Set.mem_biUnion hx (mem_component_self hx)

/-! ### The subgraph induced on a component -/

theorem induce_component_le : G.induce (G.component u) ≤ G :=
  induce_le component_subset_vertexSet

theorem mem_vertexSet_induce_component : v ∈ V(G.induce (G.component u)) ↔ G.Reaches u v :=
  Iff.rfl

/-- **A walk out of a component stays in it**: every vertex it visits is reachable from the
component's base point, one step at a time. -/
theorem IsWalk.walkVertices_subset_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    G.walkVertices x W ⊆ G.component u := by
  induction h with
  | nil => simpa using hx
  | @cons x' w y e W hl _ ih =>
    intro z hz
    rcases mem_walkVertices_cons hl hz with rfl | hz'
    · exact hx
    · exact ih (mem_component_of_isLink hx hl) hz'

/-- A walk that starts in a component is a walk of the subgraph induced on it. Both ends of
each of its edges are vertices it visits, so the edges survive the induction. -/
theorem IsWalk.induce_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    (G.induce (G.component u)).IsWalk x W y := by
  refine h.anti induce_component_le hx fun g hg ↦ ?_
  obtain ⟨s, t, hst⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  exact ⟨s, t, hst,
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_left⟩),
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_right⟩)⟩

/-- **The subgraph induced on a component is connected**, with the base point as hub. -/
theorem induce_component_connected (hu : u ∈ V(G)) : (G.induce (G.component u)).Connected := by
  refine Connected.of_hub (mem_component_self hu) fun z hz ↦ ?_
  obtain ⟨W, hW⟩ := mem_component_iff.1 hz
  exact ⟨W, hW.induce_component (mem_component_self hu)⟩

/-! ### Shortest walks and shortest paths -/

/-- **A shortest walk exists** between any two vertices one of which reaches the other: the
lengths of such walks form a nonempty set of naturals. No finiteness is needed. -/
theorem exists_minLength_isWalk (h : G.Reaches u v) :
    ∃ W, G.IsWalk u W v ∧ ∀ W', G.IsWalk u W' v → W.length ≤ W'.length := by
  classical
  obtain ⟨W₀, hW₀⟩ := h
  have hex : ∃ n, ∃ W, G.IsWalk u W v ∧ W.length = n := ⟨W₀.length, W₀, hW₀, rfl⟩
  obtain ⟨W, hW, hlen⟩ := Nat.find_spec hex
  exact ⟨W, hW, fun W' hW' ↦ hlen ▸ Nat.find_le ⟨W', hW', rfl⟩⟩

/-- **A shortest walk is a path.** If the vertex a step departs from were visited again, the
tail could be cut there (`Graph.IsPath.from_visited`) and the result would be a strictly
shorter walk with the same ends — strictly, because a path repeats no edge and the cut piece
is a sublist-up-to-permutation of what it came from. -/
theorem IsWalk.isPath_of_minLength (h : G.IsWalk u W v)
    (hmin : ∀ W', G.IsWalk u W' v → W.length ≤ W'.length) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW ih =>
    -- The tail is shortest among walks from the waypoint: prepending `e` to a shorter one
    -- would beat the whole walk.
    have hmin' : ∀ W', G.IsWalk w W' v → W.length ≤ W'.length := fun W' hW' ↦ by
      have := hmin (e :: W') (.cons hl hW')
      simp only [List.length_cons] at this
      omega
    have hP : G.IsPath w W v := ih hmin'
    refine .cons hl hP fun hmem ↦ ?_
    obtain ⟨T, hT, hTW⟩ := hP.from_visited hmem
    have h₁ : T.length ≤ W.length := (List.subperm_of_subset hT.nodup hTW).length_le
    have h₂ := hmin T hT.isWalk
    simp only [List.length_cons] at h₂
    omega

/-- **A shortest path exists**: among all walks between two vertices, one of least length,
and it is a path. This is the blueprint's "shortest path". -/
theorem exists_minLength_isPath (h : G.Reaches u v) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  let ⟨W, hW, hmin⟩ := exists_minLength_isWalk h
  ⟨W, hW.isPath_of_minLength hmin, hmin⟩

theorem Connected.exists_minLength_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  _root_.Graph.exists_minLength_isPath (h.reaches hu hv)

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

/-- A walk of `G - S` visits only vertices of `G` outside `S` — computed in `G`, which is the
form the freshness clause of a path of `G` reads. -/
theorem IsWalk.walkVertices_subset_of_deleteVerts (h : (G.deleteVerts S).IsWalk u W v) :
    G.walkVertices u W ⊆ V(G) \ S := by
  intro z hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨g, hg, hinc⟩
  · simpa using h.left_mem
  -- An edge of the walk survives the deletion, so both of its ends do.
  have hgE := h.edge_mem hg
  rw [edgeSet_deleteVerts] at hgE
  obtain ⟨s, t, hst, hs, ht⟩ := hgE
  rcases hinc.eq_or_eq_of_isLink hst with rfl | rfl
  exacts [⟨hst.left_mem, hs⟩, ⟨hst.right_mem, ht⟩]

/-- The component of `G - S` at `x`, seen in `G`: outside `S`, and inside `V(G)`. -/
theorem component_deleteVerts_subset : (G.deleteVerts S).component x ⊆ V(G) \ S := by
  intro z hz
  have := component_subset_vertexSet hz
  rwa [vertexSet_deleteVerts] at this

/-- **A neighbour of a component of `G - S` that is outside `S` is in the component.** The
edge joining them survives the deletion, so it extends the walk. -/
theorem mem_component_deleteVerts_of_isLink (hp : p ∈ (G.deleteVerts S).component x)
    (hl : G.IsLink e p q) (hq : q ∉ S) : q ∈ (G.deleteVerts S).component x :=
  mem_component_of_isLink hp
    ((deleteVerts_isLink G S).2 ⟨hl, (component_deleteVerts_subset hp).2, hq⟩)

/-- **Walking out of a component of `G - S` meets `S` along an edge.** The walk may live in
any subgraph `K` of `G` — it is run inside `G - c` once — but the component is always the one
of `G - S`, which is what makes the conclusion usable twice.

This is `Graph.IsWalk.crossing` plus the previous lemma: the crossing edge's far end is
outside the component, so it cannot be outside `S`. -/
theorem exists_isLink_out_of_component {K : Graph α β} (hKG : K ≤ G)
    (h : K.IsWalk x W v) (hx : x ∈ (G.deleteVerts S).component x) (hv : v ∈ S) :
    ∃ p ∈ (G.deleteVerts S).component x, ∃ g ∈ W, ∃ t ∈ S, K.IsLink g p t := by
  have hvL : v ∉ (G.deleteVerts S).component x := fun hmem ↦
    (component_deleteVerts_subset hmem).2 hv
  obtain ⟨g, hg, s, t, hst, hs, ht⟩ := h.crossing hx hvL
  refine ⟨s, hs, g, hg, t, ?_, hst⟩
  by_contra htS
  exact ht (mem_component_deleteVerts_of_isLink hs (hst.mono hKG) htS)

/-! ### The two neighbours of a component, and the path through it -/

/-- **A component of `G - S` has two distinct neighbours in `S`** — the first half of
`lem:relative-ear`, with the blueprint's contradiction turned into a construction.

`S` must contain two distinct vertices; in the application it is the vertex set of a
2-connected subgraph, which has three. The first neighbour `c` comes from a walk of `G` out of
the component to a vertex of `S`; the second from the same walk run inside `G - c`, which is
still connected because `G` is 2-connected, and aimed at a vertex of `S` other than `c`. -/
theorem IsTwoConnected.component_two_neighbors (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (∃ p ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g p c) ∧
      (∃ q ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g q d) := by
  have hxD : x ∈ V(G.deleteVerts S) := by rw [vertexSet_deleteVerts]; exact ⟨hx, hxS⟩
  have hxL : x ∈ (G.deleteVerts S).component x := mem_component_self hxD
  -- First neighbour: walk from `x` to `a` in `G` and take the edge where it leaves.
  obtain ⟨W, hW⟩ := hG.connected.reaches hx (hS ha)
  obtain ⟨p, hp, g, -, c, hc, hgpc⟩ := exists_isLink_out_of_component le_rfl hW hxL ha
  -- Second neighbour: aim at a vertex of `S` other than `c`, inside `G - c`.
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ S, t ≠ c := by
    rcases eq_or_ne a c with rfl | hac
    · exact ⟨b, hb, fun h ↦ hab h.symm⟩
    · exact ⟨a, ha, hac⟩
  have hxc : x ∈ V(G.deleteVerts {c}) :=
    mem_deleteVerts_singleton_of_ne hx fun h ↦ hxS (h ▸ hc)
  have htc' : t ∈ V(G.deleteVerts {c}) := mem_deleteVerts_singleton_of_ne (hS ht) htc
  obtain ⟨W', hW'⟩ := (hG.deleteVerts_connected' c).reaches hxc htc'
  obtain ⟨q, hq, g', -, d, hd, hgqd⟩ :=
    exists_isLink_out_of_component deleteVerts_le hW' hxL ht
  -- The second crossing edge lives in `G - c`, so its far end is not `c`.
  have hdc : d ≠ c := by
    have := ((deleteVerts_isLink G {c}).1 hgqd).2.2
    simpa using this
  exact ⟨c, hc, d, hd, fun h ↦ hdc h.symm, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd.mono deleteVerts_le⟩⟩

/-- Reading off the vertices of a walk with one edge appended at the far end. Purely about
lists; used to check the freshness clause when a path inside a component is capped with an
edge back into `S`. -/
theorem mem_walkVertices_append_singleton (hy : y ∈ G.walkVertices u (W ++ [e])) :
    y ∈ G.walkVertices u W ∨ G.Inc e y := by
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with h | ⟨g, hg, hinc⟩
  · exact Or.inl (mem_walkVertices_of_mem_covered h)
  · obtain rfl : g = e := by simpa using hg
    exact Or.inr hinc

/-- **The path through a component** — the second half of `lem:relative-ear`, without the word
*ear*: in a 2-connected `G`, from a vertex outside a set `S` that has two distinct vertices,
one gets a path of `G` whose two endpoints are distinct vertices of `S`, whose every other
vertex is outside `S`, which has at least one vertex outside `S`, and each of whose edges has
an end outside `S`.

The last two clauses are what make the ear process terminate and what make the path *new*: it
really does add a vertex, and none of its edges belongs to a subgraph whose vertices all lie
in `S`.

The path is built from the two neighbours of the component: the edge into the component, a
path across the component (in `G - S`, hence never touching `S`), and the edge back out. -/
theorem IsTwoConnected.exists_path_through_component (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, ∃ P, c ≠ d ∧ G.IsPath c P d ∧
      (∀ y ∈ G.walkVertices c P, y ≠ c → y ≠ d → y ∉ S) ∧
      (∃ y ∈ G.walkVertices c P, y ∉ S) ∧
      ∀ f ∈ P, ∃ y, G.Inc f y ∧ y ∉ S := by
  obtain ⟨c, hc, d, hd, hcd, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd⟩⟩ :=
    hG.component_two_neighbors hS ha hb hab hx hxS
  have hpS : p ∉ S := (component_deleteVerts_subset hp).2
  have hqS : q ∉ S := (component_deleteVerts_subset hq).2
  -- A path across the component, taken in `G - S` so that it cannot touch `S`.
  obtain ⟨Q, hQ⟩ := Reaches.exists_isPath (Reaches.trans (Reaches.symm hq) hp)
  have hQvert : G.walkVertices q Q ⊆ V(G) \ S :=
    hQ.isWalk.walkVertices_subset_of_deleteVerts
  have hQG : G.IsPath q Q p := hQ.mono deleteVerts_le
  -- Cap it with the edge `p — c`, which is fresh because `c ∈ S`.
  have hcQ : c ∉ G.walkVertices q Q := fun hmem ↦ (hQvert hmem).2 hc
  have hQc : G.IsPath q (Q ++ [g]) c := hQG.extend_at_target hgpc hcQ
  -- Prepend the edge `d — q`, fresh because `d ∈ S` and `d ≠ c`.
  have hdQc : d ∉ G.walkVertices q (Q ++ [g]) := by
    intro hmem
    rcases mem_walkVertices_append_singleton hmem with hmem' | hinc
    · exact (hQvert hmem').2 hd
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS hd, hcd rfl]
  have hpath : G.IsPath d (g' :: (Q ++ [g])) c := .cons hgqd.symm hQc hdQc
  refine ⟨d, hd, c, hc, _, fun h ↦ hcd h.symm, hpath, fun y hy hyd hyc ↦ ?_,
    ⟨q, mem_walkVertices_cons_of_mem hgqd.symm mem_walkVertices_self, hqS⟩, fun f hf ↦ ?_⟩
  · -- Every vertex is `d`, `c`, or one that `G - S` reached.
    rcases mem_walkVertices_cons hgqd.symm hy with rfl | hy'
    · exact absurd rfl hyd
    rcases mem_walkVertices_append_singleton hy' with hmem | hinc
    · exact (hQvert hmem).2
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS, absurd rfl hyc]
  · -- Every edge touches the component: the two capping edges at `q` and at `p`, the rest at
    -- both of their ends.
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨q, hgqd.inc_left, hqS⟩
    rcases List.mem_append.1 hf' with hf' | hf'
    · have hfE := hQ.isWalk.edge_mem hf'
      rw [edgeSet_deleteVerts] at hfE
      obtain ⟨s, t, hst, hs, -⟩ := hfE
      exact ⟨s, hst.inc_left, hs⟩
    · obtain rfl : f = g := by simpa using hf'
      exact ⟨p, hgpc.inc_left, hpS⟩

end Graph
