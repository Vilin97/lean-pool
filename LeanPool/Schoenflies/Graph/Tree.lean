/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.Cycle
import LeanPool.Schoenflies.Graph.Degree

/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

open Set
open scoped Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

namespace Graph

/-! ### Trees -/

/-- `G.IsTree` : a connected graph in which no edge lies on a cycle. Connectedness carries
nonemptiness (`Graph.Connected`), which is what makes the counting statements below true as
stated. -/
def IsTree (G : Graph α β) : Prop := G.Connected ∧ G.IsAcyclic

theorem IsTree.connected (h : G.IsTree) : G.Connected := h.1

theorem IsTree.isAcyclic (h : G.IsTree) : G.IsAcyclic := h.2

theorem isTree_iff : G.IsTree ↔ G.Connected ∧ G.IsAcyclic := Iff.rfl

/-! ### A walk departs along an edge -/

/-- A walk that gets anywhere leaves along an edge at its source. -/
theorem IsWalk.exists_inc_source (h : G.IsWalk u W v) (hW : W ≠ []) : ∃ e ∈ W, G.Inc e u := by
  cases h with
  | nil => exact absurd rfl hW
  | cons hl _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩

/-- A path between two distinct vertices takes at least one edge. -/
theorem IsPath.ne_nil (h : G.IsPath u P v) (huv : u ≠ v) : P ≠ [] := by
  rintro rfl
  exact huv h.isWalk.eq_of_nil

/-- **In a connected graph on two or more vertices nothing is isolated.** -/
theorem Connected.degree_pos [G.Finite] (hG : G.Connected) (h2 : 2 ≤ V(G).ncard)
    (hx : x ∈ V(G)) : 0 < G.degree x := by
  obtain ⟨b, hb, hbx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
  obtain ⟨R, hR⟩ := hG.exists_isPath hx hb
  obtain ⟨e, -, hinc⟩ := hR.isWalk.exists_inc_source (hR.ne_nil (Ne.symm hbx))
  exact degree_pos_of_inc hinc

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-- An edge of a path incident with the path's source is the one the path departs along. -/
theorem IsPath.eq_head_of_inc_source (h : G.IsPath u (e :: W) v) (hf : f ∈ e :: W)
    (hinc : G.Inc f u) : f = e := by
  cases h with
  | cons hl hW hfresh =>
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hfresh

/-- **A path has at most one edge at its source.** -/
theorem IsPath.inc_source_unique (h : G.IsPath u P v) (hf : f ∈ P) (he : e ∈ P)
    (hfi : G.Inc f u) (hei : G.Inc e u) : f = e := by
  cases P with
  | nil => simp at hf
  | cons a t => rw [h.eq_head_of_inc_source hf hfi, h.eq_head_of_inc_source he hei]

/-! ### A longest path -/

/-- A path repeats no edge, so it is no longer than the graph has edges. -/
theorem IsPath.length_le_ncard_edgeSet [G.Finite] (h : G.IsPath u P v) :
    P.length ≤ E(G).ncard := by
  classical
  have hsub : P.toFinset ⊆ G.edgeFinset := fun f hf ↦
    mem_edgeFinset.2 (h.edge_mem (List.mem_toFinset.1 hf))
  calc P.length = P.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
    _ = E(G).ncard := card_edgeFinset

/-- **A finite graph with a vertex has a longest path.** The lengths of paths are bounded by
the number of edges, so `Nat.findGreatest` picks the largest length that occurs, and the
witnessing path is longest. -/
theorem exists_longest_path [G.Finite] (hu : u ∈ V(G)) :
    ∃ x y Q, G.IsPath x Q y ∧ ∀ x' y' (Q' : List β), G.IsPath x' Q' y' → Q'.length ≤ Q.length := by
  classical
  -- `p n` : some path has length exactly `n`.
  set p : ℕ → Prop :=
    fun n ↦ ∃ (x : α) (y : α) (Q : List β), G.IsPath x Q y ∧ Q.length = n with hp
  have hp0 : p 0 := ⟨u, u, [], .nil hu, rfl⟩
  obtain ⟨x, y, Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le E(G).ncard) hp0
  refine ⟨x, y, Q, hQ, fun x' y' Q' hQ' ↦ ?_⟩
  have hle := Nat.le_findGreatest (P := p) hQ'.length_le_ncard_edgeSet ⟨x', y', Q', hQ', rfl⟩
  omega

/-! ### Both ends of a longest path are leaves -/

/-- **Every edge at the source of a longest path is one of the path's own edges.** The two
ways out are both closed: an edge onto a vertex the path visits closes a cycle
(`Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices`), and an edge to a vertex it does not
visit extends the path. -/
theorem IsAcyclic.longest_path_source_edge (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : e ∈ P := by
  obtain ⟨z, hl⟩ := hinc
  by_cases hz : z ∈ G.walkVertices u P
  · exact hac.mem_of_isLink_of_mem_walkVertices hP hl hz
  · have hlt := hlong z v (e :: P) (.cons hl.symm hP hz)
    rw [List.length_cons] at hlt
    omega

/-- **The source of a longest path in an acyclic graph is a leaf**, as soon as it carries an
edge at all: every edge there is one of the path's, and the path leaves the vertex only once,
so they are all the same edge. -/
theorem IsAcyclic.longest_path_source_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : G.IsLeaf u := by
  refine isLeaf_of_isNonloopAt hinc.vertex_mem (fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ hg ▸ hinc⟩)
    (hinc.isLoopAt_or_isNonloopAt.resolve_left (hac.not_isLoopAt e u))
  exact hP.inc_source_unique (hac.longest_path_source_edge hP hlong hg)
    (hac.longest_path_source_edge hP hlong hinc) hg hinc

/-- **The target of a longest path in an acyclic graph is a leaf** too: reversing a path
preserves its length, so the reverse is longest as well. -/
theorem IsAcyclic.longest_path_target_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e v) : G.IsLeaf v := by
  refine hac.longest_path_source_is_leaf hP.reverse (fun x' y' Q hQ ↦ ?_) hinc
  rw [List.length_reverse]
  exact hlong x' y' Q hQ

/-- **A tree on two or more vertices has a leaf.** Two distinct vertices are joined by a path
that takes an edge, so a longest path takes one too, and its source is a leaf. -/
theorem IsTree.has_leaf [G.Finite] (hT : G.IsTree) (h2 : 2 ≤ V(G).ncard) :
    ∃ x, G.IsLeaf x := by
  obtain ⟨a, ha⟩ := hT.connected.nonempty
  obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) a
  obtain ⟨x, y, Q, hQ, hlong⟩ := exists_longest_path ha
  -- Some path is nonempty, so the longest one is.
  obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha hb
  have hRpos : 1 ≤ R.length := List.length_pos_iff.2 (hR.ne_nil (Ne.symm hba))
  have hQne : Q ≠ [] := by
    intro hQnil
    have hle := hlong a b R hR
    rw [hQnil, List.length_nil] at hle
    omega
  obtain ⟨e, -, hinc⟩ := hQ.isWalk.exists_inc_source hQne
  exact ⟨x, hT.isAcyclic.longest_path_source_is_leaf hQ hlong hinc⟩

/-! ### A path steers clear of a leaf -/

/-- **A path whose two ends are elsewhere never visits a vertex of degree one.** To pass
through such a vertex the path would have to arrive and leave along that vertex's single
edge, and a path takes no edge twice. This is what makes connectivity survive the deletion of
a leaf. -/
theorem IsLeaf.path_avoids [G.Finite] (hx : G.IsLeaf x) (hP : G.IsPath u P v) :
    u ≠ x → v ≠ x → x ∉ G.walkVertices u P := by
  induction hP with
  | nil hy =>
    intro hu _ hmem
    rw [walkVertices_nil] at hmem
    exact hu hmem.symm
  | @cons a w b e W hl hW hfresh ih =>
    intro ha hb hmem
    rcases mem_walkVertices_cons hl hmem with rfl | hmem'
    · exact ha rfl
    by_cases hwx : w = x
    · -- The step arrives at the leaf, so the rest has to leave it — along the leaf's one
      -- edge, which the step has already used.
      subst hwx
      have hWne : W ≠ [] := hW.ne_nil (Ne.symm hb)
      obtain ⟨g, hg, hginc⟩ := hW.isWalk.exists_inc_source hWne
      obtain ⟨e', -, huniq⟩ := hx.existsUnique_inc
      have hge : g = e := (huniq g hginc).trans (huniq e hl.inc_right).symm
      exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hge ▸ hg, hl.inc_left⟩)
    · exact ih hwx hb hmem'

/-! ### Vertex deletion -/

/-- **A walk that visits no deleted vertex survives the deletion.** Both ends of each of its
edges are vertices it visits, so they too survive. -/
theorem IsWalk.deleteVerts {X : Set α} (h : G.IsWalk u W v)
    (hX : ∀ z ∈ G.walkVertices u W, z ∉ X) : (G.deleteVerts X).IsWalk u W v := by
  refine h.anti deleteVerts_le ?_ fun g hg ↦ ?_
  · exact ⟨h.left_mem, hX u mem_walkVertices_self⟩
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
    simp only [edgeSet_deleteVerts, Set.mem_ofPred_eq]
    exact ⟨p, q, hpq, hX p (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_left⟩),
      hX q (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_right⟩)⟩

/-- Deleting a vertex removes exactly the edges that meet it. -/
theorem edgeSet_deleteVerts_singleton (G : Graph α β) (x : α) :
    E(G.deleteVerts {x}) = E(G) \ G.incidenceSet x := by
  ext g
  simp only [edgeSet_deleteVerts, Set.mem_ofPred_eq, Set.mem_sdiff, mem_incidenceSet,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨p, q, hpq, hp, hq⟩ ↦ ⟨hpq.edge_mem, fun hinc ↦ ?_⟩, fun ⟨hg, hninc⟩ ↦ ?_⟩
  · rcases hinc.eq_or_eq_of_isLink hpq with rfl | rfl
    exacts [hp rfl, hq rfl]
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
    exact ⟨p, q, hpq, fun h ↦ hninc (h ▸ hpq.inc_left), fun h ↦ hninc (h ▸ hpq.inc_right)⟩

/-- **A tree minus a leaf is a tree.** Acyclicity is inherited by every subgraph;
connectedness survives because every path between two surviving vertices already steered
clear of the leaf (`Graph.IsLeaf.path_avoids`). -/
theorem IsTree.delete_leaf [G.Finite] (hT : G.IsTree) (hx : G.IsLeaf x) (h2 : 2 ≤ V(G).ncard) :
    (G.deleteVerts {x}).IsTree := by
  refine ⟨⟨?_, fun a ha b hb ↦ ?_⟩, hT.isAcyclic.anti deleteVerts_le⟩
  · obtain ⟨c, hc, hcx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
    exact ⟨c, by rw [vertexSet_deleteVerts]; exact ⟨hc, by simpa using hcx⟩⟩
  · rw [vertexSet_deleteVerts] at ha hb
    obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha.1 hb.1
    have havoid := hx.path_avoids hR (by simpa using ha.2) (by simpa using hb.2)
    exact ⟨R, hR.isWalk.deleteVerts fun z hz hzX ↦ havoid (Set.mem_singleton_iff.1 hzX ▸ hz)⟩

/-! ### A tree has one edge fewer than it has vertices -/

/-- The induction behind `Graph.IsTree.edge_count`, with a bound on the number of vertices to
walk down: peel a leaf and recurse on what is left, which is a tree with one vertex and one
edge fewer. -/
private theorem isTree_edge_count_aux :
    ∀ (n : ℕ) (G : Graph α β), G.Finite → V(G).ncard ≤ n → G.IsTree →
      E(G).ncard + 1 = V(G).ncard := by
  intro n
  induction n with
  | zero =>
    intro G hfin hle hT
    let _ := hfin
    obtain ⟨a, ha⟩ := hT.connected.nonempty
    have := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
    omega
  | succ n ih =>
    intro G hfin hle hT
    let _ := hfin
    by_cases h2 : 2 ≤ V(G).ncard
    · obtain ⟨x, hx⟩ := hT.has_leaf h2
      let _ : (G.deleteVerts {x}).Finite := Finite.of_le deleteVerts_le
      have hT' : (G.deleteVerts {x}).IsTree := hT.delete_leaf hx h2
      have hV : V(G.deleteVerts {x}).ncard = V(G).ncard - 1 := by
        rw [vertexSet_deleteVerts, Set.ncard_sdiff_singleton_of_mem hx.mem_vertexSet]
      -- A leaf sits on exactly one edge, and that edge is what the deletion removes.
      obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 hx.ncard_incidenceSet
      have he₀G : e₀ ∈ E(G) :=
        G.incidenceSet_subset_edgeSet x (he₀ ▸ Set.mem_singleton e₀)
      have hE : E(G.deleteVerts {x}).ncard = E(G).ncard - 1 := by
        rw [edgeSet_deleteVerts_singleton, he₀, Set.ncard_sdiff_singleton_of_mem he₀G]
      have hEpos := (Set.ncard_pos (finite_edgeSet G)).2 ⟨e₀, he₀G⟩
      have := ih _ inferInstance (by omega) hT'
      omega
    · -- A single vertex, and no edge: an edge would be a loop, and no acyclic graph has one.
      obtain ⟨a, ha⟩ := hT.connected.nonempty
      have hpos := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
      have hV1 : V(G).ncard = 1 := by omega
      obtain ⟨c, hVc⟩ := Set.ncard_eq_one.1 hV1
      have hE : E(G).ncard = 0 := by
        refine (Set.ncard_eq_zero (finite_edgeSet G)).2 (Set.eq_empty_iff_forall_notMem.2 ?_)
        intro g hg
        obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
        have hp : p = c := by have := hpq.left_mem; rw [hVc] at this; exact this
        have hq : q = c := by have := hpq.right_mem; rw [hVc] at this; exact this
        rw [hp, hq] at hpq
        exact hT.isAcyclic.not_isLoopAt g c hpq
      omega

/-- **A tree has one edge fewer than it has vertices.** -/
theorem IsTree.edge_count [G.Finite] (hT : G.IsTree) : E(G).ncard + 1 = V(G).ncard :=
  isTree_edge_count_aux V(G).ncard G inferInstance le_rfl hT

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

/-- **A tree with exactly three leaves has a vertex of degree three, and every other vertex
has degree at most two** — so it is a leaf or has degree exactly two, and the vertex of degree
three is unique.

The count: with `k` non-leaf vertices the tree has `k + 3` vertices, hence `k + 2` edges
(`Graph.IsTree.edge_count`), hence degree sum `2k + 4` (the handshake lemma). The leaves
contribute `3`, so the non-leaves contribute `2k + 1`; each contributes at least `2`, so
between them they carry exactly one degree above two. -/
theorem IsTree.three_leaves [G.Finite] (hT : G.IsTree)
    (hleaves : {z | G.IsLeaf z}.ncard = 3) :
    ∃ x ∈ V(G), G.degree x = 3 ∧ ∀ z ∈ V(G), z ≠ x → G.degree z ≤ 2 := by
  classical
  set L : Finset α := G.vertexFinset.filter (fun z ↦ G.degree z = 1) with hL
  set I : Finset α := G.vertexFinset.filter (fun z ↦ ¬ G.degree z = 1) with hI
  -- The filter really is the set of leaves.
  have hcoe : (L : Set α) = {z | G.IsLeaf z} := by
    ext z
    simp [hL, isLeaf_iff]
  have hLcard : L.card = 3 := by rw [← Set.ncard_coe_finset, hcoe]; exact hleaves
  -- Three leaves is already three vertices.
  have h2 : 2 ≤ V(G).ncard := by
    have := Finset.card_le_card (Finset.filter_subset (fun z ↦ G.degree z = 1) G.vertexFinset)
    rw [hLcard, card_vertexFinset] at this
    omega
  -- Each leaf contributes one to the degree sum.
  have hsumL : ∑ z ∈ L, G.degree z = 3 := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Finset.mem_filter.1 hz).2, Finset.sum_const, hLcard]
    simp
  -- Each non-leaf is on at least two edges.
  have hdeg2 : ∀ z ∈ I, 2 ≤ G.degree z := by
    intro z hz
    obtain ⟨hzV, hzd⟩ := Finset.mem_filter.1 hz
    have := hT.connected.degree_pos h2 (mem_vertexFinset.1 hzV)
    omega
  -- So it contributes two plus whatever it carries above two.
  have hsumI : ∑ z ∈ I, G.degree z = 2 * I.card + ∑ z ∈ I, (G.degree z - 2) := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Nat.add_sub_cancel' (hdeg2 z hz)).symm,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- The two halves are the whole graph, and the handshake lemma reads the total.
  have hsplit : ∑ z ∈ L, G.degree z + ∑ z ∈ I, G.degree z = 2 * E(G).ncard := by
    rw [hL, hI, Finset.sum_filter_add_sum_filter_not]
    exact G.sum_degree_eq_two_mul_ncard_edgeSet
  have hcards : L.card + I.card = V(G).ncard := by
    rw [hL, hI, Finset.card_filter_add_card_filter_not, card_vertexFinset]
  -- The count: the non-leaves carry exactly one degree between them.
  have hexcess : ∑ z ∈ I, (G.degree z - 2) = 1 := by
    have hedges := hT.edge_count
    omega
  -- Whichever non-leaf carries it has degree three, and the others have degree two.
  obtain ⟨x, hxI, hxne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hexcess]; exact one_ne_zero)
  have hrest : ∑ z ∈ I.erase x, (G.degree z - 2) + (G.degree x - 2) = 1 := by
    rw [Finset.sum_erase_add _ _ hxI]; exact hexcess
  have hx3 : G.degree x = 3 := by
    have := hdeg2 x hxI
    omega
  refine ⟨x, mem_vertexFinset.1 (Finset.mem_filter.1 hxI).1, hx3, fun z hz hzx ↦ ?_⟩
  by_cases hzL : G.degree z = 1
  · omega
  · have hzI : z ∈ I := Finset.mem_filter.2 ⟨mem_vertexFinset.2 hz, hzL⟩
    have hze : z ∈ I.erase x := Finset.mem_erase.2 ⟨hzx, hzI⟩
    have hzero : ∑ z ∈ I.erase x, (G.degree z - 2) = 0 := by omega
    have := (Finset.sum_eq_zero_iff.1 hzero) z hze
    have := hdeg2 z hzI
    omega

end Graph
