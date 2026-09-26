/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# The SQRT girth cluster

A self-contained girth development: from an *edge excess* `t` on a graph one
extracts a short cycle, quantified by the SQRT bound `(g − 5)² ≤ 2|S|²/t`. The
engine is a BFS ball-excess count in a graph with no cycle of length `≤ 2r + 1`.

## Main results

* `exists_isCycle_of_excess`, `acyclic_card_edge_le`,
  `induced_pairs_eq_two_mul_edges` — from `|S|` edges inside `S`, extract a cycle
  whose support lies in `S` (the induced subgraph is not acyclic).
* `cycle_walk_to_zmod` — the `Walk.IsCycle → (c : ZMod k → Fin n)` conversion into
  the cyclic-map form the `master_cycle_fires` firing surface expects.
* `level_no_internal_edge`, `level_unique_parent`, `level_children_count`,
  `level_card_growth` — the BFS-level growth rows exposing the tree-like ball
  structure up to radius `r` (girth-only, no min-degree hypothesis).
* `ball_weighted_lower` — the quadratic degree-weighted ball lower bound
  `1 + 2r + Σ_{i<r}(r − i)·ε_i(x) ≤ |B(x, r)|` (an equality under connectivity,
  `ε_i` = level excess).
* `sum_level_excess_swap` and the SQRT double count
  `|V|·(1 + 2r) + 2·t·r² ≤ |V|²`, together with the 2-core extraction
  `two_core_of_excess` (`degWithin`, `edgeSumWithin`).
-/

public section

namespace ACMax

open SimpleGraph

variable {V : Type*}

/-- **Ordered adjacent pairs count twice the induced edges.**  The number of ordered pairs
`(x, y)` with `x, y ∈ S` and `G.Adj x y` equals `2 * (G.induce ↑S).edgeFinset.card`. -/
theorem induced_pairs_eq_two_mul_edges (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card
      = 2 * (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  have hbij : (Finset.univ : Finset (G.induce (↑S : Set V)).Dart).card
      = ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card := by
    apply Finset.card_bij (fun d _ => ((d.fst : V), (d.snd : V)))
    · intro d _
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_coe.mp d.fst.2, Finset.mem_coe.mp d.snd.2⟩, d.adj⟩
    · intro d₁ _ d₂ _ heq
      rw [Prod.mk.injEq] at heq
      exact Dart.ext _ _ (Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2))
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hq1, hq2⟩, hadj⟩ := hq
      exact ⟨⟨(⟨q.1, Finset.mem_coe.mpr hq1⟩, ⟨q.2, Finset.mem_coe.mpr hq2⟩), hadj⟩,
        Finset.mem_univ _, rfl⟩
  rw [← hbij, Finset.card_univ, dart_card_eq_twice_card_edges]

end ACMax

/-! ## The `ZMod`-cycle conversion

`cycle_walk_to_zmod`: from a cycle walk `w` whose support lies inside `S`, produce
`k = w.length ≥ 3` and an injective `c : ZMod k → Fin n` with cyclic adjacency
`c i ~ c (i+1)` and `c i ∈ S` — the cyclic-map form the `master_cycle_fires` firing
surface expects (`c i = w.getVert i.val`, injectivity via `IsCycle.isPath_dropLast`,
cyclic adjacency via `adj_getVert_succ`). -/

namespace ACMax

open SimpleGraph

/-- **The `Walk.IsCycle → ZMod k` conversion.**  A cycle walk `w` in `G` of length `k` whose
support sits inside `S` yields `3 ≤ k` and an injective cyclic map `c : ZMod k → Fin n`
(`c i ~ c (i+1)`, `c i ∈ S`) — the existential shape demanded by `GirthExcessBound`.  Reusable
for any girth discharge that produces a bounded-length cycle walk. -/
theorem cycle_walk_to_zmod {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} {w : G.Walk v v}
    (hcyc : w.IsCycle) {S : Finset (Fin n)} (hsupp : ∀ x ∈ w.support, x ∈ S) :
    3 ≤ w.length ∧ ∃ c : ZMod w.length → Fin n, Function.Injective c ∧
      (∀ i : ZMod w.length, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod w.length, c i ∈ S) := by
  have hlen3 : 3 ≤ w.length := hcyc.three_le_length
  have : NeZero w.length := ⟨by omega⟩
  -- `getVert` is injective on `{0, …, k−1}` because the cycle minus its repeated endpoint is a path
  have hinj : ∀ a b : ℕ, a < w.length → b < w.length → w.getVert a = w.getVert b → a = b := by
    intro a b ha hb hab
    have hpath : w.dropLast.IsPath := hcyc.isPath_dropLast
    have hla : w.dropLast.length = w.length - 1 := w.length_dropLast
    have hga : w.dropLast.getVert a = w.getVert a := by
      change (w.take (w.length - 1)).getVert a = w.getVert a
      rw [Walk.take_getVert, inf_eq_right.mpr (show a ≤ w.length - 1 by omega)]
    have hgb : w.dropLast.getVert b = w.getVert b := by
      change (w.take (w.length - 1)).getVert b = w.getVert b
      rw [Walk.take_getVert, inf_eq_right.mpr (show b ≤ w.length - 1 by omega)]
    have ha' : a ∈ {i | i ≤ w.dropLast.length} := by rw [Set.mem_ofPred_eq]; omega
    have hb' : b ∈ {i | i ≤ w.dropLast.length} := by rw [Set.mem_ofPred_eq]; omega
    exact hpath.getVert_injOn ha' hb' (by rw [hga, hgb]; exact hab)
  refine ⟨hlen3, fun i => w.getVert i.val, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : w.getVert i.val = w.getVert j.val := hij
    exact ZMod.val_injective w.length (hinj i.val j.val (ZMod.val_lt i) (ZMod.val_lt j) hij')
  · intro i
    have hmlt : i.val < w.length := ZMod.val_lt i
    have hval : ((i.val + 1 : ℕ) : ZMod w.length) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    have hv1 : (i + 1).val = (i.val + 1) % w.length := by rw [← hval, ZMod.val_natCast]
    change G.Adj (w.getVert i.val) (w.getVert (i + 1).val)
    rw [hv1]
    by_cases hc : i.val + 1 < w.length
    · rw [Nat.mod_eq_of_lt hc]
      exact w.adj_getVert_succ hmlt
    · have heq : i.val + 1 = w.length := by omega
      rw [heq, Nat.mod_self, w.getVert_zero]
      have hadj := w.adj_getVert_succ hmlt
      rw [heq, w.getVert_length] at hadj
      exact hadj
  · intro i
    exact hsupp _ (w.getVert_mem_support i.val)

end ACMax

/-! ## BFS-level growth rows

The BFS levels `L_i(x) = (Finset.univ.filter fun v => dist x v = i)` in a graph with no cycle of
length
`≤ 2r + 1` are tree-like: no edge inside a level (`level_no_internal_edge`), a
level-`(i+1)` vertex has a unique parent (`level_unique_parent`), a level-`i`
vertex sends `deg v − 1` edges up (`level_children_count`), and the levels grow by
`|L_{i+1}| = Σ_{v∈L_i}(deg v − 1)` (`level_card_growth`). All four are girth-only
(no min-degree hypothesis). -/

namespace ACMax

open SimpleGraph Finset

/-- The distance from `x` to a vertex on a walk `x → z` is bounded by the walk's length. -/
theorem dist_le_of_mem_support {V : Type*} (G : SimpleGraph V) {x z : V} (g : G.Walk x z) {w : V}
    (hw : w ∈ g.support) : G.dist x w ≤ g.length := by
  classical
  exact (SimpleGraph.dist_le (g.takeUntil w hw)).trans (g.length_takeUntil_le_length hw)

/-- Two distinct paths with the same endpoints whose total length is `≤ 2r + 1` are impossible
under the girth hypothesis: they close a cycle of length `≤ 2r + 1`. -/
theorem no_short_cycle_of_paths {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) {x y : V}
    {P Q : G.Walk x y} (hP : P.IsPath) (hQ : Q.IsPath) (hne : P ≠ Q)
    (hlen : P.length + Q.length ≤ 2 * r + 1) : False := by
  classical
  obtain ⟨u, -, -, c, hc, hcl⟩ := hP.exists_isCycle_length_le_add_of_ne hQ hne
  have h1 := hg u c hc
  omega

/-- On a geodesic `g : x → y`, a vertex `z ≠ y` at the same distance from `x` as `y` cannot lie on
`g` (the geodesic reaches distance `dist x y` only at its endpoint). -/
theorem notMem_geodesic_of_dist_eq {V : Type*} (G : SimpleGraph V) {x y : V} (g : G.Walk x y)
    (hglen : g.length = G.dist x y) {z : V} (hdist : G.dist x z = G.dist x y) (hne : z ≠ y) :
    z ∉ g.support := by
  classical
  intro hz
  have hAB : (g.takeUntil z hz).append (g.dropUntil z hz) = g := g.take_spec hz
  have hlen : (g.takeUntil z hz).length + (g.dropUntil z hz).length = g.length := by
    rw [← Walk.length_append, hAB]
  have hxz : G.dist x z ≤ (g.takeUntil z hz).length := SimpleGraph.dist_le _
  have hzy : G.dist z y ≤ (g.dropUntil z hz).length := SimpleGraph.dist_le _
  have hrzy : G.Reachable z y := (g.dropUntil z hz).reachable
  have hdzy : G.dist z y = 0 := by omega
  exact hne (hrzy.dist_eq_zero_iff.mp hdzy)

/-- **No same-level edge.**  Under `hg` (no cycle of length `≤ 2r + 1`), no two vertices at the same
BFS level `L_i(x)` with `1 ≤ i ≤ r` are adjacent — the edge plus two `dist`-`i` geodesics would
close a cycle of length `≤ 2i + 1 ≤ 2r + 1`. -/
theorem level_no_internal_edge {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i ≤ r) {v w : V} (hv : G.dist x v = i) (hw : G.dist x w = i) :
    ¬ G.Adj v w := by
  intro hadj
  have hrxw : G.Reachable x w := Reachable.of_dist_ne_zero (by rw [hw]; omega)
  obtain ⟨gw, hgwP, hgwlen⟩ := hrxw.exists_path_of_dist
  have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
  obtain ⟨gv, hgvP, hgvlen⟩ := hrxv.exists_path_of_dist
  have hvw : v ≠ w := hadj.ne
  have hvnotin : v ∉ gw.support :=
    notMem_geodesic_of_dist_eq G gw hgwlen (z := v) (by rw [hv, hw]) hvw
  have hadjwv : G.Adj w v := hadj.symm
  have hP1 : (gw.concat hadjwv).IsPath := hgwP.concat hvnotin hadjwv
  have hne : gw.concat hadjwv ≠ gv := by
    intro heq
    have h1 : (gw.concat hadjwv).length = i + 1 := by rw [Walk.length_concat, hgwlen, hw]
    rw [heq, hgvlen, hv] at h1
    omega
  refine no_short_cycle_of_paths G hg hP1 hgvP hne ?_
  rw [Walk.length_concat, hgwlen, hgvlen, hv, hw]
  omega

/-- **Unique parent.**  Under `hg`, a level-`(i+1)` vertex `v` (`i + 1 ≤ r`) has exactly one
neighbour at level `i`: `((N v) ∩ L_i).card = 1`.  Existence is the penultimate vertex of a
geodesic `x → v`; uniqueness is a short cycle from two length-`(i+1)` paths to `v`. -/
theorem level_unique_parent {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hir : i + 1 ≤ r) {v : V} (hv : G.dist x v = i + 1) :
    ((G.neighborFinset v).filter (fun w => G.dist x w = i)).card = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    by_contra hp1p2
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hp1 hp2
    obtain ⟨hadj1, hd1⟩ := hp1
    obtain ⟨hadj2, hd2⟩ := hp2
    have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
    have hr1 : G.Reachable x p1 := hrxv.trans hadj1.reachable
    have hr2 : G.Reachable x p2 := hrxv.trans hadj2.reachable
    obtain ⟨g1, hg1P, hg1len⟩ := hr1.exists_path_of_dist
    obtain ⟨g2, hg2P, hg2len⟩ := hr2.exists_path_of_dist
    have hvn1 : v ∉ g1.support := by
      intro hmem
      have hle := dist_le_of_mem_support G g1 hmem
      rw [hg1len, hd1, hv] at hle; omega
    have hvn2 : v ∉ g2.support := by
      intro hmem
      have hle := dist_le_of_mem_support G g2 hmem
      rw [hg2len, hd2, hv] at hle; omega
    have hadj1v : G.Adj p1 v := hadj1.symm
    have hadj2v : G.Adj p2 v := hadj2.symm
    have hP1 : (g1.concat hadj1v).IsPath := hg1P.concat hvn1 hadj1v
    have hP2 : (g2.concat hadj2v).IsPath := hg2P.concat hvn2 hadj2v
    have hne : g1.concat hadj1v ≠ g2.concat hadj2v := by
      intro heq
      apply hp1p2
      have e1 : (g1.concat hadj1v).penultimate = p1 := Walk.penultimate_concat g1 hadj1v
      have e2 : (g2.concat hadj2v).penultimate = p2 := Walk.penultimate_concat g2 hadj2v
      rw [← e1, ← e2, heq]
    refine no_short_cycle_of_paths G hg hP1 hP2 hne ?_
    rw [Walk.length_concat, Walk.length_concat, hg1len, hg2len, hd1, hd2]
    omega
  · have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
    obtain ⟨g, hgP, hglen⟩ := hrxv.exists_path_of_dist
    have hi_lt : i < g.length := by rw [hglen, hv]; omega
    have hadj_uv : G.Adj (g.getVert i) v := by
      have h := g.adj_getVert_succ hi_lt
      rwa [show i + 1 = g.length by rw [hglen, hv], g.getVert_length] at h
    have hle : G.dist x (g.getVert i) ≤ i := by
      have hw := SimpleGraph.dist_le (g.take i)
      rw [Walk.take_length, show i ⊓ g.length = i by rw [hglen, hv]; omega] at hw
      exact hw
    have hge : i ≤ G.dist x (g.getVert i) := by
      have hru : G.Reachable x (g.getVert i) := (g.take i).reachable
      have htri := hru.dist_triangle_left v
      rw [hv, SimpleGraph.dist_eq_one_iff_adj.mpr hadj_uv] at htri
      omega
    refine Finset.one_le_card.mpr ⟨g.getVert i, ?_⟩
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨hadj_uv.symm, le_antisymm hle hge⟩

/-- **Children count.**  Under `hg`, a level-`i` vertex `v` (`1 ≤ i ≤ r`) has exactly `deg v − 1`
neighbours at level `i + 1`.  Its neighbourhood splits into the unique parent (level `i − 1`), no
same-level neighbour, and the remaining `deg v − 1` children at level `i + 1`. -/
theorem level_children_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i ≤ r) {v : V} (hv : G.dist x v = i) :
    ((G.neighborFinset v).filter (fun w => G.dist x w = i + 1)).card = G.degree v - 1 := by
  classical
  have hrxv : G.Reachable x v := Reachable.of_dist_ne_zero (by rw [hv]; omega)
  have hbound : ∀ w ∈ G.neighborFinset v, G.dist x w = i - 1 ∨ G.dist x w = i + 1 := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    have hrxw : G.Reachable x w := hrxv.trans hadj.reachable
    have hvw1 : G.dist v w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have hwv1 : G.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
    have hup : G.dist x w ≤ i + 1 := by
      have htri := hrxv.dist_triangle_left w; rw [hv, hvw1] at htri; omega
    have hlow : i ≤ G.dist x w + 1 := by
      have htri := hrxw.dist_triangle_left v; rw [hv, hwv1] at htri; omega
    have hne : G.dist x w ≠ i := fun heq =>
      level_no_internal_edge G hg x hi1 hir hv heq hadj
    omega
  have hpart : (G.neighborFinset v).filter (fun w => ¬ G.dist x w = i + 1)
      = (G.neighborFinset v).filter (fun w => G.dist x w = i - 1) := by
    ext w
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hw
    have := hbound w hw
    omega
  have hpar : ((G.neighborFinset v).filter (fun w => G.dist x w = i - 1)).card = 1 := by
    have hv' : G.dist x v = (i - 1) + 1 := by rw [Nat.sub_add_cancel hi1]; exact hv
    have hir' : (i - 1) + 1 ≤ r := by rw [Nat.sub_add_cancel hi1]; exact hir
    exact level_unique_parent G hg x hir' hv'
  have hsplit := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (fun w => G.dist x w = i + 1)
  simp only [hpart, hpar, G.card_neighborFinset_eq_degree] at hsplit
  omega

/-- **Level identity.**  Under `hg`, for `1 ≤ i` and `i + 1 ≤ r` the BFS level `L_{i+1}(x)` has
cardinality `Σ_{v ∈ L_i}(deg v − 1)`.  Proof: double-count the `L_i`–`L_{i+1}` edges — the parent
map (`level_unique_parent`) counts each child once, the children map (`level_children_count`) sums
to `Σ(deg v − 1)`, and the two counts agree by symmetry of adjacency. -/
theorem level_card_growth {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i + 1 ≤ r) :
    (univ.filter (fun v => G.dist x v = i + 1)).card
      = ∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 1) := by
  classical
  set A := univ.filter (fun v => G.dist x v = i) with hA
  set B := univ.filter (fun v => G.dist x v = i + 1) with hB
  have hLHS : B.card = ∑ u ∈ B, (A.filter (fun w => G.Adj u w)).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hconv : A.filter (fun w => G.Adj u w)
        = (G.neighborFinset u).filter (fun w => G.dist x w = i) := by
      ext w
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      tauto
    rw [hconv, level_unique_parent G hg x hir hu]
  have hRHS : ∑ v ∈ A, (G.degree v - 1) = ∑ v ∈ A, (B.filter (fun w => G.Adj v w)).card := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hconv : B.filter (fun w => G.Adj v w)
        = (G.neighborFinset v).filter (fun w => G.dist x w = i + 1) := by
      ext w
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      tauto
    rw [hconv, level_children_count G hg x hi1 (by omega) hv]
  have hswap : ∑ u ∈ B, (A.filter (fun w => G.Adj u w)).card
      = ∑ v ∈ A, (B.filter (fun w => G.Adj v w)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    exact if_congr (G.adj_comm u v) rfl rfl
  rw [hLHS, hswap, hRHS]

/-! ## The quadratic degree-weighted ball lower bound

The engine behind `(g − 5)² ≤ 2|S|²/t`. For a root `x` in a **connected** graph
with minimum degree `≥ 2` and no cycle of length `≤ 2r + 1`, with level excess
`ε_i(x) = Σ_{v∈L_i}(deg v − 2)`, the ball satisfies

  `1 + 2r + Σ_{i < r}(r − i)·ε_i(x) ≤ |B(x, r)|`.

Under connectivity this is an equality: the ball partitions into levels whose
sizes telescope through `level_card_growth`, each excess `ε_i` surfacing in the
`r − i` levels `i+1, …, r`. Connectivity is essential — `SimpleGraph.dist`
returns `0` for unreachable pairs, so without it `L_0` and the ball absorb the far
part of the graph and the bound breaks (`ball_weighted_lower`). -/

/-- **Triangular double-sum identity.**  `Σ_{i < r} Σ_{k ≤ i} ε k = Σ_{k < r}(r − k)·ε k`: reindex
the lower-triangular pairs `k ≤ i < r` by their column `k`, which appears in the `r − k` rows
`k, …, r − 1`. -/
theorem sum_range_triangle (r : ℕ) (ε : ℕ → ℕ) :
    ∑ i ∈ range r, ∑ k ∈ range (i + 1), ε k = ∑ k ∈ range r, (r - k) * ε k := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (n + 1 - k) * ε k),
      Finset.sum_range_succ ε]
    have hk : ∑ k ∈ range n, (n + 1 - k) * ε k = ∑ k ∈ range n, ((n - k) * ε k + ε k) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hsub : n + 1 - k = (n - k) + 1 := by omega
      rw [hsub, add_mul, one_mul]
    rw [hk, Finset.sum_add_distrib]
    have hnn : n + 1 - n = 1 := by omega
    rw [hnn, one_mul]
    omega

/-- **Quadratic degree-weighted ball bound.**  In a connected graph with minimum degree at least
`2` and no cycle of length `≤ 2r + 1`, the ball `B(x, r) = (Finset.univ.filter fun v => dist x v ≤
r)` satisfies
`1 + 2r + Σ_{i < r}(r − i)·ε_i(x) ≤ |B(x, r)|`, where `ε_i(x) = Σ_{v ∈ L_i}(deg v − 2)` is the
excess at BFS level `L_i(x) = (Finset.univ.filter fun v => dist x v = i)`.  Under connectivity the
bound is an exact
equality; the levels telescope through `level_card_growth`. -/
theorem ball_weighted_lower {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length)
    (hconn : G.Connected) (x : V) :
    1 + 2 * r + ∑ i ∈ range r, (r - i) *
        (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      ≤ (univ.filter (fun v => G.dist x v ≤ r)).card := by
  classical
  -- Level `0` is exactly `{x}` (connectivity rules out spurious unreachable vertices).
  have hL0 : univ.filter (fun v => G.dist x v = 0) = ({x} : Finset V) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hr : G.Reachable x v := hconn.preconnected x v
      exact (hr.dist_eq_zero_iff.mp h).symm
    · rintro rfl
      exact SimpleGraph.dist_self
  -- Closed form for level sizes: `|L_j| = 2 + Σ_{i < j} ε_i` for `1 ≤ j ≤ r`.
  have hclosed : ∀ j, 1 ≤ j → j ≤ r →
      (univ.filter (fun v => G.dist x v = j)).card
        = 2 + ∑ i ∈ range j,
            (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      have hL1 : univ.filter (fun v => G.dist x v = 1) = G.neighborFinset x := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.dist_eq_one_iff_adj
      rw [Finset.sum_range_one, hL1, G.card_neighborFinset_eq_degree, hL0, Finset.sum_singleton]
      have := hmin x
      omega
    | succ n hn ih =>
      intro hnr
      have hdn := ih (by omega)
      rw [Finset.sum_range_succ, level_card_growth G hg x hn (by omega)]
      have hconv : ∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 1)
          = (∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 2))
            + (univ.filter (fun v => G.dist x v = n)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        have := hmin v
        omega
      rw [hconv, hdn]
      omega
  -- The ball is the disjoint union of the levels `L_0, …, L_r`.
  have hmem : ∀ v ∈ univ.filter (fun v => G.dist x v ≤ r), G.dist x v ∈ range (r + 1) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_range]
    omega
  have hball : (univ.filter (fun v => G.dist x v ≤ r)).card
      = ∑ i ∈ range (r + 1), (univ.filter (fun v => G.dist x v = i)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmem]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hd0 : (univ.filter (fun v => G.dist x v = 0)).card = 1 := by
    rw [hL0, Finset.card_singleton]
  -- Assemble the telescoped equality, then read off the inequality.
  have hfinal : (univ.filter (fun v => G.dist x v ≤ r)).card
      = 1 + 2 * r + ∑ i ∈ range r, (r - i) *
          (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
    rw [hball, Finset.sum_range_succ', hd0]
    have hstep : ∑ i ∈ range r, (univ.filter (fun v => G.dist x v = i + 1)).card
        = 2 * r + ∑ i ∈ range r, (r - i) *
            (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)) := by
      have h1 : ∑ i ∈ range r, (univ.filter (fun v => G.dist x v = i + 1)).card
          = ∑ i ∈ range r, (2 + ∑ k ∈ range (i + 1),
              (∑ v ∈ univ.filter (fun v => G.dist x v = k), (G.degree v - 2))) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        exact hclosed (i + 1) (by omega) (by omega)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        sum_range_triangle]
      omega
    rw [hstep]
    omega
  exact hfinal.ge

/-! ## The SQRT double count

The global double count turning the per-root `ball_weighted_lower` into
`(g − 5)² ≤ 2|S|²/t`.  Fix a **connected** graph on a finite `V`, minimum degree
`≥ 2`, edge excess `t` (`|V| + t ≤ e(G)`), and no cycle of length
`≤ 2r + 1`. Summing the ball bound over all roots, using the swap
`sum_level_excess_swap` (`Σ_x ε_i(x) = Σ_v (deg v − 2)·|L_i(v)|` by distance
symmetry), the level floor `level_card_ge_two` and the handshake
`Σ_v (deg v − 2) ≥ 2t`, yields the quadratic

  `|V|·(1 + 2r) + 2·t·r² ≤ |V|²`.

The full `GirthExcessBound` discharge additionally needs a component descent
(picking the component carrying the excess), the contrapositive arithmetic, and
the `exists_isCycle_of_excess` / `cycle_walk_to_zmod` witness plumbing. -/

/-- **Triangular Gauss sum.**  `2·Σ_{i<m}(m − i) = m·(m + 1)`: the descending run
`m, m−1, …, 1` has twice-sum `m(m+1)`. -/
theorem two_mul_sum_range_sub (m : ℕ) :
    2 * ∑ i ∈ Finset.range m, (m - i) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hsplit : ∑ i ∈ Finset.range (k + 1), (k + 1 - i)
        = (∑ i ∈ Finset.range k, (k - i)) + (k + 1) := by
      rw [Finset.sum_range_succ' (fun i => k + 1 - i) k, Nat.sub_zero]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by omega)
    rw [hsplit, Nat.mul_add, ih]
    ring

/-- **BFS levels are at least as wide as the root degree.**  The sharpening of `level_card_ge_two`
that the SQRT double count actually wants: in a graph with minimum degree at least `2` and no cycle
of length `≤ 2r + 1`, every BFS level `L_j(x) = (Finset.univ.filter fun v => dist x v = j)` with
`1 ≤ j ≤ r` has at least
`deg x` vertices — the `deg x` branches leaving `x` stay separated all the way out to radius `r`,
since two of them meeting at distance `j ≤ r` would close a cycle of length `≤ 2j ≤ 2r`.

Formally this is the *same* induction as `level_card_ge_two`, which already produces `deg x` at the
base level (`L_1(x)` is the neighbourhood) and then only ever needs `deg v − 1 ≥ 1` to carry the
floor outward; `level_card_ge_two` immediately weakens the base to `2 ≤ deg x` and loses the extra
`deg x − 2`.  Keeping it multiplies the excess term of `sqrt_double_count` by `3/2`. -/
theorem level_card_ge_deg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) (x : V) {j : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    G.degree x ≤ (univ.filter (fun v => G.dist x v = j)).card := by
  classical
  revert hjr
  induction j, hj1 using Nat.le_induction with
  | base =>
    intro _
    have hL1 : univ.filter (fun v => G.dist x v = 1) = G.neighborFinset x := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.dist_eq_one_iff_adj
    rw [hL1, G.card_neighborFinset_eq_degree]
  | succ n hn ih =>
    intro hnr
    have hgen : G.degree x ≤ (univ.filter (fun v => G.dist x v = n)).card := ih (by omega)
    rw [level_card_growth G hg x hn (by omega)]
    calc G.degree x ≤ (univ.filter (fun v => G.dist x v = n)).card := hgen
      _ = ∑ _v ∈ univ.filter (fun v => G.dist x v = n), 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ v ∈ univ.filter (fun v => G.dist x v = n), (G.degree v - 1) :=
          Finset.sum_le_sum (fun v _ => by have := hmin v; omega)

/-- **The BFS-level swap.**  Summing the level-`i` excess `Σ_{v : dist x v = i}(deg v − 2)` over all
roots `x` regroups (by symmetry of distance) as `Σ_v (deg v − 2)·|{x : dist v x = i}|`. -/
theorem sum_level_excess_swap {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : ℕ) :
    ∑ x : V, (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      = ∑ v : V, (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hfeq : univ.filter (fun x => G.dist x v = i) = univ.filter (fun x => G.dist v x = i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [SimpleGraph.dist_comm]
  rw [← Finset.sum_filter, hfeq, Finset.sum_const, smul_eq_mul]

/-- **The SQRT double count.**  In a connected graph `G` on a finite `V` with minimum degree at
least `2`, edge excess `t` (`|V| + t ≤ e(G)`), and no cycle of length `≤ 2r + 1`, the ball double
count gives `|V|·(1 + 2r) + t·(3r² − r) ≤ |V|²`.  Summing `ball_weighted_lower` over all roots,
swapping (`sum_level_excess_swap`), and feeding the handshake `Σ_v(deg v − 2) ≥ 2t` together with
the level floor `|L_i(v)| ≥ deg v` (`1 ≤ i ≤ r`, `level_card_ge_deg`) telescoped by
`two_mul_sum_range_sub`.

The excess weight is `3r² − r`, not the `2r²` obtained from the weaker floor `|L_i(v)| ≥ 2`
(`level_card_ge_two`): an excess vertex `v` is seen at distance `i` by at least `deg v ≥ 3` roots,
not merely `2`, so `W i ≥ 3D` for `1 ≤ i ≤ r` and the triangular telescope returns
`rD + 3D·r(r−1)/2 ≥ t(3r² − r)`.  Since `3r² − r ≥ 2r²` for `r ≥ 1`, this strictly strengthens the
old conclusion, and it is what pulls the import-free girth floor down. -/
theorem sqrt_double_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r t : ℕ} (hmin : ∀ v, 2 ≤ G.degree v)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length)
    (hconn : G.Connected) (hexc : Fintype.card V + t ≤ G.edgeFinset.card) :
    Fintype.card V * (1 + 2 * r) + t * (3 * r ^ 2 - r) ≤ (Fintype.card V) ^ 2 := by
  classical
  -- The per-root quadratic ball bound.
  have hbw : ∀ x : V, 1 + 2 * r + ∑ i ∈ range r, (r - i) *
      (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      ≤ (univ.filter (fun v => G.dist x v ≤ r)).card :=
    fun x => ball_weighted_lower G hmin hg hconn x
  have hsum1 : ∑ x : V, (1 + 2 * r + ∑ i ∈ range r, (r - i) *
      (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2)))
      ≤ ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card :=
    Finset.sum_le_sum (fun x _ => hbw x)
  -- Each ball fits in `V`, so the summed balls are at most `|V|²`.
  have hRHS : ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card ≤ (Fintype.card V) ^ 2 := by
    calc ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card
        ≤ ∑ _x : V, Fintype.card V :=
          Finset.sum_le_sum (fun x _ => (Finset.card_filter_le _ _).trans_eq Finset.card_univ)
      _ = Fintype.card V * Fintype.card V := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = (Fintype.card V) ^ 2 := (pow_two _).symm
  -- The excess-weighted degree data.
  set D : ℕ := ∑ v : V, (G.degree v - 2) with hD
  set W : ℕ → ℕ := fun i =>
    ∑ v : V, (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) with hW
  -- The swap: `Σ_x Σ_i (r−i)·ε_i(x) = Σ_i (r−i)·W i`.
  have hswapall : ∑ x : V, ∑ i ∈ range r, (r - i) *
        (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))
      = ∑ i ∈ range r, (r - i) * W i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    simp only [hW]
    exact sum_level_excess_swap G i
  -- `W 0 = D` (level `0` is the singleton root).
  have hW0 : W 0 = D := by
    simp only [hW, hD]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hcard : (univ.filter (fun x => G.dist v x = 0)).card = 1 := by
      have hset : univ.filter (fun x => G.dist v x = 0) = ({v} : Finset V) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          exact ((hconn.preconnected v w).dist_eq_zero_iff.mp h).symm
        · rintro rfl
          exact SimpleGraph.dist_self
      rw [hset, Finset.card_singleton]
    rw [hcard, one_mul]
  -- `3·D ≤ W i` for `1 ≤ i ≤ r` (each level is at least as wide as the root degree, which is
  -- `≥ 3` at every vertex that carries excess).
  have hWi : ∀ i, 1 ≤ i → i ≤ r → 3 * D ≤ W i := by
    intro i hi1 hir
    simp only [hW, hD]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    calc 3 * (G.degree v - 2) ≤ G.degree v * (G.degree v - 2) := by
          rcases Nat.lt_or_ge (G.degree v) 3 with hlt | hge
          · have : G.degree v - 2 = 0 := by omega
            simp [this]
          · exact Nat.mul_le_mul_right _ hge
      _ ≤ (univ.filter (fun x => G.dist v x = i)).card * (G.degree v - 2) :=
          Nat.mul_le_mul_right _ (level_card_ge_deg G hmin hg v hi1 hir)
  -- The handshake: `2t ≤ D`.
  have hD2t : 2 * t ≤ D := by
    have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
      G.sum_degrees_eq_twice_card_edges
    have hDeq : ∑ v : V, G.degree v
        = (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
      calc ∑ v : V, G.degree v = ∑ v : V, ((G.degree v - 2) + 2) :=
            Finset.sum_congr rfl (fun v _ => by have := hmin v; omega)
        _ = (∑ v : V, (G.degree v - 2)) + ∑ _v : V, (2 : ℕ) := Finset.sum_add_distrib
        _ = (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
    rw [hD]
    omega
  -- The triangular weight telescopes to `t·(3r² − r)`: the root level contributes `r·D` and each
  -- of the `r − 1` inner levels at least `3D`, so `2·Σ ≥ 2rD + 3D·r(r−1) = D·(3r² − r)`.
  have hDr : t * (3 * r ^ 2 - r) ≤ ∑ i ∈ range r, (r - i) * W i := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · rw [hr0]; simp
    · obtain ⟨m, hr⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hrw : ∑ i ∈ range r, (r - i) * W i
          = (∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D := by
        rw [hr, Finset.sum_range_succ' (fun i => (m + 1 - i) * W i) m]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          congr 1
          omega
        · rw [Nat.sub_zero, hW0]
      have hrsub : 3 * r ^ 2 - r = (m + 1) * (3 * m + 2) := by
        have h : 3 * r ^ 2 = (m + 1) * (3 * m + 2) + r := by subst hr; ring
        omega
      rw [hrw, hrsub]
      have hlow : (∑ i ∈ range m, (m - i)) * (3 * D)
          ≤ ∑ i ∈ range m, (m - i) * W (i + 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact mul_le_mul_right (hWi (i + 1) (by omega) (by omega)) (m - i)
      have hgauss : 2 * ∑ i ∈ range m, (m - i) = m * (m + 1) := two_mul_sum_range_sub m
      have hSUM : 3 * (m * (m + 1)) * D ≤ 2 * ∑ i ∈ range m, (m - i) * W (i + 1) := by
        calc 3 * (m * (m + 1)) * D = (2 * ∑ i ∈ range m, (m - i)) * (3 * D) := by
              rw [hgauss]; ring
          _ = 2 * ((∑ i ∈ range m, (m - i)) * (3 * D)) := by ring
          _ ≤ 2 * ∑ i ∈ range m, (m - i) * W (i + 1) := Nat.mul_le_mul_left 2 hlow
      -- Double both sides so the `D ≥ 2t` substitution is subtraction-free.
      refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 by norm_num)
      calc 2 * (t * ((m + 1) * (3 * m + 2)))
          = 3 * (m * (m + 1)) * (2 * t) + (m + 1) * (2 * t) * 2 := by ring
        _ ≤ 3 * (m * (m + 1)) * D + (m + 1) * D * 2 := by gcongr
        _ ≤ 2 * (∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D * 2 :=
            Nat.add_le_add_right hSUM _
        _ = 2 * ((∑ i ∈ range m, (m - i) * W (i + 1)) + (m + 1) * D) := by ring
  -- Assemble.
  calc Fintype.card V * (1 + 2 * r) + t * (3 * r ^ 2 - r)
      ≤ Fintype.card V * (1 + 2 * r) + ∑ i ∈ range r, (r - i) * W i :=
        Nat.add_le_add_left hDr _
    _ = ∑ x : V, (1 + 2 * r + ∑ i ∈ range r, (r - i) *
          (∑ v ∈ univ.filter (fun v => G.dist x v = i), (G.degree v - 2))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, hswapall]
    _ ≤ ∑ x : V, (univ.filter (fun v => G.dist x v ≤ r)).card := hsum1
    _ ≤ (Fintype.card V) ^ 2 := hRHS

end ACMax

/-! ## The 2-core extraction

The entry piece: from a graph with edge excess `t`, extract an induced subgraph of
minimum degree `≥ 2` still carrying the whole excess (`two_core_of_excess`). The
within-`S` bookkeeping is `degWithin G S v` (neighbours of `v` inside `S`) and
`edgeSumWithin G S = ∑_{u∈S} degWithin G S u` (twice the induced edge count), with
the handshake `edgeSumWithin_eq_pairs` and the erase law `edgeSumWithin_erase`. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

/-- The number of neighbours of `v` lying inside the finite set `S` — the degree of `v` in the
induced subgraph `G.induce ↑S`. -/
@[expose] def degWithin (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun w => G.Adj v w)).card

/-- Twice the number of edges of `G` with both endpoints in `S`, written as the within-`S`
degree sum. -/
def edgeSumWithin (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ u ∈ S, degWithin G S u

/-- **The within-`S` handshake.**  The within-`S` degree sum equals the number of ordered adjacent
pairs with both coordinates in `S`. -/
theorem edgeSumWithin_eq_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgeSumWithin G S = ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card := by
  classical
  rw [edgeSumWithin, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [degWithin, Finset.card_filter]

/-- **The erase law.**  Deleting a vertex `v ∈ S` drops the within-`S` degree sum by exactly twice
the within-`S` degree of `v`. -/
theorem edgeSumWithin_erase [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    edgeSumWithin G S = edgeSumWithin G (S.erase v) + 2 * degWithin G S v := by
  have hstep : ∀ u : V, degWithin G S u
      = degWithin G (S.erase v) u + (if G.Adj u v then 1 else 0) := by
    intro u
    rw [degWithin, degWithin]
    have hS : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    nth_rewrite 1 [hS]
    rw [Finset.filter_insert]
    by_cases hadj : G.Adj u v
    · have hvnotin : v ∉ (S.erase v).filter (fun w => G.Adj u w) := by
        simp [Finset.mem_filter, Finset.mem_erase]
      rw [ite_eq_left hadj, Finset.card_insert_of_notMem hvnotin, ite_eq_left hadj]
    · rw [ite_eq_right hadj, ite_eq_right hadj, add_zero]
  have hcount : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0) = degWithin G S v := by
    have h1 : ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℕ) else 0)
        = ∑ u ∈ S, (if G.Adj u v then (1 : ℕ) else 0) :=
      Finset.sum_erase (f := fun u => if G.Adj u v then (1 : ℕ) else 0) (a := v) S
        (by simp [SimpleGraph.irrefl])
    rw [h1, degWithin, Finset.card_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    exact if_congr (G.adj_comm u v) rfl rfl
  rw [edgeSumWithin, ← Finset.add_sum_erase _ _ hv]
  rw [Finset.sum_congr rfl (fun u _ => hstep u)]
  rw [Finset.sum_add_distrib, hcount, edgeSumWithin]
  omega

/-- **The 2-core induction.**  Starting from any `S` carrying the excess `2·|S| + 2t ≤
edgeSumWithin G S`, one reaches a nonempty subset of minimum within-degree `≥ 2` still carrying the
excess, by repeatedly deleting a within-degree `≤ 1` vertex. -/
theorem two_core_aux (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ}
    (ht : 1 ≤ t) :
    ∀ S : Finset V, 2 * S.card + 2 * t ≤ edgeSumWithin G S →
      ∃ S' : Finset V, S' ⊆ S ∧ S'.Nonempty ∧
        (∀ v ∈ S', 2 ≤ degWithin G S' v) ∧ 2 * S'.card + 2 * t ≤ edgeSumWithin G S' := by
  classical
  refine Finset.strongInduction (fun S ih => ?_)
  intro hinv
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [edgeSumWithin, Finset.sum_empty, Finset.card_empty] at hinv; omega
    · exact h
  by_cases hmin : ∀ v ∈ S, 2 ≤ degWithin G S v
  · exact ⟨S, subset_rfl, hSne, hmin, hinv⟩
  · simp only [not_forall, not_le] at hmin
    obtain ⟨v, hvS, hvdeg⟩ := hmin
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
    have hkey := edgeSumWithin_erase G hvS
    have hcard' : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
    have hnew : 2 * (S.erase v).card + 2 * t ≤ edgeSumWithin G (S.erase v) := by omega
    obtain ⟨S', hsub, hne', hmin', hinv'⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) hnew
    exact ⟨S', hsub.trans (Finset.erase_subset _ _), hne', hmin', hinv'⟩

end ACMax
