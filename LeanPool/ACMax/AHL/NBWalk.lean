/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Non-backtracking walks — the foundation of the AHL irregular-Moore ladder

This file begins the non-backtracking-walk proof of the irregular Moore bound
of Alon, Hoory and Linial ("The Moore bound for irregular graphs", *Graphs and
Combinatorics* **18** (2002), 53–57). The imported dependency closure includes
walk counting (`NBWalkCount`, `NBWeighted`), stationary weighted marginals
(`AHLStationary`, `AHLMarginals`), weighted AM–GM (`AHLAmGm`), and the resulting
ball bound `ahl_ball_moore` and girth bound `ahl_ball_girth_bound` in `Band.Sum`.

This file lands the *non-backtracking walk* machinery the bound is counted over.  A walk is
**non-backtracking** when it never immediately reverses a step: `w.getVert (i + 2) ≠ w.getVert i`
for every valid `i`.  This is the exact `getVert` form the SQRT ray/ball rows consume.

## Contents

* **`IsNonBacktracking`** — the predicate, plus its basic API (`nil` and length-`≤ 1` walks are
  non-backtracking; every path is non-backtracking).
* **`nb_walk_isPath_of_girth`** — the injectivity core: under the landed girth hypothesis (no cycle
  of length `≤ 2r + 1`), every non-backtracking walk of length `≤ r` is a **path**.  This
  generalizes the ray-growth injectivity `exists_isPath_len_of_min_two` (that grew *one* such path;
  here *every* non-backtracking walk is one).  The proof peels the first edge, so the tail is a
  non-backtracking walk of length `≤ r` hence a path by induction; a revisit of the start vertex
  then supplies two distinct short paths to it, closing a cycle of length `≤ r ≤ 2r + 1`.
* **`nb_extension_count`** — the `deg − 1` branching atom: the neighbours of `y` other than the
  arrived-from vertex `z` number `deg y − 1`.  This is the per-step count the future AM-GM-weighted
  AHL count consumes.

## Scope note

The degree-weighted lower bound on the *number* of non-backtracking walks and the weighted AM-GM
assembly into the Moore bound are the follow-up counting node; this file lands the foundation only.
-/

public section

namespace ACMax

open SimpleGraph

/-- A walk is **non-backtracking** when it never immediately reverses a step: for every position
`i` with `i + 2 ≤ w.length`, the vertex two steps ahead differs from the current one.  (For `nil`
and single-edge walks the condition is vacuous.) -/
@[expose] def IsNonBacktracking {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) : Prop :=
  ∀ i : ℕ, i + 2 ≤ w.length → w.getVert (i + 2) ≠ w.getVert i

/-- Any walk of length at most `1` (in particular `nil` and a single edge) is non-backtracking:
there is no position `i` with `i + 2 ≤ w.length`. -/
theorem isNonBacktracking_of_length_le_one {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} (hw : w.length ≤ 1) : IsNonBacktracking w := by
  intro i hi; omega

/-- A single-edge walk is non-backtracking. -/
theorem isNonBacktracking_cons_nil {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    IsNonBacktracking (Walk.cons h Walk.nil) :=
  isNonBacktracking_of_length_le_one (by simp)

/-- **The injectivity core.**  In a graph with no cycle of length `≤ 2r + 1`, every
non-backtracking walk of length `≤ r` is a path.  (The special case where the walk is grown one
edge at a time is the landed ray-growth `exists_isPath_len_of_min_two`.)  Peeling the first edge,
the tail is a non-backtracking walk of length `≤ r`, hence a path by induction.  If the start
vertex `x` were revisited on the tail, the sub-path to it and the single reversing edge give two
distinct paths whose total length is `≤ r`, closing a cycle of length `≤ 2r + 1` — impossible. -/
theorem nb_walk_isPath_of_girth {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 2 * r + 1 < c.length) :
    ∀ {x y : V} (w : G.Walk x y), IsNonBacktracking w → w.length ≤ r → w.IsPath := by
  classical
  intro x y w
  induction w with
  | nil => intro _ _; exact Walk.IsPath.nil
  | @cons a b c h p ih =>
    intro hnb hlen
    have hnbp : IsNonBacktracking p := by
      intro i hi
      rw [← Walk.getVert_cons_succ p h (n := i + 2), ← Walk.getVert_cons_succ p h (n := i)]
      exact hnb (i + 1) (by rw [Walk.length_cons]; omega)
    have hlenp : p.length ≤ r := by rw [Walk.length_cons] at hlen; omega
    have hp : p.IsPath := ih hnbp hlenp
    rw [Walk.cons_isPath_iff]
    refine ⟨hp, ?_⟩
    intro hx
    set Q := p.takeUntil a hx with hQdef
    have hQ : Q.IsPath := hp.takeUntil hx
    have hQle : Q.length ≤ p.length := p.length_takeUntil_le_length hx
    have hQlen_ne : Q.length ≠ 1 := by
      intro hQ1
      have hple : (1 : ℕ) ≤ p.length := by omega
      have hval : p.getVert Q.length = a := p.getVert_length_takeUntil hx
      rw [hQ1] at hval
      have hnb0 := hnb 0 (by rw [Walk.length_cons]; omega)
      rw [Walk.getVert_zero] at hnb0
      apply hnb0
      rw [show (0 : ℕ) + 2 = 1 + 1 by rfl, Walk.getVert_cons_succ, hval]
    set E := Walk.cons h.symm Walk.nil with hEdef
    have hE : E.IsPath := by
      rw [hEdef, Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simp [h.symm.ne]⟩
    have hElen : E.length = 1 := by rw [hEdef]; simp
    have hne : Q ≠ E := by
      intro heq
      apply hQlen_ne
      rw [heq, hElen]
    obtain ⟨w', -, -, c, hc, hcl⟩ := hQ.exists_isCycle_length_le_add_of_ne hE hne
    have hgc := hg w' c hc
    rw [hElen] at hcl
    rw [Walk.length_cons] at hlen
    omega

/-- **The `deg − 1` branching atom.**  A non-backtracking walk arriving at `y` from `z` may continue
to any neighbour of `y` *except* `z`; these valid next-vertices are `neighborFinset y \ {z}` and
there are exactly `deg y − 1` of them.  This is the per-step count the AHL non-backtracking-walk
count is built on. -/
theorem nb_extension_count {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {y z : V} (h : G.Adj y z) :
    (G.neighborFinset y \ {z}).card = G.degree y - 1 := by
  classical
  have hz : z ∈ G.neighborFinset y := (G.mem_neighborFinset y z).mpr h
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hz,
    G.card_neighborFinset_eq_degree]

end ACMax
