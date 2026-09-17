/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.PathGraph
import LeanPool.Schoenflies.Graph.TwoConnected

/-!
# A cycle, as two paths sharing their ends, is 2-connected

`lem:union-two-connected` says a union of two 2-connected graphs sharing two vertices is
2-connected. Its companion is the base case: a *cycle* — two internally disjoint paths with the
same two ends — is 2-connected, and neither path is 2-connected on its own, so the union lemma
cannot deliver it.

Stated for an ambient graph `K` that the two paths cover, rather than for `Graph.union`, so
that a geometric consumer never has to prove a graph equality — which is the form in which the
consumers actually arrive.

This is the general lemma extracted from a second, independent attempt at
`Schoenflies.squaresTwoConnected` (the one that landed is `Schoenflies/SquareCycle.lean`, by a
different route). It is kept because it is reusable and because at least two consumers want it:
the anchored square mesh of `prop:anchored-square-mesh`, whose collar rectangles are attached
one cycle at a time, and any later argument that has to see a subdivided closed curve as a
2-connected graph.

## Blueprint

* `Graph.isTwoConnected_of_two_paths` — the cycle base case of `lem:union-two-connected`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {K P Q : Graph α β} {u v c : α} {W₁ W₂ : List β}

/-- **A graph covered by two paths with the same two ends, meeting only there, is
2-connected.**

Stated for an ambient graph `K` that the two paths cover, rather than for `Graph.union`, so
that a geometric consumer never has to prove a graph equality.

Deleting a vertex `c`: every surviving vertex reaches an end of its own path
(`Graph.IsPathGraph.reaches_an_end`).  If `c` is neither end, then `c` misses one of the two
paths — they share only `u` and `v` — and that whole path still joins `u` to `v`, so `u` is a
hub.  If `c` is an end, the branch reaching it is impossible (a deleted vertex is reached by
nothing) and the other end is the hub. -/
theorem isTwoConnected_of_two_paths (hPK : P ≤ K) (hQK : Q ≤ K) (hV : V(K) ⊆ V(P) ∪ V(Q))
    (hP : P.IsPathGraph u W₁ v) (hQ : Q.IsPathGraph u W₂ v) (huv : u ≠ v)
    (hmeet : ∀ x ∈ V(P), x ∈ V(Q) → x = u ∨ x = v) (h3 : K.HasThreeVertices) :
    K.IsTwoConnected where
  hasThreeVertices := h3
  connected :=
    Connected.of_two_subgraphs hPK hQK hV hP.connected hQ.connected hP.source_mem hQ.source_mem
  deleteVerts_connected := by
    intro c _
    -- Whatever is deleted, every surviving vertex reaches one of the two ends.
    have hreach : ∀ x ∈ V(K), x ≠ c →
        (K.deleteVerts {c}).Reaches x u ∨ (K.deleteVerts {c}).Reaches x v := by
      intro x hx hxc
      rcases hV hx with h | h
      · exact (hP.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hPK _))
          fun hr ↦ hr.mono (deleteVerts_mono hPK _)
      · exact (hQ.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hQK _))
          fun hr ↦ hr.mono (deleteVerts_mono hQK _)
    have huK : u ∈ V(K) := hPK.vertexSet_mono hP.source_mem
    have hvK : v ∈ V(K) := hPK.vertexSet_mono hP.target_mem
    by_cases hcu : c = u
    · -- The source is gone; the target is the hub, and the branch reaching the source cannot
      -- have happened.
      refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne hvK (by rw [hcu]; exact Ne.symm huv)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact absurd hcu.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
      · exact hr.symm
    by_cases hcv : c = v
    · refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact hr.symm
      · exact absurd hcv.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
    -- Otherwise one of the two paths never had `c`, and it joins the two ends.
    have hvu : (K.deleteVerts {c}).Reaches v u := by
      by_cases hcP : c ∈ V(P)
      · have hcQ : c ∉ V(Q) := fun h ↦ by
          rcases hmeet c hcP h with h' | h'
          exacts [hcu h', hcv h']
        have hr := hQ.connected.reaches hQ.target_mem hQ.source_mem
        rw [← deleteVerts_singleton_eq_self hcQ] at hr
        exact hr.mono (deleteVerts_mono hQK _)
      · have hr := hP.connected.reaches hP.target_mem hP.source_mem
        rw [← deleteVerts_singleton_eq_self hcP] at hr
        exact hr.mono (deleteVerts_mono hPK _)
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
    intro x hx
    rw [vertexSet_deleteVerts] at hx
    have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
    rcases hreach x hx.1 hxc with hr | hr
    · exact hr.symm
    · exact (hr.trans hvu).symm

end Graph
