/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.Greedy
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# Subcubic Brooks theorem: NonRegular

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Greedy colouring along an injective rank (helper). -/
theorem colorable_of_lower_neighbors_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (rank : V → ℕ) (hrank : Function.Injective rank)
    (h : ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card < k) :
    G.Colorable k := by
  classical
  by_cases hk : 0 < k
  · obtain ⟨c, hc, _⟩ := greedy_coloring_zero G k hk rank hrank h
    exact ⟨⟨c, fun {u v} huv => hc u v huv⟩⟩
  · have : IsEmpty V := ⟨fun v => by have hv := h v; omega⟩
    exact SimpleGraph.Colorable.of_isEmpty k

omit [Fintype V] in
/-- In a connected graph, any `u ≠ v₀` has a neighbour `w`
strictly closer to `v₀` (the second vertex of a geodesic from `u` to `v₀`). -/
theorem exists_closer_neighbor (G : SimpleGraph V)
    (hconn : G.Connected) (v₀ u : V) (hu : u ≠ v₀) :
    ∃ w, G.Adj u w ∧ G.dist v₀ w < G.dist v₀ u := by
  classical
  have hreach : G.Reachable u v₀ := hconn.preconnected u v₀
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hne0 : G.dist u v₀ ≠ 0 := by
    rw [ne_eq, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable, not_or, not_not]
    exact ⟨hu, hreach⟩
  have hnp : ¬ q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  refine ⟨q.snd, ?_, ?_⟩
  · exact q.adj_snd hnp
  · have htail : G.dist q.snd v₀ ≤ q.tail.length := SimpleGraph.dist_le q.tail
    have hlen : q.tail.length + 1 = q.length := q.length_tail_add_one hnp
    have hc1 : G.dist v₀ q.snd = G.dist q.snd v₀ := SimpleGraph.dist_comm
    have hc2 : G.dist v₀ u = G.dist u v₀ := SimpleGraph.dist_comm
    rw [hc1, hc2, ← hq]
    omega

/-- A connected subcubic graph with a vertex of degree below three is three-colourable. -/
theorem connected_colorable_three_of_exists_degree_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ 3) (hlow : ∃ v, G.degree v < 3) : G.Colorable 3 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hlow
  set N := Fintype.card V with hN
  let e : V → ℕ := fun x => ((Fintype.equivFin V) x : ℕ)
  have he_lt : ∀ x, e x < N := fun x => ((Fintype.equivFin V) x).isLt
  have he_inj : Function.Injective e := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  set rank : V → ℕ := fun x => N * (N - G.dist v₀ x) + e x with hrank_def
  have hrank_inj : Function.Injective rank := by
    intro a b hab
    have hmod : ∀ x, rank x % N = e x := fun x => by
      simp only [hrank_def, Nat.mul_add_mod, Nat.mod_eq_of_lt (he_lt x)]
    have : e a = e b := by rw [← hmod a, ← hmod b, hab]
    exact he_inj this
  have hdist_lt : ∀ u, G.dist v₀ u < N := by
    intro u
    obtain ⟨p, hp, hlen⟩ := (hconn.preconnected v₀ u).exists_path_of_dist
    rw [← hlen]; exact hp.length_lt
  apply colorable_of_lower_neighbors_lt G 3 rank hrank_inj
  intro u
  by_cases hu : u = v₀
  · subst hu
    calc ((G.neighborFinset u).filter fun w => rank w < rank u).card
        ≤ (G.neighborFinset u).card := Finset.card_filter_le _ _
      _ = G.degree u := (G.card_neighborFinset_eq_degree u)
      _ < 3 := hv₀
  · obtain ⟨w, hadj, hwlt⟩ := exists_closer_neighbor G hconn v₀ u hu
    have hblock : N - G.dist v₀ u < N - G.dist v₀ w := by have := hdist_lt u; omega
    have hrank_wu : rank u < rank w := by
      rw [hrank_def]; simp only
      have h1 : N * (N - G.dist v₀ u) + e u < N * (N - G.dist v₀ u) + N := by
        have := he_lt u; omega
      have h2 : N * (N - G.dist v₀ u) + N ≤ N * (N - G.dist v₀ w) := by
        have hb : (N - G.dist v₀ u) + 1 ≤ (N - G.dist v₀ w) := by omega
        calc N * (N - G.dist v₀ u) + N = N * ((N - G.dist v₀ u) + 1) := by ring
          _ ≤ N * (N - G.dist v₀ w) := by gcongr
      omega
    have hwmem : w ∈ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hsub : ((G.neighborFinset u).filter fun x => rank x < rank u)
        ⊆ (G.neighborFinset u).erase w := by
      intro x hx
      rw [Finset.mem_filter] at hx; rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl; omega
    calc ((G.neighborFinset u).filter fun x => rank x < rank u).card
        ≤ ((G.neighborFinset u).erase w).card := Finset.card_le_card hsub
      _ = G.degree u - 1 := by rw [Finset.card_erase_of_mem hwmem, G.card_neighborFinset_eq_degree]
      _ < 3 := by have := hdeg u; omega

end BrooksSubcubic
end
