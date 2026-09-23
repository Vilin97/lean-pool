/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Push
public import LeanPool.ACMax.Reduction.Residual
public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Spectral.RayleighUpper
public import LeanPool.ACMax.Spectral.TestVector
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import LeanPool.ACMax.Counting.CompactCell
public import LeanPool.ACMax.Counting.DoubleStar

/-!
# The residual-core interface lemmas

Generic (`n`-free where possible) glue lemmas mediating between the residual-core
open Classical in
structure and the counting/covering layers. Here `M = G[D]` is the subgraph
induced on the degree-3 set `D`, and iso twins are the `M`-isolated degree-3
vertices.

## Main results

* `each_iso_three_hubs_general` — an `M`-isolated degree-3 vertex meets exactly
  the three hubs (`4 ≤ deg`).
* `hub_iso_sum_general` — the two-hub selection engine's core count
  `∑_{a∈Hub} |N(a) ∩ Iso| = 3·|Iso|`.
* `dist_le_three_of_mem_closeSet` — the metric half of the compact-ball interface:
  every membership certificate for the radius-3 combinatorial ball `closeSet G u₀`
  is a walk of length `≤ 3`, so `closeSet` sits inside the graph-distance ball.
* `s0_of_no_medge`, `deg3_eq_isoTwins_of_s0`, `twin_incidence_total` — the
  `e(M) = 0` normalization: with no degree-3–degree-3 edge, `D` *is* the iso-twin
  set and the twin incidence total is `3·|Iso|`.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- **B3 — Each `M`-isolated twin meets exactly three hubs.**  An `M`-isolated degree-`3`
twin `t` (`(N t ∩ D).card = 0`) has all three of its neighbours in `Hub`, so
`(N t ∩ Hub).card = 3`. -/
theorem each_iso_three_hubs_general {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D Hub : Finset V)
    (hmemD : ∀ v : V, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : V, v ∈ Hub ↔ 4 ≤ G.degree v)
    (h3 : ∀ v : V, 3 ≤ G.degree v)
    (t : V) (htD : t ∈ D) (htiso : (G.neighborFinset t ∩ D).card = 0) :
    (G.neighborFinset t ∩ Hub).card = 3 := by
  classical
  have hDH : ∀ v : V, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hsub : G.neighborFinset t ⊆ Hub := by
    intro x hx
    rcases hDH x with hxD | hxH
    · exfalso
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at htiso
      exact htiso x (Finset.mem_inter.mpr ⟨hx, hxD⟩)
    · exact hxH
  rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, (hmemD t).mp htD]

end ACMax

/-! ## The two-hub selection engine

Abstract `Finset` counting over given sets `Hub, Iso`: `hub_iso_sum_general`
records `∑_{a∈Hub} |N(a) ∩ Iso| = 3·|Iso|`, since each iso twin meets exactly
three hubs. -/

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- **Total iso-degree is `3·|Iso|`.**  Each `M`-isolated twin meets exactly three hubs. -/
theorem hub_iso_sum_general (G : SimpleGraph V) (Hub Iso : Finset V)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3) :
    ∑ a ∈ Hub, (G.neighborFinset a ∩ Iso).card = 3 * Iso.card := by
  rw [cross_count G Hub Iso]
  calc ∑ t ∈ Iso, (G.neighborFinset t ∩ Hub).card
      = ∑ _t ∈ Iso, 3 := Finset.sum_congr rfl (fun t ht => hiso3 t ht)
    _ = 3 * Iso.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end ACMax

/-! ## The `closeSet → dist` bound

The metric half of the compact-ball interface: every membership certificate for
the radius-3 combinatorial ball `closeSet G u₀` is a walk of length `≤ 3`, so
`closeSet` sits inside the graph-distance ball of radius 3 around `u₀`. -/

namespace ACMax

open Finset

variable {n : ℕ}

open Classical in
/-- **A `closeSet` member is within distance `3`.**  Every vertex of
the radius-`3` combinatorial ball `closeSet G u₀` is at graph distance `≤ 3` from
`u₀`; each membership certificate is a walk of length `≤ 3`.  No connectivity is
needed. -/
theorem dist_le_three_of_mem_closeSet (G : SimpleGraph (Fin n)) (u₀ v : Fin n)
    (hv : v ∈ closeSet G u₀) : G.dist u₀ v ≤ 3 := by
  unfold closeSet at hv
  rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union] at hv
  rcases hv with rfl | (hA | hB) | hC
  · rw [SimpleGraph.dist_self]; omega
  · rw [SimpleGraph.mem_neighborFinset] at hA
    have hle := SimpleGraph.dist_le (SimpleGraph.Walk.cons hA SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
    omega
  · rw [Finset.mem_biUnion] at hB
    obtain ⟨w, hw, hwv⟩ := hB
    rw [SimpleGraph.mem_neighborFinset] at hw hwv
    have hle := SimpleGraph.dist_le
      (SimpleGraph.Walk.cons hw (SimpleGraph.Walk.cons hwv SimpleGraph.Walk.nil))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
    omega
  · rw [Finset.mem_biUnion] at hC
    obtain ⟨x, hx, hxv⟩ := hC
    rw [Finset.mem_biUnion] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [SimpleGraph.mem_neighborFinset] at hw hwx hxv
    have hle := SimpleGraph.dist_le (SimpleGraph.Walk.cons hw
      (SimpleGraph.Walk.cons hwx (SimpleGraph.Walk.cons hxv SimpleGraph.Walk.nil)))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
    omega

end ACMax

/-! ## The `e(M) = 0` normalization

The normalization leaves for the `e(M) = 0` case: `s0_of_no_medge` pushes the
absence of a degree-3–degree-3 edge into the pointwise `hs0` form,
`deg3_eq_isoTwins_of_s0` shows the degree-3 set then coincides with the iso-twin
set, and `twin_incidence_total` records the resulting incidence total
`∑_{h∈Hub} |N(h) ∩ Iso| = 3·|Iso|`. -/

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- **B-0a (push).**  The negation of a degree-`3`–degree-`3` edge, in the pointwise
`hs0` form the downstream `e(M) = 0` fight consumes. -/
theorem s0_of_no_medge (G : SimpleGraph V)
    (h : ¬ ∃ v w : V, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w) :
    ∀ v w : V, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
  fun v w hv hw hadj => h ⟨v, w, hv, hw, hadj⟩

open Classical in
/-- **B-0a (identification).**  Under `hs0` (no degree-`3`–degree-`3` adjacency) every
degree-`3` vertex is `M`-isolated, so the degree-`3` set coincides with the `M`-isolated
twin set: `deg3Set G = isoTwins G`.  The forward inclusion is the `(a)`-step `hsub` of
`xmz_pigeonhole_input`; the reverse is the definitional `isoTwins ⊆ deg3Set`. -/
theorem deg3_eq_isoTwins_of_s0 (G : SimpleGraph V)
    (hs0 : ∀ v w : V, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    deg3Set G = isoTwins G := by
  apply Finset.Subset.antisymm
  · intro v hv
    have hvd3 : G.degree v = 3 := mem_deg3Set.mp hv
    exact mem_isoTwins.mpr ⟨hvd3, fun w hadj hw3 => hs0 v w hvd3 hw3 hadj⟩
  · intro v hv
    exact mem_deg3Set.mpr (mem_isoTwins.mp hv).1

open Classical in
/-- **B-0c.**  The twin-incidence total.  Under `hs0` (`e(M) = 0`) and minimum degree `3`
each `M`-isolated twin meets exactly three hubs (`each_iso_three_hubs_general`), so the
hub-to-twin incidence sum is `3·|Iso|` (`hub_iso_sum_general`):
`∑_{h∈Hub} |N(h) ∩ Iso| = 3·|Iso|`.  This is the exact shape the `B1` residue fights
(e.g. the single-heavy budget `xmz_single5_budget`) consume; the banked
`hub_iso_sum_general` already carries this statement for *given* `Hub, Iso`, and this leaf
supplies its per-twin hypothesis directly from the definition of `isoTwins` (whose members
are intrinsically `M`-isolated), so only minimum degree `3` is needed here — the `hs0`
`e(M) = 0` hypothesis of the surrounding node is what identifies `|Iso| = n₃` upstream
(`deg3_eq_isoTwins_of_s0`), not this incidence identity. -/
theorem twin_incidence_total (G : SimpleGraph V)
    (h3 : ∀ v : V, 3 ≤ G.degree v) :
    ∑ h ∈ hubSet G, (G.neighborFinset h ∩ isoTwins G).card = 3 * (isoTwins G).card := by
  apply hub_iso_sum_general G (hubSet G) (isoTwins G)
  intro t ht
  have htd3 : G.degree t = 3 := (mem_isoTwins.mp ht).1
  have htiso : ∀ w : V, G.Adj t w → G.degree w ≠ 3 := (mem_isoTwins.mp ht).2
  refine each_iso_three_hubs_general G (deg3Set G) (hubSet G)
    (fun v => mem_deg3Set) (fun v => mem_hubSet) h3 t (mem_deg3Set.mpr htd3) ?_
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter] at hx
  exact htiso x ((G.mem_neighborFinset t x).mp hx.1) (mem_deg3Set.mp hx.2)

end ACMax
