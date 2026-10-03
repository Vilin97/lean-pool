/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster Y6 (upper) — the fractional triangle-packing number is `≤ |E(G)|/3`

Standalone, Mathlib-only. The fractional relaxation cannot beat `|E(G)|/3`: each triangle uses `3`
edges, and every edge carries total weight `≤ 1`, so summing the per-edge constraint over all edges
counts every triangle `3` times, giving `3·∑_T w_T ≤ |E(G)|`. Hence `ν₃*(G) ≤ |E(G)|/3`.

Combined with `nu3_ge_nibble` (`ν₃ ≥ (1-β)|E|/3`), this pins `ν₃* − ν₃ ≤ β·|E(G)|/3` — the Y6 gap
control that, with `β → 0` and the `o(n²)` accounting, yields AX1.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType

/-! # YusterFracUpper -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The all-zero weighting is a fractional packing. -/
theorem isFracPacking_zero : IsFracPacking G (fun _ => 0) :=
  ⟨fun _ => le_refl 0, fun _ _ => rfl, fun e => by simp⟩

/-- Each hyperedge of `triangleHypergraphE G` is a set of `2`-cliques (edges). -/
theorem triangleHypergraphE_subset_edges {T : Finset (Finset V)}
    (hT : T ∈ triangleHypergraphE G) : T ⊆ G.cliqueFinset 2 := by
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  exact powersetCard_two_subset_cliqueFinset G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)

/-- **Per-packing bound.** For any fractional packing `w`, the total weight is `≤ |E(G)|/3`. Double
counting: `3·∑_T w_T = ∑_T ∑_{e∈T} w_T = ∑_e ∑_{T∋e} w_T ≤ ∑_e 1 = |E(G)|`. -/
theorem fracPacking_sum_le {w : Finset (Finset V) → ℝ} (hw : IsFracPacking G w) :
    (∑ T ∈ triangleHypergraphE G, w T) ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := by
  obtain ⟨_, _, hcon⟩ := hw
  have hTcard : ∀ T ∈ triangleHypergraphE G, T.card = 3 := triangleHypergraphE_uniform G
  have expand : ∀ T ∈ triangleHypergraphE G,
      ∑ e ∈ G.cliqueFinset 2, (if e ∈ T then w T else 0) = 3 * w T := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (triangleHypergraphE_subset_edges G hT),
      Finset.sum_const, hTcard T hT, nsmul_eq_mul]
    norm_num
  have dc : (3 : ℝ) * (∑ T ∈ triangleHypergraphE G, w T) ≤ ((G.cliqueFinset 2).card : ℝ) := by
    have lhs_eq : (3 : ℝ) * (∑ T ∈ triangleHypergraphE G, w T)
        = ∑ e ∈ G.cliqueFinset 2, ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w T else 0) := by
      rw [Finset.mul_sum, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun T hT => (expand T hT).symm)
    calc (3 : ℝ) * (∑ T ∈ triangleHypergraphE G, w T)
        = ∑ e ∈ G.cliqueFinset 2, ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w T else 0) := lhs_eq
      _ = ∑ e ∈ G.cliqueFinset 2, ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T := by
          exact Finset.sum_congr rfl (fun e _ => by rw [Finset.sum_filter])
      _ ≤ ∑ _e ∈ G.cliqueFinset 2, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcon e)
      _ = ((G.cliqueFinset 2).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith only [dc]

/-- **Y6 (upper) — `ν₃* ≤ |E(G)|/3`.** The fractional triangle-packing number is bounded by
`|E(G)|/3`. Together with `nu3_ge_nibble` this bounds the integrality gap `ν₃* − ν₃`. -/
theorem nu3star_le : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := by
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  exact fracPacking_sum_le G hw

end Nibble.YusterE
