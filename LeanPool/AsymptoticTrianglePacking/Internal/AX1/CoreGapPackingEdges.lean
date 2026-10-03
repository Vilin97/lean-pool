/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the LP weight carried by a set of edges

Part of the `ν₃*` bookkeeping of the AX1 residual (`RESIDUAL.md`, §2, (R2)).  The allocation of a
cluster pair among the triples that use it is feasible only because a fractional triangle packing
puts total weight at most `e(U, W)` on the triangles through the `U–W` edges.  This file
proves that,
in the general form:

* `Nibble.AX1.sum_fracPacking_over_edges_le` — for a fractional triangle packing `w` and any finset
  `E` of (vertex sets of) edges, the total weight of the triangles meeting `E` is at most `#E`.
* `Nibble.AX1.nu3star_le_of_edgeCover` — hence `ν₃*(G) ≤ #E` for any `E` meeting every triangle:
  the fractional packing number is at most the size of any triangle edge cover.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge

/-! # CoreGapPackingEdges -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The LP weight on the triangles through a set of edges is at most the number of edges.**
Each triangle counted on the left contains at least one `e ∈ E`, and the packing constraint at `e`
caps the weight through `e` by `1`. -/
theorem sum_fracPacking_over_edges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : Finset (Finset V) → ℝ} (hw : IsFracPacking G w) (E : Finset (Finset V)) :
    ∑ T ∈ (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T), w T ≤ (#E : ℝ) := by
  classical
  obtain ⟨hnn, -, hcon⟩ := hw
  set s := (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T) with hs
  -- 1. replace each weight by the sum of copies of it, one for each `e ∈ E` inside the triangle
  have step1 : ∑ T ∈ s, w T ≤ ∑ T ∈ s, ∑ _e ∈ E.filter (fun e => e ∈ T), w T := by
    refine Finset.sum_le_sum fun T hT => ?_
    obtain ⟨e, heE, heT⟩ := (Finset.mem_filter.mp (hs ▸ hT)).2
    exact Finset.single_le_sum (f := fun _ : Finset V => w T) (fun _ _ => hnn T) (a := e)
      (Finset.mem_filter.mpr ⟨heE, heT⟩)
  -- 2. exchange the two summations
  have step2 : ∑ T ∈ s, ∑ _e ∈ E.filter (fun e => e ∈ T), w T
      = ∑ e ∈ E, ∑ T ∈ s.filter (fun T => e ∈ T), w T := by
    have h1 : ∀ T ∈ s, ∑ _e ∈ E.filter (fun e => e ∈ T), w T
        = ∑ e ∈ E, if e ∈ T then w T else 0 := fun T _ => Finset.sum_filter _ _
    have h2 : ∀ e ∈ E, ∑ T ∈ s.filter (fun T => e ∈ T), w T
        = ∑ T ∈ s, if e ∈ T then w T else 0 := fun e _ => Finset.sum_filter _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  -- 3. the packing constraint at each edge
  have step3 : ∀ e ∈ E, ∑ T ∈ s.filter (fun T => e ∈ T), w T ≤ 1 := by
    intro e _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun T _ _ => hnn T) (hcon e)
    intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨(Finset.mem_filter.mp (hs ▸ hT.1)).1, hT.2⟩
  calc ∑ T ∈ s, w T ≤ ∑ T ∈ s, ∑ _e ∈ E.filter (fun e => e ∈ T), w T := step1
    _ = ∑ e ∈ E, ∑ T ∈ s.filter (fun T => e ∈ T), w T := step2
    _ ≤ ∑ _e ∈ E, (1 : ℝ) := Finset.sum_le_sum step3
    _ = (#E : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **A triangle edge cover bounds `ν₃*`.**  If every triangle of `G` uses an edge from `E`, then
`ν₃*(G) ≤ #E`.  (With `E` the whole edge set this is weaker than `Nibble.YusterE.nu3star_le`; the
point is the localised version, applied to the edges between two clusters.) -/
theorem nu3star_le_of_edgeCover (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Finset V))
    (hcov : ∀ T ∈ triangleHypergraphE G, ∃ e ∈ E, e ∈ T) : nu3star G ≤ (#E : ℝ) := by
  classical
  refine Real.sSup_le ?_ (Nat.cast_nonneg _)
  rintro x ⟨w, hw, rfl⟩
  have hfilter : (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T)
      = triangleHypergraphE G := Finset.filter_true_of_mem hcov
  have := sum_fracPacking_over_edges_le G hw E
  rwa [hfilter] at this

end Nibble.AX1
