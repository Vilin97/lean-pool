/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **capacity constraint of a cluster pair**

The accounting behind `Nibble.AX1.BlockCoverResidual` (`Nibble.CoreGapBlockCover`) is the fractional
triangle packing LP of the weighted cluster graph: the rectangles that the cluster triples through a
cluster pair `(U, W)` may occupy have total area at most `#U·#W`, which after multiplying by the
density of the pair is the capacity `e(U, W)`.

This file proves the matching upper bound on the LP side: **a fractional triangle packing of the
graph puts total weight at most `e(U, W)` on the triangles that use a `U–W` edge**.  It is the
per-pair constraint whose sum over the cluster triples through `(U, W)` the design has to meet, and
it is proved from `Nibble.AX1.sum_fracPacking_over_edges_le` (`Nibble.CoreGapPackingEdges`) with the
set of `U–W` edges.

* `Nibble.AX1.sum_fracPacking_cluster_pair_le` — the capacity constraint;
* `Nibble.AX1.nu3star_le_of_clusterPairCover` — its `ν₃*` form: a family of cluster pairs meeting
  every triangle caps `ν₃*` by the total number of edges across those pairs.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPackingEdges
public import Mathlib.Combinatorics.SimpleGraph.Density

/-! # CoreGapClusterCapacity -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The edges of `G` crossing the pair `(U, W)`, as vertex sets. -/
noncomputable def crossEdges (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) :
    Finset (Finset V) :=
  (G.interedges U W).image (fun p => ({p.1, p.2} : Finset V))

omit [Fintype V] in
theorem card_crossEdges_le (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) :
    #(crossEdges G U W) ≤ #(G.interedges U W) :=
  Finset.card_image_le

/-- An edge of a triangle of `G` joining `U` to `W` is one of the `U–W` edges. -/
theorem mem_crossEdges_of_mem_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {U W : Finset V} {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G)
    {x y : V} (hx : x ∈ U) (hy : y ∈ W) (hxy : ({x, y} : Finset V) ∈ T) :
    ({x, y} : Finset V) ∈ crossEdges G U W := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [Finset.mem_powersetCard] at hxy
  obtain ⟨hsub, hcard⟩ := hxy
  have hne : x ≠ y := by
    intro h
    rw [h] at hcard
    simp at hcard
  have hxt : x ∈ t := hsub (by simp)
  have hyt : y ∈ t := hsub (by simp)
  have hadj : G.Adj x y := ht.1 hxt hyt hne
  refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
  rw [SimpleGraph.mk_mem_interedges_iff]
  exact ⟨hx, hy, hadj⟩

/-- **The capacity constraint of a cluster pair.**  A fractional triangle packing puts total weight
at most the number of `U–W` edges on the triangles that use one. -/
theorem sum_fracPacking_cluster_pair_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : Finset (Finset V) → ℝ} (hw : IsFracPacking G w) (U W : Finset V) :
    ∑ T ∈ (triangleHypergraphE G).filter
        (fun T => ∃ x ∈ U, ∃ y ∈ W, ({x, y} : Finset V) ∈ T), w T
      ≤ (#(G.interedges U W) : ℝ) := by
  classical
  have hnn : ∀ T, 0 ≤ w T := hw.1
  have hsub : (triangleHypergraphE G).filter
      (fun T => ∃ x ∈ U, ∃ y ∈ W, ({x, y} : Finset V) ∈ T)
      ⊆ (triangleHypergraphE G).filter (fun T => ∃ e ∈ crossEdges G U W, e ∈ T) := by
    intro T hT
    rw [Finset.mem_filter] at hT ⊢
    obtain ⟨hTmem, x, hx, y, hy, hxy⟩ := hT
    exact ⟨hTmem, ⟨{x, y}, mem_crossEdges_of_mem_triangle G hTmem hx hy hxy, hxy⟩⟩
  have hmono : ∑ T ∈ (triangleHypergraphE G).filter
        (fun T => ∃ x ∈ U, ∃ y ∈ W, ({x, y} : Finset V) ∈ T), w T
      ≤ ∑ T ∈ (triangleHypergraphE G).filter
        (fun T => ∃ e ∈ crossEdges G U W, e ∈ T), w T :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => hnn T
  have hcap := sum_fracPacking_over_edges_le G hw (crossEdges G U W)
  have hcard : (#(crossEdges G U W) : ℝ) ≤ (#(G.interedges U W) : ℝ) := by
    exact_mod_cast card_crossEdges_le G U W
  linarith

/-- **The `ν₃*` form of the capacity constraint.**  If every triangle of `G` uses an edge crossing
one of the cluster pairs `(U i, W i)`, `i < k`, then `ν₃*(G)` is at most the total number of edges
across those pairs. -/
theorem nu3star_le_of_clusterPairCover (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (U W : ℕ → Finset V)
    (hcov : ∀ T ∈ triangleHypergraphE G, ∃ i < k, ∃ x ∈ U i, ∃ y ∈ W i,
      ({x, y} : Finset V) ∈ T) :
    nu3star G ≤ ∑ i ∈ Finset.range k, (#(G.interedges (U i) (W i)) : ℝ) := by
  classical
  refine nu3star_le_of_edgeCover G ((Finset.range k).biUnion (fun i => crossEdges G (U i) (W i)))
    ?_ |>.trans ?_
  · intro T hT
    obtain ⟨i, hi, x, hx, y, hy, hxy⟩ := hcov T hT
    exact ⟨{x, y}, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
      mem_crossEdges_of_mem_triangle G hT hx hy hxy⟩, hxy⟩
  · have h1 : #((Finset.range k).biUnion (fun i => crossEdges G (U i) (W i)))
        ≤ ∑ i ∈ Finset.range k, #(crossEdges G (U i) (W i)) := Finset.card_biUnion_le
    have h2 : ∑ i ∈ Finset.range k, #(crossEdges G (U i) (W i))
        ≤ ∑ i ∈ Finset.range k, #(G.interedges (U i) (W i)) :=
      Finset.sum_le_sum fun i _ => card_crossEdges_le G (U i) (W i)
    have : (#((Finset.range k).biUnion (fun i => crossEdges G (U i) (W i))) : ℝ)
        ≤ ((∑ i ∈ Finset.range k, #(G.interedges (U i) (W i)) : ℕ) : ℝ) := by
      exact_mod_cast le_trans h1 h2
    simpa using this

end Nibble.AX1
