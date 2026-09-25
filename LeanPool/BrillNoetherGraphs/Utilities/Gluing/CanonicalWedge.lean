/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge

/-!
# Canonical divisors on a vertex wedge

If two graphs are identified at marked vertices `x` and `y`, the canonical
divisor of the wedge is

`K_(G ∨ H) = K_G + K_H + 2(x = y)`.

The extra two chips are the valence correction at the identified vertex.  In
particular the sum of the two factor canonical divisors is canonically dual to
the doubled glue point.  Riemann--Roch then gives a useful uniform estimate:
on a connected wedge of total genus four, `K_G + K_H` has rank at least one.

This file is deliberately independent of genus two and of two-pole joins.  It
is the reusable one-pole calculation underlying the genus-two/genus-two seed.
-/

@[expose] public section

open Finset

namespace Utilities

universe u v
/-- The degree of a left vertex in a wedge is its left-factor degree, with the
right marked degree added at the common vertex. -/
theorem vertex_degree_vertexWedge_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (a : G.V) :
    vertexDegree (vertexWedge G H x y) (Sum.inl a) =
      vertexDegree G a + if a = x then vertexDegree H y else 0 := by
  unfold vertexDegree
  change
    (∑ z : Sum G.V {b : H.V // b ≠ y},
        (numEdges (vertexWedge G H x y) (Sum.inl a) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  simp_rw [num_edges_vertexWedge_left, num_edges_vertexWedge_left_right]
  by_cases ha : a = x
  · subst a
    simp only [if_pos]
    have hSplit := sum_unmarked_eq_sum_of_marked_zero H y
      (fun b => (numEdges H y b : ℤ)) (by simp)
    rw [hSplit]
  · simp [ha]
/-- A strictly-right vertex keeps its right-factor degree in a wedge. -/
theorem vertex_degree_vertexWedge_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : {b : H.V // b ≠ y}) :
    vertexDegree (vertexWedge G H x y) (Sum.inr b) =
      vertexDegree H b.1 := by
  unfold vertexDegree
  change
    (∑ z : Sum G.V {c : H.V // c ≠ y},
        (numEdges (vertexWedge G H x y) (Sum.inr b) z : ℤ)) = _
  rw [Fintype.sum_sum_type]
  have hLeft :
      (∑ a : G.V,
        (numEdges (vertexWedge G H x y) (Sum.inr b) (Sum.inl a) : ℤ)) =
        (numEdges H b.1 y : ℤ) := by
    simp_rw [num_edges_symmetric (vertexWedge G H x y) (Sum.inr b),
      num_edges_vertexWedge_left_right]
    simp_rw [Nat.cast_ite, Nat.cast_zero]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp [num_edges_symmetric H y b.1]
  rw [hLeft]
  simp_rw [num_edges_vertexWedge_right]
  have hSplit := sum_unmarked_add_marked H y
    (fun c => (numEdges H b.1 c : ℤ))
  linarith

/-- The sum of the two factor canonical divisors on their vertex wedge. -/
def wedgeCanonicalSum
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    CFDiv (vertexWedge G H x y) :=
  wedgeAddDivisor G H x y (canonicalDivisor G) (canonicalDivisor H)

/-- The doubled common vertex of a wedge. -/
def wedgeGlueDouble
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    CFDiv (vertexWedge G H x y) :=
  (2 : ℤ) • oneChip (Sum.inl x)
/-- **Canonical wedge formula.**  Identifying two vertices contributes two
additional canonical chips at the common vertex. -/
theorem canonical_divisor_vertexWedge
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    canonicalDivisor (vertexWedge G H x y) =
      wedgeCanonicalSum G H x y + wedgeGlueDouble G H x y := by
  funext z
  cases z with
  | inl a =>
      unfold canonicalDivisor wedgeCanonicalSum wedgeGlueDouble
      rw [vertex_degree_vertexWedge_inl]
      by_cases ha : a = x
      · subst a
        simp [canonicalDivisor, oneChip]
        ring
      · have hSum :
            (Sum.inl a : (vertexWedge G H x y).V) ≠ Sum.inl x :=
          fun h => ha (Sum.inl.inj h)
        simp [canonicalDivisor, oneChip, ha, hSum]
  | inr b =>
      unfold canonicalDivisor wedgeCanonicalSum wedgeGlueDouble
      rw [vertex_degree_vertexWedge_inr]
      simp [canonicalDivisor, oneChip]

/-- The doubled glue point is literally the canonical complement of the
factor-canonical sum. -/
theorem canonical_sub_wedgeCanonicalSum
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    canonicalDivisor (vertexWedge G H x y) - wedgeCanonicalSum G H x y =
      wedgeGlueDouble G H x y := by
  rw [canonical_divisor_vertexWedge]
  abel

@[simp] theorem deg_wedgeCanonicalSum
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    deg (wedgeCanonicalSum G H x y) =
      2 * genus G + 2 * genus H - 4 := by
  simp [wedgeCanonicalSum, degree_of_canonical_divisor]
  ring
@[simp] theorem deg_wedgeGlueDouble
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    deg (wedgeGlueDouble G H x y) = 2 := by
  unfold wedgeGlueDouble
  simp only [map_zsmul, deg_one_chip, smul_eq_mul]
  norm_num

/-- Riemann--Roch compares the factor-canonical sum with the doubled glue
point on a connected wedge. -/
theorem rank_wedgeCanonicalSum_sub_rank_wedgeGlueDouble
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graphConnected G) (hH : graphConnected H) :
    rank (vertexWedge G H x y) (wedgeCanonicalSum G H x y) -
        rank (vertexWedge G H x y) (wedgeGlueDouble G H x y) =
      genus G + genus H - 3 := by
  have hRR := riemann_roch_for_graphs
    (graph_connected_vertexWedge G H x y hG hH) (wedgeCanonicalSum G H x y)
  rw [canonical_sub_wedgeCanonicalSum, deg_wedgeCanonicalSum,
    genus_vertexWedge] at hRR
  linarith
/-- On a connected wedge of total genus four, the sum of the two factor
canonical divisors has rank at least one. -/
theorem rank_wedgeCanonicalSum_ge_one_of_genus_sum_four
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graphConnected G) (hH : graphConnected H)
    (hGenus : genus G + genus H = 4) :
    rank (vertexWedge G H x y) (wedgeCanonicalSum G H x y) ≥ 1 := by
  have hCompare :=
    rank_wedgeCanonicalSum_sub_rank_wedgeGlueDouble G H x y hG hH
  have hGlue : rank (vertexWedge G H x y) (wedgeGlueDouble G H x y) ≥ 0 := by
    apply (rank_geq_iff _ _ 0).mp
    apply (rank_nonneg_iff_winnable _ _).mpr
    apply winnable_of_effective
    intro z
    unfold wedgeGlueDouble
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = Sum.inl x
    · subst z
      simp [oneChip]
    · simp [oneChip, hz]
  rw [hGenus] at hCompare
  omega

end Utilities
