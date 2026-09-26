/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence

/-!
# Genus-one rigid wedges

This module isolates the cycle-ready consequence of the exact wedge
winnability convolution.  The rigidity condition is deliberately explicit:
it is *not* asserted for every genus-one graph.
-/

@[expose] public section

namespace Utilities

universe u v

/-- A pointed genus-one graph for which no other vertex is linearly
equivalent to the marked point in degree zero. -/
structure PointedGenusOneRigid (H : CFGraph.{v}) (y : H.V) : Prop where
  connected : graphConnected H
  genus_one : genus H = 1
  exists_ne : ∃ p : H.V, p ≠ y
  nontrivial : ∀ p : H.V, p ≠ y →
    ¬ linearEquiv H (oneChip y - oneChip p) 0

/-- A winnable divisor of degree zero is linearly equivalent to zero. -/
theorem linear_equiv_zero_of_winnable_deg_zero
    (K : CFGraph.{u}) (A : CFDiv K)
    (hWin : winnable K A) (hDeg : deg A = 0) : linearEquiv K A 0 := by
  obtain ⟨B, hB, hAB⟩ := hWin
  have hDegB : deg B = 0 := by
    rw [← linear_equiv_preserves_deg K A B hAB, hDeg]
  have hZero : B = 0 := eff_degree_zero B hB hDegB
  simpa [hZero] using hAB

/-- The left-supported divisor is definitionally the wedge sum with zero on
the right factor. -/
@[simp] theorem wedgeLiftLeftDivisor_eq_wedgeAdd
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (D : CFDiv G) :
    wedgeLiftLeftDivisor G H x y D = wedgeAddDivisor G H x y D 0 := rfl

/-- Winnability forces nonnegative degree. -/
theorem deg_nonneg_of_winnable
    (K : CFGraph.{u}) (A : CFDiv K) (hWin : winnable K A) :
    0 ≤ deg A := by
  obtain ⟨B, hBEffective, hAB⟩ := hWin
  have hDegree := deg_of_eff_nonneg B hBEffective
  rw [← linear_equiv_preserves_deg K A B hAB] at hDegree
  exact hDegree

/-- A nonnegative integral pile of chips at one vertex is effective. -/
theorem effective_marked_pile_of_nonneg
    (K : CFGraph.{u}) (q : K.V) (t : ℤ) (ht : 0 ≤ t) :
    effective (t • oneChip q) := by
  intro z
  by_cases hz : z = q <;> simp [oneChip, hz, ht]

/-- Adding chips at one marked vertex preserves winnability. -/
theorem winnable_chipShift_mono
    (K : CFGraph.{u}) (A : CFDiv K) (q : K.V) {s t : ℤ}
    (hst : s ≤ t) (hWin : winnable K (chipShift K A q s)) :
    winnable K (chipShift K A q t) := by
  have hAdded : effective ((t - s) • oneChip q) :=
    effective_marked_pile_of_nonneg K q (t - s) (by omega)
  have h := winnable_add_effective_divisor K
    (chipShift K A q s) ((t - s) • oneChip q) hWin hAdded
  convert h using 1
  funext z
  simp only [chipShift, zsmul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq,
    Int.cast_sub, Pi.sub_apply]
  ring

/-- Subtracting a left-factor chip from a left-supported wedge divisor stays
entirely on the left factor. -/
theorem wedgeLiftLeft_sub_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (a : G.V) :
    wedgeLiftLeftDivisor G H x y D -
        oneChip (G := vertexWedge G H x y) (Sum.inl a) =
      wedgeAddDivisor G H x y (D - oneChip a) 0 := by
  funext z
  cases z with
  | inl q =>
      change wedgeAddDivisor G H x y D 0 (Sum.inl q) -
          oneChip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inl q) =
        wedgeAddDivisor G H x y (D - oneChip a) 0 (Sum.inl q)
      rw [wedgeAddDivisor_left, wedgeAddDivisor_left]
      change (D q + if q = x then 0 else 0) -
          (if (Sum.inl q : Sum G.V {z : H.V // z ≠ y}) = Sum.inl a then 1 else 0) =
        (D q - if q = a then 1 else 0) + if q = x then 0 else 0
      simp only [Sum.inl.injEq]
      ring
  | inr q =>
      change wedgeAddDivisor G H x y D 0 (Sum.inr q) -
          oneChip (G := vertexWedge G H x y) (Sum.inl a) (Sum.inr q) =
        wedgeAddDivisor G H x y (D - oneChip a) 0 (Sum.inr q)
      rw [wedgeAddDivisor_right, wedgeAddDivisor_right]
      simp [oneChip]

/-- Subtracting a non-marked right-factor chip from a left-supported wedge
divisor puts exactly its negative on the right factor. -/
theorem wedgeLiftLeft_sub_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (p : {z : H.V // z ≠ y}) :
    wedgeLiftLeftDivisor G H x y D -
        oneChip (G := vertexWedge G H x y) (Sum.inr p) =
      wedgeAddDivisor G H x y D (-oneChip p.1) := by
  funext z
  cases z with
  | inl q =>
      change wedgeAddDivisor G H x y D 0 (Sum.inl q) -
          oneChip (G := vertexWedge G H x y) (Sum.inr p) (Sum.inl q) =
        wedgeAddDivisor G H x y D (-oneChip p.1) (Sum.inl q)
      rw [wedgeAddDivisor_left, wedgeAddDivisor_left]
      change (D q + if q = x then 0 else 0) -
          (if (Sum.inl q : Sum G.V {z : H.V // z ≠ y}) = Sum.inr p then 1 else 0) =
        D q + if q = x then -(if y = p.1 then 1 else 0) else 0
      simp [Ne.symm p.2]
  | inr q =>
      change wedgeAddDivisor G H x y D 0 (Sum.inr q) -
          oneChip (G := vertexWedge G H x y) (Sum.inr p) (Sum.inr q) =
        wedgeAddDivisor G H x y D (-oneChip p.1) (Sum.inr q)
      rw [wedgeAddDivisor_right, wedgeAddDivisor_right]
      change 0 -
          (if (Sum.inr q : Sum G.V {z : H.V // z ≠ y}) = Sum.inr p then 1 else 0) =
        -(if q.1 = p.1 then 1 else 0)
      simp only [Sum.inr.injEq]
      simp [Subtype.ext_iff]

/-- Exact rank-one criterion for attaching a pointed rigid genus-one block.
For a genuine subdivided cycle, the remaining input is precisely the familiar
fact that distinct vertices have distinct degree-one divisor classes. -/
theorem rank_wedgeLiftLeft_ge_one_iff
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hH : PointedGenusOneRigid H y) (D : CFDiv G) :
    rank (vertexWedge G H x y) (wedgeLiftLeftDivisor G H x y D) ≥ 1 ↔
      rank G D ≥ 1 ∧ winnable G (D - (2 : ℤ) • oneChip x) := by
  constructor
  · intro hRank
    have hTests :=
      (rank_ge_one_iff_winnable_sub_one_chip
        (vertexWedge G H x y) (wedgeLiftLeftDivisor G H x y D)).mp hRank
    constructor
    · rw [rank_ge_one_iff_winnable_sub_one_chip]
      intro a
      have hWa := hTests (Sum.inl a)
      rw [wedgeLiftLeft_sub_left] at hWa
      obtain ⟨t, hLeft, hRight⟩ :=
        (winnable_vertexWedge_iff_exists_chipShift
          G H x y (D - oneChip a) 0).mp hWa
      have ht : t ≤ 0 := by
        have hDegree := deg_nonneg_of_winnable H
          (chipShift H 0 y (-t)) hRight
        rw [chipShift, deg.map_add, map_zsmul, deg_one_chip] at hDegree
        simp only [map_zero, zero_add] at hDegree
        simp only [smul_eq_mul, mul_one] at hDegree
        omega
      have hMonotone := winnable_chipShift_mono G
        (D - oneChip a) x ht hLeft
      simpa [chipShift] using hMonotone
    · obtain ⟨p, hp⟩ := hH.exists_ne
      let p' : {z : H.V // z ≠ y} := ⟨p, hp⟩
      have hWp := hTests (Sum.inr p')
      rw [wedgeLiftLeft_sub_right] at hWp
      obtain ⟨t, hLeft, hRight⟩ :=
        (winnable_vertexWedge_iff_exists_chipShift
          G H x y D (-oneChip p)).mp hWp
      have htOne : t ≤ -1 := by
        have hDegree := deg_nonneg_of_winnable H
          (chipShift H (-oneChip p) y (-t)) hRight
        rw [chipShift, deg.map_add, map_zsmul, map_neg, deg_one_chip] at hDegree
        rw [deg_one_chip y] at hDegree
        simp only [smul_eq_mul, mul_one] at hDegree
        omega
      have htTwo : t ≤ -2 := by
        by_contra hnot
        have htEq : t = -1 := by omega
        subst t
        have hZero := linear_equiv_zero_of_winnable_deg_zero H
          (chipShift H (-oneChip p) y (-(-1))) hRight (by
            simp [chipShift])
        apply hH.nontrivial p hp
        have hRewrite :
            chipShift H (-oneChip p) y (-(-1)) =
              oneChip y - oneChip p := by
          unfold chipShift
          abel
        rw [hRewrite] at hZero
        exact hZero
      have hMonotone := winnable_chipShift_mono G D x htTwo hLeft
      convert hMonotone using 1
      unfold chipShift
      abel
  · rintro ⟨hRankG, hTwo⟩
    rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro z
    cases z with
    | inl a =>
        rw [wedgeLiftLeft_sub_left]
        apply (winnable_vertexWedge_iff_exists_chipShift
          G H x y (D - oneChip a) 0).mpr
        refine ⟨0, ?_, ?_⟩
        · simpa [chipShift] using
            ((rank_ge_one_iff_winnable_sub_one_chip G D).mp hRankG a)
        · have hZero : winnable H (0 : CFDiv H) :=
            winnable_of_effective H (0 : CFDiv H) (by intro z; simp)
          simpa only [chipShift, neg_zero, zero_zsmul, add_zero] using hZero
    | inr p =>
        rw [wedgeLiftLeft_sub_right]
        apply (winnable_vertexWedge_iff_exists_chipShift
          G H x y D (-oneChip p.1)).mpr
        refine ⟨-2, ?_, ?_⟩
        · convert hTwo using 1
          unfold chipShift
          abel
        · apply winnable_of_deg_ge_genus hH.connected
          rw [chipShift, deg.map_add, map_zsmul, map_neg, deg_one_chip,
            hH.genus_one]
          norm_num

end Utilities
