/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedge

/-!
# Transmission with both marks on one side of a vertex wedge

`TransmissionWedge` treats the case in which the two transmission marks lie
on opposite factors.  This file gives the complementary exact criteria: both
marks may lie on the left factor, with the right factor attached at an
unmarked cut vertex, or symmetrically both may lie on the right factor.

The first result removes the nonnegative-threshold hypothesis from the exact
vertex-wedge rank formula.  This is useful for arbitrary ASP transmission,
whose required rank `tau.s (a + 1) b - 1` can equal `-1`.
-/

namespace Utilities

universe u v

/-- The exact vertex-wedge rank-profile criterion at every integer threshold.
For negative thresholds both sides hold automatically, since graph rank is at
least `-1` and the sum of two factor ranks plus one is also at least `-1`. -/
theorem vertexWedge_rank_ge_iff_profile_inequalities_all_int
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k ↔
      ∀ ell : ℤ,
        rank G (D - (ell + 1) • one_chip x) +
            rank H (E + ell • one_chip y) + 1 ≥ k := by
  by_cases hk : 0 ≤ k
  · exact vertexWedge_rank_ge_iff_profile_inequalities G H x y D E k hk
  · have hk' : k ≤ -1 := by omega
    constructor
    · intro _ ell
      have hLeft := rank_geq_neg_one G
        (D - (ell + 1) • one_chip x)
      have hRight := rank_geq_neg_one H (E + ell • one_chip y)
      omega
    · intro _
      have hRank := rank_geq_neg_one (vertexWedge G H x y)
        (wedgeAddDivisor G H x y D E)
      omega

/-! ## Both marks on the left factor -/

/-- Twisting at two left-factor vertices commutes literally with wedge
addition.  This remains true when either marked vertex is the gluing vertex. -/
theorem wedgeAddDivisor_transmissionTwist_sameLeft
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V) (a b : ℤ) :
    wedgeAddDivisor G H x y D E +
        a • one_chip (G := vertexWedge G H x y) (Sum.inl p) -
        b • one_chip (G := vertexWedge G H x y) (Sum.inl q) =
      wedgeAddDivisor G H x y
        (D + a • one_chip p - b • one_chip q) E := by
  have hP : a • one_chip (G := vertexWedge G H x y) (Sum.inl p) =
      wedgeAddDivisor G H x y (a • one_chip p) 0 := by
    rw [← wedgeAddDivisor_one_chip_left G H x y p,
      wedgeAddDivisor_zsmul]
    simp
  have hQ : b • one_chip (G := vertexWedge G H x y) (Sum.inl q) =
      wedgeAddDivisor G H x y (b • one_chip q) 0 := by
    rw [← wedgeAddDivisor_one_chip_left G H x y q,
      wedgeAddDivisor_zsmul]
    simp
  rw [hP, hQ, wedgeAddDivisor_add, wedgeAddDivisor_sub]
  simp

/-- The factor-rank inequality for one transmission row when both marks lie
on the left factor.  `ell` records chip transfer across the gluing vertex. -/
def WedgeSameLeftTransmissionRowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V)
    (tau : AspPerm) (a b ell : ℤ) : Prop :=
  rank G
        (D + a • one_chip p - b • one_chip q -
          (ell + 1) • one_chip x) +
      rank H (E + ell • one_chip y) + 1 ≥
    tau.s (a + 1) b - 1

/-- Exact row criterion when both transmission marks lie on the left factor. -/
theorem transmissionInequality_wedgeAddDivisor_sameLeft_iff_rowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V)
    (tau : AspPerm) (a b : ℤ) :
    TransmissionInequality (vertexWedge G H x y) (Sum.inl p) (Sum.inl q)
        tau (wedgeAddDivisor G H x y D E) a b ↔
      ∀ ell : ℤ,
        WedgeSameLeftTransmissionRowProfile
          G H x y D E p q tau a b ell := by
  unfold TransmissionInequality
  rw [wedgeAddDivisor_transmissionTwist_sameLeft G H x y D E p q a b]
  rw [vertexWedge_rank_ge_iff_profile_inequalities_all_int]
  rfl

/-- The full arbitrary-ASP profile with both marks on the left factor. -/
def WedgeSameLeftTransmissionProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V) (tau : AspPerm) : Prop :=
  deg D + deg E = (genus G : ℤ) + (genus H : ℤ) + tau.χ ∧
    ∀ a b ell : ℤ,
      WedgeSameLeftTransmissionRowProfile
        G H x y D E p q tau a b ell

/-- Exact same-left-side wedge criterion for a fixed wedge-additive divisor. -/
theorem satisfiesTransmission_wedgeAddDivisor_sameLeft_iff_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V) (tau : AspPerm) :
    SatisfiesTransmission (vertexWedge G H x y) (Sum.inl p) (Sum.inl q)
        tau (wedgeAddDivisor G H x y D E) ↔
      WedgeSameLeftTransmissionProfile G H x y D E p q tau := by
  constructor
  · intro h
    constructor
    · rw [← deg_wedgeAddDivisor, h.1, genus_vertexWedge]
    · intro a b ell
      exact (transmissionInequality_wedgeAddDivisor_sameLeft_iff_rowProfile
        G H x y D E p q tau a b).mp (h.2 a b) ell
  · rintro ⟨hDegree, hRows⟩
    constructor
    · rw [deg_wedgeAddDivisor, genus_vertexWedge]
      exact hDegree
    · intro a b
      exact
        (transmissionInequality_wedgeAddDivisor_sameLeft_iff_rowProfile
          G H x y D E p q tau a b).mpr (fun ell => hRows a b ell)

/-- A same-left factor profile constructs a transmission witness on the
wedge. -/
theorem transmissionExists_vertexWedge_sameLeft_of_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (p q : G.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (h : WedgeSameLeftTransmissionProfile G H x y D E p q tau) :
    TransmissionExists (vertexWedge G H x y) (Sum.inl p) (Sum.inl q) tau :=
  ⟨wedgeAddDivisor G H x y D E,
    (satisfiesTransmission_wedgeAddDivisor_sameLeft_iff_profile
      G H x y D E p q tau).mpr h⟩

/-! ## Both marks on the right factor -/

/-- Twisting at two right-factor vertices commutes literally with wedge
addition, including the common-vertex convention of `wedgeRightVertex`. -/
theorem wedgeAddDivisor_transmissionTwist_sameRight
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V) (a b : ℤ) :
    wedgeAddDivisor G H x y D E +
        a • one_chip (G := vertexWedge G H x y)
          (wedgeRightVertex G H x y p) -
        b • one_chip (G := vertexWedge G H x y)
          (wedgeRightVertex G H x y q) =
      wedgeAddDivisor G H x y D
        (E + a • one_chip p - b • one_chip q) := by
  have hP : a • one_chip (G := vertexWedge G H x y)
      (wedgeRightVertex G H x y p) =
      wedgeAddDivisor G H x y 0 (a • one_chip p) := by
    rw [← wedgeAddDivisor_one_chip_right G H x y p,
      wedgeAddDivisor_zsmul]
    simp
  have hQ : b • one_chip (G := vertexWedge G H x y)
      (wedgeRightVertex G H x y q) =
      wedgeAddDivisor G H x y 0 (b • one_chip q) := by
    rw [← wedgeAddDivisor_one_chip_right G H x y q,
      wedgeAddDivisor_zsmul]
    simp
  rw [hP, hQ, wedgeAddDivisor_add, wedgeAddDivisor_sub]
  simp

/-- The factor-rank inequality for one transmission row when both marks lie
on the right factor. -/
def WedgeSameRightTransmissionRowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V)
    (tau : AspPerm) (a b ell : ℤ) : Prop :=
  rank G (D - (ell + 1) • one_chip x) +
      rank H
        (E + a • one_chip p - b • one_chip q + ell • one_chip y) + 1 ≥
    tau.s (a + 1) b - 1

/-- Exact row criterion when both transmission marks lie on the right factor. -/
theorem transmissionInequality_wedgeAddDivisor_sameRight_iff_rowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V)
    (tau : AspPerm) (a b : ℤ) :
    TransmissionInequality (vertexWedge G H x y)
        (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q)
        tau (wedgeAddDivisor G H x y D E) a b ↔
      ∀ ell : ℤ,
        WedgeSameRightTransmissionRowProfile
          G H x y D E p q tau a b ell := by
  unfold TransmissionInequality
  rw [wedgeAddDivisor_transmissionTwist_sameRight G H x y D E p q a b]
  rw [vertexWedge_rank_ge_iff_profile_inequalities_all_int]
  rfl

/-- The full arbitrary-ASP profile with both marks on the right factor. -/
def WedgeSameRightTransmissionProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V) (tau : AspPerm) : Prop :=
  deg D + deg E = (genus G : ℤ) + (genus H : ℤ) + tau.χ ∧
    ∀ a b ell : ℤ,
      WedgeSameRightTransmissionRowProfile
        G H x y D E p q tau a b ell

/-- Exact same-right-side wedge criterion for a fixed wedge-additive divisor. -/
theorem satisfiesTransmission_wedgeAddDivisor_sameRight_iff_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V) (tau : AspPerm) :
    SatisfiesTransmission (vertexWedge G H x y)
        (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q)
        tau (wedgeAddDivisor G H x y D E) ↔
      WedgeSameRightTransmissionProfile G H x y D E p q tau := by
  constructor
  · intro h
    constructor
    · rw [← deg_wedgeAddDivisor, h.1, genus_vertexWedge]
    · intro a b ell
      exact (transmissionInequality_wedgeAddDivisor_sameRight_iff_rowProfile
        G H x y D E p q tau a b).mp (h.2 a b) ell
  · rintro ⟨hDegree, hRows⟩
    constructor
    · rw [deg_wedgeAddDivisor, genus_vertexWedge]
      exact hDegree
    · intro a b
      exact
        (transmissionInequality_wedgeAddDivisor_sameRight_iff_rowProfile
          G H x y D E p q tau a b).mpr (fun ell => hRows a b ell)

/-- A same-right factor profile constructs a transmission witness on the
wedge. -/
theorem transmissionExists_vertexWedge_sameRight_of_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (p q : H.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (h : WedgeSameRightTransmissionProfile G H x y D E p q tau) :
    TransmissionExists (vertexWedge G H x y)
      (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q) tau :=
  ⟨wedgeAddDivisor G H x y D E,
    (satisfiesTransmission_wedgeAddDivisor_sameRight_iff_profile
      G H x y D E p q tau).mpr h⟩

end Utilities
