/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeRankFormula

/-!
# Transmission across a vertex wedge

A wedge divisor has a marked rank profile on each factor.  This module turns
the vertex-wedge rank formula into an exact, arbitrary-ASP transmission
criterion.  It is deliberately stated for every lattice point and every
integer chip-shift: no Grassmannian or rank-one specialization is used here.

For a transmission row `(a,b)`, its marked twist on the wedge splits as
`(D + a[u]) ⊕ (E - b[v])`.  The rank condition on that row is therefore
equivalent to the tropical-dot-product inequality for the two factor
profiles, indexed by the extra gluing shift `ell`.
-/

namespace Utilities

universe u v
/-- Wedge addition is additive in its two divisor arguments. -/
theorem wedgeAddDivisor_add
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D A : CFDiv G) (E B : CFDiv H) :
    wedgeAddDivisor G H x y D E + wedgeAddDivisor G H x y A B =
      wedgeAddDivisor G H x y (D + A) (E + B) := by
  funext z
  cases z with
  | inl p =>
      simp only [Pi.add_apply, wedgeAddDivisor_left]
      split_ifs <;> ring
  | inr q => rfl
/-- Wedge addition commutes with integral scalar multiplication. -/
theorem wedgeAddDivisor_zsmul
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (n : ℤ) :
    n • wedgeAddDivisor G H x y D E =
      wedgeAddDivisor G H x y (n • D) (n • E) := by
  funext z
  cases z with
  | inl p =>
      simp only [Pi.smul_apply, smul_eq_mul, wedgeAddDivisor_left]
      split_ifs <;> ring
  | inr q =>
      simp only [Pi.smul_apply, smul_eq_mul, wedgeAddDivisor_right]

/-- A left-factor chip is its literal wedge-additive lift. -/
theorem wedgeAddDivisor_one_chip_left
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (u : G.V) :
    wedgeAddDivisor G H x y (one_chip u) 0 =
      one_chip (G := vertexWedge G H x y) (Sum.inl u) := by
  funext z
  cases z with
  | inl p =>
      rw [wedgeAddDivisor_left]
      change one_chip u p + (if p = x then (0 : CFDiv H) y else 0) =
        if (Sum.inl p : Sum G.V {q : H.V // q ≠ y}) = Sum.inl u then 1 else 0
      simp only [Sum.inl.injEq]
      simp [one_chip]
  | inr q =>
      rw [wedgeAddDivisor_right]
      simp [one_chip]

/-- A right-factor chip is its wedge-additive lift, including at the common
vertex when the chip is at `y`. -/
theorem wedgeAddDivisor_one_chip_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (v : H.V) :
    wedgeAddDivisor G H x y 0 (one_chip v) =
      one_chip (G := vertexWedge G H x y) (wedgeRightVertex G H x y v) := by
  classical
  funext z
  cases z with
  | inl p =>
      rw [wedgeAddDivisor_left]
      change (0 : CFDiv G) p + (if p = x then one_chip v y else 0) =
        if (Sum.inl p : Sum G.V {q : H.V // q ≠ y}) =
          wedgeRightVertex G H x y v then 1 else 0
      by_cases hv : v = y
      · subst v
        simp [wedgeRightVertex, one_chip]
      · have hyv : y ≠ v := Ne.symm hv
        simp [wedgeRightVertex, one_chip, hv, hyv]
  | inr q =>
      rw [wedgeAddDivisor_right]
      change one_chip v q.1 = if (Sum.inr q : Sum G.V {q : H.V // q ≠ y}) =
        wedgeRightVertex G H x y v then 1 else 0
      by_cases hv : v = y
      · subst v
        simp [wedgeRightVertex, one_chip, q.2]
      · rw [wedgeRightVertex_unmarked G H x y v hv]
        simp only [Sum.inr.injEq]
        simp [one_chip, Subtype.ext_iff]

/-- The transmission twist of a wedge-additive divisor splits literally into
the corresponding left and right factor twists. -/
theorem wedgeAddDivisor_transmissionTwist
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V) (a b : ℤ) :
    wedgeAddDivisor G H x y D E +
        a • one_chip (G := vertexWedge G H x y) (Sum.inl u) -
        b • one_chip (G := vertexWedge G H x y) (wedgeRightVertex G H x y v) =
      wedgeAddDivisor G H x y (D + a • one_chip u) (E - b • one_chip v) := by
  have hLeft : a • one_chip (G := vertexWedge G H x y) (Sum.inl u) =
      wedgeAddDivisor G H x y (a • one_chip u) 0 := by
    rw [← wedgeAddDivisor_one_chip_left G H x y u,
      wedgeAddDivisor_zsmul]
    simp
  have hRight : b • one_chip (G := vertexWedge G H x y)
      (wedgeRightVertex G H x y v) =
      wedgeAddDivisor G H x y 0 (b • one_chip v) := by
    rw [← wedgeAddDivisor_one_chip_right G H x y v,
      wedgeAddDivisor_zsmul]
    simp
  rw [hLeft, hRight, wedgeAddDivisor_add, wedgeAddDivisor_sub]
  simp

/-- The profile inequality attached to a single transmission row of a wedge.
The `ell` coordinate is the chip transfer across the identified vertex. -/
def WedgeTransmissionRowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (tau : AspPerm) (a b ell : ℤ) : Prop :=
  rank G (D + a • one_chip u - (ell + 1) • one_chip x) +
      rank H (E - b • one_chip v + ell • one_chip y) + 1 ≥
    tau.s (a + 1) b - 1

/-- A wedge-additive divisor has the required transmission ranks exactly when
every row satisfies all of its factor-profile inequalities. -/
theorem transmissionInequality_wedgeAddDivisor_iff_rowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (tau : AspPerm) (a b : ℤ) :
    TransmissionInequality (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau (wedgeAddDivisor G H x y D E) a b ↔
      ∀ ell : ℤ, WedgeTransmissionRowProfile G H x y D E u v tau a b ell := by
  unfold TransmissionInequality
  rw [wedgeAddDivisor_transmissionTwist G H x y D E u v a b]
  have hTarget : -1 ≤ tau.s (a + 1) b - 1 := by
    have hNonneg := tau.s.nonneg (a + 1) b
    omega
  by_cases hNonneg : 0 ≤ tau.s (a + 1) b - 1
  · rw [vertexWedge_rank_ge_iff_profile_inequalities G H x y
      (D + a • one_chip u) (E - b • one_chip v)
      (tau.s (a + 1) b - 1) hNonneg]
    rfl
  · have hMinusOne : tau.s (a + 1) b - 1 = -1 := by omega
    rw [hMinusOne]
    constructor
    · intro _ ell
      dsimp [WedgeTransmissionRowProfile]
      have hLeft := rank_geq_neg_one G
        (D + a • one_chip u - (ell + 1) • one_chip x)
      have hRight := rank_geq_neg_one H
        (E - b • one_chip v + ell • one_chip y)
      omega
    · intro _
      exact rank_geq_neg_one _ _

/-- The usable forward direction of the row-profile criterion. -/
theorem transmissionInequality_wedgeAddDivisor_of_rowProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (tau : AspPerm) (a b : ℤ)
    (h : ∀ ell : ℤ, WedgeTransmissionRowProfile G H x y D E u v tau a b ell) :
    TransmissionInequality (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau (wedgeAddDivisor G H x y D E) a b :=
  (transmissionInequality_wedgeAddDivisor_iff_rowProfile
    G H x y D E u v tau a b).mpr h

/-- Every wedge transmission row supplies all of its factor-profile bounds. -/
theorem wedgeTransmissionRowProfile_of_transmissionInequality
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (tau : AspPerm) (a b ell : ℤ)
    (h : TransmissionInequality (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau (wedgeAddDivisor G H x y D E) a b) :
    WedgeTransmissionRowProfile G H x y D E u v tau a b ell :=
  (transmissionInequality_wedgeAddDivisor_iff_rowProfile
    G H x y D E u v tau a b).mp h ell

/-- The full factor-profile condition for a wedge divisor and an arbitrary
ASP permutation. -/
def WedgeTransmissionProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V) (tau : AspPerm) : Prop :=
  deg D + deg E = (genus G : ℤ) + (genus H : ℤ) + tau.χ ∧
    ∀ a b ell : ℤ, WedgeTransmissionRowProfile G H x y D E u v tau a b ell

/-- Exact wedge criterion for a fixed wedge-additive divisor.  In particular,
the global transmission predicate reduces to factor rank profiles with no
loss at non-special or boundary rows. -/
theorem satisfiesTransmission_wedgeAddDivisor_iff_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V) (tau : AspPerm) :
    SatisfiesTransmission (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau (wedgeAddDivisor G H x y D E) ↔
      WedgeTransmissionProfile G H x y D E u v tau := by
  constructor
  · intro h
    constructor
    · rw [← deg_wedgeAddDivisor, h.1, genus_vertexWedge]
    · intro a b ell
      exact (transmissionInequality_wedgeAddDivisor_iff_rowProfile
        G H x y D E u v tau a b).mp (h.2 a b) ell
  · rintro ⟨hDegree, hRows⟩
    constructor
    · rw [deg_wedgeAddDivisor, genus_vertexWedge]
      exact hDegree
    · intro a b
      exact (transmissionInequality_wedgeAddDivisor_iff_rowProfile
        G H x y D E u v tau a b).mpr (fun ell => hRows a b ell)

/-- A convenient one-way constructor when the factor degree and all factor
row profiles have been established independently. -/
theorem satisfiesTransmission_wedgeAddDivisor_of_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V) (tau : AspPerm)
    (h : WedgeTransmissionProfile G H x y D E u v tau) :
    SatisfiesTransmission (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau (wedgeAddDivisor G H x y D E) :=
  (satisfiesTransmission_wedgeAddDivisor_iff_profile
    G H x y D E u v tau).mpr h

/-- Existence on the wedge follows from one pair of factor divisors satisfying
the explicit wedge transmission profile. -/
theorem transmissionExists_vertexWedge_of_profile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (u : G.V) (v : H.V) (tau : AspPerm)
    (D : CFDiv G) (E : CFDiv H)
    (h : WedgeTransmissionProfile G H x y D E u v tau) :
    TransmissionExists (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) tau :=
  ⟨wedgeAddDivisor G H x y D E,
    satisfiesTransmission_wedgeAddDivisor_of_profile G H x y D E u v tau h⟩

end Utilities
