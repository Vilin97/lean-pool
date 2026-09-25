/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeSameSide

/-!
# Marked rank profiles and attained wedge convolution

A pointed rank profile records the ranks of every integral twist at one
marked vertex.  The exact vertex-wedge threshold formula implies more than a
family of lower bounds: the tropical convolution of two realized profiles is
attained at an integer phase and equals the wedge rank.  This formulation is
suited to recursive attachments and avoids any `min` or `sInf` interface.
-/

@[expose] public section

namespace Utilities

universe u v

/-- A function which records every integral one-point twist rank of `D`. -/
def PointedRankProfile (G : CFGraph.{u}) (D : CFDiv G) (q : G.V)
    (F : ℤ → ℤ) : Prop :=
  ∀ t : ℤ, rank G (D + t • oneChip q) = F t

/-- Subtractive form of a realized pointed rank profile. -/
theorem rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
    (G : CFGraph.{u}) (D : CFDiv G) (q : G.V) (F : ℤ → ℤ)
    (hF : PointedRankProfile G D q F) (t : ℤ) :
    rank G (D - t • oneChip q) = F (-t) := by
  have hDivisor : D - t • oneChip q = D + (-t) • oneChip q := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hDivisor, hF (-t)]

/-- The raw factor-rank convolution is attained, and its attained value is
exactly the rank of the wedge divisor. -/
theorem vertexWedge_rank_eq_iff_profile_inequalities_and_attained
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (r : ℤ) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) = r ↔
      (∀ ell : ℤ,
        rank G (D - (ell + 1) • oneChip x) +
            rank H (E + ell • oneChip y) + 1 ≥ r) ∧
      ∃ ell : ℤ,
        rank G (D - (ell + 1) • oneChip x) +
            rank H (E + ell • oneChip y) + 1 = r := by
  constructor
  · intro hRank
    have hLower : ∀ ell : ℤ,
        rank G (D - (ell + 1) • oneChip x) +
            rank H (E + ell • oneChip y) + 1 ≥ r :=
      (vertexWedge_rank_ge_iff_profile_inequalities_all_int
        G H x y D E r).mp (by omega)
    refine ⟨hLower, ?_⟩
    have hNotNext : ¬ rank (vertexWedge G H x y)
        (wedgeAddDivisor G H x y D E) ≥ r + 1 := by
      omega
    have hNotAll : ¬ ∀ ell : ℤ,
        rank G (D - (ell + 1) • oneChip x) +
            rank H (E + ell • oneChip y) + 1 ≥ r + 1 := by
      intro hAll
      exact hNotNext
        ((vertexWedge_rank_ge_iff_profile_inequalities_all_int
          G H x y D E (r + 1)).mpr hAll)
    push Not at hNotAll
    obtain ⟨ell, hUpper⟩ := hNotAll
    exact ⟨ell, by
      have hLowerEll := hLower ell
      omega⟩
  · rintro ⟨hLower, ell, hAttained⟩
    have hRankLower : rank (vertexWedge G H x y)
        (wedgeAddDivisor G H x y D E) ≥ r :=
      (vertexWedge_rank_ge_iff_profile_inequalities_all_int
        G H x y D E r).mpr hLower
    have hNotNext : ¬ rank (vertexWedge G H x y)
        (wedgeAddDivisor G H x y D E) ≥ r + 1 := by
      intro hNext
      have hAllNext :=
        (vertexWedge_rank_ge_iff_profile_inequalities_all_int
          G H x y D E (r + 1)).mp hNext
      have := hAllNext ell
      omega
    omega

/-- Exact attained tropical convolution for two realized pointed profiles. -/
theorem vertexWedge_rank_eq_iff_pointedRankProfile_convolution_attained
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (F Q : ℤ → ℤ)
    (hF : PointedRankProfile G D x F)
    (hQ : PointedRankProfile H E y Q) (r : ℤ) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) = r ↔
      (∀ ell : ℤ, F (-(ell + 1)) + Q ell + 1 ≥ r) ∧
      ∃ ell : ℤ, F (-(ell + 1)) + Q ell + 1 = r := by
  rw [vertexWedge_rank_eq_iff_profile_inequalities_and_attained]
  constructor
  · rintro ⟨hLower, ell, hAttained⟩
    constructor
    · intro t
      have h := hLower t
      rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
        G D x F hF (t + 1), hQ t] at h
      exact h
    · refine ⟨ell, ?_⟩
      rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
        G D x F hF (ell + 1), hQ ell] at hAttained
      exact hAttained
  · rintro ⟨hLower, ell, hAttained⟩
    constructor
    · intro t
      rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
        G D x F hF (t + 1), hQ t]
      exact hLower t
    · refine ⟨ell, ?_⟩
      rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
        G D x F hF (ell + 1), hQ ell]
      exact hAttained

/-! ## Pendant-profile rewrites for same-side transmission -/

/-- Same-left transmission data after replacing the unmarked right pendant
factor by its realized pointed rank profile. -/
def WedgeSameLeftTransmissionProfileWithRightProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (_y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V)
    (tau : AspPerm) (Q : ℤ → ℤ) : Prop :=
  deg D + deg E = (genus G : ℤ) + (genus H : ℤ) + tau.χ ∧
    ∀ a b ell : ℤ,
      rank G
          (D + a • oneChip p - b • oneChip q -
            (ell + 1) • oneChip x) +
        Q ell + 1 ≥ tau.s (a + 1) b - 1

/-- A realized right-factor profile rewrites the exact same-left transmission
profile without loss. -/
theorem wedgeSameLeftTransmissionProfile_iff_withRightProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : G.V)
    (tau : AspPerm) (Q : ℤ → ℤ)
    (hQ : PointedRankProfile H E y Q) :
    WedgeSameLeftTransmissionProfile G H x y D E p q tau ↔
      WedgeSameLeftTransmissionProfileWithRightProfile
        G H x y D E p q tau Q := by
  constructor <;> rintro ⟨hDegree, hRows⟩
  · refine ⟨hDegree, ?_⟩
    intro a b ell
    have h := hRows a b ell
    dsimp [WedgeSameLeftTransmissionRowProfile] at h
    rw [hQ ell] at h
    exact h
  · refine ⟨hDegree, ?_⟩
    intro a b ell
    dsimp [WedgeSameLeftTransmissionRowProfile]
    rw [hQ ell]
    exact hRows a b ell

/-- Same-right transmission data after replacing the unmarked left pendant
factor by its realized pointed rank profile. -/
def WedgeSameRightTransmissionProfileWithLeftProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (_x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V)
    (tau : AspPerm) (F : ℤ → ℤ) : Prop :=
  deg D + deg E = (genus G : ℤ) + (genus H : ℤ) + tau.χ ∧
    ∀ a b ell : ℤ,
      F (-(ell + 1)) +
        rank H
          (E + a • oneChip p - b • oneChip q + ell • oneChip y) + 1 ≥
      tau.s (a + 1) b - 1

/-- A realized left-factor profile rewrites the exact same-right transmission
profile without loss. -/
theorem wedgeSameRightTransmissionProfile_iff_withLeftProfile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (p q : H.V)
    (tau : AspPerm) (F : ℤ → ℤ)
    (hF : PointedRankProfile G D x F) :
    WedgeSameRightTransmissionProfile G H x y D E p q tau ↔
      WedgeSameRightTransmissionProfileWithLeftProfile
        G H x y D E p q tau F := by
  constructor <;> rintro ⟨hDegree, hRows⟩
  · refine ⟨hDegree, ?_⟩
    intro a b ell
    have h := hRows a b ell
    dsimp [WedgeSameRightTransmissionRowProfile] at h
    rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
      G D x F hF (ell + 1)] at h
    exact h
  · refine ⟨hDegree, ?_⟩
    intro a b ell
    dsimp [WedgeSameRightTransmissionRowProfile]
    rw [rank_sub_zsmul_one_chip_eq_of_pointedRankProfile
      G D x F hF (ell + 1)]
    exact hRows a b ell

end Utilities
