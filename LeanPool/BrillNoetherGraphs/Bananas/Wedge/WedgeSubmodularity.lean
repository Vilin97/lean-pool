/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBridge
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBasics
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.MarkedRankProfile
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeDemazure

/-!
# Exact transmission and submodularity across a vertex wedge

`Utilities.satisfiesTransmission_wedgeAddDivisor_star` supplies the lower
rank inequalities for the Demazure product of two transmission witnesses.
For the paper's gluing formula, one needs the stronger statement that the raw
transmission permutation of the wedge divisor is *equal* to that Demazure
product.  This file proves that equality from the attained vertex-wedge rank
formula.

The divisor algebra which turns an exact rank surface into a raw transmission
permutation is kept abstract.  This avoids unfolding `oneChip` on a concrete
wedge vertex type.
-/

@[expose] public section

namespace Bananas

open Utilities

section Generic

/-- An ASP permutation whose slipface is the exact marked rank surface is the
raw transmission permutation. -/
theorem isTransmissionPermutation_of_rank_eq_slipface
    {M : TwiceMarked} (D : CFDiv M.graph) (tau : AspPerm)
    (hRank : ∀ a b : ℤ,
      rank M.graph
          (D + a • oneChip M.u - b • oneChip M.v) =
        tau.s (a + 1) b - 1) :
    IsTransmissionPermutation M D tau.func := by
  refine ⟨tau.bijective, ?_⟩
  intro a b
  rw [← tau.Delta_eq a b]
  unfold rankDelta SlipFace.Δ
  have hU :
      D + a • oneChip M.u - b • oneChip M.v - oneChip M.u =
        D + (a - 1) • oneChip M.u - b • oneChip M.v := by
    rw [sub_smul]
    abel
  have hV :
      D + a • oneChip M.u - b • oneChip M.v - oneChip M.v =
        D + a • oneChip M.u - (b + 1) • oneChip M.v := by
    rw [add_smul, one_smul]
    abel
  have hUV :
      D + (a - 1) • oneChip M.u - b • oneChip M.v - oneChip M.v =
        D + (a - 1) • oneChip M.u - (b + 1) • oneChip M.v := by
    rw [add_smul, one_smul]
    abel
  rw [hU, hV, hUV, hRank a b, hRank (a - 1) b,
    hRank a (b + 1), hRank (a - 1) (b + 1)]
  ring_nf

end Generic

/-- Exact min-plus rank formula for an opposite-side wedge twist when the two
factor rank surfaces are represented by ASP permutations. -/
theorem rank_wedgeAddDivisor_transmissionTwist_eq_star
    (G H : CFGraph) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (alpha beta : AspPerm)
    (hD : ∀ a b : ℤ,
      rank G (D + a • oneChip u - b • oneChip x) =
        alpha.s (a + 1) b - 1)
    (hE : ∀ a b : ℤ,
      rank H (E + a • oneChip y - b • oneChip v) =
        beta.s (a + 1) b - 1)
    (a b : ℤ) :
    rank (vertexWedge G H x y)
        (wedgeAddDivisor G H x y D E +
          a • oneChip (G := vertexWedge G H x y) (Sum.inl u) -
          b • oneChip (G := vertexWedge G H x y)
            (wedgeRightVertex G H x y v)) =
      (alpha ⋆ beta).s (a + 1) b - 1 := by
  rw [wedgeAddDivisor_transmissionTwist G H x y D E u v a b]
  apply (vertexWedge_rank_eq_iff_profile_inequalities_and_attained
    G H x y (D + a • oneChip u) (E - b • oneChip v)
      ((alpha ⋆ beta).s (a + 1) b - 1)).2
  have hLeast := AspPerm.star_sf_isleast alpha beta (a + 1) b
  constructor
  · intro ell
    have hLeft := hD a (ell + 1)
    have hRight := hE ell b
    have hProduct :
        (alpha ⋆ beta).s (a + 1) b ≤
          alpha.s (a + 1) (ell + 1) + beta.s (ell + 1) b :=
      hLeast.2 ⟨ell + 1, rfl⟩
    have hLeftDiv :
        D + a • oneChip u - (ell + 1) • oneChip x =
          (D + a • oneChip u) - (ell + 1) • oneChip x := by
      rfl
    have hRightDiv :
        E + ell • oneChip y - b • oneChip v =
          (E - b • oneChip v) + ell • oneChip y := by
      abel
    rw [← hLeftDiv, ← hRightDiv, hLeft, hRight]
    omega
  · rcases hLeast.1 with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    have hLeft := hD a m
    have hRight :
        rank H (E + (m - 1) • oneChip y - b • oneChip v) =
          beta.s m b - 1 := by
      simpa using hE (m - 1) b
    have hLeft' :
        rank G ((D + a • oneChip u) - ((m - 1) + 1) • oneChip x) =
          alpha.s (a + 1) m - 1 := by
      simpa using hLeft
    have hRightDiv :
        E + (m - 1) • oneChip y - b • oneChip v =
          (E - b • oneChip v) + (m - 1) • oneChip y := by
      abel
    rw [hLeft', ← hRightDiv, hRight]
    have hm' :
        alpha.s (a + 1) m + beta.s m b =
          (alpha ⋆ beta).s (a + 1) b := hm
    omega

/-- The exact raw transmission permutation of a wedge-additive divisor is the
Demazure product of the exact raw transmission permutations of its factors. -/
theorem exists_isTransmissionPermutation_wedgeAddDivisor_star
    (G H : CFGraph) (x : G.V) (y : H.V)
    (hG : _root_.graphConnected G) (hH : _root_.graphConnected H)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (tau sigma : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u x) D tau)
    (hSigma : IsTransmissionPermutation (mark H y v) E sigma) :
    ∃ alpha beta : AspPerm,
      alpha.func = tau ∧ beta.func = sigma ∧
        IsTransmissionPermutation
          (mark (vertexWedge G H x y) (Sum.inl u)
            (wedgeRightVertex G H x y v))
          (wedgeAddDivisor G H x y D E) (alpha ⋆ beta).func := by
  obtain ⟨alpha, hAlpha, hRankD⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation
      u x hG D tau hTau
  obtain ⟨beta, hBeta, hRankE⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation
      y v hH E sigma hSigma
  refine ⟨alpha, beta, hAlpha, hBeta, ?_⟩
  apply isTransmissionPermutation_of_rank_eq_slipface
  exact rank_wedgeAddDivisor_transmissionTwist_eq_star
    G H x y D E u v alpha beta hRankD hRankE

/-- All-divisor submodularity is closed under opposite-side vertex gluing. -/
theorem allSubmodular_vertexWedge_opposite
    (G H : CFGraph) (x : G.V) (y : H.V)
    (hGconn : _root_.graphConnected G)
    (hHconn : _root_.graphConnected H)
    (u : G.V) (v : H.V)
    (hG : AllSubmodular (mark G u x))
    (hH : AllSubmodular (mark H y v)) :
    AllSubmodular
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) := by
  rw [allSubmodular_iff_rankDelta_nonneg]
  intro Q
  let D := wedgeRestrictLeftDivisor G H x y Q
  let E := wedgeRestrictRightDivisor G H x y Q
  obtain ⟨tau, hTau⟩ := exists_transmissionPermutation_of_submodular
    (mark G u x) D hGconn (hG D)
  obtain ⟨sigma, hSigma⟩ := exists_transmissionPermutation_of_submodular
    (mark H y v) E hHconn (hH E)
  obtain ⟨alpha, beta, _hAlpha, _hBeta, hWedge⟩ :=
    exists_isTransmissionPermutation_wedgeAddDivisor_star
      G H x y hGconn hHconn D E u v tau sigma hTau hSigma
  have hQ : wedgeAddDivisor G H x y D E = Q := by
    exact wedgeAddDivisor_restrict G H x y Q
  rw [hQ] at hWedge
  have hDelta :
      (if (alpha ⋆ beta).func 0 = 0 then (1 : ℤ) else 0) =
        rankDelta
          (mark (vertexWedge G H x y) (Sum.inl u)
            (wedgeRightVertex G H x y v)) Q := by
    simpa only [zero_zsmul, add_zero, sub_zero] using hWedge.2 0 0
  rw [← hDelta]
  split <;> norm_num

end Bananas
