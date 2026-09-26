/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionExistence
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedge
public import LeanPool.BrillNoetherGraphs.Demazure.Submodular

/-!
# Demazure composition across a vertex wedge

For opposite marked vertices, the vertex-wedge rank formula composes
transmission witnesses by the Demazure product.  At gluing shift `ell`, the
left and right transmission rows are respectively `(a, ell + 1)` and
`(ell, b)`.  Thus the min-plus formula for `AspPerm.star` is exactly the
factor-rank profile required by `TransmissionWedge`.

The final existence theorem is conditional only on the finite-length
factorization of an ASP permutation into two factors within prescribed genus
budgets.  The imported Demazure library supplies the min-plus product formula
but currently no theorem producing this bounded finite factorization.
-/

@[expose] public section

namespace Utilities

universe u v

/-- Opposite-side wedge addition composes two transmission witnesses by the
Demazure product. -/
theorem satisfiesTransmission_wedgeAddDivisor_star
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (alpha beta : AspPerm)
    (hD : SatisfiesTransmission G u x alpha D)
    (hE : SatisfiesTransmission H y v beta E) :
    SatisfiesTransmission (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) (alpha ⋆ beta)
      (wedgeAddDivisor G H x y D E) := by
  apply satisfiesTransmission_wedgeAddDivisor_of_profile
  constructor
  · rw [hD.1, hE.1, AspPerm.chi_star]
    ring
  · intro a b ell
    dsimp [WedgeTransmissionRowProfile]
    have hLeft := hD.2 a (ell + 1)
    unfold TransmissionInequality at hLeft
    have hRightRaw := hE.2 ell b
    unfold TransmissionInequality at hRightRaw
    have hRight :
        rank H (E - b • oneChip v + ell • oneChip y) ≥
          beta.s (ell + 1) b - 1 := by
      simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hRightRaw
    have hStar : (alpha ⋆ beta).s (a + 1) b ≤
        alpha.s (a + 1) (ell + 1) + beta.s (ell + 1) b :=
      (AspPerm.star_sf_isleast alpha beta (a + 1) b).2 ⟨ell + 1, rfl⟩
    omega

/-- The existential form of opposite-side Demazure composition. -/
theorem transmissionExists_vertexWedge_opposite_star
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (u : G.V) (v : H.V) (alpha beta : AspPerm)
    (hG : TransmissionExists G u x alpha)
    (hH : TransmissionExists H y v beta) :
    TransmissionExists (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) (alpha ⋆ beta) := by
  rcases hG with ⟨D, hD⟩
  rcases hH with ⟨E, hE⟩
  exact ⟨wedgeAddDivisor G H x y D E,
    satisfiesTransmission_wedgeAddDivisor_star G H x y D E u v alpha beta hD hE⟩

/-- A finite Demazure factorization whose two factors fit the two genus
budgets.  This is the precise combinatorial input needed to glue full
`TransmissionExistence` statements. -/
def BoundedDemazureFactorization (tau : AspPerm) (gG gH : ℤ) : Prop :=
  ∃ alpha beta : AspPerm,
    tau = alpha ⋆ beta ∧
      FiniteTransmissionPerm alpha ∧
      ((invSet alpha).ncard : ℤ) ≤ gG ∧
      FiniteTransmissionPerm beta ∧
      ((invSet beta).ncard : ℤ) ≤ gH

/-- The bounded finite Demazure-factorization assertion needed for vertex
wedge gluing.  It is isolated here because `Demazure.Submodular` proves the
min-plus product formula but does not provide this length-budgeted
factorization theorem. -/
def HasBoundedDemazureFactorizations (gG gH : ℤ) : Prop :=
  ∀ tau : AspPerm, FiniteTransmissionPerm tau ->
    ((invSet tau).ncard : ℤ) ≤ gG + gH ->
    BoundedDemazureFactorization tau gG gH

/-- Conditional gluing for the full finite-length transmission-existence
predicate.  The sole additional input is the named bounded Demazure
factorization property above. -/
theorem transmissionExistence_vertexWedge_opposite_of_factorizations
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (u : G.V) (v : H.V)
    (hG : TransmissionExistence G u x)
    (hH : TransmissionExistence H y v)
    (hFactor : HasBoundedDemazureFactorizations (genus G : ℤ) (genus H : ℤ)) :
    TransmissionExistence (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) := by
  intro tau hFinite hLength
  rw [genus_vertexWedge] at hLength
  rcases hFactor tau hFinite hLength with
    ⟨alpha, beta, hTau, hAlphaFinite, hAlphaLength, hBetaFinite, hBetaLength⟩
  rw [hTau]
  exact transmissionExists_vertexWedge_opposite_star G H x y u v alpha beta
    (hG alpha hAlphaFinite hAlphaLength) (hH beta hBetaFinite hBetaLength)

end Utilities
