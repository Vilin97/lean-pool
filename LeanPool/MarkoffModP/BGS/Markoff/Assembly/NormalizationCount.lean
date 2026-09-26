/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ElementaryCounts
public import LeanPool.MarkoffModP.BGS.Markoff.Core.Normalization

/-!
# Finite counts in normalized Markoff coordinates

This module transports the canonical two-point bound for a fixed pair of original Markoff
coordinates across `normalizationEquiv`.  It then sums that bound over a finite set of possible
first and second normalized coordinates.
-/

@[expose] public section

namespace BGS.Markoff

universe u

section NormalizedThirdCoordinateFiber

variable {F : Type u} [Field F] [Fintype F] [Invertible (3 : F)]

/-- The original coordinate whose normalized value is `a`. -/
def originalCoordinateOfNormalized (a : F) : F :=
  (⅟ (3 : F)) * a

/-- Normalized Markoff points with prescribed first and second coordinates, obtained by mapping
the canonical original-coordinate fiber through the normalization equivalence. -/
noncomputable def normalizedMarkoffPointsWithFirstTwoCoordinates (a b : F) :
    Finset (NormalizedPoint F) :=
  (markoffPointsWithFirstTwoCoordinates
      (originalCoordinateOfNormalized a) (originalCoordinateOfNormalized b)).map
    (normalizationEquiv F).toEmbedding

@[simp]
theorem mem_normalizedMarkoffPointsWithFirstTwoCoordinates_iff
    {a b : F} {x : NormalizedPoint F} :
    x ∈ normalizedMarkoffPointsWithFirstTwoCoordinates a b ↔
      IsNormalizedMarkoff x ∧ x.u1 = a ∧ x.u2 = b := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨hyMarkoff, hy1, hy2⟩ :=
      mem_markoffPointsWithFirstTwoCoordinates_iff.mp hy
    refine ⟨(isNormalizedMarkoff_toNormalized_iff y).2 hyMarkoff, ?_, ?_⟩
    · simp [normalizationEquiv, toNormalized, originalCoordinateOfNormalized, hy1,
        ← mul_assoc]
    · simp [normalizationEquiv, toNormalized, originalCoordinateOfNormalized, hy2,
        ← mul_assoc]
  · rintro ⟨hxMarkoff, hx1, hx2⟩
    let y : Point F := fromNormalized x
    have hnormalize : toNormalized y = x := by
      change (normalizationEquiv F) ((normalizationEquiv F).symm x) = x
      exact (normalizationEquiv F).apply_symm_apply x
    have hyMarkoff : IsMarkoff y := by
      apply (isNormalizedMarkoff_toNormalized_iff y).mp
      rw [hnormalize]
      exact hxMarkoff
    have hy1 : y.x1 = originalCoordinateOfNormalized a := by
      simp [y, fromNormalized, originalCoordinateOfNormalized, hx1]
    have hy2 : y.x2 = originalCoordinateOfNormalized b := by
      simp [y, fromNormalized, originalCoordinateOfNormalized, hx2]
    apply Finset.mem_map.mpr
    refine ⟨y, mem_markoffPointsWithFirstTwoCoordinates_iff.mpr ⟨hyMarkoff, hy1, hy2⟩, ?_⟩
    exact hnormalize

/-- Mapping through normalization preserves the exact cardinality of a fixed-coordinate fiber. -/
theorem normalizedMarkoffPointsWithFirstTwoCoordinates_card_eq_original (a b : F) :
    (normalizedMarkoffPointsWithFirstTwoCoordinates a b).card =
      (markoffPointsWithFirstTwoCoordinates
        (originalCoordinateOfNormalized a) (originalCoordinateOfNormalized b)).card := by
  classical
  simp [normalizedMarkoffPointsWithFirstTwoCoordinates]

/-- Fixing the first two normalized coordinates leaves at most two normalized Markoff points. -/
theorem normalizedMarkoffPointsWithFirstTwoCoordinates_card_le_two (a b : F) :
    (normalizedMarkoffPointsWithFirstTwoCoordinates a b).card ≤ 2 := by
  rw [normalizedMarkoffPointsWithFirstTwoCoordinates_card_eq_original]
  exact markoffPointsWithFirstTwoCoordinates_card_le_two _ _

/-- Normalized Markoff points whose first two coordinates both lie in `S`. -/
noncomputable def normalizedMarkoffPointsWithFirstTwoCoordinatesIn (S : Finset F) :
    Finset (NormalizedPoint F) := by
  classical
  exact (S.product S).biUnion fun ab =>
    normalizedMarkoffPointsWithFirstTwoCoordinates ab.1 ab.2

@[simp]
theorem mem_normalizedMarkoffPointsWithFirstTwoCoordinatesIn_iff
    {S : Finset F} {x : NormalizedPoint F} :
    x ∈ normalizedMarkoffPointsWithFirstTwoCoordinatesIn S ↔
      IsNormalizedMarkoff x ∧ x.u1 ∈ S ∧ x.u2 ∈ S := by
  classical
  rw [normalizedMarkoffPointsWithFirstTwoCoordinatesIn, Finset.mem_biUnion]
  constructor
  · rintro ⟨ab, hab, hx⟩
    have hab' : ab.1 ∈ S ∧ ab.2 ∈ S := Finset.mem_product.mp hab
    rw [mem_normalizedMarkoffPointsWithFirstTwoCoordinates_iff] at hx
    exact ⟨hx.1, hx.2.1 ▸ hab'.1, hx.2.2 ▸ hab'.2⟩
  · rintro ⟨hxMarkoff, hx1, hx2⟩
    refine ⟨(x.u1, x.u2), Finset.mem_product.mpr ⟨hx1, hx2⟩, ?_⟩
    exact mem_normalizedMarkoffPointsWithFirstTwoCoordinates_iff.mpr
      ⟨hxMarkoff, rfl, rfl⟩

/-- If both of the first two normalized coordinates lie in a finite set `S`, there are at most
`2 * |S|^2` normalized Markoff points. -/
theorem normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le
    (S : Finset F) :
    (normalizedMarkoffPointsWithFirstTwoCoordinatesIn S).card ≤ 2 * S.card ^ 2 := by
  classical
  calc
    (normalizedMarkoffPointsWithFirstTwoCoordinatesIn S).card ≤
        (S.product S).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro ab hab
      exact normalizedMarkoffPointsWithFirstTwoCoordinates_card_le_two ab.1 ab.2
    _ = 2 * S.card ^ 2 := by
      simp [Finset.card_product, pow_two, Nat.mul_comm]

end NormalizedThirdCoordinateFiber

end BGS.Markoff
