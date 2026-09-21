/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Action
import LeanPool.MarkoffModP.BGS.Markoff.Core.Normalization

/-!
# Normalization on the punctured Markoff surface

Scaling every original Markoff coordinate by three gives an equivalence with the normalized
punctured surface when three is invertible.  The assembly-specific small-order sets transported
through this equivalence are defined in `BGS.Markoff.Assembly.PuncturedSmallOrderCount`.
-/

namespace BGS.Markoff

universe u

/-- Scaling by three identifies the action carrier of original punctured Markoff points with the
subtype of normalized punctured Markoff points. -/
def puncturedNormalizationEquiv (R : Type u) [CommRing R] [Invertible (3 : R)] :
    PuncturedMarkoffSurface R ≃ ↑(normalizedPuncturedSurface R) :=
  (puncturedSurfaceEquiv R).trans <|
    (normalizationEquiv R).subtypeEquiv fun x => by
      change (IsMarkoff x ∧ x ≠ origin) ↔
        (IsNormalizedMarkoff (toNormalized x) ∧ toNormalized x ≠ normalizedOrigin)
      rw [isNormalizedMarkoff_toNormalized_iff]
      constructor
      · rintro ⟨hx, hx0⟩
        refine ⟨hx, ?_⟩
        intro hnormalize
        apply hx0
        apply (normalizationEquiv R).injective
        simpa [normalizationEquiv] using hnormalize
      · rintro ⟨hx, hx0⟩
        refine ⟨hx, ?_⟩
        intro horigin
        apply hx0
        simp [horigin]

@[simp]
theorem puncturedNormalizationEquiv_coe
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) :
    ((puncturedNormalizationEquiv R x : ↑(normalizedPuncturedSurface R)) :
      NormalizedPoint R) = toNormalized x.1.1 :=
  rfl

/-- Pull a finite set of normalized punctured points back to original punctured coordinates. -/
noncomputable def originalPuncturedFinsetOfNormalized
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (S : Finset ↑(normalizedPuncturedSurface R)) : Finset (PuncturedMarkoffSurface R) :=
  S.map (puncturedNormalizationEquiv R).symm.toEmbedding

@[simp]
theorem mem_originalPuncturedFinsetOfNormalized_iff
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    {S : Finset ↑(normalizedPuncturedSurface R)} {x : PuncturedMarkoffSurface R} :
    x ∈ originalPuncturedFinsetOfNormalized S ↔ puncturedNormalizationEquiv R x ∈ S := by
  classical
  simp [originalPuncturedFinsetOfNormalized]

/-- Pullback through normalization preserves the exact cardinality of every finite set. -/
theorem originalPuncturedFinsetOfNormalized_card
    {R : Type u} [CommRing R] [Invertible (3 : R)]
    (S : Finset ↑(normalizedPuncturedSurface R)) :
    (originalPuncturedFinsetOfNormalized S).card = S.card := by
  simp [originalPuncturedFinsetOfNormalized]

end BGS.Markoff
