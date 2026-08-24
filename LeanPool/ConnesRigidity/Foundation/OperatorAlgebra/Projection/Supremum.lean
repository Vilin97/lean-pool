/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 35621-35749.
Modifications: extracted projection-supremum transport from the spatial
witness, replaced the local multiplication relation by inherited operator
order, and separated the abstract specification from its concrete proof.
Paper: §3. See the upstream PORT_MAP.md.
-/
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import LeanPool.ConnesRigidity.Core

/-!
# Projection-supremum transport

This module relates the inherited operator order on projections in concrete
star subalgebras to multiplication, then transports projection suprema across
star-algebra equivalences. It supplies the normality witness consumed by the
spatial factor equivalence in Zhou §3.
-/

namespace Connes

noncomputable section

universe u v

/-- The inherited operator order agrees with the algebraic order on star-subalgebra projections. -/
theorem StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p := by
  have hp' : IsStarProjection (p : E →L[ℂ] E) := hp.map A.subtype
  have hq' : IsStarProjection (q : E →L[ℂ] E) := hq.map A.subtype
  rw [← Subtype.coe_le_coe, hp'.le_iff_mul_eq_left hq']
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- A star-algebra equivalence preserves operator order between subalgebra projections. -/
@[simp]
theorem StarAlgEquiv.map_le_map_iff_of_isStarProjection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    e p ≤ e q ↔ p ≤ q := by
  rw [StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection (hp.map e) (hq.map e),
    StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection hp hq]
  exact ⟨fun h ↦ by
      simpa only [map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h,
    fun h ↦ by simpa only [map_mul] using congrArg e h⟩

namespace IsProjectionSupremum

/-- A star-algebra equivalence carries a projection supremum to its image. -/
theorem map_starAlgEquiv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) {S : Set A} {p : A}
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine IsProjectionSupremum.intro (hp.isStarProjection.map e) ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hp.upper hq).1.map e,
      (StarAlgEquiv.map_le_map_iff_of_isStarProjection
        e (hp.upper hq).1 hp.isStarProjection).2
        (hp.upper hq).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, q ≤ e.symm r := by
      intro q hq
      have h := hupper (e q) ⟨q, hq, rfl⟩
      simpa only [StarAlgEquiv.symm_apply_apply] using
        (StarAlgEquiv.map_le_map_iff_of_isStarProjection
          e.symm ((hp.upper hq).1.map e) hr).2 h
    have h := hp.least hr' hbound
    have h' : e.symm (e p) ≤ e.symm r := by
      simpa only [StarAlgEquiv.symm_apply_apply] using h
    exact (StarAlgEquiv.map_le_map_iff_of_isStarProjection
      e.symm (hp.isStarProjection.map e) hr).1 h'

end IsProjectionSupremum

/-- Every star-algebra equivalence between operator subalgebras preserves projection suprema. -/
theorem StarAlgEquiv.isNormal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e :=
  IsNormalStarAlgEquiv.intro
    (fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e)
    (fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e.symm)

end
end Connes
