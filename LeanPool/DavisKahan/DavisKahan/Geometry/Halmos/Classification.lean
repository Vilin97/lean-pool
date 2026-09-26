/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.UnitaryEquivalence
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericRotationPredicates

/-!
# Operator-level Halmos two-projection classification

This module builds the constructive spine of Davis--Kahan 1970 Theorem 3.1: two
ordered pairs of subspaces `(U₁, V₁)` and `(U₂, V₂)` are unitarily equivalent as
pairs iff their four elementary Halmos summands are linearly isometric and their
generic cosine-square operators are unitarily equivalent.

The forward direction is proved here in full: a pair-equivalence
`e : H₁ ≃ₗᵢ[𝕜] H₂` restricts to isometric equivalences of the four elementary
summands and, on the generic remainder, intertwines the cosine-square operator.

The results now live in the stable geometry API; the frontier statement
`DavisKahan1970.twoProjection_operator_classification` is grounded by
`:=` on top of these lemmas so there is a single source of truth.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]

/-! ## Conjugation of orthogonal projections by an isometric equivalence -/

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- An isometric equivalence intertwines the orthogonal projections onto a
subspace and its image. -/
theorem isometryEquiv_intertwines_projection (e : H₁ ≃ₗᵢ[𝕜] H₂)
    {K : Submodule 𝕜 H₁} {K' : Submodule 𝕜 H₂} [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection]
    (hmap : K.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) = K') (x : H₁) :
    e (K.starProjection x) = K'.starProjection (e x) := by
  subst hmap
  have h := Submodule.starProjection_map_apply e K (e x)
  rw [e.symm_apply_apply] at h
  exact h.symm

/-! ## Restriction of an isometric equivalence to a matched subspace pair -/

/-- An isometric equivalence taking `K` onto `K'` restricts to an isometric
equivalence `K ≃ₗᵢ K'`. -/
noncomputable def summandEquiv (e : H₁ ≃ₗᵢ[𝕜] H₂) (K : Submodule 𝕜 H₁)
    {K' : Submodule 𝕜 H₂} (hmap : K.map e.toLinearMap = K') : K ≃ₗᵢ[𝕜] K' :=
  (e.submoduleMap K).trans (LinearIsometryEquiv.ofEq _ _ hmap)

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- The restricted equivalence acts by the ambient one; restricting to a
summand does not change where a vector goes.  This is what lets the four
elementary-summand equivalences be glued without tracking coercions. -/
@[simp] theorem coe_summandEquiv (e : H₁ ≃ₗᵢ[𝕜] H₂) (K : Submodule 𝕜 H₁)
    {K' : Submodule 𝕜 H₂} (hmap : K.map e.toLinearMap = K') (x : K) :
    (summandEquiv e K hmap x : H₂) = e (x : H₁) := rfl

/-! ## Forward direction: a pair-equivalence induces the operator invariant -/

variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- A pair-equivalence intertwines the Halmos cosine-square operators. -/
theorem intertwines_halmosCosineSq (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) (v : H₁) :
    e (halmosCosineSq U₁ V₁ v) = halmosCosineSq U₂ V₂ (e v) := by
  have hUc : U₁ᗮ.map e.toLinearMap = U₂ᗮ := by
    rw [Submodule.map_orthogonal_equiv, hU]
  have hVc : V₁ᗮ.map e.toLinearMap = V₂ᗮ := by
    rw [Submodule.map_orthogonal_equiv, hV]
  have hpU := isometryEquiv_intertwines_projection e hU
  have hpV := isometryEquiv_intertwines_projection e hV
  have hpUc := isometryEquiv_intertwines_projection e hUc
  have hpVc := isometryEquiv_intertwines_projection e hVc
  simp only [halmosCosineSq, add_apply,
    mul_apply_eq_comp, map_add]
  rw [hpU, hpV, hpU, hpUc, hpVc, hpUc]

/-! ### Where a pair-equivalence sends the Halmos summands

Each summand is built from `U`, `Uᗮ`, `V`, `Vᗮ` by intersections, joins and one
orthogonal complement, and an isometric equivalence commutes with all three.  So
a pair-equivalence carries every summand onto its counterpart.  These are broken
out because both directions of the classification need them: the forward
direction to restrict the equivalence, and brick (1) to restrict it to the
`U`-half of the generic part. -/

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the common part onto the common part. -/
theorem map_halmosCommonPart (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosCommonPart U₁ V₁).map e.toLinearMap = halmosCommonPart U₂ V₂ := by
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  rw [halmosCommonPart, Submodule.map_inf _ hinj, hU, hV]

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the source defect onto the source defect. -/
theorem map_halmosSourceDefect (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosSourceDefect U₁ V₁).map e.toLinearMap = halmosSourceDefect U₂ V₂ := by
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  have hVc : V₁ᗮ.map e.toLinearMap = V₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hV]
  rw [halmosSourceDefect, Submodule.map_inf _ hinj, hU, hVc]

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the target defect onto the target defect. -/
theorem map_halmosTargetDefect (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosTargetDefect U₁ V₁).map e.toLinearMap = halmosTargetDefect U₂ V₂ := by
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  have hUc : U₁ᗮ.map e.toLinearMap = U₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hU]
  rw [halmosTargetDefect, Submodule.map_inf _ hinj, hUc, hV]

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the exterior part onto the exterior part. -/
theorem map_halmosExteriorPart (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosExteriorPart U₁ V₁).map e.toLinearMap = halmosExteriorPart U₂ V₂ := by
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  have hUc : U₁ᗮ.map e.toLinearMap = U₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hU]
  have hVc : V₁ᗮ.map e.toLinearMap = V₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hV]
  rw [halmosExteriorPart, Submodule.map_inf _ hinj, hUc, hVc]

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the trivial part onto the trivial part. -/
theorem map_halmosTrivialPart (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosTrivialPart U₁ V₁).map e.toLinearMap = halmosTrivialPart U₂ V₂ := by
  simp only [halmosTrivialPart, Submodule.map_sup,
    map_halmosCommonPart U₁ V₁ U₂ V₂ e hU hV,
    map_halmosSourceDefect U₁ V₁ U₂ V₂ e hU hV,
    map_halmosTargetDefect U₁ V₁ U₂ V₂ e hU hV,
    map_halmosExteriorPart U₁ V₁ U₂ V₂ e hU hV]

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection] in
/-- A pair-equivalence carries the generic part onto the generic part. -/
theorem map_halmosGenericPart (e : H₁ ≃ₗᵢ[𝕜] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) :
    (halmosGenericPart U₁ V₁).map e.toLinearMap = halmosGenericPart U₂ V₂ := by
  rw [halmosGenericPart, Submodule.map_orthogonal_equiv,
    map_halmosTrivialPart U₁ V₁ U₂ V₂ e hU hV]

/-- **Forward direction of the operator-level Halmos classification.**  A
unitary equivalence of the ordered pairs induces isometric equivalences of the
four elementary Halmos summands together with a unitary intertwining of the
generic cosine-square operators. -/
theorem sameHalmosInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    (Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)) ∧
    (Nonempty (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)) ∧
    (Nonempty (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)) ∧
    (Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)) ∧
    BoundedOperatorsUnitaryEquivalent
      (genericHalmosCosineSq U₁ V₁) (genericHalmosCosineSq U₂ V₂) := by
  obtain ⟨e, hU, hV⟩ := h
  have hCommon := map_halmosCommonPart U₁ V₁ U₂ V₂ e hU hV
  have hSource := map_halmosSourceDefect U₁ V₁ U₂ V₂ e hU hV
  have hTarget := map_halmosTargetDefect U₁ V₁ U₂ V₂ e hU hV
  have hExterior := map_halmosExteriorPart U₁ V₁ U₂ V₂ e hU hV
  have hGen := map_halmosGenericPart U₁ V₁ U₂ V₂ e hU hV
  refine ⟨⟨summandEquiv e _ hCommon⟩, ⟨summandEquiv e _ hSource⟩,
    ⟨summandEquiv e _ hTarget⟩, ⟨summandEquiv e _ hExterior⟩, summandEquiv e _ hGen, ?_⟩
  intro x
  apply Subtype.ext
  simp only [coe_summandEquiv, genericHalmosCosineSq, DavisKahan.Sylvester.compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  calc e ((halmosGenericPart U₁ V₁).starProjection (halmosCosineSq U₁ V₁ (x : H₁)))
      = (halmosGenericPart U₂ V₂).starProjection (e (halmosCosineSq U₁ V₁ (x : H₁))) :=
        isometryEquiv_intertwines_projection e hGen _
    _ = (halmosGenericPart U₂ V₂).starProjection (halmosCosineSq U₂ V₂ (e (x : H₁))) := by
        rw [intertwines_halmosCosineSq U₁ V₁ U₂ V₂ e hU hV]

end DavisKahan
end TauCeti
