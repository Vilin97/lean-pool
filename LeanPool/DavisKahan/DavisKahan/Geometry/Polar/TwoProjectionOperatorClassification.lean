/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.OrthogonalSummandCoordinates

/-!
# Operator-level classification of two projections

The spectral-multiplicity formulation in Davis--Kahan Theorem 3.1 requires a
separate direct-integral classification theorem.  The operator-theoretic core
is more elementary: the four Halmos summands and the pair of restricted
projections on the generic part form a complete invariant.  This file proves
that core statement by joining an equivalence on the trivial part with an
equivalence on the generic part.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {H' : Type v} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [CompleteSpace H']

/-- Restriction of an ambient bounded operator to an invariant closed
subspace. -/
noncomputable def restrictToInvariant
    (T : H →L[ℂ] H) (K : Submodule ℂ H)
    (hK : ∀ x ∈ K, T x ∈ K) : K →L[ℂ] K :=
  (T ∘L K.subtypeL).codRestrict K (fun x => hK (x : H) x.property)

omit [CompleteSpace H] in
/-- The restriction to an invariant subspace acts as the original operator. -/
@[simp] theorem restrictToInvariant_apply
    (T : H →L[ℂ] H) (K : Submodule ℂ H)
    (hK : ∀ x ∈ K, T x ∈ K) (x : K) :
    restrictToInvariant T K hK x = ⟨T x, hK x x.property⟩ := rfl

omit [CompleteSpace H] in
/-- The left projection preserves the trivial Halmos part. -/
theorem projection_left_invariant_halmosTrivialPart
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ∀ x ∈ halmosTrivialPart U V, U.starProjection x ∈ halmosTrivialPart U V :=
  fun _ hx => projection_mem_halmosTrivialPart_left U V hx

omit [CompleteSpace H] in
/-- The right projection preserves the trivial Halmos part. -/
theorem projection_right_invariant_halmosTrivialPart
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ∀ x ∈ halmosTrivialPart U V, V.starProjection x ∈ halmosTrivialPart U V :=
  fun _ hx => projection_mem_halmosTrivialPart_right U V hx

/-- Restricted left projection on the elementary Halmos summand. -/
noncomputable def trivialLeftProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U V →L[ℂ] halmosTrivialPart U V :=
  restrictToInvariant (U.starProjection) (halmosTrivialPart U V)
    (projection_left_invariant_halmosTrivialPart U V)

/-- Restricted right projection on the elementary Halmos summand. -/
noncomputable def trivialRightProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U V →L[ℂ] halmosTrivialPart U V :=
  restrictToInvariant (V.starProjection) (halmosTrivialPart U V)
    (projection_right_invariant_halmosTrivialPart U V)

/-- Restricted left projection on the generic Halmos summand. -/
noncomputable def genericLeftProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariant (U.starProjection) (halmosGenericPart U V)
    (projection_left_reduces_halmosGenericPart U V).1

/-- Restricted right projection on the generic Halmos summand. -/
noncomputable def genericRightProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariant (V.starProjection) (halmosGenericPart U V)
    (projection_right_reduces_halmosGenericPart U V).1

/-- Complete operator-level invariant data for a pair of projections.

The elementary equivalence records the four discrete Halmos multiplicities.
The generic equivalence records the unitary-equivalence class of the generic
pair of projections. -/
structure TwoProjectionOperatorEquivalence
    (U V : Submodule ℂ H) (U' V' : Submodule ℂ H')
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection] where
  /-- An isometric identification of the trivial parts of the two Halmos decompositions. -/
  trivialEquiv : halmosTrivialPart U V ≃ₗᵢ[ℂ] halmosTrivialPart U' V'
  /-- An isometric identification of the generic parts of the two Halmos decompositions. -/
  genericEquiv : halmosGenericPart U V ≃ₗᵢ[ℂ] halmosGenericPart U' V'
  trivial_left :
    (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V') ∘L
        trivialLeftProjection U V =
      trivialLeftProjection U' V' ∘L
        (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V')
  trivial_right :
    (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V') ∘L
        trivialRightProjection U V =
      trivialRightProjection U' V' ∘L
        (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V')
  generic_left :
    (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V') ∘L
        genericLeftProjection U V =
      genericLeftProjection U' V' ∘L
        (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V')
  generic_right :
    (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V') ∘L
        genericRightProjection U V =
      genericRightProjection U' V' ∘L
        (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V')

namespace TwoProjectionOperatorEquivalence

variable {U V : Submodule ℂ H} {U' V' : Submodule ℂ H'}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection]

/-- Assemble the elementary and generic equivalences into an ambient unitary. -/
noncomputable def ambient
    (D : TwoProjectionOperatorEquivalence U V U' V') : H ≃ₗᵢ[ℂ] H' :=
  (halmosTrivialPart U V).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 D.trivialEquiv D.genericEquiv)
      |>.trans (halmosTrivialPart U' V').orthogonalDecomposition.symm

private theorem ambient_apply_trivial
    (D : TwoProjectionOperatorEquivalence U V U' V')
    (x : halmosTrivialPart U V) :
    D.ambient (x : H) = (D.trivialEquiv x : H') := by
  simp [ambient, LinearIsometryEquiv.trans_apply,
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.2]

private theorem ambient_apply_generic
    (D : TwoProjectionOperatorEquivalence U V U' V')
    (x : halmosGenericPart U V) :
    D.ambient (x : H) = (D.genericEquiv x : H') := by
  simp [ambient, LinearIsometryEquiv.trans_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr x.2]

/-- The assembled ambient unitary intertwines the left projections. -/
theorem ambient_intertwines_left
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    (D.ambient : H →L[ℂ] H') ∘L U.starProjection =
      U'.starProjection ∘L (D.ambient : H →L[ℂ] H') := by
  apply ContinuousLinearMap.ext
  intro x
  let T := halmosTrivialPart U V
  let G := halmosGenericPart U V
  have hsplit : x = T.starProjection x + G.starProjection x := by
    simp [T, G]
  rw [hsplit]
  simp only [map_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe]
  have ht : T.starProjection x ∈ T := T.starProjection_apply_mem x
  have hg : G.starProjection x ∈ G := G.starProjection_apply_mem x
  have hPt : U.starProjection (T.starProjection x) ∈ T :=
    projection_left_invariant_halmosTrivialPart U V _ ht
  have hPg : U.starProjection (G.starProjection x) ∈ G :=
    (projection_left_reduces_halmosGenericPart U V).1 _ hg
  have e1 : D.ambient (U.starProjection (T.starProjection x))
      = (D.trivialEquiv ⟨U.starProjection (T.starProjection x), hPt⟩ : H') :=
    D.ambient_apply_trivial ⟨_, hPt⟩
  have e2 : D.ambient (U.starProjection (G.starProjection x))
      = (D.genericEquiv ⟨U.starProjection (G.starProjection x), hPg⟩ : H') :=
    D.ambient_apply_generic ⟨_, hPg⟩
  have e3 : D.ambient (T.starProjection x)
      = (D.trivialEquiv ⟨T.starProjection x, ht⟩ : H') :=
    D.ambient_apply_trivial ⟨_, ht⟩
  have e4 : D.ambient (G.starProjection x)
      = (D.genericEquiv ⟨G.starProjection x, hg⟩ : H') :=
    D.ambient_apply_generic ⟨_, hg⟩
  rw [e1, e2, e3, e4]
  have htEq := DFunLike.congr_fun D.trivial_left ⟨T.starProjection x, ht⟩
  have hgEq := DFunLike.congr_fun D.generic_left ⟨G.starProjection x, hg⟩
  apply congrArg Subtype.val at htEq
  apply congrArg Subtype.val at hgEq
  simpa [trivialLeftProjection, genericLeftProjection,
    restrictToInvariant_apply] using congrArg₂ (· + ·) htEq hgEq

/-- The assembled ambient unitary intertwines the right projections. -/
theorem ambient_intertwines_right
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    (D.ambient : H →L[ℂ] H') ∘L V.starProjection =
      V'.starProjection ∘L (D.ambient : H →L[ℂ] H') := by
  apply ContinuousLinearMap.ext
  intro x
  let T := halmosTrivialPart U V
  let G := halmosGenericPart U V
  have hsplit : x = T.starProjection x + G.starProjection x := by
    simp [T, G]
  rw [hsplit]
  simp only [map_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe]
  have ht : T.starProjection x ∈ T := T.starProjection_apply_mem x
  have hg : G.starProjection x ∈ G := G.starProjection_apply_mem x
  have hPt : V.starProjection (T.starProjection x) ∈ T :=
    projection_right_invariant_halmosTrivialPart U V _ ht
  have hPg : V.starProjection (G.starProjection x) ∈ G :=
    (projection_right_reduces_halmosGenericPart U V).1 _ hg
  have e1 : D.ambient (V.starProjection (T.starProjection x))
      = (D.trivialEquiv ⟨V.starProjection (T.starProjection x), hPt⟩ : H') :=
    D.ambient_apply_trivial ⟨_, hPt⟩
  have e2 : D.ambient (V.starProjection (G.starProjection x))
      = (D.genericEquiv ⟨V.starProjection (G.starProjection x), hPg⟩ : H') :=
    D.ambient_apply_generic ⟨_, hPg⟩
  have e3 : D.ambient (T.starProjection x)
      = (D.trivialEquiv ⟨T.starProjection x, ht⟩ : H') :=
    D.ambient_apply_trivial ⟨_, ht⟩
  have e4 : D.ambient (G.starProjection x)
      = (D.genericEquiv ⟨G.starProjection x, hg⟩ : H') :=
    D.ambient_apply_generic ⟨_, hg⟩
  rw [e1, e2, e3, e4]
  have htEq := DFunLike.congr_fun D.trivial_right ⟨T.starProjection x, ht⟩
  have hgEq := DFunLike.congr_fun D.generic_right ⟨G.starProjection x, hg⟩
  apply congrArg Subtype.val at htEq
  apply congrArg Subtype.val at hgEq
  simpa [trivialRightProjection, genericRightProjection,
    restrictToInvariant_apply] using congrArg₂ (· + ·) htEq hgEq

/-- The assembled unitary maps the first subspace onto the first subspace. -/
theorem map_left
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    U.map D.ambient.toLinearMap = U' := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hpx : U.starProjection x = x := U.starProjection_eq_self_iff.mpr hx
    have h := DFunLike.congr_fun D.ambient_intertwines_left x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hpx] at h
    exact U'.starProjection_eq_self_iff.mp h.symm
  · intro y hy
    refine ⟨D.ambient.symm y, ?_, D.ambient.apply_symm_apply y⟩
    have hpy : U'.starProjection y = y := U'.starProjection_eq_self_iff.mpr hy
    have h := DFunLike.congr_fun D.ambient_intertwines_left (D.ambient.symm y)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply, hpy] at h
    apply U.starProjection_eq_self_iff.mp
    apply D.ambient.injective
    rw [D.ambient.apply_symm_apply]
    exact h

/-- The assembled unitary maps the second subspace onto the second subspace. -/
theorem map_right
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    V.map D.ambient.toLinearMap = V' := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hpx : V.starProjection x = x := V.starProjection_eq_self_iff.mpr hx
    have h := DFunLike.congr_fun D.ambient_intertwines_right x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hpx] at h
    exact V'.starProjection_eq_self_iff.mp h.symm
  · intro y hy
    refine ⟨D.ambient.symm y, ?_, D.ambient.apply_symm_apply y⟩
    have hpy : V'.starProjection y = y := V'.starProjection_eq_self_iff.mpr hy
    have h := DFunLike.congr_fun D.ambient_intertwines_right (D.ambient.symm y)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply, hpy] at h
    apply V.starProjection_eq_self_iff.mp
    apply D.ambient.injective
    rw [D.ambient.apply_symm_apply]
    exact h

end TwoProjectionOperatorEquivalence

/-- Modern operator-level form of Davis--Kahan Theorem 3.1.

The paper's spectral-multiplicity statement follows once a separate theorem
identifies unitary equivalence of the generic self-adjoint cosine operators
with equality of their spectral multiplicity functions. -/
theorem twoProjection_operator_classification
    {U V : Submodule ℂ H} {U' V' : Submodule ℂ H'}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection]
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    ∃ W : H ≃ₗᵢ[ℂ] H',
      U.map W.toLinearMap = U' ∧ V.map W.toLinearMap = V' := by
  exact ⟨D.ambient, D.map_left, D.map_right⟩

end

end DavisKahan
end TauCeti
