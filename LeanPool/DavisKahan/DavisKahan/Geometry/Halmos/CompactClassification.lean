/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericReconstruction
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence

/-! # Compact Classification -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Corollary 3.1: the compact case

When `P_U P_V P_U` is compact the angle operator is a compact positive operator
with trivial kernel, and such an operator is determined up to unitary
equivalence by its eigenvalue list with multiplicity.  So in the compact case
the invariant of Theorem 3.1 collapses to *numbers*: the four elementary Halmos
multiplicities, and the dimension of each eigenspace of `cos²Θ`.

The eigenvalue list is recorded here coordinate-free, as
`μ ↦ dim ker(cos²Θ - μ)`, rather than as a decreasing sequence.  The two carry
the same information — for a compact positive operator with trivial kernel the
nonzero eigenvalues have finite multiplicity and accumulate only at `0`, so the
dimension function is exactly the multiset of the decreasing list — and the
dimension function needs no ordering theory to state.

The paper's "including possible zero multiplicity" bookkeeping is not lost: a
zero or right angle is an *elementary* summand (`U ⊓ V`, `U ⊓ Vᗮ`, `Uᗮ ⊓ V`,
`Uᗮ ⊓ Vᗮ`), and those are carried by the four `Nonempty` fields, separately from
the generic angle data.

## Main results

* `TauCeti.DavisKahan.SameCompactAngleData`
* `TauCeti.DavisKahan.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


open Module (finrank)
open Module.End (eigenspace)

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The angle eigenvalue list -/

/-- Ordered eigenvalue data for a compact positive contraction: the
approximation-number sequence of `A`.

For a compact **positive** operator this is exactly the ordered eigenvalue list
*with multiplicity* -- `aₙ(A)` is the `n`-th largest singular value, and singular
values coincide with eigenvalues when the operator is positive, so a repeated
eigenvalue is repeated in the sequence.

The list is `ℝ`-valued over every scalar field, because the eigenvalues of a
compact positive self-adjoint operator are real.

Note the definition is total: it is stated for every `A`, and only *means* the
angle eigenvalue list under the compactness and positivity hypotheses that the
consumers carry.  This mirrors `approximationNumber` itself, which is total in
the same way. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] (A : K →L[𝕜] K) : ℕ → ℝ :=
  fun n => A.approximationNumber n

/-- **Approximation numbers are a unitary invariant.**  Conjugating by a linear isometric
equivalence sandwiches the operator between two contractions in both directions, so no
approximation number can move. -/
theorem approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (h : BoundedOperatorsUnitaryEquivalent A B) (n : ℕ) :
    A.approximationNumber n = B.approximationNumber n := by
  obtain ⟨U, hU⟩ := h
  have hUapp : ∀ x, B (U x) = U (A x) := fun x => (hU x).symm
  have hUnorm : ‖(U : E →L[𝕜] F)‖ ≤ 1 :=
    U.toLinearIsometry.norm_toContinuousLinearMap_le
  have hUsnorm : ‖(U.symm : F →L[𝕜] E)‖ ≤ 1 :=
    U.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hBfact : B = (U : E →L[𝕜] F) ∘L A ∘L (U.symm : F →L[𝕜] E) := by
    ext y
    change B y = U (A (U.symm y))
    rw [← hUapp (U.symm y), U.apply_symm_apply]
  have hAfact : A = (U.symm : F →L[𝕜] E) ∘L B ∘L (U : E →L[𝕜] F) := by
    ext x
    change A x = U.symm (B (U x))
    rw [hUapp x, U.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hAfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U.symm : F →L[𝕜] E) (U : E →L[𝕜] F) hUsnorm hUnorm n
  · conv_lhs => rw [hBfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U : E →L[𝕜] F) (U.symm : F →L[𝕜] E) hUnorm hUsnorm n

/-! ## The angle operator is compact with trivial kernel -/

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The cosine block is the compression of `P_U P_V P_U` to the `U`-half.

On the `U`-half the outer `P_U` is the identity and the outer projection onto
the half agrees with `P_U`, so the two compressions coincide.  This is the form
in which the paper's compactness hypothesis reaches the angle operator. -/
theorem genericCosineBlock_eq_compress_halmos :
    genericCosineBlock U V =
      DavisKahan.Sylvester.compressOperator (genericLeftHalf U V)
        (U.starProjection ∘L V.starProjection ∘L U.starProjection) := by
  refine ContinuousLinearMap.ext fun m => ?_
  apply Subtype.ext
  have hmU : U.starProjection (m : H) = (m : H) :=
    Submodule.starProjection_eq_self_iff.mpr m.2.1
  have hgen : V.starProjection (m : H) ∈ halmosGenericPart U V :=
    projection_mem_halmosGenericPart_right U V m.2.2
  have hMV : (genericLeftHalf U V).starProjection (V.starProjection (m : H)) =
      U.starProjection (V.starProjection (m : H)) :=
    starProjection_genericLeftHalf_of_mem_generic U V hgen
  have hLHS : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := by
    simp [genericCosineBlock, DavisKahan.Sylvester.compressOperator]
  have hRHS : ((DavisKahan.Sylvester.compressOperator (genericLeftHalf U V)
      (U.starProjection ∘L V.starProjection ∘L U.starProjection) m : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection
        (U.starProjection (V.starProjection (U.starProjection (m : H)))) := by
    simp [DavisKahan.Sylvester.compressOperator]
  rw [hLHS, hRHS, hmU, ← hMV,
    Submodule.starProjection_eq_self_iff.mpr
      ((genericLeftHalf U V).starProjection_apply_mem _)]

/-- **The angle operator is compact** when `P_U P_V P_U` is. -/
theorem isCompactOperator_genericCosineBlock
    (hc : IsCompactOperator (U.starProjection ∘L V.starProjection ∘L U.starProjection)) :
    IsCompactOperator (genericCosineBlock U V) := by
  rw [genericCosineBlock_eq_compress_halmos, DavisKahan.Sylvester.compressOperator]
  exact (hc.comp_clm (genericLeftHalf U V).subtypeL).clm_comp
    (genericLeftHalf U V).orthogonalProjectionOnto

/-- **The angle operator has trivial kernel.**  Generic position: its quadratic
form is `‖P_V m‖²`, which vanishes only at `0`. -/
theorem eigenspace_genericCosineBlock_zero :
    eigenspace (genericCosineBlock U V).toLinearMap 0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro m hm
  by_contra hne
  have hzero : genericCosineBlock U V m = 0 := by
    have := Module.End.mem_eigenspace_iff.mp hm
    simpa using this
  have hpos := re_inner_genericCosineBlock_pos U V hne
  rw [hzero] at hpos
  simp at hpos

/-! ## From the generic cosine block to the ambient block

Corollary 3.1's classifying invariant is the eigenvalue list of the *generic* cosine
block `genericCosineBlock U V`, an operator on the `U`-half of the generic part, while a
realization is naturally computed for the *ambient* block `P_U P_V P_U` on the whole
space.  When the four elementary Halmos summands are trivial the two carry the same
eigenvalue list, because the generic part is then everything and the ambient block is the
extension of the generic block by zero off `U`. -/

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- With the four elementary Halmos summands trivial, the generic part is everything and
the `U`-half of it is `U` itself. -/
theorem genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) : genericLeftHalf U V = U := by
  have hgen : halmosGenericPart U V = ⊤ := by
    change (halmosTrivialPart U V)ᗮ = ⊤
    rw [h]
    exact Submodule.bot_orthogonal_eq_top
  change U ⊓ halmosGenericPart U V = U
  rw [hgen, inf_top_eq]

/-- The orthogonal projection onto the `U`-half of the generic part is the projection onto
`U` when the four elementary Halmos summands are trivial. -/
theorem starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) (x : H) :
    (genericLeftHalf U V).starProjection x = U.starProjection x :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).ge (U.starProjection_apply_mem x))
    fun w hw =>
      Submodule.starProjection_inner_eq_zero x w
        ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).le hw)

/-- **The ambient block is the generic cosine block extended by zero.**

`genericCosineBlock U V` is the compression of `P_V` to the `U`-half of the generic part;
when the four elementary Halmos summands are trivial that half is `U`, and transporting the
block back to the ambient space by the inclusion and the orthogonal projection reproduces
`P_U P_V P_U` exactly. -/
theorem subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto
    (h : halmosTrivialPart U V = ⊥) :
    (genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
        (genericLeftHalf U V).orthogonalProjectionOnto =
      U.starProjection ∘L V.starProjection ∘L U.starProjection := by
  have hproj := starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h
  refine ContinuousLinearMap.ext fun x => ?_
  have hcoe : ∀ m : genericLeftHalf U V,
      ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := fun m => by
    simp [genericCosineBlock, DavisKahan.Sylvester.compressOperator]
  calc ((genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
          (genericLeftHalf U V).orthogonalProjectionOnto) x
      = (genericLeftHalf U V).starProjection
          (V.starProjection ((genericLeftHalf U V).starProjection x)) :=
        hcoe ((genericLeftHalf U V).orthogonalProjectionOnto x)
    _ = U.starProjection (V.starProjection (U.starProjection x)) := by
        rw [hproj, hproj]
    _ = (U.starProjection ∘L V.starProjection ∘L U.starProjection) x := rfl

/-- **The bridge between Corollary 3.1's two cosine blocks.**

The generic cosine block and the ambient block `P_U P_V P_U` have the same
approximation-number sequence -- hence the same `compactAngleEigenvalueList` -- whenever the
four elementary Halmos summands are trivial.

Mathematically this is "extension by zero preserves approximation numbers": off the generic
part the ambient block vanishes, so the two operators carry the same nonzero singular data.
The general fact is
`TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto`;
nothing about angles is reproved here. -/
theorem approximationNumber_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) (n : ℕ) :
    (genericCosineBlock U V).approximationNumber n =
      (U.starProjection ∘L V.starProjection ∘L U.starProjection).approximationNumber n := by
  rw [← subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto U V h,
    TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto
      (genericLeftHalf U V) (genericCosineBlock U V) n]

/-- The `compactAngleEigenvalueList` form of
`approximationNumber_genericCosineBlock_eq_ambient`. -/
theorem compactAngleEigenvalueList_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) :
    compactAngleEigenvalueList (genericCosineBlock U V) =
      compactAngleEigenvalueList
        (U.starProjection ∘L V.starProjection ∘L U.starProjection) :=
  funext fun n => approximationNumber_genericCosineBlock_eq_ambient U V h n

end OneSpace

/-! ## The compact classification -/

section TwoSpaces

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970 Corollary 3.1's invariant.**  The four elementary Halmos
multiplicities, together with the multiplicity of every angle: the paper's
decreasing eigenvalue list, written as a dimension function. -/
structure SameCompactAngleData : Prop where
  common : Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)
  angleMultiplicity : ∀ μ : 𝕜,
    finrank 𝕜 (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
      finrank 𝕜 (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ)

/-- A unitary intertwining two operators carries eigenspaces onto eigenspaces,
hence preserves their dimensions. -/
theorem finrank_eigenspace_eq_of_intertwiner
    {W : genericLeftHalf U₁ V₁ ≃ₗᵢ[𝕜] genericLeftHalf U₂ V₂}
    (hW : ∀ m, W (genericCosineBlock U₁ V₁ m) = genericCosineBlock U₂ V₂ (W m))
    (μ : 𝕜) :
    finrank 𝕜 (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
      finrank 𝕜 (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ) := by
  have hsymm : ∀ y, W.symm (genericCosineBlock U₂ V₂ y) =
      genericCosineBlock U₁ V₁ (W.symm y) := by
    intro y
    apply W.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hW, LinearIsometryEquiv.apply_symm_apply]
  have hfwd : ∀ m : genericLeftHalf U₁ V₁,
      m ∈ eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ →
      W m ∈ eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ := by
    intro m hm
    have hm' : genericCosineBlock U₁ V₁ m = μ • m := Module.End.mem_eigenspace_iff.mp hm
    rw [Module.End.mem_eigenspace_iff]
    change genericCosineBlock U₂ V₂ (W m) = μ • W m
    rw [← hW m, hm', map_smul]
  have hbwd : ∀ y : genericLeftHalf U₂ V₂,
      y ∈ eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ →
      W.symm y ∈ eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ := by
    intro y hy
    have hy' : genericCosineBlock U₂ V₂ y = μ • y := Module.End.mem_eigenspace_iff.mp hy
    rw [Module.End.mem_eigenspace_iff]
    change genericCosineBlock U₁ V₁ (W.symm y) = μ • W.symm y
    rw [← hsymm y, hy', map_smul]
  have hmap : (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ).map
      (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) =
      eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact hfwd m hm
    · intro y hy
      exact ⟨W.symm y, hbwd y hy, by simp⟩
  have hinj : Function.Injective
      (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) :=
    W.injective
  have hequiv := Submodule.equivMapOfInjective
    (W.toLinearEquiv : genericLeftHalf U₁ V₁ →ₗ[𝕜] genericLeftHalf U₂ V₂) hinj
    (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ)
  rw [← hmap]
  exact hequiv.finrank_eq


/-- **Davis--Kahan 1970, Corollary 3.1.**

When `P_U P_V P_U` is compact on both sides, two ordered pairs of subspaces are
unitarily equivalent as pairs exactly when their four elementary Halmos summands
are isometric and every angle has the same multiplicity.

This is Theorem 3.1 with the operator invariant replaced by numbers.  The
replacement is legitimate precisely because compactness makes the angle operator
one for which the eigenvalue list *is* a complete invariant. -/
theorem pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    (hc₁ : IsCompactOperator (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hc₂ : IsCompactOperator (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ := by
  constructor
  · intro h
    obtain ⟨hc, hs, ht, he, _⟩ := sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
    obtain ⟨W, hW⟩ := exists_cosineBlockEquiv_of_pairEquiv U₁ V₁ U₂ V₂ h
    exact ⟨hc, hs, ht, he, finrank_eigenspace_eq_of_intertwiner U₁ V₁ U₂ V₂ hW⟩
  · rintro ⟨⟨ec⟩, ⟨es⟩, ⟨et⟩, ⟨ee⟩, hmult⟩
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq
        (isCompactOperator_genericCosineBlock U₁ V₁ hc₁)
        (isSelfAdjoint_genericCosineBlock U₁ V₁)
        (isCompactOperator_genericCosineBlock U₂ V₂ hc₂)
        (isSelfAdjoint_genericCosineBlock U₂ V₂)
        (eigenspace_genericCosineBlock_zero U₁ V₁)
        (eigenspace_genericCosineBlock_zero U₂ V₂) hmult
    exact pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv U₁ V₁ U₂ V₂ W hW
      ec es et ee

end TwoSpaces

end DavisKahan
end TauCeti
