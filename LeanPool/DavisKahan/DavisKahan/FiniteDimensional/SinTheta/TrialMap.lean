/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.FrameFactorization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.TrialMap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval

/-!
# Generalized finite-dimensional Davis--Kahan theorems

This file records the finite-dimensional forms of the generalizations stated
after the four headline theorems in Davis--Kahan (1970).

Literature map:

* `prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 5--11.
* Davis--Kahan (1970), Theorems 6.1--6.3 and 8.2.

The important extra features are non-orthonormal trial vectors, comparison of
subspaces of unequal dimension, the square-norm fallback under arbitrary
spectral separation, and the continuation argument selecting the acute branch
of a double-angle estimate.  These are kept separate from the sharp clean API
so their conditioning losses are visible in theorem statements.
-/


/-! ## Construction status

The shared injective-trial-map coordinate layer now lives in
`DavisKahan.FiniteDimensional.FrameFactorization`.  It provides the canonical rectangular
polar factorization `X = Q T`, proves that `Q` is isometric with
`range Q = range X`, and packages the positive Gram square root `T` as a
linear equivalence.  It also proves `‖T⁻¹‖ ≤ ε⁻¹`, the corresponding
right-ideal estimate for every rectangular UI norm, and the assembled
frame-to-sine transport inequality
`ε * N (P_{Vᗮ} Q) ≤ N (P_{Vᗮ} X)`.

Theorem 6.1 is assembled below from this coordinate layer and the raw
projected Sylvester identity.  The source-complete endpoints accept either
interval/exterior orientation, derive injectivity from either the positive
lower frame bound or the paper's Gram-operator inequality, and keep coordinate
operators such as `M` in their original self-adjoint coordinates throughout.
The final wrapper also accepts any `sin Θ₀` operator with the canonical complete
singular-value sequence.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators Topology
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The geometric sine block is the raw complementary trial block followed by
the inverse frame coordinate. -/
theorem complementaryTrialBlock_comp_trialGramSqrtEquiv_symm
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    complementaryTrialBlock U X ∘ₗ
        (trialGramSqrtEquiv X hX).symm.toLinearMap =
      sinThetaEmbedding U (orthonormalizedEmbedding X hX) := by
  rw [complementaryTrialBlock, sinThetaEmbedding, LinearMap.comp_assoc,
    trialMap_comp_trialGramSqrtEquiv_symm X hX]

/-- Lower-frame transport from the raw complementary block to the canonical
sine-angle map in every rectangular unitarily invariant norm. -/
theorem lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {ε : ℝ} (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    ε * N (sinThetaEmbedding U (orthonormalizedEmbedding X hX)) ≤
      N (complementaryTrialBlock U X) := by
  have hideal := uiNorm_comp_trialGramSqrtEquiv_symm_le
    N X hX hframe hε (complementaryTrialBlock U X)
  rw [complementaryTrialBlock_comp_trialGramSqrtEquiv_symm U X hX] at hideal
  calc
    ε * N (sinThetaEmbedding U (orthonormalizedEmbedding X hX)) ≤
        ε * (N (complementaryTrialBlock U X) * ε⁻¹) :=
      mul_le_mul_of_nonneg_left hideal hε.le
    _ = N (complementaryTrialBlock U X) := by
      field_simp [hε.ne']

/-- Symmetric compression after whitening a full-column-rank trial map.

If `X = Q G^{1/2}` is the polar/whitening factorization, this is `Q⋆ A Q`.
The coordinate Rayleigh quotient `(X⋆X)⁻¹ X⋆ A X` is similar to this operator
but is generally only self-adjoint for the Gram inner product. -/
noncomputable def generalizedCompression (A : E →ₗ[𝕜] E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) : F →ₗ[𝕜] F :=
  compression A (orthonormalizedEmbedding X hX)

/-- The whitened generalized compression is symmetric for a symmetric
ambient operator.

Signature audit: Valid because the public compression is now the whitened
ordinary-self-adjoint operator.
-/
theorem isSymmetric_generalizedCompression {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (generalizedCompression A X hX).IsSymmetric := by
  exact isSymmetric_compression hA (orthonormalizedEmbedding X hX)

/-- The interval/exterior spectral hypothesis for a generalized trial pair,
in either orientation.

The first branch places the coordinate spectrum of `M` in `[a,b]` and the
unwanted exact spectrum of `A` on `Vᗮ` outside the enlarged interval.  The
second branch reverses those roles, as allowed in Davis--Kahan Theorem 6.1. -/
def TrialComplementIntervalGap (M : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] E)
    (V : Submodule 𝕜 E) (a b δ : ℝ) : Prop :=
  (PointSpectrumIn M ⊤ (Set.Icc a b) ∧
      PointSpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) ∨
    (PointSpectrumIn A Vᗮ (Set.Icc a b) ∧
      PointSpectrumIn M ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})

/-- **Raw generalized sine-block residual estimate, every UI norm.**

For an arbitrary trial map `X`, the complementary block `P_{Vᗮ} X` satisfies
the sharp interval/exterior Sylvester estimate in either spectral orientation.
No injectivity or lower frame bound is needed at this stage. -/
theorem complementaryTrialBlock_residual_le_of_intervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * N (complementaryTrialBlock V X) ≤ N (generalResidual A X M) := by
  have hVperp : IsInvariant A Vᗮ := isInvariant_orthogonal_of_isSymmetric hA hV
  let AV : Vᗮ →ₗ[𝕜] Vᗮ := A.restrict hVperp
  let Y : F →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X
  let C : F →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ generalResidual A X M
  let NV : UnitarilyInvariantSeminorm 𝕜 F Vᗮ :=
    N.codomainIsometryTransport Vᗮ.subtypeₗᵢ
  have hAV : AV.IsSymmetric := hA.restrict_invariant hVperp
  have hgap' : UnorderedIntervalSylvesterGap AV M a b δ := by
    rcases hgap with hforward | hreverse
    · exact Or.inl ⟨hforward.1,
        (pointSpectrumIn_restrict_iff A hVperp _).2 hforward.2⟩
    · exact Or.inr ⟨
        (pointSpectrumIn_restrict_iff A hVperp _).2 hreverse.1,
        hreverse.2⟩
  have hEq : AV ∘ₗ Y - Y ∘ₗ M = C := by
    ext x
    have hx := LinearMap.congr_fun
      (sylvester_complementaryTrialBlock_eq_projectedGeneralResidual hA hV X M) x
    simpa [AV, Y, C, complementaryTrialBlock, complementaryProjection, projection,
      LinearMap.comp_apply] using hx
  have hY : NV Y = N (complementaryTrialBlock V X) := by
    change N (Vᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) =
      N (complementaryTrialBlock V X)
    congr 1
  have hC : NV C =
      N (complementaryProjection V ∘ₗ generalResidual A X M) := by
    change N (Vᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection V ∘ₗ generalResidual A X M)
    congr 1
  have hproj : ‖(complementaryProjection V).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection V).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    change ‖Vᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Vᗮ.norm_starProjection_apply_le x
  have hC_le : NV C ≤ N (generalResidual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection V ∘ₗ generalResidual A X M)
          ≤ ‖(complementaryProjection V).toContinuousLinearMap‖ *
              N (generalResidual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (generalResidual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (generalResidual A X M) := one_mul _
  have hSylvester :=
    uiNorm_sylvester_le_of_unorderedIntervalGap NV hAV hM hδ hgap' hEq
  rw [hY] at hSylvester
  exact hSylvester.trans hC_le

/-- **Davis--Kahan Theorem 6.1, source-complete interval/exterior form.**

A positive lower frame bound supplies injectivity automatically.  The theorem
allows either interval/exterior orientation and compares subspaces of unequal
dimension through the directed sine block. -/
theorem generalizedSinTheta_residual_le_of_intervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hframe.injective hε))) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X (hframe.injective hε) hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ hgap
  calc
    δ * ε * N (sinThetaEmbedding V
        (orthonormalizedEmbedding X (hframe.injective hε))) =
        δ * (ε * N (sinThetaEmbedding V
          (orthonormalizedEmbedding X (hframe.injective hε)))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

/-- **Davis--Kahan Theorem 6.1 with the paper's Gram hypothesis.**

This source-facing wrapper accepts the operator inequality
`X⋆ X ≥ ε² I` through `GramLowerBound`, rather than requiring callers to
translate it into a pointwise norm bound. -/
theorem generalizedSinTheta_residual_le_of_gramLowerBound
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hgram.injective hε))) ≤
      N (generalResidual A X M) := by
  exact generalizedSinTheta_residual_le_of_intervalGap
    N hA hV X hM hδ hε (hgram.lowerFrameBound hε.le) hgap

/-- **Davis--Kahan Theorem 6.1 in its permissive `sin Θ₀` form.**

The paper allows `sin Θ₀` to be any rectangular operator with the same complete
singular-value sequence as the canonical directed sine block.  Since every
rectangular unitarily invariant norm depends only on that sequence, the
canonical Gram-bound theorem transfers without loss. -/
theorem generalizedSinTheta0_residual_le_of_gramLowerBound
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ)
    (sinTheta0 : F →ₗ[𝕜] E)
    (hsin : sinTheta0.singularValues =
      (sinThetaEmbedding V
        (orthonormalizedEmbedding X (hgram.injective hε))).singularValues) :
    δ * ε * N sinTheta0 ≤ N (generalResidual A X M) := by
  have hcanonical := generalizedSinTheta_residual_le_of_gramLowerBound
    N hA hV X hM hδ hε hgram hgap
  have hnorm : N sinTheta0 = N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hgram.injective hε))) :=
    N.eq_of_same_singularValues hsin
  rw [hnorm]
  exact hcanonical

/-- Compatibility specialization of Theorem 6.1 with the coordinate spectrum
inside `[a,b]` and the unwanted exact spectrum outside the enlarged interval.

The explicit injectivity argument is retained for callers of the earlier API;
the source-complete theorem above derives it from the positive lower frame
bound. -/
theorem generalizedSinTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hMspec : PointSpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : PointSpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X hX hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ (Or.inl ⟨hMspec, hAspec⟩)
  calc
    δ * ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) =
        δ * (ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

end DavisKahan.FiniteDimensional
end TauCeti
