/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.SinTheta.TrialMap
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Residual.AngleEmbeddings
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTwoThetaResidual

/-!
# Generalized finite-dimensional residual theorems

This module contains the remaining source-level finite extensions after the
canonical trial-map theorem.  The arbitrary-separation square-norm theorem
uses the correctly whitened coordinate operator.  Infinite-dimensional
contour continuation belongs to the concrete `Continuation*` hierarchy and is
not imported through this finite module.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators Topology unitInterval
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Coordinate operator obtained after the canonical Gram whitening
`X = Q T`.  If the original pair is `A X - X M`, then the normalized pair is
`A Q - Q (T M T⁻¹)`. -/
noncomputable def whitenedCoordinateOperator
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) (M : F →ₗ[𝕜] F) :
    F →ₗ[𝕜] F :=
  (trialGramSqrtEquiv X hX).toLinearMap ∘ₗ M ∘ₗ
    (trialGramSqrtEquiv X hX).symm.toLinearMap

/-- The normalized residual is the original residual followed by the inverse
Gram coordinate.  This is the algebraic identity that was missing from the
historical generalized square-norm proof. -/
theorem residual_orthonormalizedEmbedding_whitenedCoordinateOperator
    (A : E →ₗ[𝕜] E) (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (M : F →ₗ[𝕜] F) :
    residual A (orthonormalizedEmbedding X hX)
        (whitenedCoordinateOperator X hX M) =
      generalResidual A X M ∘ₗ
        (trialGramSqrtEquiv X hX).symm.toLinearMap := by
  ext y
  simp only [residual, generalResidual, whitenedCoordinateOperator,
    LinearMap.sub_apply, LinearMap.comp_apply]
  -- the goal carries `.toLinearMap`, not the isometry's function coercion,
  -- and both occurrences have to be unfolded before the inverse cancels
  simp only [show ∀ z : F, (orthonormalizedEmbedding X hX).toLinearMap z =
    X ((trialGramSqrtEquiv X hX).symm z) from fun _ => rfl]
  -- the inner application arrives through the linear-map coercion, so the
  -- equiv cancellation lemma needs `simp` rather than a bare rewrite
  simp
  congr 1
  exact (trialGramSqrtEquiv X hX).symm_apply_apply _

/-- Davis--Kahan Theorem 6.2 for an injective nonorthonormal trial map.

The self-adjointness and spectral-separation hypotheses are imposed on the
whitened coordinate operator `T M T⁻¹`, which is the operator that actually
occurs in the normalized Sylvester equation. -/
theorem generalizedSinTheta_frobenius_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F}
    (hM : (whitenedCoordinateOperator X hX M).IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : PointSpectraSeparated (whitenedCoordinateOperator X hX M) ⊤ A Vᗮ δ) :
    δ * ε * UnitarilyInvariantSeminorm.frobenius
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      UnitarilyInvariantSeminorm.frobenius
        (generalResidual A X M) := by
  let Q := orthonormalizedEmbedding X hX
  let Mhat := whitenedCoordinateOperator X hX M
  have hnormalized := frobenius_sinTheta_residual_le_of_spectralDistance
    hA hV Q hM hδ hgap
  have hfactor : residual A Q Mhat = generalResidual A X M ∘ₗ
      (trialGramSqrtEquiv X hX).symm.toLinearMap := by
    simpa [Q, Mhat] using
      residual_orthonormalizedEmbedding_whitenedCoordinateOperator A X hX M
  have hright :=
    (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E)).comp_le_mul_opNorm
      (generalResidual A X M)
      (trialGramSqrtEquiv X hX).symm.toLinearMap
  rw [← hfactor] at hright
  have hinv := opNorm_trialGramSqrtEquiv_symm_le X hX hframe hε
  have hres : UnitarilyInvariantSeminorm.frobenius (residual A Q Mhat) ≤
      UnitarilyInvariantSeminorm.frobenius (generalResidual A X M) * ε⁻¹ :=
    hright.trans (mul_le_mul_of_nonneg_left hinv
      ((UnitarilyInvariantSeminorm.frobenius
        (𝕜 := 𝕜) (E := F) (F := E)).nonneg _))
  calc
    δ * ε * UnitarilyInvariantSeminorm.frobenius
        (sinThetaEmbedding V Q) =
      ε * (δ * UnitarilyInvariantSeminorm.frobenius
        (sinThetaEmbedding V Q)) := by ring
    _ ≤ ε * UnitarilyInvariantSeminorm.frobenius
        (residual A Q Mhat) := mul_le_mul_of_nonneg_left hnormalized hε.le
    _ ≤ ε * (UnitarilyInvariantSeminorm.frobenius
        (generalResidual A X M) * ε⁻¹) :=
      mul_le_mul_of_nonneg_left hres hε.le
    _ = UnitarilyInvariantSeminorm.frobenius
        (generalResidual A X M) := by field_simp [hε.ne']

/-- Nuclear fallback obtained from Theorem 6.2 and finite Cauchy--Schwarz. -/
theorem generalizedSinTheta_nuclear_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F}
    (hM : (whitenedCoordinateOperator X hX M).IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : PointSpectraSeparated (whitenedCoordinateOperator X hX M) ⊤ A Vᗮ δ) :
    δ * ε * UnitarilyInvariantSeminorm.nuclear
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      Real.sqrt (finrank 𝕜 F) *
        UnitarilyInvariantSeminorm.frobenius
          (generalResidual A X M) := by
  let S := sinThetaEmbedding V (orthonormalizedEmbedding X hX)
  have hHS := generalizedSinTheta_frobenius_le_of_spectralDistance
    hA hV X hX hM hδ hε hframe hgap
  have hnuc := UnitarilyInvariantSeminorm.nuclear_le_sqrt_finrank_mul_frobenius S
  have hδε : 0 ≤ δ * ε := mul_nonneg hδ.le hε.le
  calc
    δ * ε * UnitarilyInvariantSeminorm.nuclear S ≤
        δ * ε * (Real.sqrt (finrank 𝕜 F) *
          UnitarilyInvariantSeminorm.frobenius S) :=
      mul_le_mul_of_nonneg_left hnuc hδε
    _ = Real.sqrt (finrank 𝕜 F) *
        (δ * ε * UnitarilyInvariantSeminorm.frobenius S) := by ring
    _ ≤ Real.sqrt (finrank 𝕜 F) *
        UnitarilyInvariantSeminorm.frobenius (generalResidual A X M) :=
      mul_le_mul_of_nonneg_left hHS (Real.sqrt_nonneg _)

/-- Davis--Kahan Theorem 6.3 in whitened trial coordinates. -/
theorem generalizedTanTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : IsInvariant A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (_hdim : finrank 𝕜 F ≤ finrank 𝕜 V)
    (_htrans : IsTransverse
      (approximateSubspace (orthonormalizedEmbedding X hX)) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap (generalizedCompression A X hX) ⊤ A Vᗮ δ) :
    δ * N (tanThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (residual A (orthonormalizedEmbedding X hX)
        (generalizedCompression A X hX)) :=
  tanTheta_residual_le N hA hV (orthonormalizedEmbedding X hX)
    (isSymmetric_generalizedCompression hA X hX) rfl hδ hgap

/-- Unequal-dimensional ordered-gap `sin 2Θ` residual extension. -/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) :=
  sinTwoTheta_residual_le_of_orderedGap N hA hU X hM hδ hgap


end DavisKahan.FiniteDimensional
end TauCeti
