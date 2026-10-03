/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Generalized
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Real

/-! # Bounded -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded natural spectral-subspace specializations

These wrappers convert bounded self-adjoint operators to full-domain closed
operators and apply the natural unbounded spectral-subspace theorems. The
residual is the ordinary bounded defect `A X - X A0`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


noncomputable section

universe v

section Complex

-- `open ` would resolve to the nested
-- `ExactSinTheta` namespace introduced by `RealSpectrumBridge`,
-- which shadows the intended one, so the full path is spelled out here.
open TauCeti.DavisKahan

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Bounded complex isometric theorem with a canonical spectral subspace. -/
theorem sinTheta_bounded_spectralSubspace_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap
      ((A0.toLinearMap.toPMap ⊤))
      (selfAdjointSpectralRestriction
        ((A.toLinearMap.toPMap ⊤))
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
        Sᶜ hS.compl) δ)
    (hR : N.Mem
      (generalResidual A X A0)) :
    N.Mem
      ((ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS ∘L
        (selfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS).adjoint) ∘L X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℂ E -
          selfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS ∘L
          (selfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS).adjoint) ∘L X)
        ≤ N.gauge
          (generalResidual A X A0) := by
  apply sinTheta_unbounded_spectralSubspace_of_spectrumGap
    N ((A.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
      S hS ((A0.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A0)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA0))
      X (generalResidual A X A0) hX
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hδ => exact hδ
  case hgap => exact hgap
  case hR => exact hR

/-- Bounded complex lower-frame theorem with a canonical spectral subspace. -/
theorem generalizedSinTheta_bounded_spectralSubspace_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectralSylvesterGap
      ((A0.toLinearMap.toPMap ⊤))
      (selfAdjointSpectralRestriction
        ((A.toLinearMap.toPMap ⊤))
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
        Sᶜ hS.compl) δ)
    (hR : N.Mem
      (generalResidual A X A0)) :
    N.Mem
      (directedSinThetaOperator X
        (selfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS) hframe hε) ∧
      δ * ε * N.gauge
        (directedSinThetaOperator X
          (selfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS) hframe hε)
        ≤ N.gauge
          (generalResidual A X A0) := by
  apply generalizedSinTheta_unbounded_spectralSubspace_of_spectrumGap
    N ((A.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
      S hS ((A0.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A0)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA0))
      X (generalResidual A X A0) hδ hε hframe
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hgap => exact hgap
  case hR => exact hR

end Complex

section Real

open RealSpectralRestriction

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Bounded real isometric theorem with a canonical descended spectral
subspace. -/
theorem sinTheta_bounded_spectralSubspace_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℝ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℝ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      ((A0.toLinearMap.toPMap ⊤))
      (realSelfAdjointSpectralRestriction
        ((A.toLinearMap.toPMap ⊤))
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
        Sᶜ hS.compl) δ)
    (hR : N.Mem
      (generalResidual A X A0)) :
    N.Mem
      ((ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS ∘L
        (realSelfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS).adjoint) ∘L X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℝ E -
          realSelfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS ∘L
          (realSelfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS).adjoint) ∘L X)
        ≤ N.gauge
          (generalResidual A X A0) := by
  apply sinTheta_unbounded_real_spectralSubspace
    N ((A.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
      S hS ((A0.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A0)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA0))
      X (generalResidual A X A0) hX
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hδ => exact hδ
  case hgap => exact hgap
  case hR => exact hR

/-- Bounded real lower-frame theorem with a canonical descended spectral
subspace. -/
theorem sinTheta_generalized_bounded_spectralSubspace_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℝ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℝ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : FormBoundedSylvesterGap
      ((A0.toLinearMap.toPMap ⊤))
      (realSelfAdjointSpectralRestriction
        ((A.toLinearMap.toPMap ⊤))
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
        Sᶜ hS.compl) δ)
    (hR : N.Mem
      (generalResidual A X A0)) :
    N.Mem
      (directedSinThetaOperatorReal X
        (realSelfAdjointSpectralSubspaceInclusion
          ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
          S hS) hframe hε) ∧
      δ * ε * N.gauge
        (directedSinThetaOperatorReal X
          (realSelfAdjointSpectralSubspaceInclusion
            ((A.toLinearMap.toPMap ⊤))
            (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
            S hS) hframe hε)
        ≤ N.gauge
          (generalResidual A X A0) := by
  apply generalizedSinTheta_unbounded_real_spectralSubspace
    N ((A.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
      S hS ((A0.toLinearMap.toPMap ⊤))
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A0)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA0))
      X (generalResidual A X A0) hδ hε hframe
  case hXdom => intro x; simp
  case hReq => intro x; rfl
  case hgap => exact hgap
  case hR => exact hR

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
