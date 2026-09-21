/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.AllGap
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionOperator

/-! # Spectral Subspace -/

open TauCeti.DavisKahan.Sylvester

/-!
# Natural spectral-projection inputs for the unbounded sine-theta theorem

This module constructs the internal complementary restriction, inclusion,
domain laws, intertwining law, and orthogonal exact decomposition from a
measurable spectral set of the ambient self-adjoint operator.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta



universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The canonical exact and complementary spectral inclusions form a complete
orthogonal coordinate decomposition of the ambient Hilbert space. -/
theorem spectralSubspace_orthogonalExactDecomposition
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
    OrthogonalExactDecomposition
      (selfAdjointSpectralSubspaceInclusion A hA S hS)
      (selfAdjointSpectralSubspaceInclusion A hA Sᶜ hS.compl) := by
  let U := selfAdjointSpectralSubspace A hA S hS
  let Uc := selfAdjointSpectralSubspace A hA Sᶜ hS.compl
  have hUcProjection : Uc.starProjection =
      ContinuousLinearMap.id ℂ E - U.starProjection := by
    rw [← selfAdjointSpectralProjection_eq_starProjection A hA Sᶜ hS.compl,
      show selfAdjointSpectralProjection A hA Sᶜ hS.compl
          = ContinuousLinearMap.id ℂ E -
            selfAdjointSpectralProjection A hA S hS from
        (TauCeti.LinearPMap.spectralPVM hA).proj_compl S hS]
    change ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralProjection A hA S hS =
      ContinuousLinearMap.id ℂ E - U.starProjection
    rw [selfAdjointSpectralProjection_eq_starProjection A hA S hS]
  refine
    { isometry₀ := selfAdjointSpectralSubspaceInclusion_isometric A hA S hS
      isometry₁ := selfAdjointSpectralSubspaceInclusion_isometric A hA Sᶜ hS.compl
      orthogonal := ?_
      projection_sum := ?_ }
  · change U.subtypeL.adjoint ∘L Uc.subtypeL = 0
    rw [Submodule.adjoint_subtypeL]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change U.starProjection (x : E) = 0
    have hfix : Uc.starProjection (x : E) = (x : E) :=
      Submodule.starProjection_eq_self_iff.mpr x.property
    rw [hUcProjection] at hfix
    have hfix' : (x : E) - U.starProjection (x : E) = (x : E) := by
      simpa only [sub_apply,
        ContinuousLinearMap.id_apply] using hfix
    exact sub_eq_self.mp hfix'
  · change U.subtypeL ∘L U.subtypeL.adjoint +
        Uc.subtypeL ∘L Uc.subtypeL.adjoint = ContinuousLinearMap.id ℂ E
    rw [Submodule.adjoint_subtypeL, Submodule.adjoint_subtypeL]
    change U.starProjection + Uc.starProjection = ContinuousLinearMap.id ℂ E
    rw [hUcProjection]
    abel

/-- Construct the internal unbounded sine-theta bookkeeping directly from a
measurable exact spectral set and a bounded residual extension. -/
noncomputable def unboundedSinThetaDataOfSpectralSubspace
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℂ] F) (_hA0 : IsSelfAdjoint A0)
    (X Rop : F →L[ℂ] E)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F)
      (G := selfAdjointSpectralSubspace A hA Sᶜ hS.compl) where
  A := A
  A₀ := A0
  Λ₁ := selfAdjointSpectralRestriction A hA Sᶜ hS.compl
  X := X
  F₁ := selfAdjointSpectralSubspaceInclusion A hA Sᶜ hS.compl
  residual := Rop
  X_maps_domain := hXdom
  F₁_maps_domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain A hA Sᶜ hS.compl
  residual_eq := hReq
  intertwines :=
    selfAdjointSpectralRestriction_inclusion_intertwines A hA Sᶜ hS.compl

/-- Public isometric unbounded sine-theta theorem from natural spectral inputs.
The complementary restriction and all exact-space bookkeeping are constructed
internally. -/
theorem sinTheta_unbounded_spectralSubspace_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℂ] F)
    (hA0 : IsSelfAdjoint A0)
    (X Rop : F →L[ℂ] E)
    (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hR : N.Mem Rop) :
    N.Mem
      ((ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℂ E -
          selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
            (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X)
        ≤ N.gauge Rop := by
  let D := unboundedSinThetaDataOfSpectralSubspace
    A hA S hS A0 hA0 X Rop hXdom hReq
  have hLambda : _root_.IsSelfAdjoint D.Λ₁ := by
    exact selfAdjointSpectralRestriction_isSelfAdjoint A hA Sᶜ hS.compl
  have hdecomp : OrthogonalExactDecomposition
      (selfAdjointSpectralSubspaceInclusion A hA S hS) D.F₁ := by
    simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using
      spectralSubspace_orthogonalExactDecomposition A hA S hS
  have hDA : _root_.IsSelfAdjoint D.A := by
    simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using hA
  have hDA₀ : _root_.IsSelfAdjoint D.A₀ := by
    simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using hA0
  have hmain := sinTheta_unbounded_exact_of_spectrumGap
    N D (selfAdjointSpectralSubspaceInclusion A hA S hS)
      hDA hDA₀ hLambda hX hdecomp hδ hgap hR
  simpa only [D, unboundedSinThetaDataOfSpectralSubspace] using hmain

end ExactSinTheta
end DavisKahan
end TauCeti
