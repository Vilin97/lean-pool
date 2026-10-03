/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Generalized
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction

/-! # Real -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Natural real spectral inputs for the unbounded sine-theta theorem

This module is the real counterpart of `NaturalGenuine`.  A measurable real
spectral set of the ambient self-adjoint operator determines canonical exact
and complementary real spectral ranges, the self-adjoint restriction to the
complement, both inclusion intertwiners, and the orthogonal decomposition.

Consequently the public sine-theta theorems require only the ambient and trial
operators, the trial map, its domain law, a bounded residual extension, a gap,
and ideal membership.  No spectral restriction or complementary bookkeeping
is supplied by the caller.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


open RealSpectralRestriction

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The canonical exact and complementary real spectral inclusions form a
complete orthogonal coordinate decomposition of the ambient Hilbert space. -/
theorem realSpectralSubspace_orthogonalExactDecomposition
    (A : E →ₗ.[ℝ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
    OrthogonalExactDecomposition
      (realSelfAdjointSpectralSubspaceInclusion A hA S hS)
      (realSelfAdjointSpectralSubspaceInclusion A hA Sᶜ hS.compl) := by
  let U := realSelfAdjointSpectralSubspace A hA S hS
  let Uc := realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl
  have hUcProjection : Uc.starProjection =
      ContinuousLinearMap.id ℝ E - U.starProjection := by
    rw [← realSelfAdjointSpectralProjection_eq_starProjection A hA Sᶜ hS.compl]
    change realSelfAdjointSpectralProjection A hA Sᶜ hS.compl =
      ContinuousLinearMap.id ℝ E - U.starProjection
    rw [realSelfAdjointSpectralProjection_compl A hA S hS,
      realSelfAdjointSpectralProjection_eq_starProjection A hA S hS]
  refine
    { isometry₀ :=
        realSelfAdjointSpectralSubspaceInclusion_isometric A hA S hS
      isometry₁ :=
        realSelfAdjointSpectralSubspaceInclusion_isometric A hA Sᶜ hS.compl
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
        Uc.subtypeL ∘L Uc.subtypeL.adjoint = ContinuousLinearMap.id ℝ E
    rw [Submodule.adjoint_subtypeL, Submodule.adjoint_subtypeL]
    change U.starProjection + Uc.starProjection = ContinuousLinearMap.id ℝ E
    rw [hUcProjection]
    abel

/-- Construct the internal real unbounded sine-theta bookkeeping from a
measurable exact spectral set and a bounded residual extension. -/
noncomputable def unboundedSinThetaDataOfRealSpectralSubspace
    (A : E →ₗ.[ℝ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℝ] F)
    (X Rop : F →L[ℝ] E)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F)) :
    UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F)
      (G := realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl) where
  A := A
  A₀ := A0
  Λ₁ := realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl
  X := X
  F₁ := realSelfAdjointSpectralSubspaceInclusion A hA Sᶜ hS.compl
  residual := Rop
  X_maps_domain := hXdom
  F₁_maps_domain :=
    realSelfAdjointSpectralRestriction_inclusion_mem_domain
      A hA Sᶜ hS.compl
  residual_eq := hReq
  intertwines :=
    realSelfAdjointSpectralRestriction_inclusion_intertwines
      A hA Sᶜ hS.compl

/-- Public real isometric unbounded sine-theta theorem from natural spectral
inputs.  The real spectral projection, complementary self-adjoint restriction,
and all exact-space bookkeeping are constructed internally. -/
theorem sinTheta_unbounded_real_spectralSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℝ] F)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℝ] E)
    (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A0
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hR : N.Mem Rop) :
    N.Mem
      ((ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (realSelfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℝ E -
          realSelfAdjointSpectralSubspaceInclusion A hA S hS ∘L
            (realSelfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X)
        ≤ N.gauge Rop := by
  let D := unboundedSinThetaDataOfRealSpectralSubspace
    A hA S hS A0 X Rop hXdom hReq
  have hLambda : _root_.IsSelfAdjoint D.Λ₁ := by
    exact realSelfAdjointSpectralRestriction_isSelfAdjoint
      A hA Sᶜ hS.compl
  have hdecomp : OrthogonalExactDecomposition
      (realSelfAdjointSpectralSubspaceInclusion A hA S hS) D.F₁ := by
    simpa only [D, unboundedSinThetaDataOfRealSpectralSubspace] using
      realSpectralSubspace_orthogonalExactDecomposition A hA S hS
  have hmain := sinTheta_unbounded_exact_real
    N D (realSelfAdjointSpectralSubspaceInclusion A hA S hS)
      hA hA0 hLambda hX hdecomp hδ hgap hR
  simpa only [D, unboundedSinThetaDataOfRealSpectralSubspace] using hmain

/-- Public real generalized unbounded sine-theta theorem from natural spectral
inputs.  It retains the sharp lower-frame factor and the exact directed sine
operator while constructing the complementary spectral restriction
internally. -/
theorem generalizedSinTheta_unbounded_real_spectralSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℝ] F)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℝ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    (hgap : FormBoundedSylvesterGap A0
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hR : N.Mem Rop) :
    N.Mem
      (directedSinThetaOperatorReal X
        (realSelfAdjointSpectralSubspaceInclusion A hA S hS)
        hframe hε) ∧
      δ * ε * N.gauge
        (directedSinThetaOperatorReal X
          (realSelfAdjointSpectralSubspaceInclusion A hA S hS)
          hframe hε)
        ≤ N.gauge Rop := by
  let D := unboundedSinThetaDataOfRealSpectralSubspace
    A hA S hS A0 X Rop hXdom hReq
  have hLambda : _root_.IsSelfAdjoint D.Λ₁ := by
    exact realSelfAdjointSpectralRestriction_isSelfAdjoint
      A hA Sᶜ hS.compl
  have hdecomp : OrthogonalExactDecomposition
      (realSelfAdjointSpectralSubspaceInclusion A hA S hS) D.F₁ := by
    simpa only [D, unboundedSinThetaDataOfRealSpectralSubspace] using
      realSpectralSubspace_orthogonalExactDecomposition A hA S hS
  have hmain := generalizedSinTheta_unbounded_exact_real
    N D (realSelfAdjointSpectralSubspaceInclusion A hA S hS)
      hA hA0 hLambda hdecomp hδ hε hframe hgap hR
  simpa only [D, unboundedSinThetaDataOfRealSpectralSubspace] using hmain

end

end ExactSinTheta
end DavisKahan
end TauCeti
