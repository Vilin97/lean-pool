/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.SpectralSubspace

/-! # Generalized -/

open TauCeti.DavisKahan.Sylvester

/-!
# Generalized complex sine-theta theorem from natural spectral inputs

The compiler-accepted `NaturalGenuine` module contains the canonical isometric
specialization.  This separate leaf adds the lower-frame result without
modifying that verified module.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta



universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Public generalized complex unbounded sine-theta theorem from natural
spectral inputs. The lower-frame polar factorization and every complementary
spectral restriction are constructed internally. -/
theorem generalizedSinTheta_unbounded_spectralSubspace_of_spectrumGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℂ] F)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℂ] E)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    (hgap : SpectralSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hR : N.Mem Rop) :
    N.Mem
      (directedSinThetaOperator X
        (selfAdjointSpectralSubspaceInclusion A hA S hS)
        hframe hε) ∧
      δ * ε * N.gauge
        (directedSinThetaOperator X
          (selfAdjointSpectralSubspaceInclusion A hA S hS)
          hframe hε)
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
  have hmain := generalizedSinTheta_unbounded_exact_of_spectrumGap
    N D (selfAdjointSpectralSubspaceInclusion A hA S hS)
      hDA
      hDA₀
      hLambda hdecomp hδ hε hframe hgap hR
  simpa only [D, unboundedSinThetaDataOfSpectralSubspace,
    UnboundedSinThetaData] using hmain

end ExactSinTheta
end DavisKahan
end TauCeti
