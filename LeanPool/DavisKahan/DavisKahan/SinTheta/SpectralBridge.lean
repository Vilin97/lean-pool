/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.Bounded
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed

/-! # Spectral Bridge -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded spectral bridge: definitions

The affine-shift interface that converts the paper's spectral hypotheses into
the norm and inverse bounds Theorem 5.1 needs.  The four estimates themselves
are still open and stay in
`DavisKahan.InfiniteDimensional.SinTheta.SpectralBridge`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Real spectrum of a bounded operator, defined through the same closed-operator
spectral API used by the canonical unbounded theorem.  This avoids maintaining
an unrelated bounded spectrum placeholder and makes bounded gap hypotheses
eligible for a direct full-domain specialization bridge. -/
noncomputable def boundedRealSpectrum (A : E →L[𝕜] E) : Set ℝ :=
  TauCeti.LinearPMap.realSpectrum (A.toLinearMap.toPMap ⊤)

/-- The real spectrum is contained in a set. -/
def SpectrumInRealSet (A : E →L[𝕜] E) (s : Set ℝ) : Prop :=
  boundedRealSpectrum A ⊆ s

/-- The two blocks satisfy the interval/exterior configuration in either orientation. -/
def IntervalExteriorGap
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (β α δ : ℝ) : Prop :=
  (SpectrumInRealSet A (Set.Icc β α) ∧
    SpectrumInRealSet B {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (SpectrumInRealSet B (Set.Icc β α) ∧
    SpectrumInRealSet A {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- Centered norm/inverse data in either interval/exterior orientation. -/
inductive CenteredIntervalExteriorWitness
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (β α δ : ℝ) : Type (max u v) where
  | intervalOnLeft
      (hA : ‖A - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 E‖ ≤ (α - β) / 2)
      (hB : BoundedInverseData
        (B - (((β + α) / 2 : ℝ) : 𝕜) •
          ContinuousLinearMap.id 𝕜 F))
      (hBnorm : ‖hB.inv‖ ≤ ((α - β) / 2 + δ)⁻¹)
  | intervalOnRight
      (hB : ‖B - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 F‖ ≤ (α - β) / 2)
      (hA : BoundedInverseData
        (A - (((β + α) / 2 : ℝ) : 𝕜) •
          ContinuousLinearMap.id 𝕜 E))
      (hAnorm : ‖hA.inv‖ ≤ ((α - β) / 2 + δ)⁻¹)
end ExactSinTheta
end DavisKahan
end TauCeti
