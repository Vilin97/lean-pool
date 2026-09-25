/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# Interfaces for spectral cutoffs and bounded truncations

These two records say what a spectral cutoff and a bounded truncation must
provide, without saying how to build one.  Keeping the interface apart from any
particular construction is what let a second implementation be supplied while the
legacy construction remained an open obligation; the implementation that did so
came from the vendored Spectra package, retired on 2026-07-29, and the native
spectral calculus supplies it now.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace Topology
open Filter


universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The exact projection, domain, commutation, and strong-convergence laws
needed from a spectral cutoff family. -/
structure SpectralCutoffInterface
    (A : E →ₗ.[𝕜] E) (hA : IsSelfAdjoint A) where
  /-- The family of orthogonal spectral cutoffs preserving the operator domain. -/
  cutoff : ℝ → E →L[𝕜] E
  isOrthogonalProjection : ∀ τ,
    cutoff τ ∘L cutoff τ = cutoff τ ∧ (cutoff τ).IsSymmetric
  range_le_domain : ∀ τ, LinearMap.range (cutoff τ).toLinearMap ≤ A.domain
  commutes_on_domain : ∀ τ (x : A.domain),
    ∃ hx : cutoff τ (x : E) ∈ A.domain,
      A ⟨cutoff τ (x : E), hx⟩ = cutoff τ (A x)
  tendsto_identity : ∀ x,
    Tendsto (fun τ : ℝ => cutoff τ x) atTop (𝓝 x)

/-- The bounded truncation laws needed after a cutoff family has been chosen. -/
structure BoundedTruncationInterface
    (A : E →ₗ.[𝕜] E) (hA : IsSelfAdjoint A)
    (P : SpectralCutoffInterface A hA) where
  /-- The bounded symmetric truncations agreeing with the operator on each cutoff range. -/
  truncation : ℝ → E →L[𝕜] E
  isSymmetric : ∀ τ, (truncation τ).IsSymmetric
  eq_on_cutoff : ∀ τ x,
    ∃ hx : P.cutoff τ x ∈ A.domain,
      truncation τ x = A ⟨P.cutoff τ x, hx⟩
  tendsto_on_domain : ∀ x : A.domain,
    Tendsto (fun τ : ℝ => truncation τ (x : E)) atTop
      (𝓝 (A x))
  lowerBound : ∀ {c : ℝ}, TauCeti.LinearPMap.SemiboundedBelow A c →
    ∀ {τ : ℝ}, 0 ≤ τ → ∀ x,
      c * ‖P.cutoff τ x‖ ^ 2 ≤
        RCLike.re ⟪truncation τ x, P.cutoff τ x⟫_𝕜
  upperBound : ∀ {c : ℝ}, TauCeti.LinearPMap.SemiboundedAbove A c →
    ∀ {τ : ℝ}, 0 ≤ τ → ∀ x,
      RCLike.re ⟪truncation τ x, P.cutoff τ x⟫_𝕜 ≤
        c * ‖P.cutoff τ x‖ ^ 2
  commutes_cutoff : ∀ τ,
    truncation τ ∘L P.cutoff τ = truncation τ ∧
      P.cutoff τ ∘L truncation τ = truncation τ

end Sylvester
end DavisKahan
end TauCeti
