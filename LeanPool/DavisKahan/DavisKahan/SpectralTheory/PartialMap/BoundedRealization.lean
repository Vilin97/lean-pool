/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Bounded realizations of closed operators

A closed operator whose domain is the whole space is the restriction of a
bounded operator.  `BoundedRealization` packages that bounded operator together
with the domain identity and the agreement statement.

This file is deliberately independent of the spectral hypotheses that usually
produce such a realization: the structure is pure bookkeeping, so it belongs
with the closed-operator basics rather than with any particular criterion.
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

/-- Bounded realization of a closed operator on its full domain. -/
structure BoundedRealization
    (A : E →ₗ.[𝕜] E) where
  /-- The bounded ambient operator agreeing with the everywhere-defined partial map. -/
  operator : E →L[𝕜] E
  domain_eq_top : A.domain = ⊤
  agrees : ∀ x : A.domain, operator (x : E) = A x

end ExactSinTheta
end DavisKahan
end TauCeti
