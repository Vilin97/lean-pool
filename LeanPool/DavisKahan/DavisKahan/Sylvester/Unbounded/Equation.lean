/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# The one-unbounded Sylvester equation

This is not a second equation model.  It is the closed Sylvester equation of
`DavisKahan.Sylvester.ClosedSylvesterEquation` with the right block embedded as
a full-domain closed operator, so every lemma about the closed equation applies
verbatim.
-/

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Equation with one unbounded left block and one bounded right block.

This is not a second equation model: it is the closed Sylvester equation with
the right block embedded as a full-domain closed operator. -/
abbrev HasUnboundedBoundedSylvesterEquation
    (A : E →ₗ.[𝕜] E)
    (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  TauCeti.LinearPMap.UnboundedBoundedSylvesterEquation A B X C

end Sylvester
end DavisKahan
end TauCeti
