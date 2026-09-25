/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Closed Sylvester equations and everywhere-bounded inverses

The proved front of the unbounded spectral development: the closed Sylvester
equation interface, closed resolvent data, and everywhere-defined bounded
inverses.  The spectral projection and truncation theory that is still open
stays in `DavisKahan.InfiniteDimensional.Core.UnboundedSpectral`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]


namespace SylvesterEquation

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rewrite the Sylvester equation with an arbitrary output-domain witness.
Proof irrelevance identifies it with the witness the equation stores. -/
theorem equation_of_mem
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (h : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (x : B.domain) (hx : X (x : F) ∈ A.domain) :
    A ⟨X (x : F), hx⟩ - X (B x) = C (x : F) := by
  have heq := h.equation x
  have harg :
      (⟨X (x : F), hx⟩ : A.domain) =
        ⟨X (x : F), h.mapsTo_domain x⟩ := by
    apply Subtype.ext
    rfl
  rw [harg]
  exact heq

end SylvesterEquation

end Sylvester
end DavisKahan
end TauCeti
