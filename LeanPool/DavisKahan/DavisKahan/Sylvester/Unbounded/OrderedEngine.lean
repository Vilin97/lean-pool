/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.CutoffInterface
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Replaceable ordered two-unbounded Sylvester engine

The two ordered half-line configurations are packaged behind one small record.
This leaf contains only the record and its source-facing contract, so a direct
implementation need not import the legacy unbounded Sylvester theorem.  The
compatibility implementation remains isolated in
`Experimental/InfiniteDimensional/Sylvester/OrderedEngineLegacy.lean`.
-/

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

namespace TauCeti
namespace DavisKahan
namespace Sylvester

universe v

/-- The two ordered orientations of the fully unbounded ideal-gauge Sylvester
estimate.

The hypothesis binders are `_`-prefixed because they are proof-valued and the
conclusion `N.Mem X ∧ δ * N.gauge X ≤ N.gauge C` cannot mention them; the names
are kept for documentation rather than dropped to `_`. -/
structure OrderedSylvesterEngine : Prop where
  lowerUpper :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : FanDominantIdealFamily (𝕜 := ℂ))
      {A : E →ₗ.[ℂ] E}
      {B : F →ₗ.[ℂ] F}
      (_hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (_hδ : 0 < δ)
      (_hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
      (_hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
      (_hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
      (_hC : N.Mem C),
      N.Mem X ∧
        δ * N.gauge X ≤
          N.gauge C
  upperLower :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : FanDominantIdealFamily (𝕜 := ℂ))
      {A : E →ₗ.[ℂ] E}
      {B : F →ₗ.[ℂ] F}
      (_hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (_hδ : 0 < δ)
      (_hAc : TauCeti.LinearPMap.SemiboundedAbove A c)
      (_hBc : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))
      (_hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
      (_hC : N.Mem C),
      N.Mem X ∧
        δ * N.gauge X ≤
          N.gauge C

end Sylvester
end DavisKahan
end TauCeti
