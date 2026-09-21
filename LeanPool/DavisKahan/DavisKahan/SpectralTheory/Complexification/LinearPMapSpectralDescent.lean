/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Complexification.SpectralDescent
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace

/-!
# Complexification of real `LinearPMap` spectral ranges

The operator-theory layer in `ForTauCeti` descends the canonical Cayley spectral
projection of a complexified real self-adjoint `LinearPMap` to a real spectral
range.  This file connects that operator-level construction to the Davis--Kahan
subspace-complexification API.

The main theorem says that complexifying the descended real spectral range gives
exactly the canonical complex spectral range.  This is the representation bridge
needed by real perturbation theorems that reuse complex subspace geometry.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

open scoped InnerProductSpace
open TauCeti.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Complexification of the canonical real spectral range agrees exactly with
the canonical complex spectral range of the complexified partial map. -/
theorem complexifySubmodule_realSpecRange
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    complexifySubmodule (TauCeti.LinearPMap.realSpecRange hA S hS) =
      TauCeti.LinearPMap.specRange
        (TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA) S hS := by
  ext z
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [starProjection_complexifySubmodule,
    ← TauCeti.LinearPMap.realSpecProjection_eq_starProjection,
    TauCeti.LinearPMap.complexify_realSpecProjection,
    ← TauCeti.LinearPMap.specProjection_eq_starProjection_specRange]

end

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
