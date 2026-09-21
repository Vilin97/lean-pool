/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.Core
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal

/-!
# Strong cutoffs and finite Ky Fan gauges over real Hilbert spaces

The real forms of cutoff convergence and of the infinite-dimensional Ky Fan triangle
inequality:

* `approximationSingularValue_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_add_le_real`.

Until 2026-07-28 each of these was proved here from scratch, and each proof was its complex
counterpart in `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean` with `ℂ` replaced by
`ℝ` — the same span, the same `Σ n : Fin k, Fin (n.1 + 1)` index type, the same three-step
`calc`.  Neither argument uses the field.

What does use the field is one fact: strictly below every approximation number there is a
strictly larger uniform lower modulus on an `(n+1)`-dimensional subspace.  Over `ℂ` that is
the min--max theorem, proved from the continuous functional calculus on `T.modulus`; over `ℝ`
it is `Threshold.lean`'s transport through the complexification, which is a genuinely
different proof and stays.  It is now isolated as
`ContinuousLinearMap.HasMinMaxLowerBound`, everything above it is stated once against that
predicate, and this module is what remains: three instantiations at
`TauCeti.ApproximationNumber.hasMinMaxLowerBound_real`.
-/

open scoped InnerProductSpace Topology

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace ApproximationNumbersReal

open Filter

noncomputable section

universe v vF w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Real-Hilbert-space cutoff convergence for approximation singular values. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    TauCeti.ApproximationNumber.hasMinMaxLowerBound_real hPproj hP n K

/-- Real-Hilbert-space cutoff convergence for finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (k : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    TauCeti.ApproximationNumber.hasMinMaxLowerBound_real hPproj hP k K

/-- **The real infinite-dimensional Ky Fan triangle inequality.**  No compactness and no
finite-dimensionality; the only real-specific input is `TauCeti.ApproximationNumber.hasMinMaxLowerBound_real`. -/
theorem kyFanApproximationGauge_add_le_real
    (k : ℕ) (K L : E →L[ℝ] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  kyFanApproximationGauge_add_le_of_minMax TauCeti.ApproximationNumber.hasMinMaxLowerBound_real k K L

end

end ApproximationNumbersReal
end ExactSinTheta
end DavisKahan
end TauCeti
