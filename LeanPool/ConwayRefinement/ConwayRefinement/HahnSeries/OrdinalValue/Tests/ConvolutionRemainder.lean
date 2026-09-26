/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ConvolutionRemainder

/-!
# API check for the convolution remainder

The paper uses the estimate for actual translated truncation series. The underlying proof first
establishes a germ-valued inequality, so it would be easy to expose only that nearby but weaker
interface. This check pins the public result to `ordinalValue` of the displayed series remainder and
to one left neighbourhood uniform in the cutoff.
-/

public noncomputable section

namespace Tests

open HahnSeries HahnSeries.Nonpositive Berarducci

universe v

variable {K : Type v} [Field K]

/-- The remainder estimate holds for the translated truncation series, uniformly for every
cutoff in one left neighbourhood of zero. -/
theorem convolutionRemainder_actualSeries
    (b c : SeriesWithOrdinalValueAboveOne K)
    (hp : b.principalValue ≤ c.principalValue) :
    ∃ eta < (0 : ℝ), ∀ gamma : ℝ, eta < gamma → gamma < 0 →
      ordinalValue
          (translatedTruncation (((b.1 * c.1 : Series K) : K⟦ℝ⟧)) gamma
            - translatedTruncation (b.1 : K⟦ℝ⟧) gamma * c.1
            - b.1 * translatedTruncation (c.1 : K⟦ℝ⟧) gamma) <
        b.residualValue * ordinalValue c.1 :=
  exists_ordinalValue_convolution_remainder_lt b c hp

end Tests
