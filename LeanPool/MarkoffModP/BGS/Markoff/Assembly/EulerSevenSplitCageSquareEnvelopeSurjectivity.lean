/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenSplitCageSquareEnvelopeFrontier
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.TransitivitySurjectivity

/-!
# Euler-seven square-envelope reduction surjectivity

This separate façade converts the exact split-cage transitivity endpoint to
surjectivity of natural Markoff reduction using the canonical equivalence.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

/-- Natural Markoff reduction is surjective under the exact Euler-seven
split-cage square-envelope hypotheses. -/
theorem
    markoffReduction_surjective_of_splitCage_eulerSevenSquareEnvelope_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p
      (normalizedSurfaceOfPunctured
        (puncturedNormalizationEquiv (ZMod p) c)))
    (hhalfThreshold :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ))
    (squareEnvelope : ℕ → ℕ)
    (hsquare : ∀ d : ℕ,
      maximalDivisorCountSum p (d + 1) ^ 2 ≤ squareEnvelope d)
    (hglobal : ∀ d : ℕ,
      35721 * squareEnvelope d ^ 4 < 8 * p)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 ^ 2 * squareEnvelope d * d ^ 2 < p ^ 2)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    Function.Surjective (markoffReduction p) :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective
      p Fact.out).mp
    (puncturedMarkoffTransitiveAt_of_splitCage_eulerSevenSquareEnvelope_frontier
      p hpSeven c hbase hhalfThreshold squareEnvelope
      hsquare hglobal hlinear hlarge)

end BGS.Markoff
