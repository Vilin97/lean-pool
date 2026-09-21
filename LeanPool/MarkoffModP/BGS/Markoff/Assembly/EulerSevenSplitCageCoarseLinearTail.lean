/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.CoarseLinearTail
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenSplitCageSquareEnvelopeSurjectivity

/-!
# Euler-seven split-cage frontier with automatic linear tail

Above `24^15 * 2^687`, the tenth-moment estimate discharges the full linear
middle-game family.  Only the square-envelope cube obstruction remains.
-/

namespace BGS.Markoff

open BGS.NumberTheory

/-- Split-cage transitivity with no separate linear-table hypothesis. -/
theorem
    puncturedMarkoffTransitiveAt_of_splitCage_eulerSevenSquareEnvelope_coarseLinearTail
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (hpLinearTail : 24 ^ 15 * 2 ^ 687 < p)
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
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  apply
    puncturedMarkoffTransitiveAt_of_splitCage_nonparabolicComplement_eulerSevenPairedMaximalDivisor_frontier
      p hpSeven c hbase hhalfThreshold
  · intro d _hd hcount
    by_contra hnot
    have hdegree :
        d ≤ 189 * maximalDivisorCountSum p (d + 1) ^ 3 :=
      Nat.le_of_not_gt hnot
    have hbad :
        8 * p ≤ 35721 * squareEnvelope d ^ 4 :=
      eight_mul_le_35721_mul_fourth_of_count_degree_squareEnvelope
        hcount hdegree (hsquare d)
    exact (Nat.not_le_of_lt (hglobal d)) hbad
  · intro d hd
    exact maximalDivisorCountSum_linear_lt_of_coarseBound hpLinearTail hd
  · exact hlarge

/-- Natural Markoff reduction surjectivity with the same automatic linear
tail and no separate linear-table hypothesis. -/
theorem
    markoffReduction_surjective_of_splitCage_eulerSevenSquareEnvelope_coarseLinearTail
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (hpLinearTail : 24 ^ 15 * 2 ^ 687 < p)
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
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    Function.Surjective (markoffReduction p) :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective
      p Fact.out).mp
    (puncturedMarkoffTransitiveAt_of_splitCage_eulerSevenSquareEnvelope_coarseLinearTail
      p hpSeven hpLinearTail c hbase hhalfThreshold
      squareEnvelope hsquare hglobal hlarge)

end BGS.Markoff
