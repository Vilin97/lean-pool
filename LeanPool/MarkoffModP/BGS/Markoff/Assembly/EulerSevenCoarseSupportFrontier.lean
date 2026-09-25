/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.CoarseEndgame
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenSplitCageCoarseLinearTail

/-!
# Euler-seven frontier with all support tails discharged

At `2^756 < p`, the simultaneous tenth-moment estimate now supplies the
linear middle game, primitive endgame, cage connectivity, split-cage base,
and half-order comparison.  The only remaining arithmetic certificate is a
square envelope for the joint maximal-divisor count together with its exact
Euler-seven cubic inequality.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- Punctured transitivity above the unified support cutoff.  All non-cubic
arithmetic and all endgame/cage hypotheses have been discharged. -/
theorem
    puncturedMarkoffTransitiveAt_of_eulerSevenSquareEnvelope_coarseSupport
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSupport : 2 ^ 756 < p)
    (squareEnvelope : ℕ → ℕ)
    (hcount : ∀ d : ℕ,
      maximalDivisorCountSum p (d + 1) ^ 2 ≤ squareEnvelope d)
    (hcubic : ∀ d : ℕ,
      35721 * squareEnvelope d ^ 4 < 8 * p) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  have hpSeven : 7 ≤ p := seven_le_of_twoPow756_lt hpSupport
  obtain ⟨baseNormalized, hbaseCage⟩ :=
    exists_normalizedPunctured_splitCagePoint p hpSeven
  let base : PuncturedMarkoffSurface (ZMod p) :=
    (puncturedNormalizationEquiv (ZMod p)).symm baseNormalized
  apply
    puncturedMarkoffTransitiveAt_of_splitCage_eulerSevenSquareEnvelope_coarseLinearTail
      p hpSeven (twentyFour_support_margin.trans hpSupport)
      base ?_ (coarse_halfOrderThreshold hpSupport)
      squareEnvelope hcount hcubic
  · intro z hzLarge
    have hcoordinate :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u1 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u2 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u3 := by
      by_contra hsmall
      push Not at hsmall
      have hmaxSmall : (maximalCoordinateRotationOrder z.1 : ℝ) <
          (p : ℝ) ^ (5 / 6 : ℝ) := by
        rw [maximalCoordinateRotationOrder, Nat.cast_max, Nat.cast_max]
        exact max_lt hsmall.1 (max_lt hsmall.2.1 hsmall.2.2)
      exact (not_lt_of_ge hzLarge) hmaxSmall
    have hcomponent :=
      coarse_sameNormalizedComponent_of_largeOrder_to_splitCage
        hpSupport (normalizedSurfaceOfPunctured baseNormalized)
        z hbaseCage hcoordinate
    simpa [base] using hcomponent
  · simpa [base] using hbaseCage

/-- Natural Markoff reduction is surjective under the same support-closed
Euler-seven square-envelope certificate. -/
theorem
    markoffReduction_surjective_of_eulerSevenSquareEnvelope_coarseSupport
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSupport : 2 ^ 756 < p)
    (squareEnvelope : ℕ → ℕ)
    (hcount : ∀ d : ℕ,
      maximalDivisorCountSum p (d + 1) ^ 2 ≤ squareEnvelope d)
    (hcubic : ∀ d : ℕ,
      35721 * squareEnvelope d ^ 4 < 8 * p) :
    Function.Surjective (markoffReduction p) :=
  (puncturedMarkoffTransitiveAt_iff_markoffReduction_surjective
      p Fact.out).mp
    (puncturedMarkoffTransitiveAt_of_eulerSevenSquareEnvelope_coarseSupport
      p hpSupport squareEnvelope hcount hcubic)

end

end BGS.Markoff
