/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenSplitCageNonparabolicComplementFrontier
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.JointMaximalDivisorFrontier
public import LeanPool.MarkoffModP.BGS.NumberTheory.NonparabolicComplementCriterion

/-!
# Root-free Euler-seven split-cage square-envelope frontier

For `M = maximalDivisorCountSum p (d + 1)`, a certificate `M^2 ≤ S`
reduces the exact Euler-seven cube branch to

`35721 * S^4 < 8 * p`,

because `35721 = 189^2`.  The linear branch is independently reduced to

`24^2 * S * d^2 < p^2`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- The exact Euler-seven split-cage endpoint in root-free square-envelope
form.  The split-cage base, half-threshold comparison, and large-order orbit
bridge remain explicit inputs. -/
theorem
    puncturedMarkoffTransitiveAt_of_splitCage_eulerSevenSquareEnvelope_frontier
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
    exact
      coefficient_mul_count_mul_order_lt_of_squareEnvelope
        (coefficient := 24)
        (count := maximalDivisorCountSum p (d + 1))
        (envelope := squareEnvelope d)
        (order := d) (p := p)
        (hsquare d) (hlinear d hd)
  · exact hlarge

end

end BGS.Markoff
