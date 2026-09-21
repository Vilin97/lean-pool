/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MaximalDivisorPuncturedTransitivity
import LeanPool.MarkoffModP.BGS.NumberTheory.JointMaximalDivisorCriterion

/-!
# Root-free joint maximal-divisor frontier

The improved arithmetic naturally controls the square of the sum of the two
maximal-divisor counts.  This module keeps that square envelope intact instead
of taking an integer square root and losing information.
-/

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

private def jointNormalizedPuncturedPoint
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

/-- A square envelope converts a root-free sixth-power comparison into the
cube inequality required by the middle game. -/
theorem coefficient_mul_count_cube_lt_of_squareEnvelope
    {coefficient count envelope order : ℕ}
    (hsquare : count ^ 2 ≤ envelope)
    (hstrict : coefficient ^ 6 * envelope ^ 3 < order ^ 2) :
    (coefficient * count) ^ 3 < order := by
  have hpower :
      ((coefficient * count) ^ 3) ^ 2 ≤
        coefficient ^ 6 * envelope ^ 3 := by
    calc
      ((coefficient * count) ^ 3) ^ 2 =
          coefficient ^ 6 * (count ^ 2) ^ 3 := by ring
      _ ≤ coefficient ^ 6 * envelope ^ 3 := by gcongr
  by_contra hnot
  have hreverse : order ≤ (coefficient * count) ^ 3 :=
    Nat.le_of_not_gt hnot
  have hreverseSq :
      order ^ 2 ≤ ((coefficient * count) ^ 3) ^ 2 :=
    Nat.pow_le_pow_left hreverse 2
  exact (Nat.not_le_of_lt (hpower.trans_lt hstrict)) hreverseSq

/-- A square envelope also converts the linear middle-game comparison into a
root-free quadratic comparison. -/
theorem coefficient_mul_count_mul_order_lt_of_squareEnvelope
    {coefficient count envelope order p : ℕ}
    (hsquare : count ^ 2 ≤ envelope)
    (hstrict :
      coefficient ^ 2 * envelope * order ^ 2 < p ^ 2) :
    coefficient * count * order < p := by
  have hpower :
      (coefficient * count * order) ^ 2 ≤
        coefficient ^ 2 * envelope * order ^ 2 := by
    calc
      (coefficient * count * order) ^ 2 =
          coefficient ^ 2 * count ^ 2 * order ^ 2 := by ring
      _ ≤ coefficient ^ 2 * envelope * order ^ 2 := by gcongr
  by_contra hnot
  have hreverse : p ≤ coefficient * count * order :=
    Nat.le_of_not_gt hnot
  have hreverseSq :
      p ^ 2 ≤ (coefficient * count * order) ^ 2 :=
    Nat.pow_le_pow_left hreverse 2
  exact (Nat.not_le_of_lt (hpower.trans_lt hstrict)) hreverseSq

/-- Punctured transitivity from a square envelope for the two neighboring
maximal-divisor counts.  Both numerical hypotheses are polynomial
inequalities over natural numbers. -/
theorem puncturedMarkoffTransitiveAt_of_jointSquareEnvelope_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (squareEnvelope : ℕ → ℕ)
    (hsquare : ∀ d : ℕ,
      (maximalDivisorCountSum p (d + 1)) ^ 2 ≤ squareEnvelope d)
    (hcube : ∀ d : ℕ, 0 < d →
      p ≤ 2 * (2 + d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      corvajaZannierCorollaryTwoSafeCoefficient ^ 6 *
          (squareEnvelope d) ^ 3 < d ^ 2)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      corvajaZannierCorollaryTwoSafeCoefficient ^ 2 *
          squareEnvelope d * d ^ 2 < p ^ 2)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (jointNormalizedPuncturedPoint c) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  apply puncturedMarkoffTransitiveAt_of_maximalDivisor_frontier
    p hpThree c
  · intro d hd hpLow
    exact coefficient_mul_count_cube_lt_of_squareEnvelope
      (hsquare d) (hcube d hd hpLow)
  · intro d hd
    exact coefficient_mul_count_mul_order_lt_of_squareEnvelope
      (hsquare d) (hlinear d hd)
  · intro z hz
    exact hlarge z hz

/-- Specialization of the square-envelope frontier to the new
`C^2 + 3J` bound. -/
theorem puncturedMarkoffTransitiveAt_of_jointMaximalDivisorBounds
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (central productEnvelope : ℕ → ℕ)
    (hminus : ∀ d : ℕ,
      (maximalDivisorsBelow (p - 1) (d + 1)).card ≤ central d)
    (hplus : ∀ d : ℕ,
      (maximalDivisorsBelow (p + 1) (d + 1)).card ≤ central d)
    (hproduct : ∀ d : ℕ,
      (maximalDivisorsBelow (p - 1) (d + 1)).card *
          (maximalDivisorsBelow (p + 1) (d + 1)).card ≤
        productEnvelope d)
    (hcube : ∀ d : ℕ, 0 < d →
      p ≤ 2 * (2 + d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      corvajaZannierCorollaryTwoSafeCoefficient ^ 6 *
          (central d ^ 2 + 3 * productEnvelope d) ^ 3 < d ^ 2)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      corvajaZannierCorollaryTwoSafeCoefficient ^ 2 *
          (central d ^ 2 + 3 * productEnvelope d) * d ^ 2 < p ^ 2)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (jointNormalizedPuncturedPoint c) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  apply puncturedMarkoffTransitiveAt_of_jointSquareEnvelope_frontier
    p hpThree c (fun d ↦ central d ^ 2 + 3 * productEnvelope d)
  · intro d
    simpa [maximalDivisorCountSum] using
      maximalDivisorCounts_add_sq_le
        (hminus d) (hplus d) (hproduct d)
  · exact hcube
  · exact hlinear
  · exact hlarge

end

end BGS.Markoff
