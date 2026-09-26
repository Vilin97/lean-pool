/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEulerSevenLargeBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.ElementaryFiniteFieldBound
public import Mathlib.Tactic

/-!
# The exact Euler-seven weighted trace bound

Above the elementary range this is the χ≤7 Proposition Two endpoint. Below
that range the roots-of-unity count lands directly in the unchanged
quotient-by-characteristic branch.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The χ≤7 weighted trace estimate in every characteristic. -/
theorem weightedTraceTorsionIntersection_card_cast_le_eulerSeven
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n) :
    ((BGS.External.torusCurveTorsionIntersection K
        (weightedTraceTorusClosurePolynomial alpha beta) m n).card : ℝ) ≤
      corvajaZannierCorollaryTwoNumericalBound p m n 2 2 7 := by
  by_cases hlarge : 48 < p
  · exact
      weightedTraceTorsionIntersection_card_cast_le_eulerSeven_of_largeChar
        alpha beta hadmissible m n hm hn hmPrime hnPrime hlarge
  · have hsmall : p ≤ 48 := Nat.le_of_not_gt hlarge
    have hcardNat :=
      BGS.External.torusCurveTorsionIntersection_card_le_orders
        (weightedTraceTorusClosurePolynomial alpha beta) m n hm hn
    have hcardReal :
        ((BGS.External.torusCurveTorsionIntersection K
          (weightedTraceTorusClosurePolynomial alpha beta) m n).card : ℝ) ≤
            ((m * n : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    have hpReal : (0 : ℝ) < p := by
      exact_mod_cast (Fact.out : p.Prime).pos
    have hscaledNat : p * (m * n) ≤ 48 * (m * n) :=
      Nat.mul_le_mul_right (m * n) hsmall
    have hscaledReal :
        (p : ℝ) * ((m * n : ℕ) : ℝ) ≤
          48 * ((m * n : ℕ) : ℝ) := by
      exact_mod_cast hscaledNat
    have hquotient :
        ((m * n : ℕ) : ℝ) ≤
          48 * ((m * n : ℕ) : ℝ) / (p : ℝ) := by
      apply (le_div_iff₀ hpReal).2
      simpa [mul_comm] using hscaledReal
    have hright :
        48 * ((m * n : ℕ) : ℝ) / (p : ℝ) =
          12 * ((m * n * 2 * 2 : ℕ) : ℝ) / (p : ℝ) := by
      push_cast
      ring
    unfold corvajaZannierCorollaryTwoNumericalBound
    calc
      ((BGS.External.torusCurveTorsionIntersection K
          (weightedTraceTorusClosurePolynomial alpha beta) m n).card : ℝ)
          ≤ ((m * n : ℕ) : ℝ) := hcardReal
      _ ≤ 48 * ((m * n : ℕ) : ℝ) / (p : ℝ) := hquotient
      _ = 12 * ((m * n * 2 * 2 : ℕ) : ℝ) / (p : ℝ) := hright
      _ ≤ max
          (3 * (2 * ((m * n * 2 * 2 : ℕ) : ℝ) * 7) ^
            ((1 : ℝ) / 3))
          (12 * ((m * n * 2 * 2 : ℕ) : ℝ) / (p : ℝ)) :=
        le_max_right _ _

end

end BGS.Markoff
