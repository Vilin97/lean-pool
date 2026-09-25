/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.RightInversionPairing

/-!
# The sharp Corvaja--Zannier bound after right-inversion pairing

The unconditional general plane-curve theorem specializes at bidegree `(2, 2)`
to Euler-characteristic bound `8`.  Its two numerical branches are

* `12 * (leftOrder * rightOrder)^(1/3)`, and
* `48 * leftOrder * rightOrder / p`.

Right-coordinate inversion pairs all solutions whose right coordinate is not
two-torsion.  Dividing the exact source bound by two therefore gives
coefficients `6` and `24` for the nonparabolic left support.

No genus-one or Euler-characteristic-`3` assertion is used here.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The exact coefficient improvement obtained by pairing the two
right-coordinate inverses before taking the left support. -/
def pairedCorvajaZannierTraceUpperBound
    (p leftOrder rightOrder : ℕ) : ℝ :=
  max
    (6 * (((leftOrder * rightOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)))
    (24 * (((leftOrder * rightOrder : ℕ) : ℝ) / p))

private lemma sixtyFour_rpow_one_third_eq_four :
    (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
  rw [show (64 : ℝ) = 4 ^ (3 : ℕ) by norm_num]
  convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (3 : ℕ) ≠ 0) using 1
  all_goals norm_num

/-- At bidegree `(2,2)` and the unconditional Euler bound `8`, the
source-faithful Corvaja--Zannier right-hand side is exactly twice the paired
bound.  Keeping this equality explicit prevents the cube-root branch from
being weakened to the older coefficient-`48` envelope before pairing. -/
theorem corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_eq_twice_paired
    (p leftOrder rightOrder : ℕ) :
    corvajaZannierCorollaryTwoNumericalBound
        p leftOrder rightOrder 2 2 8 =
      2 * pairedCorvajaZannierTraceUpperBound
        p leftOrder rightOrder := by
  let x : ℝ := ((leftOrder * rightOrder : ℕ) : ℝ)
  have hx : 0 ≤ x := by positivity
  unfold corvajaZannierCorollaryTwoNumericalBound
    pairedCorvajaZannierTraceUpperBound
  have horders :
      (((leftOrder * rightOrder * 2 * 2 : ℕ) : ℝ)) = 4 * x := by
    simp [x]
    ring
  rw [horders]
  rw [show 2 * (4 * x) * 8 = (64 : ℝ) * x by ring]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) hx,
    sixtyFour_rpow_one_third_eq_four]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1 <;> ring

/-- The unconditional bidegree-`(2,2)`, Euler-bound-`8`
Corvaja--Zannier theorem, combined with right inversion, gives the sharp
nonparabolic left-support estimate

`max (6 * (|H₁| |H₂|)^(1/3), 24 * |H₁| |H₂| / p)`.
-/
theorem weightedTraceEquationNonparabolicLeftSupport_card_cast_le_pairedCorvajaZannier
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta) :
    ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta H₁ H₂).card : ℝ) ≤
      pairedCorvajaZannierTraceUpperBound
        p (Nat.card H₁) (Nat.card H₂) := by
  obtain ⟨hleftPositive, hrightPositive, hleftPrime, hrightPrime⟩ :=
    multiplicativeSubgroups_satisfy_weightedTraceBoundOrderHypotheses
      p E H₁ H₂
  have hsource :=
    BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem
      p E (weightedTraceTorusClosurePolynomial alpha beta)
      2 2 (Nat.card H₂) (Nat.card H₁)
      (by norm_num) (by norm_num)
      (weightedTraceTorusClosurePolynomial_hasBidegreeAtMost
        alpha beta hadmissible.2.1)
      (weightedTraceCurve_isGeneralCorvajaZannierPlaneCurve
        alpha beta hadmissible)
      hrightPositive hleftPositive hrightPrime hleftPrime
  rw [generalTorusTorsionIntersection_weightedTrace_eq] at hsource
  rw [show BGS.External.planeTorusEulerCharacteristicBound 2 2 = 8 by
    norm_num [BGS.External.planeTorusEulerCharacteristicBound]] at hsource
  have hsolutions :
      ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) ≤
        corvajaZannierCorollaryTwoNumericalBound
          p (Nat.card H₂) (Nat.card H₁) 2 2 8 := by
    calc
      ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) ≤
          ((weightedTraceCurveTorsionIntersection alpha beta
            (Nat.card H₁) (Nat.card H₂)).card : ℝ) := by
        exact_mod_cast
          weightedTraceEquationSolutions_card_le_curveTorsionIntersection
            alpha beta H₁ H₂
      _ ≤ corvajaZannierCorollaryTwoNumericalBound
            p (Nat.card H₂) (Nat.card H₁) 2 2 8 := hsource
  have hpaired :
      2 * ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta H₁ H₂).card : ℝ) ≤
          ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) := by
    exact_mod_cast
      two_mul_weightedTraceEquationNonparabolicLeftSupport_card_le_solutions
        alpha beta H₁ H₂
  have htwice :
      2 * ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta H₁ H₂).card : ℝ) ≤
        2 * pairedCorvajaZannierTraceUpperBound
          p (Nat.card H₁) (Nat.card H₂) := by
    calc
      2 * ((weightedTraceEquationNonparabolicLeftSupport
          alpha beta H₁ H₂).card : ℝ) ≤
          ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) :=
        hpaired
      _ ≤ corvajaZannierCorollaryTwoNumericalBound
            p (Nat.card H₂) (Nat.card H₁) 2 2 8 := hsolutions
      _ = 2 * pairedCorvajaZannierTraceUpperBound
            p (Nat.card H₁) (Nat.card H₂) := by
        rw [
          corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_eight_eq_twice_paired]
        unfold pairedCorvajaZannierTraceUpperBound
        congr 1 <;> simp [Nat.mul_comm]
  nlinarith

end

end BGS.Markoff
