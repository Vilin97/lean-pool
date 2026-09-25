/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEulerSevenBound
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.RightInversionPairing
public import Mathlib.Tactic

/-!
# Right-inversion pairing with Euler budget seven

For bidegree `(2,2)` and Euler budget `7`, the source cube-root branch is
`3 * (56mn)^(1/3)`. Right-coordinate inversion divides the nonparabolic
support by two. The resulting root coefficient has cube

`((3/2) * 56^(1/3))^3 = 189`.

The quotient-by-characteristic coefficient remains exactly `24`.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The exact right-inversion-paired χ≤7 numerical bound. -/
def pairedEulerSevenCorvajaZannierTraceUpperBound
    (p leftOrder rightOrder : ℕ) : ℝ :=
  max
    ((3 / 2 : ℝ) *
      (56 * ((leftOrder * rightOrder : ℕ) : ℝ)) ^ ((1 : ℝ) / 3))
    (24 * (((leftOrder * rightOrder : ℕ) : ℝ) / p))

/-- The source χ≤7 bound is exactly twice the paired bound. -/
theorem
    corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_seven_eq_twice_paired
    (p leftOrder rightOrder : ℕ) :
    corvajaZannierCorollaryTwoNumericalBound
        p leftOrder rightOrder 2 2 7 =
      2 * pairedEulerSevenCorvajaZannierTraceUpperBound
        p leftOrder rightOrder := by
  let x : ℝ := ((leftOrder * rightOrder : ℕ) : ℝ)
  have horders :
      (((leftOrder * rightOrder * 2 * 2 : ℕ) : ℝ)) = 4 * x := by
    simp [x]
    ring
  unfold corvajaZannierCorollaryTwoNumericalBound
    pairedEulerSevenCorvajaZannierTraceUpperBound
  rw [horders]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show 2 * (4 * x) * 7 = 56 * x by ring]
  dsimp only [x]
  congr 1 <;> ring

/-- The weighted-trace χ≤7 theorem combined with right inversion gives the
exact nonparabolic left-support estimate whose root coefficient cubes to
`189`. -/
theorem
    weightedTraceEquationNonparabolicLeftSupport_card_cast_le_pairedEulerSeven
    (p : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta : E) (Hleft Hright : Subgroup Eˣ)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta) :
    ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta Hleft Hright).card : ℝ) ≤
      pairedEulerSevenCorvajaZannierTraceUpperBound
        p (Nat.card Hleft) (Nat.card Hright) := by
  obtain ⟨hleftPositive, hrightPositive, hleftPrime, hrightPrime⟩ :=
    multiplicativeSubgroups_satisfy_weightedTraceBoundOrderHypotheses
      p E Hleft Hright
  have hsource :=
    weightedTraceTorsionIntersection_card_cast_le_eulerSeven
      (p := p) alpha beta hadmissible
      (Nat.card Hright) (Nat.card Hleft)
      hrightPositive hleftPositive hrightPrime hleftPrime
  rw [generalTorusTorsionIntersection_weightedTrace_eq] at hsource
  have hsolutions :
      ((weightedTraceEquationSolutions alpha beta Hleft Hright).card : ℝ) ≤
        corvajaZannierCorollaryTwoNumericalBound
          p (Nat.card Hleft) (Nat.card Hright) 2 2 7 := by
    calc
      ((weightedTraceEquationSolutions alpha beta Hleft Hright).card : ℝ) ≤
          ((weightedTraceCurveTorsionIntersection alpha beta
            (Nat.card Hleft) (Nat.card Hright)).card : ℝ) := by
        exact_mod_cast
          weightedTraceEquationSolutions_card_le_curveTorsionIntersection
            alpha beta Hleft Hright
      _ ≤ corvajaZannierCorollaryTwoNumericalBound
          p (Nat.card Hright) (Nat.card Hleft) 2 2 7 := hsource
      _ = corvajaZannierCorollaryTwoNumericalBound
          p (Nat.card Hleft) (Nat.card Hright) 2 2 7 := by
        unfold corvajaZannierCorollaryTwoNumericalBound
        congr 1 <;> simp [Nat.mul_comm]
  have hpaired :
      2 * ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta Hleft Hright).card : ℝ) ≤
          ((weightedTraceEquationSolutions alpha beta Hleft Hright).card : ℝ) := by
    exact_mod_cast
      two_mul_weightedTraceEquationNonparabolicLeftSupport_card_le_solutions
        alpha beta Hleft Hright
  have htwice :
      2 * ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta Hleft Hright).card : ℝ) ≤
        2 * pairedEulerSevenCorvajaZannierTraceUpperBound
          p (Nat.card Hleft) (Nat.card Hright) := by
    calc
      2 * ((weightedTraceEquationNonparabolicLeftSupport
          alpha beta Hleft Hright).card : ℝ) ≤
          ((weightedTraceEquationSolutions
            alpha beta Hleft Hright).card : ℝ) := hpaired
      _ ≤ corvajaZannierCorollaryTwoNumericalBound
            p (Nat.card Hleft) (Nat.card Hright) 2 2 7 := hsolutions
      _ = 2 * pairedEulerSevenCorvajaZannierTraceUpperBound
            p (Nat.card Hleft) (Nat.card Hright) := by
        rw [
          corvajaZannierCorollaryTwoNumericalBound_bidegree_two_euler_seven_eq_twice_paired]
  nlinarith

end

end BGS.Markoff
