/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierSeparability
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierSourceBound

/-!
# The weighted-trace torsion-intersection bound

This module records the exact numerical statement consumed by the Markoff middle game.  The
statement is intentionally independent of how the estimate is proved, so low-level escape lemmas
do not import the full general Corvaja--Zannier development.

The bound is uniform in the two weights and the two torsion orders.  Its hypotheses expose the
actual curve admissibility, positivity, and prime-to-characteristic requirements.  The completed
producer `corvajaZannierWeightedTraceBound` supplies this statement from the in-repository general
Corvaja--Zannier theorem.

The conclusion is the safe coefficient-`48` envelope used by the downstream middle game.  This
permits the genuine degree-only Euler bound `χ ≤ 8` for a general bidegree-`(2,2)` torus curve; no
unsupported genus-one identification is built into the interface.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The numerical weighted-trace torsion-intersection statement used by the middle game.

This is a lightweight internal proof boundary, not an external assumption.  The selected BGS path
constructs it with `corvajaZannierWeightedTraceBound`. -/
def WeightedTraceTorsionIntersectionBound
    (p : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Fintype E] [CharP E p] : Prop :=
  ∀ (alpha beta : E) (leftOrder rightOrder : ℕ),
    WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta →
      0 < leftOrder →
        0 < rightOrder →
          ¬ p ∣ leftOrder →
            ¬ p ∣ rightOrder →
              ((weightedTraceCurveTorsionIntersection alpha beta
                leftOrder rightOrder).card : ℝ) ≤
                  corvajaZannierTraceUpperBound p leftOrder rightOrder

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Fintype E] [CharP E p]

/-- Multiplicative subgroup orders satisfy every arithmetic side condition in the weighted-trace
torsion-intersection bound. -/
theorem multiplicativeSubgroups_satisfy_weightedTraceBoundOrderHypotheses
    (H₁ H₂ : Subgroup Eˣ) :
    0 < Nat.card H₁ ∧ 0 < Nat.card H₂ ∧
      ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ := by
  refine ⟨Nat.card_pos, Nat.card_pos, ?_⟩
  exact weightedTraceCurveTorsionIntersection_orders_primeToCharacteristic p H₁ H₂

/-- Apply the weighted-trace torsion-intersection bound after Lean has proved the concrete curve is
admissible and both subgroup orders satisfy the source's arithmetic hypotheses. -/
theorem weightedTraceEquationSolutions_card_cast_le_of_weightedTraceBound
    (hBound : WeightedTraceTorsionIntersectionBound p E)
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta) :
    ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) ≤
      corvajaZannierTraceUpperBound p (Nat.card H₁) (Nat.card H₂) := by
  have hfinite :
      ((weightedTraceEquationSolutions alpha beta H₁ H₂).card : ℝ) ≤
        ((weightedTraceCurveTorsionIntersection alpha beta
          (Nat.card H₁) (Nat.card H₂)).card : ℝ) := by
    exact_mod_cast weightedTraceEquationSolutions_card_le_curveTorsionIntersection
      alpha beta H₁ H₂
  obtain ⟨hleftPositive, hrightPositive, hleftPrime, hrightPrime⟩ :=
    multiplicativeSubgroups_satisfy_weightedTraceBoundOrderHypotheses p E H₁ H₂
  have hsource := hBound alpha beta (Nat.card H₁) (Nat.card H₂)
    hadmissible hleftPositive hrightPositive hleftPrime hrightPrime
  exact hfinite.trans hsource

end

end BGS.Markoff
