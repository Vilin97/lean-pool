/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import LeanPool.Erdos1196.Markov

/-!
# Rewriting the primitive weight using visit probabilities

This file records the exact algebraic bridge from the explicit visit-probability formula
`v_x(n) = 1 / (B_x n log n)` to the weighted series identity
`f(A) = B_x * ∑_{n ∈ A} v_x(n)`, and packages the final deterministic reduction from a
summable hit series to the logarithmic-series bound.

## Main statements

* `summable_indicatorLogSeries_and_tsum_le_of_hitMass`
-/

open scoped BigOperators

namespace PrimitiveSetsAboveX

/-- If the visit-probability series on `A` is summable and has total mass at most `1`, then the
logarithmic series on `A` is summable as well, and the normalization estimate converts this into
the final upper bound for `∑_{n ∈ A} 1 / (n log n)`. -/
theorem summable_indicatorLogSeries_and_tsum_le_of_hitMass
    {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x) {A : Set ℕ} (hA : A ⊆ Set.Ici x)
    (hB : 0 < normalizationConstant x Y)
    (hHitSummable : Summable (A.indicator (chain.visitProbability)))
    (hHit : (∑' n : ℕ, A.indicator (chain.visitProbability) n) ≤ 1)
    {C : ℝ} (hNorm : |normalizationConstant x Y - 1| ≤ C / Real.log (x : ℝ)) :
    Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
      (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
        1 + C / Real.log (x : ℝ) := by
  have hpoint (n : ℕ) :
      normalizationConstant x Y * A.indicator (chain.visitProbability) n =
        A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ))) n := by
    by_cases hnA : n ∈ A
    · simp [hnA, visitProbabilityFormula chain hx (hA hnA)]
      grind only
    · simp [hnA]
  constructor
  · exact (hHitSummable.mul_left _).congr fun n =>
      hpoint n
  · have hWeight :
        (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
          normalizationConstant x Y := by
      calc
        ∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m
          = ∑' n : ℕ, normalizationConstant x Y * A.indicator (chain.visitProbability) n := by
              simpa using tsum_congr fun n => (hpoint n).symm
        _ = normalizationConstant x Y * ∑' n : ℕ, A.indicator (chain.visitProbability) n := by
              rw [tsum_mul_left]
        _ ≤ normalizationConstant x Y * 1 := by
              gcongr
        _ = normalizationConstant x Y := by ring
    refine hWeight.trans ?_
    have hupper : normalizationConstant x Y - 1 ≤ C / Real.log (x : ℝ) := (abs_le.mp hNorm).2
    linarith

end PrimitiveSetsAboveX
