/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.Markov
import LeanPool.Erdos1196.HitMass
import LeanPool.Erdos1196.PrimitiveWeight

/-!
# Main theorem for primitive sets above `x`

This file contains the public theorem solving Erdős Problem `#1196` in the quantitative form
`1 + O(1 / log x)`. It packages the eventual choice of the cutoff `Y`, builds the explicit
Markov layer with visiting probabilities `1 / (B_x n log n)`, and combines the hit-mass and
normalization estimates into the final logarithmic-series bound.

## Main statements

* `mainTheorem`
-/

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/--
There is a fixed admissible cutoff `Y ≥ 2` for which the transition weights eventually satisfy the
sub-Markov row-sum bound. This packages the choice extracted from
`subMarkovRowSumBound` for later use in `mainTheorem`.
-/
private lemma exists_eventual_subMarkov_cutoff :
    ∃ Y : ℕ, 2 ≤ Y ∧
      ∃ x₀ : ℕ, Y ≤ x₀ ∧
        ∀ ⦃m : ℕ⦄, x₀ ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1 := by
  rcases subMarkovRowSumBound with ⟨C, hCpos, hC⟩
  let Y : ℕ := Nat.ceil (Real.exp (2 * C)) + 1
  have hceil_lt_Y : Nat.ceil (Real.exp (2 * C)) < Y := by
    simp [Y]
  have hYlarge : Real.exp (2 * C) < (Y : ℝ) := by
    exact lt_of_le_of_lt (Nat.le_ceil (Real.exp (2 * C))) (by exact_mod_cast hceil_lt_Y)
  rcases hC hYlarge with ⟨x₀, hYx₀, hx₀⟩
  refine ⟨Y, ?_, x₀, hYx₀, hx₀⟩
  have hY_gt_one : (1 : ℝ) < (Y : ℝ) := by
    refine lt_trans ?_ hYlarge
    simpa using Real.one_lt_exp_iff.2 (by nlinarith [hCpos])
  exact_mod_cast hY_gt_one

/--
Formal solution of Erdős Problem `#1196`: there exist constants `C` and `x₀` such that for every
cutoff `x ≥ x₀` and every primitive set `A ⊆ Ici x`, the logarithmic series
`∑_{a ∈ A} 1 / (a log a)` is summable and bounded above by `1 + C / log x`.
-/
theorem mainTheorem :
    ∃ C : ℝ, ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        ∀ {A : Set ℕ}, PrimitiveSet A → A ⊆ Set.Ici x →
          Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
            (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
              1 + C / Real.log (x : ℝ) := by
  rcases exists_eventual_subMarkov_cutoff with ⟨Y, hY, xCut, hYxCut, hSub⟩
  rcases normalizationEstimate (Y := Y) hY with ⟨C, hCpos, xNorm, hNorm⟩
  let xLog : ℕ := Nat.ceil (Real.exp C) + 1
  refine ⟨C, max xCut (max xNorm xLog), ?_⟩
  intro x hx A hPrimitive hA
  have hxCut : xCut ≤ x := by omega
  have hxNorm : xNorm ≤ x := by omega
  have hxLog : xLog ≤ x := by omega
  have hxY : Y ≤ x := by omega
  have hxTwo : 2 ≤ x := by omega
  have hExp_lt_x : Real.exp C < (x : ℝ) := by
    refine lt_of_le_of_lt (Nat.le_ceil (Real.exp C)) ?_
    exact_mod_cast
      (lt_of_lt_of_le (Nat.lt_succ_self (Nat.ceil (Real.exp C))) (by simpa [xLog] using hxLog))
  have hlog_gt : C < Real.log (x : ℝ) := by
    simpa [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hExp_lt_x)
  have hlog_pos : 0 < Real.log (x : ℝ) := lt_trans hCpos hlog_gt
  have hBpos : 0 < normalizationConstant x Y := by
    have hBnear : |normalizationConstant x Y - 1| < 1 := by
      refine lt_of_le_of_lt (hNorm hxNorm) ?_
      have hlog_ne : Real.log (x : ℝ) ≠ 0 := hlog_pos.ne'
      field_simp [hlog_ne]
      nlinarith
    linarith [(abs_lt.mp hBnear).1]
  let visit : ℕ → ℝ := fun n =>
    if x ≤ n then
      1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ))
    else 0
  let chain : MarkovLayer x Y := {
    transitionSubMarkov := by
      intro m hm
      exact hSub (le_trans hxCut hm)
    visitProbability := visit
    visitProbabilityRecurrence := by
      intro n hn
      simpa [visit, hn] using
        (explicitFormula_eq_recurrence_rhs (x := x) (Y := Y) (n := n) hxTwo hn
          (f := visit) <| by
            intro q hq hqx hq1
            have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
              Nat.cast_div (Nat.dvd_of_mem_divisors hq)
                (by exact_mod_cast (Nat.pos_of_mem_divisors hq).ne')
            simp [visit, hqx.2, hcast_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm])
  }
  have hinit : (∑' n : ℕ, initialMass x Y n) ≤ 1 :=
    (tsum_initialMass_eq_one (x := x) (Y := Y) hBpos).le
  have hVisitMass : visitMass chain A ≤ 1 :=
    visitMass_le_of_bounds chain A (by omega) (le_trans (by decide : 1 ≤ 2) hY) hinit
      chain.kernelRowBound
  rcases PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one
      chain hPrimitive hA hxTwo hY hBpos hVisitMass with
    ⟨hHitSummable, hHit⟩
  exact summable_indicatorLogSeries_and_tsum_le_of_hitMass
    chain hxTwo hA hBpos hHitSummable hHit (hNorm hxNorm)

end PrimitiveSetsAboveX
