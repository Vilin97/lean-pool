/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.UpperBoundParameters

/-!
# Paper-facing formulation

This file contains wrappers whose statements follow the exposition in the
paper.  The proof-producing modules use relational predicates and explicit
integer cost bounds; here we package those results as statements about a
noncomputable optimal pebbling number `optimalPebblingNumber n` and the explicit
constant `CLean`.
-/

namespace PebblingLean

namespace Hypercube

namespace Paper

open Pebbling

/-- The finite cutoff used by the fully explicit Lean upper bound. -/
def N0 : ℕ :=
  PaperParameters.explicitCutoff

theorem N0_eq :
    N0 = 36_329_454_321_664 := by
  rfl

theorem N0_pos : 0 < N0 := by
  simpa [N0] using PaperParameters.explicitCutoff_pos

/-- The explicit constant certified by the Lean proof. -/
noncomputable def CLean : ℝ :=
  Real.exp (4 * PaperParameters.loss N0) *
    finiteBaseNormalizedBound
      (PaperParameters.recursiveCostBound (217 : ℝ) N0) N0

theorem CLean_nonneg : 0 ≤ CLean := by
  unfold CLean
  exact mul_nonneg (Real.exp_nonneg _)
    (finiteBaseNormalizedBound_nonneg _ _)

/-- The same constant in the displayed form used in the paper. -/
theorem CLean_eq_paper_formula :
    CLean =
      Real.exp (4 / (N0 : ℝ) ^ 2) *
        ∑ j ∈ Finset.range N0,
          (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by
  unfold CLean finiteBaseNormalizedBound normalizedCost
  have hexp :
      Real.exp (4 * PaperParameters.loss N0) =
        Real.exp (4 / (N0 : ℝ) ^ 2) := by
    simp [PaperParameters.loss, div_eq_mul_inv]
  have hsum :
      (∑ j ∈ Finset.range N0,
        (PaperParameters.recursiveCostBound (217 : ℝ) N0 j : ℝ) /
          (((4 : ℝ) / 3) ^ j)) =
        ∑ j ∈ Finset.range N0,
          (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < N0 := Finset.mem_range.mp hj
    rw [PaperParameters.recursiveCostBound_base
      (K := (217 : ℝ)) (n0 := N0) (n := j) hjlt]
    change ((2 ^ j * 2 ^ (j / 5) : ℕ) : ℝ) /
        (((4 : ℝ) / 3) ^ j) =
      (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j)
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [div_pow]
    field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0),
      pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul, ← pow_mul]
    rw [Nat.mul_comm]
  rw [hexp, hsum]

theorem one_le_CLean_sum :
    (1 : ℝ) ≤
      ∑ j ∈ Finset.range N0,
        (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by
  let f : ℕ → ℝ := fun j =>
    (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j)
  have hmem : 0 ∈ Finset.range N0 := Finset.mem_range.mpr N0_pos
  have hnonneg : ∀ j ∈ Finset.range N0, 0 ≤ f j := by
    intro j _hj
    dsimp [f]
    positivity
  have hsingle : f 0 ≤ ∑ j ∈ Finset.range N0, f j :=
    Finset.single_le_sum hnonneg hmem
  have hf0 : f 0 = 1 := by
    simp [f]
  simpa [f, hf0] using hsingle

theorem CLean_pos : 0 < CLean := by
  rw [CLean_eq_paper_formula]
  exact mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one one_le_CLean_sum)

/-- There is always at least one solvable distribution on `Q_n`: put one pebble
on every vertex. -/
theorem exists_solvable_size (n : ℕ) :
    ∃ k : ℕ, HasSolvableSize (graph n) k := by
  refine ⟨2 ^ n, ?_⟩
  refine ⟨constantDistribution n 1, ?_, ?_⟩
  · simpa using size_constantDistribution n 1
  · simpa [Solvable] using solvableAtLeast_constantDistribution n 1

/-- A noncomputable version of the optimal pebbling number `o(Q_n)`.  The
paper works with this number; the main proof modules avoid choosing it by using
the relational predicate `IsOptimalNumber`. -/
noncomputable def optimalPebblingNumber (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_solvable_size n)

theorem optimalPebblingNumber_hasSolvableSize (n : ℕ) :
    HasSolvableSize (graph n) (optimalPebblingNumber n) := by
  classical
  simpa [optimalPebblingNumber] using
    Nat.find_spec (exists_solvable_size n)

theorem isOptimalNumber_optimalPebblingNumber (n : ℕ) :
    IsOptimalNumber (graph n) (optimalPebblingNumber n) := by
  classical
  constructor
  · exact optimalPebblingNumber_hasSolvableSize n
  · intro l hl
    simpa [optimalPebblingNumber] using
      Nat.find_min (exists_solvable_size n) hl

/-- Paper lower bound: `o(Q_n) ≥ (4/3)^n`. -/
theorem lower_bound (n : ℕ) :
    ((4 : ℚ) / 3) ^ n ≤ (optimalPebblingNumber n : ℚ) :=
  lower_bound_of_isOptimalNumber
    (isOptimalNumber_optimalPebblingNumber n)

/-- Real-valued form of the paper lower bound. -/
theorem lower_bound_real (n : ℕ) :
    ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) := by
  have hcast :
      ((((4 : ℚ) / 3) ^ n : ℚ) : ℝ) ≤
        ((optimalPebblingNumber n : ℚ) : ℝ) := by
    exact_mod_cast lower_bound n
  simpa using hcast

/-- Paper upper bound with the explicit Lean constant. -/
theorem upper_bound (n : ℕ) :
    (optimalPebblingNumber n : ℝ) ≤
      CLean * (((4 : ℝ) / 3) ^ n) := by
  simpa [CLean, N0] using
    PaperParameters.explicit_upper_bound_of_isOptimalNumber
      (isOptimalNumber_optimalPebblingNumber n)

/-- The two inequalities in the final theorem, stated directly for
`optimalPebblingNumber`. -/
theorem bounds (n : ℕ) :
    ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
      (optimalPebblingNumber n : ℝ) ≤
        CLean * (((4 : ℝ) / 3) ^ n) :=
  ⟨lower_bound_real n, upper_bound n⟩

/-- Paper conclusion: the optimal pebbling number of the hypercube has order
`(4/3)^n`.  This is stated as an explicit two-sided big-Theta witness. -/
theorem optimalPebblingNumber_theta :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
          (optimalPebblingNumber n : ℝ) ≤
            C * (((4 : ℝ) / 3) ^ n) := by
  exact ⟨CLean, CLean_pos, fun n => bounds n⟩

end Paper

end Hypercube

end PebblingLean
