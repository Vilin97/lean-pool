/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.Nonvanishing
import LeanPool.LiCriterion.Lc.LiCriterion.GenusOnePairedSumFormula
import LeanPool.LiCriterion.Lc.LiCriterion.HadamardBridge
import LeanPool.LiCriterion.Lc.LiCriterion.HadamardSummabilityBridge

/-!
# RH / Li Bridge

This file connects the project-local Li-criterion theorems to mathlib's
`RiemannHypothesis`, and packages the clean Hadamard-order-one route to the final
biconditional.
-/

open Complex
open scoped Topology

namespace LiCriterion

/-- The project-local critical-strip formulation of RH is equivalent to mathlib's
`RiemannHypothesis`. -/
theorem rh_equiv_mathlib :
    RiemannHypothesis ↔
      (∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1 / 2) := by
  constructor
  · intro hRH s hs hstrip
    have hnot_trivial : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have hn_pos : (0 : ℝ) < n + 1 := by positivity
      have htriv_re : ((-2 * ((n + 1 : ℂ))).re : ℝ) = -2 * (n + 1) := by
        norm_num
      rw [htriv_re] at hstrip
      linarith
    have hs_ne_one : s ≠ 1 := by
      intro hs1
      have : (1 : ℝ) < 1 := by simpa [hs1] using hstrip.2
      linarith
    exact hRH s hs hnot_trivial hs_ne_one
  · intro hstrip s hs hnot_trivial hs_ne_one
    have hs_lt_one : s.re < 1 := by
      by_contra hs_ge_one
      push Not at hs_ge_one
      exact (riemannZeta_ne_zero_of_one_le_re hs_ge_one) hs
    have hs_pos : 0 < s.re := by
      by_contra hs_nonpos
      push Not at hs_nonpos
      have hs_ne_zero : s ≠ 0 := by
        intro hs0
        rw [hs0, riemannZeta_zero] at hs
        norm_num at hs
      have hGammaR_ne : Gammaℝ s ≠ 0 := by
        intro hGammaR
        rcases Gammaℝ_eq_zero_iff.mp hGammaR with ⟨n, hn⟩
        cases n with
        | zero =>
            exact hs_ne_zero (by simpa using hn)
        | succ n =>
            exact hnot_trivial ⟨n, by
              simpa [Nat.succ_eq_add_one, mul_assoc, mul_left_comm, mul_comm] using hn⟩
      have hCompleted : completedRiemannZeta s = 0 := by
        rw [riemannZeta_def_of_ne_zero hs_ne_zero] at hs
        exact (div_eq_zero_iff.mp hs).resolve_right hGammaR_ne
      have h1ms_ge_one : 1 ≤ (1 - s).re := by
        simp only [sub_re, one_re]
        linarith
      have h1ms_ne_zero : 1 - s ≠ 0 := by
        intro hzero
        exact hs_ne_one (sub_eq_zero.mp hzero).symm
      have hCompleted' : completedRiemannZeta (1 - s) = 0 := by
        rw [completedRiemannZeta_one_sub]
        exact hCompleted
      have h1ms_zero : riemannZeta (1 - s) = 0 := by
        rw [riemannZeta_def_of_ne_zero h1ms_ne_zero, hCompleted', zero_div]
      exact (riemannZeta_ne_zero_of_one_le_re h1ms_ge_one) h1ms_zero
    exact hstrip s hs ⟨hs_pos, hs_lt_one⟩

/-- The existing conditional Li criterion equivalence restated against mathlib's
`RiemannHypothesis`. -/
theorem biconditional_rh_li_of_standard_hypotheses
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    (RiemannHypothesis ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) := by
  rw [rh_equiv_mathlib]
  exact li_criterion_equiv hgenus hhad

theorem biconditional_rh_li_of_weighted_standard_hypotheses
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : xi_factorization_prod_with_multiplicity) :
    (RiemannHypothesis ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) := by
  rw [rh_equiv_mathlib]
  exact li_criterion_equiv_of_weighted_standard_hypotheses hgenus hhad

/-- The Li criterion biconditional under the clean Hadamard order assumptions for `riemannXi`.

This packages the multiplicity-aware genus-one bridge and removes the last explicit
shifted-factorization hypothesis from the biconditional. -/
theorem biconditional_rh_li_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    (RiemannHypothesis ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) := by
  exact biconditional_rh_li_of_weighted_standard_hypotheses
    (xi_weighted_genus_one_of_hadamard_order_one hfinite horder)
    (xi_factorization_prod_with_multiplicity_of_hadamard_order_one hfinite horder)

end LiCriterion
