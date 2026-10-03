/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.Zeta5Irrational.Constants
public import LeanPool.Zeta5Irrational.Degree
public import LeanPool.Zeta5Irrational.Stirling
public import LeanPool.Zeta5Irrational.Zeta5
public import LeanPool.Zeta5Irrational.Measure
public import LeanPool.Zeta5Irrational.EnergyConst
public import LeanPool.Zeta5Irrational.Positivity
public import LeanPool.Zeta5Irrational.EnergyBound

/-! # Section 6 of the paper: the real determinant, decomposed

A variant of Proposition 6.3 (`real_bound`) with `27 K log K` in place of the paper's
`24 K log K` is derived from
* `Δ_pos` : `Δ_K(ζ(5)) > 0` — proved in `Zeta5Irrational.Positivity` from the moment representation
  `moment_rep` (Proposition 2.2);
* `log_Δ_le`: a variant of (6.14) with `22 h log K + 50 h` in place of
  `18 h log K + 160 h`, proved in `Zeta5Irrational.EnergyBound` from Andréief's identity
  (6.10), variants of (6.11)–(6.12), and the variant of (6.9) `energy_ineq`
  (proved in `Zeta5Irrational.EnergyFinal` from Lemmas 6.1 and 6.2);
* `energy_const` : the numerical inequality (6.4), `λ M₀ - I(ρ) + C* ≤ U` — Appendix A.4 —
  proved in `Zeta5Irrational.EnergyConst`;
* `log_S_le` : the Stirling bound (6.15) — proved.
-/

public section

open Polynomial Filter Topology Finset

namespace Zeta5Irrational

/--
A variant of **(6.14)** with `22 h log K + 50 h` instead of `18 h log K + 160 h`,
proved in `Zeta5Irrational.EnergyBound` from the configuration inequality `energy_ineq`. -/
theorem log_Δ_le (n : ℕ) (hn : 0 < n) :
    Real.log (aeval zeta5 (Δ n)) ≤
      2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
            (lam * M0 - Irho) * Kr n ^ 2 +
          22 * (37 * n) * Real.log (Kr n) +
        50 * (37 * n) :=
  log_Δ_le' n hn

/-- **(6.15)**: the Stirling bound for `log S_K`. -/
theorem log_S_le (n : ℕ) (hn : 0 < n) :
    Real.log (S n) ≤
      (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 * Real.log (Kr n) + Cstar * Kr n ^ 2 +
          6 * (37 * n) * Real.log (Kr n) +
        6 * (37 * n) := by
  have hS :
    ((S n : ℚ) : ℝ) =
      ((40 * n).factorial : ℝ) ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) /
        (((3 * n).factorial : ℝ) ^ (12 * (37 * n)) *
          ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2) :=
    by simp only [S]; push_cast; rfl
  have hprod : (0 : ℝ) < ∏ i ∈ Icc 1 (37 * n - 1), ((2 * i).factorial : ℝ) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  rw [hS, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_prod (fun i _ => by positivity)]
  simp only [Real.log_pow, ← Finset.mul_sum]
  have h1 := log_factorial_le (m := 40 * n) (by omega)
  have h2 := log_factorial_ge (3 * n)
  have h3 := sum_log_factorial_two_mul_ge (h := 37 * n) (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : Real.log (3 * (n : ℝ)) = Real.log (3 / 40) + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have h2h : Real.log (2 * (37 * (n : ℝ))) = Real.log (37 / 20) + Real.log (40 * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hlog37 : Real.log (37 / 20) ≤ 0.85 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 37 / 20); linarith
  have hlog40 : 3 ≤ Real.log (40 * (n : ℝ)) := by
    have hexp : Real.exp 3 < 40 := by
      have h := Real.exp_one_lt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      calc
        Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := by gcongr
        _ < 40 := by norm_num
    calc
      (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (40 * n) := Real.log_le_log (Real.exp_pos 3) (by linarith)
  have hh1 : ((37 * n - 1 : ℕ) : ℝ) = 37 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)];
    push_cast; ring
  have hC :
    Cstar =
      -2 * (37 / 40) + 12 * (3 / 40) * (37 / 40) * (1 - Real.log (3 / 40)) + 3 * (37 / 40) ^ 2 -
        2 * (37 / 40) ^ 2 * Real.log (37 / 20) :=
    by unfold Cstar; norm_num
  rw [hC, hh1]
  push_cast at h1 h2 h3 ⊢
  rw [hN] at h2
  rw [h2h] at h3
  simp only [Kr, lam, alph]
  have hA : 0 ≤ 37 * (n : ℝ) - 1 := by linarith
  have hB : 0 ≤ 4 * (37 * (n : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog4 hA, mul_le_mul_of_nonneg_left hlog37 hB,
    mul_le_mul_of_nonneg_left hlog40 (by positivity : (0 : ℝ) ≤ 37 * n)]

/-- A weakening of **Proposition 6.3**, from the four statements above:
we use `27 K log K` in place of the paper's `24 K log K`. -/
theorem real_bound' (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        (U : ℝ) * Kr n ^ 2 + 27 * Kr n * Real.log (Kr n) + 200 * Kr n := by
  have hS : (0 : ℝ) < S n := by exact_mod_cast S_pos n
  have hΔ := Δ_pos n hn
  have hF : aeval zeta5 (F n) = (S n : ℝ) * aeval zeta5 (Δ n) := by simp [F, aeval_C]
  refine ⟨by rw [hF]; positivity, ?_⟩
  rw [hF, Real.log_mul hS.ne' hΔ.ne']
  have h1 := log_Δ_le n hn
  have h2 := log_S_le n hn
  have h3 := energy_const
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  have hlogK : 0 ≤ Real.log (Kr n) := Real.log_nonneg (by simp only [Kr]; norm_cast; omega)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3' : (lam * M0 - Irho + Cstar) * Kr n ^ 2 ≤ (U : ℝ) * Kr n ^ 2 :=
    mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  have hlow : 0 ≤ (n : ℝ) * Real.log (Kr n) := mul_nonneg hn' hlogK
  simp only [Kr] at *
  norm_num [lam, alph] at h1 h2 h3' hlow ⊢
  nlinarith

end Zeta5Irrational
