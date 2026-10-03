/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A factorial induction with the corrected factor two. -/

@[expose] public section

namespace AVenhance.Infra.Section4

theorem theta_analytic_bound_of_energy_recursion
    {E M : ℕ → ℝ} {B R L κ : ℝ}
    (hB : 0 < B) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hE0 : E 0 ≤ B)
    (hMnonneg : ∀ q, 0 ≤ M q)
    (hLinitial : 2 / R ≤ L)
    (hQ1scale : ∀ (n : ℕ), 1 ≤ n →
      4 * Real.sqrt ((n : ℝ) * M 2 / κ) *
          ((n - 1).factorial : ℝ) * L ^ (n - 1) ≤
        (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n)
    (hHighscale : ∀ n, 1 ≤ n →
      4 * (∑ q ∈ Finset.range (n + 1),
        if 2 ≤ q then
          ((n.choose q : ℕ) : ℝ) * (M q / κ) *
            ((n - q).factorial : ℝ) * L ^ (n - q)
        else 0) ≤
        (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n)
    (hrec : ∀ n, 1 ≤ n →
      E n ≤ 2 * B * ((n.factorial : ℝ) / R ^ n) +
        4 * Real.sqrt ((n : ℝ) * M 2 / κ) * E (n - 1) +
        4 * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.choose q : ℕ) : ℝ) * (M q / κ) * E (n - q)
          else 0)) :
    ∀ n, E n ≤ 2 * B * (n.factorial : ℝ) * L ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa using hE0.trans (by nlinarith [hB])
      | succ k =>
          let n := k + 1
          have hn : 1 ≤ n := by simp [n]
          have hprev := ih k (by omega)
          have hrecn := hrec n hn
          have hRinv : 1 / R ≤ L / 2 := by
            have hhalf : (1 / R) = (2 / R) / 2 := by field_simp
            rw [hhalf]
            exact div_le_div_of_nonneg_right hLinitial (by norm_num)
          have hinitpow : (1 / R) ^ n ≤ (L / 2) ^ n :=
            pow_le_pow_left₀ (by positivity) hRinv n
          have hhalfPow : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
            simpa [pow_one] using
              (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
                (by norm_num : (1 / 2 : ℝ) ≤ 1) hn)
          have hinit : 2 * B * ((n.factorial : ℝ) / R ^ n) ≤
              (1 / 2 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by
            have hpow : 1 / R ^ n ≤ (1 / 2 : ℝ) * L ^ n := by
              calc
                1 / R ^ n = (1 / R) ^ n := by simp [one_div, inv_pow]
                _ ≤ (L / 2) ^ n := hinitpow
                _ = L ^ n * (1 / 2 : ℝ) ^ n := by
                  rw [div_pow]
                  simp [div_eq_mul_inv, inv_pow]
                _ ≤ L ^ n * (1 / 2 : ℝ) :=
                  mul_le_mul_of_nonneg_left hhalfPow (pow_nonneg hL.le _)
                _ = (1 / 2 : ℝ) * L ^ n := by ring
            have hfac : 0 ≤ (n.factorial : ℝ) := by positivity
            calc
              2 * B * ((n.factorial : ℝ) / R ^ n) ≤
                  2 * B * (n.factorial : ℝ) * ((1 / 2 : ℝ) * L ^ n) := by
                    simpa [mul_assoc, div_eq_mul_inv] using
                      mul_le_mul_of_nonneg_left hpow
                        (mul_nonneg (by positivity : 0 ≤ 2 * B) hfac)
              _ = (1 / 2 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by ring
          have hq1 : 4 * Real.sqrt ((n : ℝ) * M 2 / κ) * E (n - 1) ≤
              (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by
            have hscale := hQ1scale n hn
            have hBfac : 0 ≤ 2 * B := by positivity
            have hidx : n - 1 = k := by simp [n]
            calc
              4 * Real.sqrt ((n : ℝ) * M 2 / κ) * E (n - 1) =
                  4 * Real.sqrt ((n : ℝ) * M 2 / κ) * E k := by rw [hidx]
              _ ≤ 4 * Real.sqrt ((n : ℝ) * M 2 / κ) *
                    (2 * B * (k.factorial : ℝ) * L ^ k) :=
                      mul_le_mul_of_nonneg_left hprev (by positivity)
              _ = (2 * B) *
                    (4 * Real.sqrt ((n : ℝ) * M 2 / κ) *
                      (n - 1).factorial * L ^ (n - 1)) := by rw [hidx]; ring
              _ ≤ (2 * B) * ((1 / 4 : ℝ) *
                    (n.factorial : ℝ) * L ^ n) :=
                      mul_le_mul_of_nonneg_left hscale hBfac
              _ = (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by ring
          have hhigh :
              4 * (∑ q ∈ Finset.range (n + 1),
                if 2 ≤ q then
                  ((n.choose q : ℕ) : ℝ) * (M q / κ) * E (n - q)
                else 0) ≤
              (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by
            have hsum :
                (∑ q ∈ Finset.range (n + 1),
                  if 2 ≤ q then
                    ((n.choose q : ℕ) : ℝ) * (M q / κ) * E (n - q)
                  else 0) ≤
                (∑ q ∈ Finset.range (n + 1),
                  if 2 ≤ q then
                    ((n.choose q : ℕ) : ℝ) * (M q / κ) *
                      (2 * B * ((n - q).factorial : ℝ) * L ^ (n - q))
                  else 0) := by
              apply Finset.sum_le_sum
              intro q hq
              by_cases hq2 : 2 ≤ q
              · have hqle : q ≤ n := by simp only [Finset.mem_range] at hq; omega
                have hsmall : n - q < n := by omega
                have hqprev := ih (n - q) hsmall
                simp only [hq2]
                have hcoef : 0 ≤ ((n.choose q : ℕ) : ℝ) * (M q / κ) := by
                  exact mul_nonneg (by positivity)
                    (div_nonneg (hMnonneg q) hκ.le)
                exact mul_le_mul_of_nonneg_left hqprev hcoef
              · simp [hq2]
            have hsum' := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
            have hscale := hHighscale n hn
            have hsumfactor :
                (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then
                      ((n.choose q : ℕ) : ℝ) * (M q / κ) *
                        (2 * B * ((n - q).factorial : ℝ) * L ^ (n - q))
                    else 0) =
                  (2 * B) * (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then
                      ((n.choose q : ℕ) : ℝ) * (M q / κ) *
                        ((n - q).factorial : ℝ) * L ^ (n - q)
                    else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hq2 : 2 ≤ q
              · simp [hq2]
                ring_nf
              · simp [hq2]
            calc
              _ ≤ 4 * (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then
                      ((n.choose q : ℕ) : ℝ) * (M q / κ) *
                        (2 * B * ((n - q).factorial : ℝ) * L ^ (n - q))
                    else 0) := hsum'
              _ = (2 * B) * (4 * (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then
                      ((n.choose q : ℕ) : ℝ) * (M q / κ) *
                        ((n - q).factorial : ℝ) * L ^ (n - q)
                    else 0)) := by rw [hsumfactor]; ring
              _ ≤ (2 * B) * ((1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n) :=
                    mul_le_mul_of_nonneg_left hscale (by positivity)
              _ = (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := by ring
          have hparts := add_le_add (add_le_add hinit hq1) hhigh
          have hfinal : E n ≤ 2 * B * (n.factorial : ℝ) * L ^ n := by
            calc
              E n ≤ 2 * B * ((n.factorial : ℝ) / R ^ n) +
                  4 * Real.sqrt ((n : ℝ) * M 2 / κ) * E (n - 1) +
                  4 * (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then
                      ((n.choose q : ℕ) : ℝ) * (M q / κ) * E (n - q)
                    else 0) := hrecn
              _ ≤ (1 / 2 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) +
                  (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) +
                  (1 / 4 : ℝ) * (2 * B * (n.factorial : ℝ) * L ^ n) := hparts
              _ = 2 * B * (n.factorial : ℝ) * L ^ n := by ring
          simpa [n] using hfinal

end AVenhance.Infra.Section4
