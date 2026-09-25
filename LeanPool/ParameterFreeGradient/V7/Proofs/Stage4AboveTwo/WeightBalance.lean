/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwo.Constants

/-!
The above-two weight scale balances accumulated residual error against terminal weight growth.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage4AboveTwo

private theorem plateau_increment_formula (gamma : ℝ) (n k : ℕ)
    (hk : k < n) :
    let u : ScalarSeq := fun j =>
      if j < n then gamma * ((j : ℝ) + 1) ^ (2 : ℕ)
      else gamma * (n : ℝ) ^ (2 : ℕ)
    u k - (if k = 0 then 0 else u (k - 1)) =
      gamma * (2 * (k : ℝ) + 1) := by
  dsimp
  rw [ite_eq_left hk]
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · rw [ite_eq_right hk0]
    have hpred : k - 1 < n := by omega
    rw [ite_eq_left hpred]
    have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hkone]
      norm_num
    rw [hkcast]
    ring

private theorem increment_ratio_le (gamma : ℝ) (hgamma : 0 < gamma)
    (n k : ℕ) (hk : k < n) :
    let u : ScalarSeq := fun j =>
      if j < n then gamma * ((j : ℝ) + 1) ^ (2 : ℕ)
      else gamma * (n : ℝ) ^ (2 : ℕ)
    let dw : ScalarSeq := fun j => u j - (if j = 0 then 0 else u (j - 1))
    0 ≤ (dw k) ^ (2 : ℕ) / u k ∧
      (dw k) ^ (2 : ℕ) / u k ≤ 4 * gamma := by
  dsimp
  rw [ite_eq_left hk]
  have hdw : gamma * ((k : ℝ) + 1) ^ (2 : ℕ) -
      (if k = 0 then 0
       else if k - 1 < n then gamma * (((k - 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ)
       else gamma * (n : ℝ) ^ (2 : ℕ)) =
      gamma * (2 * (k : ℝ) + 1) := by
    simpa only [ite_eq_left hk] using plateau_increment_formula gamma n k hk
  rw [hdw]
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkp : 0 < (k : ℝ) + 1 := by positivity
  have hu : 0 < gamma * ((k : ℝ) + 1) ^ (2 : ℕ) :=
    mul_pos hgamma (sq_pos_of_pos hkp)
  constructor
  · exact div_nonneg (sq_nonneg _) hu.le
  · rw [div_le_iff₀ hu]
    have hlin : 2 * (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by linarith
    have hsquare := (sq_le_sq₀ (by linarith) (by positivity)).2 hlin
    nlinarith

private theorem gamma_error_power {p eta : ℝ} {n : ℕ}
    (hp : 2 < p) (heta : 0 < eta) (hn : 1 ≤ n) :
    (aboveGamma p eta n) ^ (aboveErrorPower p) =
      eta / (2 * aboveBudgetConstant p * n) := by
  let base := eta / (2 * aboveBudgetConstant p * (n : ℝ))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hbase : 0 < base := by
    dsimp [base]
    exact div_pos heta
      (mul_pos (mul_pos (by norm_num) (budgetConstant_pos hp)) hnpos)
  unfold aboveGamma
  change (base ^ (aboveBudgetExponent p)) ^ (aboveErrorPower p) = base
  rw [← Real.rpow_mul hbase.le]
  rw [show aboveBudgetExponent p * aboveErrorPower p = 1 by
    rw [mul_comm, errorPower_mul_budgetExponent hp]]
  exact Real.rpow_one base

private theorem gamma_endpoint_identity {p eta : ℝ} {n : ℕ}
    (hp : 2 < p) (heta : 0 < eta) (hn : 1 ≤ n) :
    aboveGamma p eta n * (n : ℝ) ^ (2 : ℕ) =
      aboveGrowthConstant p * eta ^ (aboveBudgetExponent p) *
        (n : ℝ) ^ ((p + 2) / p) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hB : 0 < aboveBudgetConstant p := budgetConstant_pos hp
  unfold aboveGamma aboveGrowthConstant aboveBudgetExponent
  rw [Real.div_rpow heta.le
    (mul_nonneg (mul_nonneg (by norm_num) hB.le) hnpos.le)]
  rw [Real.mul_rpow (mul_nonneg (by norm_num) hB.le) hnpos.le]
  have htwoB : 0 < 2 * aboveBudgetConstant p := mul_pos (by norm_num) hB
  have hinv : (2 * aboveBudgetConstant p) ^ (-((p - 2) / p)) =
      ((2 * aboveBudgetConstant p) ^ ((p - 2) / p))⁻¹ := by
    exact Real.rpow_neg htwoB.le _
  have hnmerge : (n : ℝ) ^ (2 : ℕ) /
      (n : ℝ) ^ ((p - 2) / p) =
      (n : ℝ) ^ ((p + 2) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hnpos]
    congr 1
    field_simp [show p ≠ 0 by linarith]
    ring
  rw [hinv]
  have hAp : 0 < (2 * aboveBudgetConstant p) ^ ((p - 2) / p) :=
    Real.rpow_pos_of_pos htwoB _
  have hNp : 0 < (n : ℝ) ^ ((p - 2) / p) :=
    Real.rpow_pos_of_pos hnpos _
  calc
    eta ^ ((p - 2) / p) /
          ((2 * aboveBudgetConstant p) ^ ((p - 2) / p) *
            (n : ℝ) ^ ((p - 2) / p)) * (n : ℝ) ^ (2 : ℕ) =
        ((2 * aboveBudgetConstant p) ^ ((p - 2) / p))⁻¹ *
          eta ^ ((p - 2) / p) *
            ((n : ℝ) ^ (2 : ℕ) /
              (n : ℝ) ^ ((p - 2) / p)) := by
        field_simp [hAp.ne', hNp.ne']
    _ = ((2 * aboveBudgetConstant p) ^ ((p - 2) / p))⁻¹ *
          eta ^ ((p - 2) / p) * (n : ℝ) ^ ((p + 2) / p) := by
        rw [hnmerge]

end V7.Stage4AboveTwo

namespace V7

theorem aboveWeightErrorBalance : AboveWeightErrorBalanceStatement := by
  intro p hp n hn eta heta
  dsimp only
  let gamma := aboveGamma p eta n
  have hgamma : 0 < gamma := Stage4AboveTwo.gamma_pos hp heta hn
  let u : ScalarSeq := fun k =>
    if k < n then gamma * ((k : ℝ) + 1) ^ (2 : ℕ)
    else gamma * (n : ℝ) ^ (2 : ℕ)
  let dw : ScalarSeq := fun k => u k - (if k = 0 then 0 else u (k - 1))
  change aboveErrorSum p n u dw ≤ eta / 2 ∧
    u n = aboveGrowthConstant p * eta ^ (aboveBudgetExponent p) *
      (n : ℝ) ^ ((p + 2) / p)
  constructor
  · unfold aboveErrorSum
    have hpoint : ∀ k ∈ Finset.range n,
        ((dw k) ^ (2 : ℕ) / u k) ^ (aboveErrorPower p) ≤
          (4 * gamma) ^ (aboveErrorPower p) := by
      intro k hk
      have hklt := Finset.mem_range.mp hk
      have hrange := Stage4AboveTwo.increment_ratio_le gamma hgamma n k hklt
      exact Real.rpow_le_rpow hrange.1 hrange.2
        (le_trans (by norm_num) (Stage4AboveTwo.errorPower_gt_one hp).le)
    calc
      aboveErrorConstant p *
          ∑ k ∈ Finset.range n,
            ((dw k) ^ (2 : ℕ) / u k) ^ (aboveErrorPower p) ≤
          aboveErrorConstant p *
            ∑ k ∈ Finset.range n,
              (4 * gamma) ^ (aboveErrorPower p) := by
            apply mul_le_mul_of_nonneg_left _
              (Stage4AboveTwo.errorConstant_pos hp).le
            exact Finset.sum_le_sum fun k hk => hpoint k hk
      _ = aboveBudgetConstant p * (n : ℝ) *
          gamma ^ (aboveErrorPower p) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hgamma.le]
            unfold aboveBudgetConstant
            ring
      _ = eta / 2 := by
            rw [Stage4AboveTwo.gamma_error_power hp heta hn]
            have hB := Stage4AboveTwo.budgetConstant_pos hp
            have hnpos : 0 < (n : ℝ) := by
              exact_mod_cast (Nat.zero_lt_of_lt hn)
            field_simp [hB.ne', hnpos.ne']
  · dsimp [u]
    rw [ite_eq_right (lt_irrefl n)]
    exact Stage4AboveTwo.gamma_endpoint_identity hp heta hn

end V7
