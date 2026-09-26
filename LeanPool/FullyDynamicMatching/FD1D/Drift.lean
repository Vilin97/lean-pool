/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Arithmetic

/-! # Drift -/

@[expose] public section

namespace FD1D

noncomputable section

/-!
# Harmonic-potential drift

This module separates the stochastic bookkeeping from the concrete tree. The
tree module supplies `D`, `R`, and `H`; the lemmas below prove the exact
one-coordinate drift identity and the arithmetic implications used in the
stationary and finite-horizon arguments.
-/

/-- The finite harmonic potential used at a node with inventory `k`. -/
def harmonicPotential (a : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, 1 / (j + a)

@[simp] theorem harmonicPotential_zero (a : ℝ) :
    harmonicPotential a 0 = 0 := by
  simp [harmonicPotential]

theorem harmonicPotential_succ (a : ℝ) (k : ℕ) :
    harmonicPotential a (k + 1) =
      harmonicPotential a k + 1 / (k + 1 + a) := by
  rw [harmonicPotential, harmonicPotential, Finset.sum_Icc_succ_top]
  · simp [add_comm]
  · omega

/-- Exact drift of one node under an independent deletion and arrival. -/
theorem node_harmonic_drift_identity
    (a N p q : ℝ) (hNa : N + a ≠ 0) (hNa1 : N + a + 1 ≠ 0) :
    p * (1 - q) / (N + a + 1) - q * (1 - p) / (N + a) =
      (p - q) / (N + a) -
        p * (1 - q) / ((N + a) * (N + a + 1)) := by
  field_simp
  ring

/-- The remainder term is bounded by `p h²` using `p ≤ (N+a)h`. -/
theorem node_remainder_le
    {a N p q h : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hNa : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    0 ≤ p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ∧
      p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 := by
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hNa1 : 0 < N + a + 1 := by linarith
  have hh : 0 ≤ h := by
    by_contra hn
    have hhneg : h < 0 := lt_of_not_ge hn
    have : (N + a) * h < 0 := mul_neg_of_pos_of_neg hNa hhneg
    linarith
  constructor
  · positivity
  · have hp_div : p / (N + a) ≤ h := by
      apply (div_le_iff₀ hNa).2
      simpa [mul_comm] using hmajor
    have hp_div' : p / (N + a + 1) ≤ h := by
      calc
        p / (N + a + 1) ≤ p / (N + a) := by
          exact div_le_div_of_nonneg_left hp hNa (by linarith)
        _ ≤ h := hp_div
    calc
      p ^ 3 * (1 - q) / ((N + a) * (N + a + 1))
          ≤ p ^ 3 / ((N + a) * (N + a + 1)) := by
            have hp3 : 0 ≤ p ^ 3 := by positivity
            have hnum : p ^ 3 * (1 - q) ≤ p ^ 3 := by
              calc
                p ^ 3 * (1 - q) ≤ p ^ 3 * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith) hp3
                _ = p ^ 3 := mul_one _
            exact div_le_div_of_nonneg_right hnum (by positivity)
      _ = p * (p / (N + a)) * (p / (N + a + 1)) := by
            field_simp
      _ ≤ p * h ^ 2 := by
            have hmul :
                (p / (N + a)) * (p / (N + a + 1)) ≤ h * h :=
              mul_le_mul hp_div hp_div' (by positivity) hh
            simpa [pow_two, mul_assoc] using
              mul_le_mul_of_nonneg_left hmul hp

/--
The numerical core of the stationary hazard estimate. This is equation (11)
after the deterministic Bellman lower bound and the stochastic remainder
upper bound have been combined.
-/
theorem stationary_hazard_bound
    {a L m H : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hH : 0 ≤ H)
    (haL : 200 * L ≤ a)
    (hmain :
      (a / 100 - L) * H ≤ 103 * a / (300 * m ^ 2)) :
    H ≤ 206 / (3 * m ^ 2) := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hcoef : a / 200 ≤ a / 100 - L := by
    linarith
  have ha200 : 0 < a / 200 := by positivity
  have hscaled : (a / 200) * H ≤ 103 * a / (300 * m ^ 2) := by
    calc
      (a / 200) * H ≤ (a / 100 - L) * H :=
        mul_le_mul_of_nonneg_right hcoef hH
      _ ≤ _ := hmain
  apply (mul_le_mul_iff_of_pos_left ha200).mp
  calc
    a / 200 * H ≤ 103 * a / (300 * m ^ 2) := hscaled
    _ = a / 200 * (206 / (3 * m ^ 2)) := by
      field_simp
      ring

/-- Algebraic form of the transient averaged hazard estimate (12). -/
theorem transient_hazard_bound
    {a L m T H logTerm : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hT : 0 < T)
     (hH : 0 ≤ H)
    (haL : 200 * L ≤ a) (hlogA : 200 * logTerm ≤ a)
    (hmain :
      (a / 100 - L) * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T) :
    H ≤ 206 / (3 * m ^ 2) + 1 / T := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hcoef : a / 200 ≤ a / 100 - L := by linarith
  have ha200 : 0 < a / 200 := by positivity
  have hscaled :
      (a / 200) * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T := by
    calc
      (a / 200) * H ≤ (a / 100 - L) * H :=
        mul_le_mul_of_nonneg_right hcoef hH
      _ ≤ _ := hmain
  have hlogScaled : logTerm / T ≤ (a / 200) * (1 / T) := by
    apply (div_le_iff₀ hT).2
    field_simp
    nlinarith
  apply (mul_le_mul_iff_of_pos_left ha200).mp
  calc
    a / 200 * H ≤
        103 * a / (300 * m ^ 2) + logTerm / T := hscaled
    _ ≤ a / 200 * (206 / (3 * m ^ 2)) +
        a / 200 * (1 / T) := by
      apply add_le_add
      · field_simp
        norm_num
      · exact hlogScaled
    _ = a / 200 * (206 / (3 * m ^ 2) + 1 / T) := by ring

/-- The initialization-period arithmetic used in the final horizon bound. -/
theorem main_horizon_long_enough {m N : ℕ} (hm : 1 ≤ m)
    (hN : 2 * m ^ 2 ≤ N) : m ^ 2 ≤ N - m := by
  have hmm : m ≤ m ^ 2 := by
    nlinarith [Nat.mul_le_mul_left m hm]
  omega

/-- Adding at most `m` initialization cost preserves the advertised constant. -/
theorem initialization_average_bound
    {a m N mainCost : ℝ}
    (ha : 1 ≤ a) (hm : 0 < m) (hN : m ^ 2 ≤ N)
    (hmain : mainCost ≤ 6 * a / m) :
    m / N + mainCost ≤ 7 * a / m := by
  have hNpos : 0 < N := lt_of_lt_of_le (sq_pos_of_pos hm) hN
  have hinit : m / N ≤ 1 / m := by
    rw [div_le_div_iff₀ hNpos hm]
    nlinarith
  have hone : 1 / m ≤ a / m := by
    exact div_le_div_of_nonneg_right ha hm.le
  calc
    m / N + mainCost ≤ 1 / m + 6 * a / m :=
      add_le_add hinit hmain
    _ ≤ a / m + 6 * a / m := add_le_add_left hone _
    _ = 7 * a / m := by ring

end

end FD1D
