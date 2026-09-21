/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.TruncatedOrderTotient
import Mathlib.Tactic

/-!
# Rational Rankin bounds for truncated exact-order sums

This isolates the analytic inequality from any particular factorization
certificate.  Rational weights make every later finite certificate exactly
checkable.
-/

namespace BGS.NumberTheory

/-- The weighted divisor sum used by the rational Rankin estimate. -/
def weightedTotientDivisorSum
    (N : ℕ) (weight : ℕ → ℚ) : ℚ :=
  ∑ order ∈ N.divisors,
    (order.totient : ℚ) / order * weight order

private theorem one_le_cap_mul_weight_of_twelfthPower
    {order bound : ℕ} {weight cap : ℚ}
    (horderPos : 0 < order)
    (horderBound : order ≤ bound)
    (hweightNonneg : 0 ≤ weight)
    (hweightPower : 1 ≤ (order : ℚ) * weight ^ 12)
    (hcapNonneg : 0 ≤ cap)
    (hboundCap : (bound : ℚ) ≤ cap ^ 12) :
    1 ≤ cap * weight := by
  have hboundNonneg : (0 : ℚ) ≤ bound := by positivity
  have hproduct :
      (bound : ℚ) ≤
        (order : ℚ) * (cap * weight) ^ 12 := by
    calc
      (bound : ℚ) = (bound : ℚ) * 1 := by ring
      _ ≤ cap ^ 12 * ((order : ℚ) * weight ^ 12) := by
        gcongr
      _ = (order : ℚ) * (cap * weight) ^ 12 := by ring
  have horderCast : (order : ℚ) ≤ bound := by
    exact_mod_cast horderBound
  have horderProduct :
      (order : ℚ) ≤
        (order : ℚ) * (cap * weight) ^ 12 :=
    horderCast.trans hproduct
  have hpower : (1 : ℚ) ≤ (cap * weight) ^ 12 := by
    apply
      (mul_le_mul_iff_right₀
        (show (0 : ℚ) < order by exact_mod_cast horderPos)).mp
    simpa using horderProduct
  have hcapWeightNonneg : 0 ≤ cap * weight :=
    mul_nonneg hcapNonneg hweightNonneg
  apply
    (pow_le_pow_iff_left₀
      (show (0 : ℚ) ≤ 1 by norm_num)
      hcapWeightNonneg
      (show (12 : ℕ) ≠ 0 by norm_num)).mp
  simpa using hpower

/-- Abstract rational-weight Rankin bound.

For every divisor order in the truncated range, the hypotheses say that
`weight(order)` is at least its inverse twelfth root, while `cap` is at
least the twelfth root of `bound`.  The conclusion bounds the exact
truncated root count by a weighted sum over all divisors of `N`. -/
theorem truncatedOrderTotientSum_cast_le_weightedRankin
    (N bound : ℕ) (weight : ℕ → ℚ) (cap : ℚ)
    (hweightNonneg :
      ∀ order ∈ N.divisors, 0 ≤ weight order)
    (hweightPower :
      ∀ order ∈ N.divisors,
        1 ≤ (order : ℚ) * (weight order) ^ 12)
    (hcapNonneg : 0 ≤ cap)
    (hboundCap : (bound : ℚ) ≤ cap ^ 12) :
    (truncatedOrderTotientSum N bound : ℚ) ≤
      (bound : ℚ) * cap *
        weightedTotientDivisorSum N weight := by
  let selected :=
    N.divisors.filter
      (fun order ↦ 2 < order ∧ order ≤ bound)
  let summand : ℕ → ℚ := fun order ↦
    (order.totient : ℚ) / order * weight order
  have hsummandNonneg :
      ∀ order ∈ N.divisors, 0 ≤ summand order := by
    intro order horder
    exact mul_nonneg
      (div_nonneg (by positivity) (by positivity))
      (hweightNonneg order horder)
  have hselectedWeighted :
      (∑ order ∈ selected, summand order) ≤
        ∑ order ∈ N.divisors, summand order := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
    intro order horder _hnotSelected
    exact hsummandNonneg order horder
  have hterm :
      ∀ order ∈ selected,
        (order.totient : ℚ) ≤
          (bound : ℚ) * cap * summand order := by
    intro order horder
    have horderData := (Finset.mem_filter.mp horder)
    have horderDvd := (Nat.mem_divisors.mp horderData.1).1
    have hNNe := (Nat.mem_divisors.mp horderData.1).2
    have horderNe : order ≠ 0 := by
      intro hzero
      subst order
      simp only [zero_dvd_iff] at horderDvd
      exact hNNe horderDvd
    have horderPos : 0 < order := Nat.pos_of_ne_zero horderNe
    have hone :
        (1 : ℚ) ≤ cap * weight order :=
      one_le_cap_mul_weight_of_twelfthPower
        horderPos horderData.2.2
        (hweightNonneg order horderData.1)
        (hweightPower order horderData.1)
        hcapNonneg hboundCap
    have horderLe :
        (order : ℚ) ≤ (bound : ℚ) * cap * weight order := by
      calc
        (order : ℚ) ≤ bound := by exact_mod_cast horderData.2.2
        _ = (bound : ℚ) * 1 := by ring
        _ ≤ (bound : ℚ) * (cap * weight order) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
        _ = (bound : ℚ) * cap * weight order := by ring
    have hratioNonneg :
        0 ≤ (order.totient : ℚ) / order :=
      div_nonneg (by positivity) (by positivity)
    calc
      (order.totient : ℚ) =
          ((order.totient : ℚ) / order) * order := by
            rw [div_mul_cancel₀]
            exact_mod_cast horderNe
      _ ≤ ((order.totient : ℚ) / order) *
          ((bound : ℚ) * cap * weight order) :=
        mul_le_mul_of_nonneg_left horderLe hratioNonneg
      _ = (bound : ℚ) * cap * summand order := by
        simp only [summand]
        ring
  have hselected :
      (∑ order ∈ selected, (order.totient : ℚ)) ≤
        (bound : ℚ) * cap *
          (∑ order ∈ selected, summand order) := by
    calc
      (∑ order ∈ selected, (order.totient : ℚ)) ≤
          ∑ order ∈ selected,
            ((bound : ℚ) * cap * summand order) :=
        Finset.sum_le_sum hterm
      _ = (bound : ℚ) * cap *
          (∑ order ∈ selected, summand order) := by
        rw [Finset.mul_sum]
  calc
    (truncatedOrderTotientSum N bound : ℚ) =
        ∑ order ∈ selected, (order.totient : ℚ) := by
      simp only [truncatedOrderTotientSum, selected, Nat.cast_sum]
    _ ≤ (bound : ℚ) * cap *
        (∑ order ∈ selected, summand order) :=
      hselected
    _ ≤ (bound : ℚ) * cap *
        (∑ order ∈ N.divisors, summand order) :=
      mul_le_mul_of_nonneg_left hselectedWeighted
        (mul_nonneg (by positivity) hcapNonneg)
    _ = (bound : ℚ) * cap *
        weightedTotientDivisorSum N weight := by
      simp only [weightedTotientDivisorSum, summand]

end BGS.NumberTheory
