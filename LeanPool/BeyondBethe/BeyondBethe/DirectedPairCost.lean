/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.DirectedElementary
public import LeanPool.BeyondBethe.BeyondBethe.TransferIdentity
public import LeanPool.BeyondBethe.BeyondBethe.Gain
public import Mathlib.Tactic

/-! # Directed Pair Cost -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Directed rational evaluation of the four-core transfer cost

The algorithm does not need to approximate a pair capacity.  It only needs a
one-sided test for the local transfer cost used by the clean-pair lemma.  The
formula below evaluates every logarithm over `ℚ` and is deliberately directed
upward: passing the rational test proves that the true real cost passes.
-/

/-- The precision-scheduled lower endpoint for a positive rational logarithm. -/
def scheduledLogLower (q : ℚ) (p : ℕ) : ℚ :=
  directedLogLower q (directedLogTerms q p)

/-- The precision-scheduled upper endpoint for a positive rational logarithm. -/
def scheduledLogUpper (q : ℚ) (p : ℕ) : ℚ :=
  directedLogUpper q (directedLogTerms q p)

theorem scheduledLogLower_le_log {q : ℚ} (hq : 0 < q) (p : ℕ) :
    (scheduledLogLower q p : ℝ) ≤ Real.log (q : ℝ) :=
  directedLogLower_le_log hq _

theorem log_le_scheduledLogUpper {q : ℚ} (hq : 0 < q) (p : ℕ) :
    Real.log (q : ℝ) ≤ (scheduledLogUpper q p : ℝ) :=
  log_le_directedLogUpper hq _

theorem scheduledLog_width_le {q : ℚ} (hq : 0 < q) (p : ℕ) :
    scheduledLogUpper q p - scheduledLogLower q p ≤ (1 / 2 : ℚ) ^ p :=
  directedLog_width_le_dyadic hq p

/-- Directed upper endpoint for `log (1 / transferU τ (X i) j)`.
The final sum is `log (complementProduct (X i))`. -/
def directedTransferCostUpper {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (p : ℕ) : ℚ :=
  -(1 + τ) * scheduledLogLower (X i j) p -
      scheduledLogLower (1 - X i j) p +
    ∑ k, scheduledLogUpper (1 - X i k) p

theorem transferCost_le_directedTransferCostUpper
    {n : ℕ} {τ : ℚ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ : -1 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (i j : Fin n) (p : ℕ) :
    Real.log (1 / transferU (τ : ℝ)
        (fun k ↦ ((X i k : ℚ) : ℝ)) j) ≤
      (directedTransferCostUpper τ X i j p : ℝ) := by
  have hxq : 0 < X i j := by
    have h := (hXint i).2 j |>.1
    norm_num only [Rat.cast_pos] at h
    exact h
  have hcxq : 0 < 1 - X i j := by
    have := (hXint i).2 j |>.2
    have hxltq : X i j < 1 :=
      (Rat.cast_lt (K := ℝ)).mp (by simpa using this)
    linarith
  have hlogx := scheduledLogLower_le_log hxq p
  have hlogc := scheduledLogLower_le_log hcxq p
  have hcoef : (0 : ℝ) ≤ 1 + (τ : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) ≤ 1 + τ)
  have hfirst : -(1 + (τ : ℝ)) * Real.log (X i j : ℝ) ≤
      -(1 + (τ : ℝ)) * (scheduledLogLower (X i j) p : ℝ) := by
    exact mul_le_mul_of_nonpos_left hlogx (neg_nonpos.mpr hcoef)
  have hsecond : -Real.log ((1 - X i j : ℚ) : ℝ) ≤
      -(scheduledLogLower (1 - X i j) p : ℝ) := neg_le_neg hlogc
  have hsum : Real.log (complementProduct
      (fun k ↦ ((X i k : ℚ) : ℝ))) ≤
      ∑ k, (scheduledLogUpper (1 - X i k) p : ℝ) := by
    rw [complementProduct, Real.log_prod]
    · exact Finset.sum_le_sum fun k _ ↦ by
        have hckq : 0 < 1 - X i k := by
          have := (hXint i).2 k |>.2
          have hxltq : X i k < 1 :=
            (Rat.cast_lt (K := ℝ)).mp (by simpa using this)
          linarith
        simpa using log_le_scheduledLogUpper hckq p
    · intro k _
      exact (sub_pos.mpr ((hXint i).2 k |>.2)).ne'
  rw [log_one_div_transferU (hXint i)]
  rw [directedTransferCostUpper]
  push_cast
  norm_num only [Rat.cast_sub, Rat.cast_one] at hlogc hsecond ⊢
  linarith

/-- The directed endpoint exceeds the true transfer cost by at most one
dyadic unit for each logarithm, with coefficient `1+τ` on the distinguished
coordinate. -/
theorem directedTransferCostUpper_le_add_error
    {n : ℕ} {τ : ℚ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (i j : Fin n) (p : ℕ) :
    (directedTransferCostUpper τ X i j p : ℝ) ≤
      Real.log (1 / transferU (τ : ℝ)
        (fun k ↦ ((X i k : ℚ) : ℝ)) j) +
        (n + 3 : ℝ) * ((1 / 2 : ℚ) ^ p : ℚ) := by
  have hxq : 0 < X i j := by
    have h := (hXint i).2 j |>.1
    norm_num only [Rat.cast_pos] at h
    exact h
  have hcxq : 0 < 1 - X i j := by
    have := (hXint i).2 j |>.2
    have hxltq : X i j < 1 :=
      (Rat.cast_lt (K := ℝ)).mp (by simpa using this)
    linarith
  let e : ℚ := (1 / 2 : ℚ) ^ p
  have hwidthx := scheduledLog_width_le hxq p
  have hwidthc := scheduledLog_width_le hcxq p
  have hxlo := scheduledLogLower_le_log hxq p
  have hxhi := log_le_scheduledLogUpper hxq p
  have hclo := scheduledLogLower_le_log hcxq p
  have hchi := log_le_scheduledLogUpper hcxq p
  have hxerr : Real.log (X i j : ℝ) ≤
      (scheduledLogLower (X i j) p : ℝ) + (e : ℝ) := by
    have hw : ((scheduledLogUpper (X i j) p -
        scheduledLogLower (X i j) p : ℚ) : ℝ) ≤ (e : ℝ) := by
      exact_mod_cast hwidthx
    push_cast at hw
    linarith
  have hcerr : Real.log ((1 - X i j : ℚ) : ℝ) ≤
      (scheduledLogLower (1 - X i j) p : ℝ) + (e : ℝ) := by
    have hw : ((scheduledLogUpper (1 - X i j) p -
        scheduledLogLower (1 - X i j) p : ℚ) : ℝ) ≤ (e : ℝ) := by
      exact_mod_cast hwidthc
    push_cast at hw
    linarith
  have hsumUpper :
      ∑ k, (scheduledLogUpper (1 - X i k) p : ℝ) ≤
        Real.log (complementProduct (fun k ↦ ((X i k : ℚ) : ℝ))) +
          n * (e : ℝ) := by
    rw [complementProduct, Real.log_prod]
    · have hpoint : ∀ k : Fin n,
          (scheduledLogUpper (1 - X i k) p : ℝ) ≤
            Real.log (((1 - X i k : ℚ) : ℝ)) + (e : ℝ) := by
        intro k
        have hckq : 0 < 1 - X i k := by
          have := (hXint i).2 k |>.2
          have hxltq : X i k < 1 :=
            (Rat.cast_lt (K := ℝ)).mp (by simpa using this)
          linarith
        have hw := scheduledLog_width_le hckq p
        have hlo := scheduledLogLower_le_log hckq p
        have hwR : ((scheduledLogUpper (1 - X i k) p -
            scheduledLogLower (1 - X i k) p : ℚ) : ℝ) ≤ (e : ℝ) := by
          exact_mod_cast hw
        push_cast at hwR
        linarith
      calc
        ∑ k, (scheduledLogUpper (1 - X i k) p : ℝ) ≤
            ∑ k, (Real.log (((1 - X i k : ℚ) : ℝ)) + (e : ℝ)) :=
          Finset.sum_le_sum fun k _ ↦ hpoint k
        _ = (∑ k, Real.log (((1 - X i k : ℚ) : ℝ))) + n * (e : ℝ) := by
          simp [Finset.sum_add_distrib]
        _ = (∑ k, Real.log (1 - (X i k : ℝ))) + n * (e : ℝ) := by
          congr 2
          funext k
          norm_num
    · intro k _
      exact (sub_pos.mpr ((hXint i).2 k |>.2)).ne'
  have hτR0 : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ0
  have hτR1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hmul : -(1 + (τ : ℝ)) *
        (scheduledLogLower (X i j) p : ℝ) ≤
      -(1 + (τ : ℝ)) * Real.log (X i j : ℝ) +
        2 * (e : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hxerr
      (show 0 ≤ 1 + (τ : ℝ) by linarith)
    nlinarith
  have hnegc : -(scheduledLogLower (1 - X i j) p : ℝ) ≤
      -Real.log ((1 - X i j : ℚ) : ℝ) + (e : ℝ) := by linarith
  change (directedTransferCostUpper τ X i j p : ℝ) ≤
    Real.log (1 / transferU (τ : ℝ)
      (fun k ↦ ((X i k : ℚ) : ℝ)) j) + (n + 3 : ℝ) * (e : ℝ)
  rw [log_one_div_transferU (hXint i)]
  rw [directedTransferCostUpper]
  push_cast
  norm_num only [Rat.cast_sub, Rat.cast_one] at hcerr hnegc ⊢
  calc
    -(1 + (τ : ℝ)) * (scheduledLogLower (X i j) p : ℝ) -
          (scheduledLogLower (1 - X i j) p : ℝ) +
        ∑ k, (scheduledLogUpper (1 - X i k) p : ℝ) ≤
        (-(1 + (τ : ℝ)) * Real.log (X i j : ℝ) +
            2 * (e : ℝ)) +
          (-Real.log (1 - (X i j : ℝ)) +
            (e : ℝ)) +
          (Real.log (complementProduct (fun k ↦ ((X i k : ℚ) : ℝ))) +
            n * (e : ℝ)) := by
      linarith
    _ = -(1 + (τ : ℝ)) * Real.log (X i j : ℝ) -
          Real.log (1 - (X i j : ℝ)) +
          Real.log (complementProduct (fun k ↦ ((X i k : ℚ) : ℝ))) +
          (n + 3 : ℝ) * (e : ℝ) := by ring

/-- Directed upper endpoint for the sum of the four core transfer costs. -/
def directedFourCoreCostUpper {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (r s a b : Fin n) (p : ℕ) : ℚ :=
  directedTransferCostUpper τ X r a p +
    directedTransferCostUpper τ X r b p +
    directedTransferCostUpper τ X s a p +
    directedTransferCostUpper τ X s b p

theorem fourCoreTransferCost_le_directedFourCoreCostUpper
    {n : ℕ} {τ : ℚ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ : -1 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (r s a b : Fin n) (p : ℕ) :
    fourCoreTransferCost (τ : ℝ)
        (fun i j ↦ ((X i j : ℚ) : ℝ)) r s a b ≤
      (directedFourCoreCostUpper τ X r s a b p : ℝ) := by
  unfold fourCoreTransferCost directedFourCoreCostUpper
  push_cast
  linarith [transferCost_le_directedTransferCostUpper hτ hXint r a p,
    transferCost_le_directedTransferCostUpper hτ hXint r b p,
    transferCost_le_directedTransferCostUpper hτ hXint s a p,
    transferCost_le_directedTransferCostUpper hτ hXint s b p]

theorem directedFourCoreCostUpper_le_add_error
    {n : ℕ} {τ : ℚ} {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (r s a b : Fin n) (p : ℕ) :
    (directedFourCoreCostUpper τ X r s a b p : ℝ) ≤
      fourCoreTransferCost (τ : ℝ)
        (fun i j ↦ ((X i j : ℚ) : ℝ)) r s a b +
        4 * (n + 3 : ℝ) * ((1 / 2 : ℚ) ^ p : ℚ) := by
  have hra := directedTransferCostUpper_le_add_error hτ0 hτ1 hXint r a p
  have hrb := directedTransferCostUpper_le_add_error hτ0 hτ1 hXint r b p
  have hsa := directedTransferCostUpper_le_add_error hτ0 hτ1 hXint s a p
  have hsb := directedTransferCostUpper_le_add_error hτ0 hτ1 hXint s b p
  have hecast : ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) = (1 / 2 : ℝ) ^ p := by
    norm_num
  unfold fourCoreTransferCost directedFourCoreCostUpper
  push_cast
  rw [← hecast]
  linarith

end BeyondBethe
