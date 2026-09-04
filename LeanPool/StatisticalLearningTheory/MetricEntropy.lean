/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.StatisticalLearningTheory.CoveringNumber

/-!
# Metric Entropy

Metric entropy and its square root, together with the monotonicity and cardinality estimates used
in Dudley's bound.

## Main definitions

* `metricEntropy`: log N(ε, s)
* `sqrtEntropy`: √log N(ε, s)

## Main results

* Monotonicity of metric entropy and square-root entropy in the covering radius
* `sqrt_log_card_le_sqrtEntropy_of_card_le`

-/

noncomputable section

namespace LeanPool.StatisticalLearningTheory

open Set Metric Real MeasureTheory
open scoped BigOperators ENNReal

section

variable {A : Type*} [PseudoMetricSpace A]

/-!
## Metric Entropy (Real-valued)
-/

/-- Helper to compute metric entropy given a natural number. -/
def metricEntropyOfNat (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else Real.log n

lemma metricEntropyOfNat_mono {n m : ℕ} (h : n ≤ m) :
    metricEntropyOfNat n ≤ metricEntropyOfNat m := by
  unfold metricEntropyOfNat
  split_ifs with hn hm hm
  · exact le_rfl
  · push Not at hm
    exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_of_lt hm))
  · push Not at hn
    omega
  · push Not at hn
    exact Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < n)) (Nat.cast_le.mpr h)

/-- Metric entropy: log of the covering number.
    Returns 0 if the covering number is infinite or ≤ 1 (to avoid log issues). -/
def metricEntropy (eps : ℝ) (s : Set A) : ℝ :=
  match _h : coveringNumber eps s with
  | ⊤ => 0
  | (n : ℕ) => metricEntropyOfNat n

/-- Metric entropy is anti-monotone in ε. Requires `coveringNumber eps1 s < ⊤`. -/
lemma metricEntropy_anti_eps {eps1 eps2 : ℝ} {s : Set A}
    (heps : eps1 ≤ eps2)
    (hfin1 : coveringNumber eps1 s < ⊤) : metricEntropy eps2 s ≤ metricEntropy eps1 s := by
  unfold metricEntropy
  have hcov := coveringNumber_anti_eps heps (s := s)
  have hfin2 : coveringNumber eps2 s < ⊤ := lt_of_le_of_lt hcov hfin1
  split
  · rename_i h2
    rw [h2] at hfin2
    exact absurd rfl (ne_of_lt hfin2)
  · split
    · rename_i n2 h2 h1
      rw [h1] at hfin1
      exact absurd rfl (ne_of_lt hfin1)
    · rename_i n2 h2 n1 h1
      have hle : n2 ≤ n1 := by
        rw [h1, h2] at hcov
        exact WithTop.coe_le_coe.mp hcov
      exact metricEntropyOfNat_mono hle

/-!
## Square Root of Entropy (Real-valued)
-/

/-- Square root of metric entropy: √log N(ε, s). -/
def sqrtEntropy (eps : ℝ) (s : Set A) : ℝ :=
  Real.sqrt (metricEntropy eps s)

/-- Square root entropy is anti-monotone in epsilon (requires finite covering number). -/
lemma sqrtEntropy_anti_eps {eps1 eps2 : ℝ} {s : Set A}
    (heps : eps1 ≤ eps2) (hfin1 : coveringNumber eps1 s < ⊤) :
    sqrtEntropy eps2 s ≤ sqrtEntropy eps1 s :=
  Real.sqrt_le_sqrt (metricEntropy_anti_eps heps hfin1)

/-- Square root entropy is anti-monotone in epsilon for totally bounded sets. -/
lemma sqrtEntropy_anti_eps_of_totallyBounded {eps1 eps2 : ℝ} {s : Set A}
    (heps1 : 0 < eps1) (heps : eps1 ≤ eps2) (hs : TotallyBounded s) :
    sqrtEntropy eps2 s ≤ sqrtEntropy eps1 s :=
  sqrtEntropy_anti_eps heps (coveringNumber_lt_top_of_totallyBounded heps1 hs)

/-- If a finset has cardinality ≤ coveringNumber(eps, s), then √(log card) ≤ sqrtEntropy.
    This is the key lemma for using GoodDyadicNets in the Dudley bound. -/
lemma sqrt_log_card_le_sqrtEntropy_of_card_le {eps : ℝ} {s : Set A} {n : ℕ}
    (heps : 0 < eps) (hs : TotallyBounded s)
    (hle : (n : WithTop ℕ) ≤ coveringNumber eps s) :
    Real.sqrt (Real.log n) ≤ sqrtEntropy eps s := by
  have hfin : coveringNumber eps s < ⊤ := coveringNumber_lt_top_of_totallyBounded heps hs
  have hne : coveringNumber eps s ≠ ⊤ := ne_top_of_lt hfin
  let m := (coveringNumber eps s).untop hne
  have hm : coveringNumber eps s = m := (WithTop.coe_untop _ hne).symm
  rw [hm] at hle
  have hnm : n ≤ m := WithTop.coe_le_coe.mp hle
  unfold sqrtEntropy metricEntropy
  split
  · -- Case: coveringNumber = ⊤ (contradicts hfin)
    rename_i h; rw [h] at hfin; exact absurd rfl (ne_of_lt hfin)
  · -- Case: coveringNumber = some m'
    rename_i m' hm'
    have hmm' : m = m' := by
      have h1 : (↑m : WithTop ℕ) = coveringNumber eps s := hm.symm
      have h2 : coveringNumber eps s = ↑m' := hm'
      have : (↑m : WithTop ℕ) = ↑m' := h1.trans h2
      exact WithTop.coe_injective this
    subst hmm'
    apply Real.sqrt_le_sqrt
    unfold metricEntropyOfNat
    split_ifs with h1
    · -- Case m ≤ 1: metricEntropyOfNat = 0
      have hn_le : n ≤ 1 := le_trans hnm h1
      interval_cases n
      · simp
      · simp
    · -- Case m > 1: metricEntropyOfNat = log m
      push Not at h1
      by_cases hn1 : n ≤ 1
      · -- n ≤ 1: log n ≤ 0 ≤ log m
        have hlog_n : Real.log n ≤ 0 := by
          interval_cases n
          · simp
          · simp
        have hlog_m : 0 ≤ Real.log (m : ℝ) :=
          Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ m))
        linarith
      · -- n > 1: use log monotonicity
        push Not at hn1
        apply Real.log_le_log
        · exact Nat.cast_pos.mpr (by omega : 0 < n)
        · exact Nat.cast_le.mpr hnm

end

end LeanPool.StatisticalLearningTheory
