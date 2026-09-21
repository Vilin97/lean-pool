/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Basic

/-!
# Parameter choices

This file makes the parameter choices in the hierarchical matching argument
computationally exact.  Natural-number division is the floor in the definition
of the tree depth.
-/

namespace FD1D

noncomputable section

open Filter Asymptotics

/-- The regularization parameter `a = 200 * ceil(log₂(m+1))`. -/
def parameterA (m : ℕ) : ℕ :=
  200 * Nat.clog 2 (m + 1)

/-- The positive integer whose largest dyadic power determines the tree. -/
def depthTarget (m : ℕ) : ℕ :=
  max 1 (m / parameterA m)

/-- The depth of the complete dyadic tree. -/
def treeDepth (m : ℕ) : ℕ :=
  Nat.log 2 (depthTarget m)

/-- The number `n = 2^L` of leaves in the complete dyadic tree. -/
def leafCount (m : ℕ) : ℕ :=
  2 ^ treeDepth m

@[simp] theorem policyA_eq_parameterA (m : ℕ) :
    policyA m = parameterA m := by
  unfold policyA parameterA
  rw [← Real.natCeil_logb_natCast 2 (m + 1)]
  norm_num

theorem parameterA_eq_policyA (m : ℕ) :
    parameterA m = policyA m :=
  (policyA_eq_parameterA m).symm

theorem parameterA_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < parameterA m := by
  unfold parameterA
  exact Nat.mul_pos (by norm_num)
    (Nat.clog_pos (by norm_num) (by omega))

theorem parameterA_ne_zero {m : ℕ} (hm : 1 ≤ m) :
    parameterA m ≠ 0 :=
  (parameterA_pos hm).ne'

theorem parameterA_cast_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < (parameterA m : ℝ) := by
  exact_mod_cast parameterA_pos hm

theorem parameterA_cast_ne_zero {m : ℕ} (hm : 1 ≤ m) :
    (parameterA m : ℝ) ≠ 0 :=
  (parameterA_cast_pos hm).ne'

@[simp] theorem natFloor_parameterRatio (m : ℕ) :
    ⌊(m : ℝ) / (parameterA m : ℝ)⌋₊ = m / parameterA m := by
  simpa using
    (Nat.floor_div_natCast (m : ℝ) (parameterA m))

theorem depthTarget_pos (m : ℕ) :
    0 < depthTarget m := by
  simp [depthTarget]

theorem depthTarget_ne_zero (m : ℕ) :
    depthTarget m ≠ 0 :=
  (depthTarget_pos m).ne'

theorem depthTarget_le {m : ℕ} (hm : 1 ≤ m) :
    depthTarget m ≤ m := by
  simp only [depthTarget, max_le_iff]
  exact ⟨hm, Nat.div_le_self _ _⟩

theorem treeDepth_le_clog {m : ℕ} (hm : 1 ≤ m) :
    treeDepth m ≤ Nat.clog 2 (m + 1) := by
  calc
    treeDepth m = Nat.log 2 (depthTarget m) := rfl
    _ ≤ Nat.log 2 m := Nat.log_mono_right (depthTarget_le hm)
    _ ≤ Nat.clog 2 m := Nat.log_le_clog 2 m
    _ ≤ Nat.clog 2 (m + 1) :=
      Nat.clog_mono_right 2 (Nat.le_succ m)

theorem two_hundred_mul_treeDepth_le_parameterA {m : ℕ}
    (hm : 1 ≤ m) :
    200 * treeDepth m ≤ parameterA m := by
  simpa [parameterA] using
    Nat.mul_le_mul_left 200 (treeDepth_le_clog hm)

theorem parameterA_ge_treeDepth {m : ℕ} (hm : 1 ≤ m) :
    parameterA m ≥ 200 * treeDepth m :=
  two_hundred_mul_treeDepth_le_parameterA hm

theorem parameterA_cast_ge_treeDepth {m : ℕ} (hm : 1 ≤ m) :
    (200 : ℝ) * treeDepth m ≤ parameterA m := by
  exact_mod_cast two_hundred_mul_treeDepth_le_parameterA hm

@[simp] theorem leafCount_eq_pow (m : ℕ) :
    leafCount m = 2 ^ treeDepth m :=
  rfl

theorem leafCount_pos (m : ℕ) :
    0 < leafCount m := by
  simp [leafCount]

theorem one_le_leafCount (m : ℕ) :
    1 ≤ leafCount m :=
  (leafCount_pos m)

theorem leafCount_ne_zero (m : ℕ) :
    leafCount m ≠ 0 :=
  (leafCount_pos m).ne'

theorem leafCount_cast_pos (m : ℕ) :
    0 < (leafCount m : ℝ) := by
  exact_mod_cast leafCount_pos m

theorem leafCount_cast_ne_zero (m : ℕ) :
    (leafCount m : ℝ) ≠ 0 :=
  (leafCount_cast_pos m).ne'

/-- `n` is a power of two not exceeding `max(1, floor(m/a))`. -/
theorem leafCount_le_depthTarget (m : ℕ) :
    leafCount m ≤ depthTarget m := by
  exact Nat.pow_log_le_self 2 (depthTarget_ne_zero m)

/-- Exponent form of the fact that `n` is the largest admissible power of two. -/
theorem pow_le_depthTarget_iff {m k : ℕ} :
    2 ^ k ≤ depthTarget m ↔ k ≤ treeDepth m := by
  rw [treeDepth, Nat.le_log_iff_pow_le (by norm_num) (depthTarget_ne_zero m)]

/-- Every power of two below the target is at most `n`. -/
theorem pow_le_leafCount_of_pow_le_depthTarget {m k : ℕ}
    (hk : 2 ^ k ≤ depthTarget m) :
    2 ^ k ≤ leafCount m := by
  exact Nat.pow_le_pow_right (by norm_num)
    (pow_le_depthTarget_iff.mp hk)

/-- The target is strictly less than twice its largest dyadic power. -/
theorem depthTarget_lt_two_mul_leafCount (m : ℕ) :
    depthTarget m < 2 * leafCount m := by
  change depthTarget m < 2 * 2 ^ Nat.log 2 (depthTarget m)
  simpa [pow_succ'] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (depthTarget m))

theorem parameterQuotient_lt_two_mul_leafCount (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by
  exact (le_max_right 1 (m / parameterA m)).trans_lt
    (depthTarget_lt_two_mul_leafCount m)

/-- Natural-number form of the reciprocal leaf-size estimate. -/
theorem m_le_two_mul_parameterA_mul_leafCount {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 * parameterA m * leafCount m := by
  have hlt : m < (2 * leafCount m) * parameterA m :=
    (Nat.div_lt_iff_lt_mul (parameterA_pos hm)).mp
      (parameterQuotient_lt_two_mul_leafCount m)
  calc
    m ≤ (2 * leafCount m) * parameterA m := Nat.le_of_lt hlt
    _ = 2 * parameterA m * leafCount m := by ac_rfl

/-- The paper's estimate `1/n ≤ 2a/m`, over the reals. -/
theorem one_div_leafCount_le_two_mul_parameterA_div {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by
  apply (div_le_div_iff₀ (leafCount_cast_pos m)
    (by exact_mod_cast hm)).2
  norm_num
  exact_mod_cast m_le_two_mul_parameterA_mul_leafCount hm

/-- A convenient explicit logarithmic bound, still written in base two. -/
theorem parameterA_cast_le_logb {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 800 * Real.logb 2 m := by
  have hlog_one :
      (1 : ℝ) ≤ Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    calc
      (1 : ℝ) = Real.logb 2 2 :=
        (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        exact_mod_cast (show 2 ≤ m + 1 by omega)
  have hceil :
      (Nat.clog 2 (m + 1) : ℝ) ≤
        2 * Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_le_two_mul (by linarith)
  have hsq : m + 1 ≤ m ^ 2 := by
    nlinarith
  have hlog_sq :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        2 * Real.logb 2 (m : ℝ) := by
    calc
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
          Real.logb 2 ((m : ℝ) ^ 2) := by
        apply Real.logb_le_logb_of_le (by norm_num)
          (by positivity)
        exact_mod_cast hsq
      _ = 2 * Real.logb 2 m := by
        rw [Real.logb_pow]
        norm_num
  rw [parameterA, Nat.cast_mul]
  norm_num
  nlinarith

/-- Explicit natural-log form of `a = O(log m)`, valid for `m ≥ 2`. -/
theorem parameterA_cast_le_log {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (800 / Real.log 2) * Real.log m := by
  calc
    (parameterA m : ℝ) ≤ 800 * Real.logb 2 m :=
      parameterA_cast_le_logb hm
    _ = (800 / Real.log 2) * Real.log m := by
      rw [← Real.log_div_log]
      ring

/-- Asymptotic form of the explicit logarithmic estimate. -/
theorem parameterA_isBigO_log :
    (fun m : ℕ => (parameterA m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  refine IsBigO.of_bound (800 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  exact parameterA_cast_le_log hm

end

end FD1D
