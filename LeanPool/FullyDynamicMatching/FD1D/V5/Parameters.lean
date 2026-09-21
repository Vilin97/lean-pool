/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Tree

/-!
# Parameters for manuscript bundle v5

This module records the exact choices

`a = 2000 * ceil(log₂(m+1))` and
`n = 2^L = 2^floor(log₂(max(1, floor(m/a))))`.
-/

namespace FD1D.V5

noncomputable section

open Filter Asymptotics

/-- The v5 regularization parameter. -/
def parameterA (m : ℕ) : ℕ :=
  2000 * Nat.clog 2 (m + 1)

/-- The positive integer whose largest dyadic power determines the depth. -/
def depthTarget (m : ℕ) : ℕ :=
  max 1 (m / parameterA m)

/-- The depth of the complete dyadic partition. -/
def treeDepth (m : ℕ) : ℕ :=
  Nat.log 2 (depthTarget m)

/-- The number of leaves in the complete dyadic partition. -/
def leafCount (m : ℕ) : ℕ :=
  2 ^ treeDepth m

theorem parameterA_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < parameterA m := by
  unfold parameterA
  exact Nat.mul_pos (by norm_num)
    (Nat.clog_pos (by norm_num) (by omega))

theorem parameterA_cast_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < (parameterA m : ℝ) := by
  exact_mod_cast parameterA_pos hm

theorem depthTarget_pos (m : ℕ) :
    0 < depthTarget m := by
  simp [depthTarget]

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

/-- The exact depth budget `a ≥ 2000 L`. -/
theorem two_thousand_mul_treeDepth_le_parameterA {m : ℕ}
    (hm : 1 ≤ m) :
    2000 * treeDepth m ≤ parameterA m := by
  simpa [parameterA] using
    Nat.mul_le_mul_left 2000 (treeDepth_le_clog hm)

theorem parameterA_cast_ge_treeDepth {m : ℕ} (hm : 1 ≤ m) :
    (2000 : ℝ) * treeDepth m ≤ parameterA m := by
  exact_mod_cast two_thousand_mul_treeDepth_le_parameterA hm

theorem leafCount_pos (m : ℕ) :
    0 < leafCount m := by
  simp [leafCount]

theorem leafCount_cast_pos (m : ℕ) :
    0 < (leafCount m : ℝ) := by
  exact_mod_cast leafCount_pos m

theorem leafCount_le_depthTarget (m : ℕ) :
    leafCount m ≤ depthTarget m := by
  exact Nat.pow_log_le_self 2 (depthTarget_pos m).ne'

theorem depthTarget_lt_two_mul_leafCount (m : ℕ) :
    depthTarget m < 2 * leafCount m := by
  change depthTarget m < 2 * 2 ^ Nat.log 2 (depthTarget m)
  simpa [pow_succ'] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (depthTarget m))

theorem parameterQuotient_lt_two_mul_leafCount (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by
  exact (le_max_right 1 (m / parameterA m)).trans_lt
    (depthTarget_lt_two_mul_leafCount m)

theorem m_le_two_mul_parameterA_mul_leafCount {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 * parameterA m * leafCount m := by
  have hlt : m < (2 * leafCount m) * parameterA m :=
    (Nat.div_lt_iff_lt_mul (parameterA_pos hm)).mp
      (parameterQuotient_lt_two_mul_leafCount m)
  calc
    m ≤ (2 * leafCount m) * parameterA m := Nat.le_of_lt hlt
    _ = 2 * parameterA m * leafCount m := by ac_rfl

/-- The spatial discretization estimate `1/n ≤ 2a/m`. -/
theorem one_div_leafCount_le_two_mul_parameterA_div {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by
  apply (div_le_div_iff₀ (leafCount_cast_pos m)
    (by exact_mod_cast hm)).2
  norm_num
  exact_mod_cast m_le_two_mul_parameterA_mul_leafCount hm

/-- The potential budget used in the transient energy estimate. -/
theorem log_one_add_two_mul_div_le_parameterA_div_two_thousand
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log
        (1 + 2 * (m : ℝ) / (parameterA m : ℝ)) ≤
      (parameterA m : ℝ) / 2000 := by
  have haNat : 2 ≤ parameterA m := by
    have := parameterA_pos hm
    unfold parameterA at *
    omega
  have ha : (2 : ℝ) ≤ parameterA m := by exact_mod_cast haNat
  have hratio :
      2 * (m : ℝ) / (parameterA m : ℝ) ≤ m := by
    calc
      2 * (m : ℝ) / (parameterA m : ℝ)
          ≤ 2 * (m : ℝ) / 2 := by
            gcongr
      _ = m := by ring
  have hlog :
      Real.log (1 + 2 * (m : ℝ) / (parameterA m : ℝ)) ≤
        Real.log (((m + 1 : ℕ) : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · norm_num at hratio ⊢
      linarith
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog_nonneg :
      0 ≤ Real.log (((m + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have hlog_le_logb :
      Real.log (((m + 1 : ℕ) : ℝ)) ≤
        Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_div_log]
    apply (le_div_iff₀ hlog_two_pos).2
    nlinarith
  have hlogb_le_clog :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        (Nat.clog 2 (m + 1) : ℝ) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  calc
    Real.log
        (1 + 2 * (m : ℝ) / (parameterA m : ℝ))
        ≤ (Nat.clog 2 (m + 1) : ℝ) :=
      hlog.trans (hlog_le_logb.trans hlogb_le_clog)
    _ = (parameterA m : ℝ) / 2000 := by
      simp [parameterA]

/-- A convenient explicit base-two logarithmic upper bound. -/
theorem parameterA_cast_le_logb {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 8000 * Real.logb 2 m := by
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
  have hsq : m + 1 ≤ m ^ 2 := by nlinarith
  have hlog_sq :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        2 * Real.logb 2 (m : ℝ) := by
    calc
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
          Real.logb 2 ((m : ℝ) ^ 2) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
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
      (8000 / Real.log 2) * Real.log (m : ℝ) := by
  calc
    (parameterA m : ℝ) ≤ 8000 * Real.logb 2 m :=
      parameterA_cast_le_logb hm
    _ = (8000 / Real.log 2) * Real.log (m : ℝ) := by
      rw [← Real.log_div_log]
      ring

/-- The same bound in the manuscript's displayed `log(m+1)` form. -/
theorem parameterA_cast_le_log_succ {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (8000 / Real.log 2) * Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono :
      Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 1 ≤ m by omega)
    · exact_mod_cast Nat.le_succ m
  exact (parameterA_cast_le_log hm).trans
    (mul_le_mul_of_nonneg_left hmono
      (div_nonneg (by norm_num) hlogTwo.le))

/-- Asymptotic natural-log form of the parameter estimate. -/
theorem parameterA_isBigO_log :
    (fun m : ℕ => (parameterA m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  refine IsBigO.of_bound (8000 / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega)))]
  exact parameterA_cast_le_log hm

end

end FD1D.V5
