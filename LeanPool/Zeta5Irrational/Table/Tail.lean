/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Potential
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic

/-! # The tail `t ≥ 2` of the potential inequality (6.2): the bound (6.8)
-/

public section

open Finset Set

namespace Zeta5Irrational

/-- For `t ≥ b`, `Uω a b t ≤ log t`. -/
lemma Uω_le_log {a b t : ℝ} (ha : 0 < a) (hab : a < b) (h : b ≤ t) : Uω a b t ≤ Real.log t := by
  rw [Uω_of_ge hab h]
  have hm : 0 < t - (a + b) / 2 := by linarith
  have hsq : Real.sqrt ((t - a) * (t - b)) ≤ t - (a + b) / 2 :=
    sqrt_le_of_sq_le hm.le (by nlinarith)
  have hs0 := Real.sqrt_nonneg ((t - a) * (t - b))
  exact Real.log_le_log (by linarith) (by linarith)

/-- For `t ≥ 2`, `Uρ t ≤ (37/40) log t` (total mass of `ρ` is `37/40`). -/
lemma Uρ_le_log {t : ℝ} (ht : 2 ≤ t) : Uρ t ≤ 37 / 40 * Real.log t := by
  rw [Uρ_expand]
  have h1 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 1) (b := bρ 1) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 1 ≤ 2).trans ht))
      (cρ_pos 1 (by norm_num)).le
  have h2 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 2) (b := bρ 2) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 2 ≤ 2).trans ht))
      (cρ_pos 2 (by norm_num)).le
  have h3 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 3) (b := bρ 3) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 3 ≤ 2).trans ht))
      (cρ_pos 3 (by norm_num)).le
  have h4 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 4) (b := bρ 4) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 4 ≤ 2).trans ht))
      (cρ_pos 4 (by norm_num)).le
  have h5 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 5) (b := bρ 5) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 5 ≤ 2).trans ht))
      (cρ_pos 5 (by norm_num)).le
  have h6 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 6) (b := bρ 6) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 6 ≤ 2).trans ht))
      (cρ_pos 6 (by norm_num)).le
  have h7 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 7) (b := bρ 7) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 7 ≤ 2).trans ht))
      (cρ_pos 7 (by norm_num)).le
  have h8 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 8) (b := bρ 8) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 8 ≤ 2).trans ht))
      (cρ_pos 8 (by norm_num)).le
  have h9 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 9) (b := bρ 9) (by norm_num [aρ, table1]) (by norm_num [aρ, bρ, table1])
        ((by norm_num [bρ, table1] : bρ 9 ≤ 2).trans ht))
      (cρ_pos 9 (by norm_num)).le
  have h10 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 10) (b := bρ 10) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 10 ≤ 2).trans ht))
      (cρ_pos 10 (by norm_num)).le
  have h11 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 11) (b := bρ 11) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 11 ≤ 2).trans ht))
      (cρ_pos 11 (by norm_num)).le
  have h12 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 12) (b := bρ 12) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 12 ≤ 2).trans ht))
      (cρ_pos 12 (by norm_num)).le
  have h13 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 13) (b := bρ 13) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 13 ≤ 2).trans ht))
      (cρ_pos 13 (by norm_num)).le
  have h14 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 14) (b := bρ 14) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 14 ≤ 2).trans ht))
      (cρ_pos 14 (by norm_num)).le
  have h15 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 15) (b := bρ 15) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 15 ≤ 2).trans ht))
      (cρ_pos 15 (by norm_num)).le
  have h16 :=
    mul_le_mul_of_nonneg_left
      (Uω_le_log (a := aρ 16) (b := bρ 16) (by norm_num [aρ, table1])
        (by norm_num [aρ, bρ, table1]) ((by norm_num [bρ, table1] : bρ 16 ≤ 2).trans ht))
      (cρ_pos 16 (by norm_num)).le
  norm_num [cρ, table1] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 ⊢
  linarith

/-- The lower bound for `V` used in (6.8): `V(t) ≥ 2π√t + log t - 6α (log t + α²/t)`. -/
lemma Vfield_ge_tail {t : ℝ} (ht : 2 ≤ t) :
    2 * Real.pi * Real.sqrt t + Real.log t - 6 * (3 / 40) * (Real.log t + (3 / 40) ^ 2 / t) ≤
      Vfield t := by
  unfold Vfield
  have ht0 : 0 < t := by linarith
  have hcont : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    (continuous_const.add (continuous_pow 2)).log
      (fun u => by simp only [Pi.add_apply]; nlinarith [sq_nonneg u])
  have h1 : Real.log t ≤ ∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2) := by
    have e : ∫ u in (0 : ℝ)..1, Real.log t = Real.log t := by simp
    rw [← e]
    refine
      intervalIntegral.integral_mono_on zero_le_one (by simp) (hcont.intervalIntegrable _ _) ?_
    intro u _
    exact Real.log_le_log ht0 (by nlinarith)
  have h2 :
    ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) ≤ 3 / 40 * (Real.log t + (3 / 40) ^ 2 / t) := by
    have e :
      ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + (3 / 40) ^ 2) =
        3 / 40 * Real.log (t + (3 / 40) ^ 2) :=
      by simp
    have hle :
      ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) ≤
        ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + (3 / 40) ^ 2) := by
      refine
        intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _) (by simp)
          ?_
      intro u hu
      exact Real.log_le_log (by positivity) (by nlinarith [hu.1, hu.2])
    have hlog : Real.log (t + (3 / 40) ^ 2) ≤ Real.log t + (3 / 40) ^ 2 / t := by
      have e2 : Real.log (t + (3 / 40) ^ 2) = Real.log t + Real.log (1 + (3 / 40) ^ 2 / t) := by
        rw [← Real.log_mul ht0.ne' (by positivity)]
        congr 1; field_simp
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (3 / 40) ^ 2 / t by positivity)
      linarith
    linarith
  linarith

/-- The tail `t ≥ 2` of the potential inequality (6.2), via (6.8). -/
lemma potential_ineq_tail {t : ℝ} (ht : 2 ≤ t) : 2 * Uρ t - Vfield t ≤ M0 := by
  have ht0 : 0 < t := by linarith
  have h1 := Uρ_le_log ht
  have h2 := Vfield_ge_tail ht
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs2 : (141 / 100 : ℝ) ≤ Real.sqrt t :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num; linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have e : Real.log (Real.sqrt t ^ 2) = 2 * Real.log (Real.sqrt t) := by
      rw [Real.log_pow];
      norm_num
    rw [hs] at e
    rw [e]
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hq : (3 / 40 : ℝ) ^ 2 / t ≤ (3 / 40) ^ 2 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hpi := Real.pi_gt_d2
  have hprod : 314 / 100 * Real.sqrt t ≤ Real.pi * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (by norm_num at hpi; linarith) hs0.le
  unfold M0
  linarith

end Zeta5Irrational
