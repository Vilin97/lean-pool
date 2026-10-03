/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Local finite-sum continuity of the time-dependent corrector. -/

@[expose] public section

noncomputable section

open Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section3

open AVenhance

theorem xiMK_index_abs_bound {β : ℝ} (I : Ingredients β)
    {m : ℕ} (t₀ t : ℝ) (k : ℤ)
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1))
    (hxi : I.xiMK m k t ≠ 0) :
    |(k : ℝ)| ≤ (|t₀| + 1) / tau β I.Λ m + 5 / 4 := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hcoord :
      (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∈
        Set.Icc (-(5 / 4 : ℝ)) (5 / 4) := by
    by_contra hnot
    exact hxi (xiMK_eq_zero_outside I k t hnot)
  have hlo := (le_div_iff₀ hτ).mp hcoord.1
  have hhi := (div_le_iff₀ hτ).mp hcoord.2
  have hklower : (t - (5 / 4 : ℝ) * tau β I.Λ m) /
      tau β I.Λ m ≤ (k : ℝ) := by
    apply (div_le_iff₀ hτ).2
    nlinarith
  have hkupper : (k : ℝ) ≤
      (t + (5 / 4 : ℝ) * tau β I.Λ m) / tau β I.Λ m := by
    apply (le_div_iff₀ hτ).2
    nlinarith
  have htabs : |t| ≤ |t₀| + 1 := by
    rw [abs_le]
    constructor
    · have htlo := ht.1
      have := neg_le_abs t₀
      linarith
    · have hthi := ht.2
      have := le_abs_self t₀
      linarith
  have hratio : |t / tau β I.Λ m| ≤ (|t₀| + 1) / tau β I.Λ m := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right htabs (le_of_lt hτ)
  have hklower' : t / tau β I.Λ m - 5 / 4 ≤ (k : ℝ) := by
    calc
      t / tau β I.Λ m - 5 / 4 =
          (t - (5 / 4 : ℝ) * tau β I.Λ m) / tau β I.Λ m := by
            field_simp [ne_of_gt hτ]
      _ ≤ (k : ℝ) := hklower
  have hkupper' : (k : ℝ) ≤ t / tau β I.Λ m + 5 / 4 := by
    calc
      (k : ℝ) ≤ (t + (5 / 4 : ℝ) * tau β I.Λ m) / tau β I.Λ m := hkupper
      _ = t / tau β I.Λ m + 5 / 4 := by
            field_simp [ne_of_gt hτ]
  rw [abs_le]
  constructor
  · have h := neg_le_abs (t / tau β I.Λ m)
    linarith
  · have h := le_abs_self (t / tau β I.Λ m)
    linarith

theorem ChiMTimeRegularity.chiM_eq_bounded_index_sum {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ t₀ t : ℝ) (x : Vec 2)
    (N : ℕ) (hN : (|t₀| + 1) / tau β I.Λ m + 2 < (N : ℝ))
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1)) :
    I.chiM κ m t x =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        I.xiMK m k t • I.chiMK κ m k t x := by
  classical
  unfold Ingredients.chiM
  apply tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
  intro k hk
  have hnot : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := hk
  have hxi : I.xiMK m k t = 0 := by
    by_contra hne
    have hreal := xiMK_index_abs_bound I t₀ t k ht hne
    have hN' : |(k : ℝ)| < (N : ℝ) := by
      exact lt_of_le_of_lt hreal (by linarith)
    have hkiR := abs_le.mp (le_of_lt hN')
    have hkiZ : -(N : ℤ) ≤ k ∧ k ≤ N := by
      exact_mod_cast hkiR
    exact hnot (Finset.mem_Icc.mpr hkiZ)
  simp [hxi]

end AVenhance.Infra.Section3
