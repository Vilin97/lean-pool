/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMSupport

/-! The active refresh flow starts at time zero. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance

/-- Only indices -1, 0 and 1 can be active initially. -/
theorem relative_initial_active_index {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (hk : I.xiMK m k 0 ≠ 0) :
    k ∈ Finset.Icc (-1 : ℤ) 1 := by
  have hw := Infra.Section3.xiMK_index_mem_window I hm k 0 hk
  change (k : ℝ) ∈ Set.Icc (0 / tau β I.Λ m - 5 / 4)
    (0 / tau β I.Λ m + 5 / 4) at hw
  simp only [zero_div, zero_sub, zero_add] at hw
  have hlo : (-2 : ℝ) < (k : ℝ) := by linarith [hw.1]
  have hhi : (k : ℝ) < (2 : ℝ) := by linarith [hw.2]
  have hlo' : (-2 : ℤ) < k := by exact_mod_cast hlo
  have hhi' : k < (2 : ℤ) := by exact_mod_cast hhi
  simp only [Finset.mem_Icc]
  omega

/-- Uniform finite cutoff budget for the actual initial corrector sum. -/
theorem relative_initial_cutoff_sum {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ (I.xiMK_support_finite m 0).toFinset, |I.xiMK m k 0| ≤ 3 := by
  classical
  have hs : (I.xiMK_support_finite m 0).toFinset ⊆ Finset.Icc (-1 : ℤ) 1 := by
    intro k hk
    exact relative_initial_active_index I hm k (by simpa using hk)
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-1 : ℤ) 1, |I.xiMK m k 0| :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _k ∈ Finset.Icc (-1 : ℤ) 1, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_of_nonneg (Infra.Section3.xiMK_mem_Icc I hm k 0).1]
      exact (Infra.Section3.xiMK_mem_Icc I hm k 0).2
    _ = 3 := by norm_num

/-- Zero lies in the core of refresh cutoff zero. -/
theorem relative_hatZeta_zero {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) : I.hatZetaML m 0 0 = 1 := by
  have hp : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
    Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)) _
  have hc : (1 : ℝ) ≤ (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hp))
  have hf : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    linarith
  have ht : 5 * tauP β I.Λ m ≤ tauPP β I.Λ m := by
    rw [Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP hm]
    exact mul_le_mul_of_nonneg_right hf (le_of_lt
      (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le))
  have hcore : indIcc ((0 - 1 / 2 : ℝ) * tauPP β I.Λ m + 2 * tauP β I.Λ m)
      ((0 + 1 / 2 : ℝ) * tauPP β I.Λ m - 2 * tauP β I.Λ m) 0 = 1 := by
    unfold indIcc
    rw [Set.indicator_of_mem (show (0 : ℝ) ∈ Set.Icc _ _ by
      constructor <;> linarith [I.tauPP_pos' m])]
  have hlo := I.hatZeta_ge m hm 0 0
  change indIcc _ _ 0 ≤ I.hatZetaML m 0 0 at hlo
  simp only [Int.cast_zero] at hlo
  rw [hcore] at hlo
  have hup := I.hatZeta_le m hm 0 0
  change I.hatZetaML m 0 0 ≤ indIcc _ _ 0 at hup
  have hind : ∀ a b t : ℝ, indIcc a b t ≤ 1 := by
    intro a b t
    unfold indIcc
    by_cases h : t ∈ Set.Icc a b <;> simp [h]
  exact le_antisymm (hup.trans (hind _ _ _)) hlo

/-- Every initial active small cutoff is assigned to refresh cell zero. -/
theorem relative_initial_active_lIdx {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (hk : I.xiMK m k 0 ≠ 0) :
    lIdx β I.Λ m k = 0 := by
  exact lIdx_eq_of_hatZeta_xiMK_ne_zero I m hm 0 k 0
    (by rw [relative_hatZeta_zero I hm]; norm_num) hk

/-- The active initial flow is exactly the identity, without a flow-size premise. -/
theorem relative_initial_active_xFlow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (hk : I.xiMK m k 0 ≠ 0) :
    I.xFlow hΦ m (lIdx β I.Λ m k) 0 = id := by
  rw [relative_initial_active_lIdx I hm k hk]
  funext x
  unfold Ingredients.xFlow
  simpa using (flow_isFlow (streamVel (Φ (m - 1)))
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz).1 x 0

/-- Discharged active-flow entry bound for the corrector estimate. -/
theorem relative_initial_active_flowGrad_le_two {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (hk : I.xiMK m k 0 ≠ 0)
    (x : Vec 2) (i j : Fin 2) :
    |I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x i j| ≤ 2 := by
  apply relative_flowGrad_entry_le_two I hΦ m _ _ x i j
  intro y
  rw [relative_initial_active_xFlow I hΦ hm k hk, fderiv_id]
  exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1).trans
    (by norm_num)
end AVenhance.Infra.Section5.RelativeError
