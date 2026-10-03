/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML

/-! # Iterates Flow Support

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- The enlarged hat cutoff stays within one refresh cell. -/
theorem iterate_hatXi_time_window {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {l : ℤ} {t : ℝ}
    (hne : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m := by
  have hτp := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hceil : 1 ≤ (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.ceil_pos.mpr
      (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le) _))
  have hF : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    linarith only [hceil]
  have hratio := Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP (β := β) (Λ := I.Λ) hm
  have htime : 5 * tauP β I.Λ m ≤ tauPP β I.Λ m := by
    rw [hratio]
    exact mul_le_mul_of_nonneg_right hF hτp.le
  have hmem : t ∈ Set.Icc
      (((l : ℝ) - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      (((l : ℝ) + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hn
    have hu := I.hatXi_le m hm l t
    have hl := I.hatXi_ge m hm l t
    have hi : indIcc
      (((l : ℝ) - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      (((l : ℝ) + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) t = 0 := by
      exact Set.indicator_of_notMem hn _
    rw [hi] at hu
    have hnon : 0 ≤ indIcc
      (((l : ℝ) - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      (((l : ℝ) + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) t := by
      unfold indIcc
      exact Set.indicator_nonneg (fun _ _ => by norm_num) _
    exact hne (le_antisymm hu (hnon.trans hl))
  rw [abs_le]
  constructor <;> nlinarith only [hmem.1, hmem.2, htime, hτp.le]

/-- Refresh time times the preceding shear amplitude retains the rho gain. -/
theorem iterate_refresh_amplitude_bound {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    tauPP β I.Λ m * a β I.Λ (m - 1) ≤
      (2 : ℝ) ^ (-25 : ℤ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have ht := (Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2
  have hp := mul_le_mul_of_nonneg_right ht ha.le
  have hid : epsilon β I.Λ (m - 1) ^ (2 - β + 2 * delta β) * a β I.Λ (m - 1) =
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    unfold a
    rw [← Real.rpow_add he]
    congr 1
    ring
  simpa only [mul_assoc, hid] using hp

/-- The hat support fits the signed-time Section 2 flow window. -/
theorem iterate_hatXi_section2_window {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {l : ℤ} {t : ℝ}
    (hne : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤
      (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  have hd := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hδ0 : 0 ≤ 2 * delta β := by linarith only [hd]
  have hρ := Real.rpow_le_one he.le he1 hδ0
  have hprod := (iterate_refresh_amplitude_bound I hm).trans
    (mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ (2 : ℝ) ^ (-25 : ℤ)))
  have ht : tauPP β I.Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ ha]
    simpa only [mul_one] using hprod
  exact (iterate_hatXi_time_window I hm hne).trans ht

end AVenhance.Infra.Section4
