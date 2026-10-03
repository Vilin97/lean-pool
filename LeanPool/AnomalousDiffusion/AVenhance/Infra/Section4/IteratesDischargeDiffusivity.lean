/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDischargeScalars
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LRecurseTop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds

/-! # Iterates Discharge Diffusivity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

/-- The exact predecessor identity, without importing the energy hierarchy. -/
theorem iterate_chain_previous_eq {β : ℝ} (I : Ingredients β)
    (κ : ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    I.kappaAt κ (m - 1) (M - (m - 1)) =
      I.KhomScalar (I.kappaAt κ m (M - m)) m := by
  have hd : M - (m - 1) = (M - m) + 1 := by omega
  have hi : m - 1 + 1 = m := by omega
  rw [hd, Ingredients.kappaAt, hi]

/-- A terminal-aware exprat bound. The interior diffusivity-recursion estimate is never applied at
    m=M. -/
theorem iterate_chain_ratio_bound {β Ck P κ : ℝ} (I : Ingredients β)
    (hCk : 0 ≤ Ck) (hP : Ck ≤ P)
    (hPt : Infra.Section3.kappaPrimeEndpointExpratConstant β ≤ P)
    {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) (hκ : 0 < κ)
    (hPerm : κ ∈ permittedInterval β I.Λ M)
    (hA5 : ∀ j : ℕ, 2 ≤ j → j < M →
      epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ≤
        Ck * epsilon β I.Λ (j - 1) ^ (4 * delta β)) :
    epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
      P * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  by_cases ht : m = M
  · subst m
    have htop := (Infra.Section3.l_recurse_top I.one_lt_beta I.beta_lt
      I.two_pow_seven_le hκ hPerm (by omega)).2
    simpa only [Nat.sub_self, Ingredients.kappaAt] using htop.trans
      (mul_le_mul_of_nonneg_right hPt (Real.rpow_nonneg he.le _))
  · have hi := hA5 m hm (by omega)
    have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m - 1)
    have hd := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
    have hp := Real.rpow_le_rpow_of_exponent_ge he he1
      (show 2 * delta β ≤ 4 * delta β by linarith only [hd])
    exact hi.trans ((mul_le_mul_of_nonneg_left hp hCk).trans
      (mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg he.le _)))

/-- One-step enhancement controls its whole size, including the terminal step.
This is the same terminal-aware mechanism used by Amnr and RelativeError KappaProduct. -/
theorem iterate_chain_step_size {β Ccut κ : ℝ} (I : Ingredients β)
    (hz : I.Czeta ≤ Ccut) (hh : I.Chat ≤ Ccut) {m M : ℕ}
    (hm : 1 ≤ m) (hmM : m ≤ M) (hκ : 0 < κ)
    (hsmall : Infra.Section3.lAmtOneStepConstant β Ccut *
      (epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) +
        epsilon β I.Λ (m - 1) ^ delta β) ≤ 9 / 160) :
    I.kappaAt κ m (M - m) +
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) ≤
      (160 / 9) * I.kappaAt κ (m - 1) (M - (m - 1)) := by
  have hk := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have he := Infra.Section3.KhomScalar_one_step_error_unconditional I hz hh hm hk
  rw [← iterate_chain_previous_eq I κ hm hmM] at he
  have hB : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) := by positivity
  have herr := mul_le_mul_of_nonneg_right hsmall hB
  have hlower := (abs_le.mp he).1
  nlinarith only [hlower, herr, hk.le]

/-- Kmat is time-only; its zeroth entry bound needs no material flow estimate. -/
theorem iterate_chain_Kmat_entry_bound {β Ccut κ : ℝ} (I : Ingredients β)
    (hz : I.Czeta ≤ Ccut) {m M : ℕ} (hm : 1 ≤ m) (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * tau β I.Λ m / 2)
    (hsize : I.kappaAt κ m (M - m) +
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) ≤
      (160 / 9) * I.kappaAt κ (m - 1) (M - (m - 1))) :
    ∀ t j k, |I.Kmat (I.kappaAt κ m (M - m)) m t j k| ≤
      ((160 / 9) * (1 + (Nstar β : ℝ) * Ccut)) * I.kappaAt κ (m - 1) (M - (m - 1)) := by
  have hk := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hB : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m) := by positivity
  have hCcut : 0 ≤ Ccut := (by linarith only [I.one_le_Czeta] : 0 ≤ I.Czeta).trans hz
  have hNc : 0 ≤ (Nstar β : ℝ) * Ccut := mul_nonneg (Nat.cast_nonneg _) hCcut
  have hcondition' : epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * tau β I.Λ m := by
    have hp := mul_pos hk (I.tau_pos' m)
    linarith only [hcondition, hp]
  intro t j k
  have he := Infra.Section3.Kmat_entry_abs_le_zero I hm hk hcondition' t j k
  rw [show (Nstar β : ℝ) *
    (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m)) =
      (Nstar β : ℝ) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
        I.kappaAt κ m (M - m)) * I.Czeta by ring] at he
  have hc := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ (Nstar β : ℝ) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m)) by
        positivity)
  have hcross := mul_nonneg hNc hk.le
  have hlast := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1 + (Nstar β : ℝ) * Ccut by positivity)
  nlinarith only [he, hc, hcross, hB, hlast]

end AVenhance.Infra.Section4
