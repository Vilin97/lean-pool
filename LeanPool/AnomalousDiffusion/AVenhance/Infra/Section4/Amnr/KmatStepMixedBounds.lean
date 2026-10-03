/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.KappaStepSourceSize

/-! Kmat jets from the actual one-step diffusivity size comparison. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Step constant for mixed derivatives of the effective diffusivity matrix. -/
def amnrKmatStepConstant (β C₀ : ℝ) : ℝ :=
  (1 + (AVenhance.Nstar β : ℝ) * 2 ^ AVenhance.Nstar β * C₀ ^ 3) * (160 / 9)

theorem amnr_Kmat_mixed_bound_of_step_size {β C₀ κm κprev : ℝ}
    (I : AVenhance.Ingredients β) (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκprev : 0 ≤ κprev)
    (hratio : AVenhance.epsilon β I.Λ m ^ 2 ≤ κm * AVenhance.tau β I.Λ m)
    (hsize : κm + AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κm ≤
      (160 / 9) * κprev)
    (b : AmnrSpace → Vec 2) {S : ℝ} (hS : 0 ≤ S) (α : List (Fin 2)) (r : ℕ)
    (hbudget : α.length + 2 * r ≤ AVenhance.Nstar β) (i j : Fin 2) (z : AmnrSpace) :
    |amnrWord b (amnrMixedWord α r) (fun y => I.Kmat κm m y.1 i j) z| ≤
      (amnrKmatStepConstant β C₀ * κprev) *
        amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ (amnrMixedWord α r) := by
  have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hz]
  have hQ : 0 ≤ amnrKmatStepConstant β C₀ := by unfold amnrKmatStepConstant; positivity
  have hτ := AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hf : ContDiff ℝ (AVenhance.Nstar β) (fun t => I.Kmat κm m t i j) :=
    (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp
      (Section3.Kmat_contDiff I hm hκm))
  rw [amnrWord_timeOnly_mixed hf α r (by omega), amnrMixedWord_weight]
  by_cases hα : α = []
  · subst α
    simp only [ite_true, List.length_nil, pow_zero]
    have hmixed := Section3.Kmat_derivative_norm_le I hz hh hm hκm hratio
      (show r ≤ AVenhance.Nstar β by omega) z.1
    have hentry := (norm_le_pi_norm
      (fun q : Fin 2 => iteratedDeriv r (fun t => I.Kmat κm m t i q) z.1) j).trans
      (norm_le_pi_norm (fun p q : Fin 2 => iteratedDeriv r
        (fun t => I.Kmat κm m t p q) z.1) i)
    rw [Real.norm_eq_abs] at hentry
    refine (hentry.trans hmixed).trans ?_
    have hs := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ (1 + (AVenhance.Nstar β : ℝ) * 2 ^ AVenhance.Nstar β * C₀ ^ 3) /
        AVenhance.tauP β I.Λ m ^ r by positivity)
    convert hs using 1
    dsimp [amnrKmatStepConstant]
    rw [inv_pow, div_eq_mul_inv]
    ring
  · simp only [hα, ↓reduceIte, Pi.zero_apply, abs_zero]
    have hW := amnrWeight_nonneg hS (inv_nonneg.mpr hτ.le) (amnrMixedWord α r)
    rw [amnrMixedWord_weight] at hW
    exact mul_nonneg (mul_nonneg hQ hκprev) hW

end AVenhance.Infra.Section4
