/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowGeometry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSource

/-! # Iterates Flow Bounds

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- All coordinate words, with explicit constants fixed before ingredients. -/
theorem iterate_flowGrad_word_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m) {l : ℤ} {t : ℝ} (hne : I.hatXiML m l t ≠ 0)
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateSpatialWord w (fun y => (I.flowGrad hΦ m l t y - 1) i j) x| ≤
      40 * (w.length.factorial : ℝ) * (2 ^ 10 / epsilon β I.Λ (m - 1)) ^ w.length := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => (I.flowGrad hΦ m l t y - 1) i j) := by
    have h := (amnr_flowGrad_joint_contDiff_infty I hΦ m l i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
    exact h.sub contDiff_const
  have hb := iterate_word_abs_factorial_bound_of_barNorm hs (by positivity)
    (by norm_num : (0 : ℝ) ≤ 40) w (iterate_flowGrad_barNorm I hΦ hm hne w.length i j) x
  have hd : 1 ≤ ((w.length : ℝ) + 1) ^ 2 := by
    have h := Nat.cast_nonneg (α := ℝ) w.length
    nlinarith only [h]
  have hdrop := div_le_self (by positivity : 0 ≤
    40 * (w.length.factorial : ℝ) *
      (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹) ^ w.length) hd
  simpa only [div_eq_mul_inv] using hb.trans hdrop

end AVenhance.Infra.Section4
