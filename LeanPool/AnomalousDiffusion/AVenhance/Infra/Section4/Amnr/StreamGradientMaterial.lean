/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPrimitive
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! First spatial derivatives of material jets of the actual stream summands. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A stream summand and all its differential words vanish beyond the
large cutoff window. This support property applies to the actual construction. -/
theorem amnr_nextStreamTerm_word_zero_off_large {β : ℝ} (I : AVenhance.Ingredients β)
    {φ : ℝ → Vec 2 → ℝ} (hφ : AVenhance.IsAdmissibleStream φ)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (b : AmnrSpace → Vec 2)
    (w : List (Option (Fin 2))) (z : AmnrSpace)
    (hfar : AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m <
      |z.1 - (AVenhance.lIdx β I.Λ m k : ℝ) * AVenhance.tauPP β I.Λ m|) :
    amnrWord b w (fun y => I.nextStreamTerm m φ hφ y.1 y.2 k) z = 0 := by
  let l := AVenhance.lIdx β I.Λ m k
  let V := {y : AmnrSpace | AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m <
    |y.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m|}
  have hV : IsOpen V := isOpen_lt continuous_const (by fun_prop)
  have heq : Set.EqOn (fun y => I.nextStreamTerm m φ hφ y.1 y.2 k)
      (0 : AmnrSpace → ℝ) V := by
    intro y hy
    have hz : I.hatZetaML m l y.1 = 0 := by
      by_contra hne
      have hmem : y.1 ∈ Set.Icc
          ((l - 1 / 2) * AVenhance.tauPP β I.Λ m + AVenhance.tauP β I.Λ m)
          ((l + 1 / 2) * AVenhance.tauPP β I.Λ m - AVenhance.tauP β I.Λ m) := by
        by_contra hnot
        have hh := I.hatZeta_le m hm l y.1
        rw [AVenhance.indIcc_eq_zero_of_not_mem hnot] at hh
        exact hne (le_antisymm hh (AVenhance.Infra.Section3.hatZetaML_mem_Icc I hm l y.1).1)
      have ht := AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := m)
      have hdist : |y.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
          AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m := by
        apply abs_le.mpr
        constructor <;> linarith [hmem.1, hmem.2]
      exact (not_lt_of_ge hdist) hy
    simp [AVenhance.Ingredients.nextStreamTerm, hz, l]
  have hh := amnrWord_congr hV (b := b) heq w hfar
  simpa only [amnrWord_zero, Pi.zero_apply] using hh

/-- All derivatives of the actual stream time amplitude have the fine rate. -/
theorem amnr_stream_timeAmplitude_derivative_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (ℓ : ℕ) (hℓ : ℓ ≤ AVenhance.Nstar β) (t : ℝ) :
    |iteratedDeriv ℓ (I.hatZetaML m (AVenhance.lIdx β I.Λ m k) * I.zetaMK m k) t| ≤
      (2 : ℝ) ^ ℓ * I.Chat * I.Czeta * (AVenhance.tau β I.Λ m)⁻¹ ^ ℓ := by
  have hh : ContDiff ℝ (AVenhance.Nstar β) (I.hatZetaML m (AVenhance.lIdx β I.Λ m k)) := by
    unfold AVenhance.Ingredients.hatZetaML AVenhance.shiftCutoff
    exact ((I.hatZeta_smooth m).comp (by fun_prop)).of_le (by simp)
  have hz : ContDiff ℝ (AVenhance.Nstar β) (I.zetaMK m k) := by
    unfold AVenhance.Ingredients.zetaMK AVenhance.scaledCutoff
    exact (I.zeta_smooth.comp (by fun_prop)).of_le (by simp)
  exact amnr_iteratedDeriv_product_abs_le hh hz hℓ
    (by linarith [I.one_le_Chat]) (by linarith [I.one_le_Czeta]) (inv_nonneg.mpr (I.tau_pos' m).le)
    (fun j hj t => amnr_hatZeta_derivative_abs_le I hm _ hj t)
    (fun j hj t => amnr_zeta_derivative_abs_le I m k hj t) t

end AVenhance.Infra.Section4
