/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CoarseSourceRates

/-! Actual transported fast jets with a uniform finite-budget constant. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Uniform constant controlling the higher-order fast velocity estimates. -/
def amnrHigherFastConstant {β : ℝ} (I : AVenhance.Ingredients β) (K : ℝ) : ℝ :=
  max 1 ((1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * K) ^ (AVenhance.Nstar β) *
    amnrStreamMixedCurrentConstant I)

theorem amnrHigherFastConstant_one_le {β K : ℝ} (I : AVenhance.Ingredients β) :
    1 ≤ amnrHigherFastConstant I K := le_max_left _ _

/-- The current fast jet is obtained from the actual transported stream;
only strictly lower material levels of the coarse gradient are consumed. -/
theorem amnr_fastVelocity_mixed_abs_le_of_source_lower_levels {β C K : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {cut m : ℕ} (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 0 ≤ K)
    (hm : 1 ≤ m) (α : List (Fin 2)) (r : ℕ) (hr : r ≤ cut + 1)
    (hbudget : α.length + 1 + 2 * r ≤ AVenhance.Nstar β) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i -
        AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i) z| ≤
      amnrHigherFastConstant I K * AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r := by
  have hh := amnr_fastVelocity_mixed_abs_le_of_lower_gradient_bounds I hΦ hreg hm hK α r
    hbudget i z (fun p q η s hs hη =>
      amnrSourceJetLevels_coarse_gradient I hlevels hK hm η s (by omega) hη p q z)
  have hR : 1 ≤ 1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * K := by
    have hh : 0 ≤ (2 : ℝ) ^ (AVenhance.Nstar β + 1) * K := by positivity
    linarith
  have hp := pow_le_pow_right₀ hR (show r ≤ AVenhance.Nstar β by omega)
  have hKC : (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * K) ^ r *
      amnrStreamMixedCurrentConstant I ≤ amnrHigherFastConstant I K := by
    apply (mul_le_mul_of_nonneg_right hp (amnrStreamMixedCurrentConstant_pos I).le).trans
    exact le_max_right _ _
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  exact hh.trans (by gcongr)

end AVenhance.Infra.Section4
