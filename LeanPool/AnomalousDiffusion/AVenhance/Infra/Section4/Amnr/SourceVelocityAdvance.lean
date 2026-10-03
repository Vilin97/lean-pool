/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherVelocitySourceSum

/-! Actual velocity induction through the next material level. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Constant controlling the velocity source when advancing the derivative cutoff. -/
def amnrSourceVelocityAdvanceConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (cut : ℕ) : ℝ :=
  K + 2 * amnrHigherVelocityStepConstant I K (cut + 1) (AVenhance.Nstar β)

theorem amnrSourceVelocityAdvanceConstant_ge {β K : ℝ} (I : AVenhance.Ingredients β)
    (hK : 0 ≤ K) (cut : ℕ) : K ≤ amnrSourceVelocityAdvanceConstant I K cut := by
  have hh := amnrHigherVelocityStepConstant_nonneg I hK (cut + 1) (AVenhance.Nstar β)
  unfold amnrSourceVelocityAdvanceConstant
  linarith

/-- All actual velocity levels up to the next material order follow from
the lower source invariant, with one scale-independent constant. -/
theorem amnr_source_velocity_advance {β C K : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {cut : ℕ}
    (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 1 ≤ K)
    (m : ℕ) (α : List (Fin 2)) (r : ℕ) (hr : r ≤ cut + 1)
    (hne : amnrMixedWord α r ≠ []) (hbudget : α.length + 2 * r + 1 ≤ AVenhance.Nstar β)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      amnrSourceVelocityAdvanceConstant I K cut * AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r := by
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hge := amnrSourceVelocityAdvanceConstant_ge I (show 0 ≤ K by linarith) cut
  by_cases hrc : r ≤ cut
  · exact (hlevels.velocity m α r hrc hne hbudget i z).trans (by gcongr)
  · have he : r = cut + 1 := by omega
    subst r
    have hlevels' : AmnrSourceJetLevels I Φ K (cut + 1 - 1) := by simpa using hlevels
    have hh := amnr_velocity_higher_material_abs_le_of_source_lower_levels I hΦ hreg
      (by omega) hlevels' hK m α hbudget i z
    have hp := amnrHigherVelocityStepConstant_mono_spatial I (show 0 ≤ K by linarith)
      (cut + 1) (show α.length ≤ AVenhance.Nstar β by omega)
    have hc : 2 * amnrHigherVelocityStepConstant I K (cut + 1) α.length ≤
        amnrSourceVelocityAdvanceConstant I K cut := by
      unfold amnrSourceVelocityAdvanceConstant
      linarith
    exact hh.trans (by gcongr)

end AVenhance.Infra.Section4
