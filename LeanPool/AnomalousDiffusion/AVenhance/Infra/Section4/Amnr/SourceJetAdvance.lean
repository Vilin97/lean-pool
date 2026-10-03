/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceVelocityAdvance

/-! Joint source induction for actual higher velocity and gradient jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- One complete source induction level. The new velocity bound is obtained
by actual scale summation; the new gradient bound then uses only lower
gradient levels and the just-proved velocity level. -/
theorem amnrSourceJetLevels_advance {β C K : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {cut : ℕ}
    (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 1 ≤ K) :
    ∃ Knew : ℝ, 1 ≤ Knew ∧ AmnrSourceJetLevels I Φ Knew (cut + 1) := by
  let Kv := amnrSourceVelocityAdvanceConstant I K cut
  let R := 1 + (2 : ℝ) ^ (AVenhance.Nstar β) * K
  let Knew := Kv + R ^ (cut + 1) * Kv + 1
  have hKvK : K ≤ Kv := amnrSourceVelocityAdvanceConstant_ge I (by linarith) cut
  have hKv : 0 ≤ Kv := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hnewV : Kv ≤ Knew := by
    have hh : 0 ≤ R ^ (cut + 1) * Kv := by positivity
    dsimp [Knew]
    linarith
  have hnewG : R ^ (cut + 1) * Kv ≤ Knew := by dsimp [Knew]; linarith
  have hnewK : K ≤ Knew := hKvK.trans hnewV
  refine ⟨Knew, by linarith, ?_⟩
  constructor
  · intro m α r hr hne hbudget i z
    have hh := amnr_source_velocity_advance I hΦ hreg hlevels hK m α r hr hne hbudget i z
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    exact hh.trans (by gcongr)
  · intro m α r hr hbudget i p z
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    by_cases hrc : r ≤ cut
    · exact (hlevels.gradient m α r hrc hbudget i p z).trans (by gcongr)
    · have he : r = cut + 1 := by omega
      subst r
      let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
      have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
        (AVenhance.Infra.Construction.smoothPeriodic_streamVel
          (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
      have hVS : AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ = AVenhance.a β I.Λ m := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
        unfold AVenhance.a
        congr 1
        ring
      have hh := amnr_velocityGradient_mixed_abs_le_of_bounded_velocity_jets hb
        (inv_nonneg.mpr hE.le) hA.le (Real.rpow_nonneg hE.le _) hKv (by linarith)
        hVS α (cut + 1) hbudget i p z
        (fun η s hs hne hη => amnr_source_velocity_advance I hΦ hreg hlevels hK m η s hs hne hη i z)
        (fun j q η s hs hη => hlevels.gradient m η s (by omega) hη j q z)
      have hc : (1 + (2 : ℝ) ^ (AVenhance.Nstar β) * K) ^ (cut + 1) * Kv ≤ Knew := hnewG
      exact hh.trans (by gcongr)

/-- All higher mixed source jets through any finite material cut follow
from the stream-regularity estimates and the actual stream construction. No mixed primitive bound
    is an
extra premise. Every level retains its field's weighted source budget. -/
theorem amnr_source_jet_levels_exist {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) (cut : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ AmnrSourceJetLevels I Φ K cut := by
  induction cut with
  | zero =>
    exact ⟨_, le_max_left _ _, amnrSourceJetLevels_spatial I hΦ hreg⟩
  | succ cut ih =>
    obtain ⟨K, hK, hlevels⟩ := ih
    exact amnrSourceJetLevels_advance I hΦ hreg hlevels hK

end AVenhance.Infra.Section4
