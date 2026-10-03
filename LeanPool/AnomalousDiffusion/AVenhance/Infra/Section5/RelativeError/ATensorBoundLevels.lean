/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceJetAdvance

/-! # Uniform source jet levels for the S-amplitude AMNR Hessian

The upstream source-jet induction (`amnr_source_jet_levels_exist`) produces its constant after the
ingredients `I`.  The constants are however explicit functions of `β`, `I.Chat` and `I.Czeta`, and
    are
monotone in the latter two.  This module re-runs the induction with a constant that depends only on
`β` and a common bound `C₀ ≥ I.Czeta, I.Chat`, so that it may be chosen before `I`. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open AVenhance.Infra.Section4

namespace AVenhance.Infra.Section5.RelativeError

/-- `I`-free majorant of `amnrStreamMixedCurrentConstant I`. -/
def uniStreamCurrent (β C₀ : ℝ) : ℝ :=
  3 * C₀ * C₀ * amnrTransportSpatialConstant (AVenhance.Nstar β) *
    (2 * max 1 (amnrFineMaterialConstant β)) ^ AVenhance.Nstar β

theorem amnrStreamMixedCurrentConstant_le_uni {β C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) :
    amnrStreamMixedCurrentConstant I ≤ uniStreamCurrent β C₀ := by
  have h1 : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have h2 : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have ht := amnrTransportSpatialConstant_pos (AVenhance.Nstar β)
  have hC0 : 0 ≤ C₀ := h1.trans hz
  unfold amnrStreamMixedCurrentConstant amnrFastSpatialConstant uniStreamCurrent
  gcongr

/-- `I`-free majorant of `amnrHigherFastConstant I K`. -/
def uniHigherFast (β C₀ K : ℝ) : ℝ :=
  max 1 ((1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * K) ^ (AVenhance.Nstar β) *
    uniStreamCurrent β C₀)

/-- `I`-free majorant of `amnrHigherVelocityStepConstant I K n k`. -/
def uniHigherStep (β C₀ K : ℝ) (n k : ℕ) : ℝ :=
  let D := uniHigherFast β C₀ K
  let R := amnrNormalOrderConstant (AVenhance.Nstar β - 1) K (AVenhance.Nstar β - 1)
  D + ((amnrMaterialErrorCardinality n * (n + 1) ^ k : ℕ) : ℝ) *
    (R * D) ^ n * (R * (K + D))

theorem amnrHigherVelocityStepConstant_le_uni {β C₀ K : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) (hK : 0 ≤ K) (n k : ℕ) :
    amnrHigherVelocityStepConstant I K n k ≤ uniHigherStep β C₀ K n k := by
  have hD : amnrHigherFastConstant I K ≤ uniHigherFast β C₀ K := by
    unfold amnrHigherFastConstant uniHigherFast
    refine max_le_max le_rfl ?_
    exact mul_le_mul_of_nonneg_left (amnrStreamMixedCurrentConstant_le_uni I hz hh)
      (by positivity)
  have hD1 := amnrHigherFastConstant_one_le (K := K) I
  have hR := amnrNormalOrderConstant_one_le (N := AVenhance.Nstar β - 1) hK
    (AVenhance.Nstar β - 1)
  have hD0 : 0 ≤ amnrHigherFastConstant I K := by linarith
  have hU0 : 0 ≤ uniHigherFast β C₀ K := hD0.trans hD
  have hR0 : 0 ≤ amnrNormalOrderConstant (AVenhance.Nstar β - 1) K (AVenhance.Nstar β - 1) := by
    linarith
  unfold amnrHigherVelocityStepConstant uniHigherStep
  dsimp only
  gcongr

/-- The advance constant of one source induction level, `I`-free. -/
def uniAdvance (β C₀ K : ℝ) (cut : ℕ) : ℝ :=
  K + 2 * uniHigherStep β C₀ K (cut + 1) (AVenhance.Nstar β)

theorem amnrSourceVelocityAdvanceConstant_le_uni {β C₀ K : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) (hK : 0 ≤ K) (cut : ℕ) :
    amnrSourceVelocityAdvanceConstant I K cut ≤ uniAdvance β C₀ K cut := by
  unfold amnrSourceVelocityAdvanceConstant uniAdvance
  have := amnrHigherVelocityStepConstant_le_uni I hz hh hK (cut + 1) (AVenhance.Nstar β)
  linarith

/-- The `I`-free constant of the next source level. -/
def uniNew (β C₀ K : ℝ) (cut : ℕ) : ℝ :=
  uniAdvance β C₀ K cut +
    (1 + (2 : ℝ) ^ (AVenhance.Nstar β) * K) ^ (cut + 1) * uniAdvance β C₀ K cut + 1

/-- The `I`-free constants of the source jet levels. -/
def uniLevelConst (β C₀ : ℝ) : ℕ → ℝ
  | 0 => max 1 (amnrSpatialVelocityConstant (AVenhance.Nstar β))
  | cut + 1 => uniNew β C₀ (uniLevelConst β C₀ cut) cut

theorem uniHigherStep_nonneg (β C₀ : ℝ) {K : ℝ} (hK : 0 ≤ K) (n k : ℕ) :
    0 ≤ uniHigherStep β C₀ K n k := by
  have hD : 1 ≤ uniHigherFast β C₀ K := le_max_left _ _
  have hR := amnrNormalOrderConstant_one_le (N := AVenhance.Nstar β - 1) hK
    (AVenhance.Nstar β - 1)
  unfold uniHigherStep
  dsimp only
  have : 0 ≤ amnrNormalOrderConstant (AVenhance.Nstar β - 1) K (AVenhance.Nstar β - 1) := by
    linarith
  positivity

theorem one_le_uniNew (β C₀ : ℝ) {K : ℝ} (hK : 1 ≤ K) (cut : ℕ) : 1 ≤ uniNew β C₀ K cut := by
  have h0 : 0 ≤ uniHigherStep β C₀ K (cut + 1) (AVenhance.Nstar β) :=
    uniHigherStep_nonneg β C₀ (by linarith) _ _
  have hA : 1 ≤ uniAdvance β C₀ K cut := by unfold uniAdvance; linarith
  have : 0 ≤ (1 + (2 : ℝ) ^ (AVenhance.Nstar β) * K) ^ (cut + 1) * uniAdvance β C₀ K cut := by
    have : 0 ≤ K := by linarith
    positivity
  unfold uniNew
  linarith

theorem uniLevelConst_one_le (β C₀ : ℝ) (cut : ℕ) : 1 ≤ uniLevelConst β C₀ cut := by
  induction cut with
  | zero => exact le_max_left _ _
  | succ cut ih => exact one_le_uniNew β C₀ ih cut

/-- One complete source induction level with the `I`-free constant `uniNew`. -/
theorem amnrSourceJetLevels_advance_uni {β C C₀ K : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {cut : ℕ}
    (hlevels : AmnrSourceJetLevels I Φ K cut) (hK : 1 ≤ K) :
    AmnrSourceJetLevels I Φ (uniNew β C₀ K cut) (cut + 1) := by
  let Kv := amnrSourceVelocityAdvanceConstant I K cut
  let R := 1 + (2 : ℝ) ^ (AVenhance.Nstar β) * K
  let Knew := uniNew β C₀ K cut
  have hKvK : K ≤ Kv := amnrSourceVelocityAdvanceConstant_ge I (by linarith) cut
  have hKv : 0 ≤ Kv := by linarith
  have hKvu : Kv ≤ uniAdvance β C₀ K cut :=
    amnrSourceVelocityAdvanceConstant_le_uni I hz hh (by linarith) cut
  have hKvu0 : 0 ≤ uniAdvance β C₀ K cut := hKv.trans hKvu
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hnewV : Kv ≤ Knew := by
    have hh : 0 ≤ R ^ (cut + 1) * uniAdvance β C₀ K cut := by positivity
    dsimp only [Knew, uniNew]
    linarith
  have hnewG : R ^ (cut + 1) * Kv ≤ Knew := by
    have h1 := mul_le_mul_of_nonneg_left hKvu (pow_nonneg hR (cut + 1))
    dsimp only [Knew, uniNew]
    have := hKvu0
    linarith
  have hnewK : K ≤ Knew := hKvK.trans hnewV
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

/-- All source jet levels hold with the `I`-free constants `uniLevelConst`. -/
theorem uniLevelConst_spec {β C C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) (cut : ℕ) :
    AmnrSourceJetLevels I Φ (uniLevelConst β C₀ cut) cut := by
  induction cut with
  | zero => exact amnrSourceJetLevels_spatial I hΦ hreg
  | succ cut ih =>
    exact amnrSourceJetLevels_advance_uni I hz hh hΦ hreg ih (uniLevelConst_one_le β C₀ cut)

end AVenhance.Infra.Section5.RelativeError
