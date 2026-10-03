/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherFastSourceRates

/-! Higher scale-step estimates from the actual lower source levels. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Step constant for higher-order velocity derivatives in the material recursion. -/
def amnrHigherVelocityStepConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (n k : ℕ) : ℝ :=
  let D := amnrHigherFastConstant I K
  let R := amnrNormalOrderConstant (AVenhance.Nstar β - 1) K (AVenhance.Nstar β - 1)
  D + ((amnrMaterialErrorCardinality n * (n + 1) ^ k : ℕ) : ℝ) *
    (R * D) ^ n * (R * (K + D))

/-- Source scale step: the only inputs are the already established actual
lower source levels. Fast jets and every correction are proved from them. -/
theorem amnr_velocity_higher_source_step {β C K : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hlevels : AmnrSourceJetLevels I Φ K (n - 1)) (hK : 1 ≤ K)
    (α : List (Fin 2)) (hbudget : α.length + 2 * n + 1 ≤ AVenhance.Nstar β)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (List.replicate n none)
          (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) -
        amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          (List.replicate n none) (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i)) z| ≤
      amnrHigherVelocityStepConstant I K n α.length * AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
  let c := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let S := (AVenhance.epsilon β I.Λ m)⁻¹
  let H := AVenhance.a β I.Λ m
  let V := AVenhance.epsilon β I.Λ m ^ (β - 1)
  let D := amnrHigherFastConstant I K
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hH : 0 ≤ H := (AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m
      := m)).le
  have hVS : V * S = H := by
    dsimp [V, S, H, AVenhance.a]
    rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
    congr 1
    ring
  have hfast (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hη : η.length + 2 * r + 1 ≤ AVenhance.Nstar β) (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (amnrAdvectionVelocity b c p) z| ≤
        (D * V) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := amnr_fastVelocity_mixed_abs_le_of_source_lower_levels I hΦ hreg hlevels
      (by linarith) hm η r (by omega) (by omega) p z
    rw [amnrMixedWord_weight]
    exact hh.trans_eq (by ring)
  have hcoarse (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hne : amnrMixedWord η r ≠ []) (hη : η.length + 2 * r + 1 ≤ AVenhance.Nstar β)
      (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (fun y => c y p) z| ≤
        (K * V) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := amnrSourceJetLevels_coarse_velocity I hlevels (by linarith) hm η r
      (by omega) hne hη p z
    rw [amnrMixedWord_weight]
    exact hh.trans_eq (by ring)
  have hB (p q : Fin 2) (η : List (Fin 2)) (r : ℕ) (hr : r < n)
      (hη : η.length + 2 * r + 2 ≤ AVenhance.Nstar β) :
      |amnrWord c (amnrMixedWord η r) (amnrVelocityGradient c p q) z| ≤
        (K * H) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := amnrSourceJetLevels_coarse_gradient I hlevels (by linarith) hm η r (by omega) hη p
        q z
    rw [amnrMixedWord_weight]
    exact hh.trans_eq (by ring)
  have htop := amnr_fastVelocity_mixed_abs_le_of_source_lower_levels I hΦ hreg hlevels
    (by linarith) hm α n (by omega) (by omega) i z
  exact amnr_velocity_higher_step_abs_le_of_lower_bounds hb hc (inv_nonneg.mpr hE.le) hH
    (Real.rpow_nonneg hE.le _) (amnrHigherFastConstant_one_le I) (by linarith) (by linarith)
    hVS α n hn (by omega) i z hfast hcoarse hB htop

end AVenhance.Infra.Section4
