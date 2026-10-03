/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge

/-! # TUpgrade Consumers Profile

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Closedness of squared energy bounds under strictly enlarged amplitudes. -/
theorem iterate_squared_amplitude_bound {a N K : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K)
    (h : ∀ B, N < B → a ≤ B ^ 2 * K) : a ≤ N ^ 2 * K := by
  apply iterate_amplitude_bound_of_strict_enlargements hK
  intro D hD
  have hDpos : 0 ≤ D := (sq_nonneg N).trans hD.le
  have hroot : N < Real.sqrt D := by
    by_contra hn
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg D) hN).mpr (le_of_not_gt hn)
    rw [Real.sq_sqrt hDpos] at hs
    exact (not_le_of_gt hD) hs
  simpa only [Real.sq_sqrt hDpos] using h (Real.sqrt D) hroot

/-- The generic initial-trace profile also permits zero dissipation amplitude. -/
theorem theta_iterate_profile_of_initial_trace_nonneg_A3_A5
    {β : ℝ} {M m : ℕ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsStreamSeq I Φ)
    (hm : 2 ≤ m) (hmM : m ≤ M) {κ : ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {c C B R C₀ : ℝ} (hc : 0 < c) (hC : c < C)
    (hB : 0 ≤ B) (hR : 0 < R)
    (hRadius : 8 * max (thetaAnalyticRadiusBase c) 2 ≤ C₀)
    (hscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R)
    (hzero : I.kappaSeq κ M (m - 1) *
      spaceTimeGradNormSq (fun t => spaceGrad (θ t)) ≤ B ^ 2)
    (hTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube, (classicalWordDerivative w θ₀ x) ^ 2) ≤
      B * ((w.length.factorial : ℝ) / R ^ w.length))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤ I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)))
    (hsol : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1))
      (fun _ _ => 0) θ₀ θ) :
    iterateCoordinateEnergyProfile θ (I.kappaSeq κ M (m - 1)) B
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0 := by
  have hp : ∀ D, B < D → iterateCoordinateEnergyProfile θ
      (I.kappaSeq κ M (m - 1)) D
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0 := by
    intro D hBD
    apply theta_iterate_profile_of_initial_trace_A3_A5 I Φ hΦ hm hmM hc hC
      (hB.trans_lt hBD) hR hRadius hscale
    · exact hzero.trans ((sq_le_sq₀ hB (hB.trans hBD.le)).mpr hBD.le)
    · intro w hw
      exact (hTrace w hw).trans (mul_le_mul_of_nonneg_right hBD.le (by positivity))
    · exact hA3
    · exact hA5
    · exact hsol
  constructor
  · intro w hw s hs hs1
    apply iterate_squared_amplitude_bound hB (sq_nonneg _)
    intro D hBD
    exact (hp D hBD).1 w hw s hs hs1
  · intro w
    have hb : spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (θ t))) ≤
        B ^ 2 * ((Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ ^ 2 *
          iterateAnalyticWeight w.length 0
            (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) ^ 2) := by
      apply iterate_squared_amplitude_bound hB (by positivity)
      intro D hBD
      simpa only [div_eq_mul_inv, mul_pow, mul_assoc] using (hp D hBD).2 w
    simpa only [div_eq_mul_inv, mul_pow, mul_assoc] using hb

end AVenhance.Infra.Section4
