/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import LeanPool.NavierStokesAndEuler.Euler.PacketIdealSize
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
import LeanPool.NavierStokesAndEuler.Euler.PacketHorizonSize
import LeanPool.NavierStokesAndEuler.Euler.PacketTargetAmplification
import Mathlib.Algebra.Order.Star.Real

/-! Bounds for the actual source choice of the packet amplitude. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth

/-- Primary amplitude, given by `δ*hchild/(‖r t‖*‖w t‖)`. -/
def primaryAmplitude (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ) : ℝ :=
  δ*hchild/(‖r t‖*‖w t‖)

theorem primaryAmplitude_nonneg (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) : 0 ≤ primaryAmplitude δ hchild r w t := by
  unfold primaryAmplitude
  positivity

theorem primaryAmplitude_target_identity (δ hchild : ℝ) (r w : ℝ → Space) (t : ℝ)
    (ht : 0 < ‖r t‖ * ‖w t‖) :
    primaryAmplitude δ hchild r w t*(‖r t‖*‖w t‖) = δ*hchild := by
  unfold primaryAmplitude
  exact div_mul_cancel₀ _ (ne_of_gt ht)

theorem primaryAmplitude_exponential_bound (r w : ℝ → Space)
    {δ hchild s₀ Θ x t : ℝ} (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) (hs₀ : 0 < s₀) (hΘ : 0 < Θ)
    (hgrowth : s₀ * exp x ≤ 4 * Θ * (‖r t‖ * ‖w t‖)) :
    primaryAmplitude δ hchild r w t ≤ (4*Θ*δ*hchild/s₀)*exp (-x) := by
  have hb := (ratio_bound_from_target_growth hs₀ hΘ (mul_nonneg hδ hh) le_rfl hgrowth).2
  simpa only [primaryAmplitude, mul_assoc] using hb

/-- The profile-weighted amplitude is bounded uniformly on the full
forward horizon, including before scaled time one. -/
theorem primaryAmplitude_profile_bound (r w : ℝ → Space)
    {δ hchild s₀ σ T H targetTime : ℝ} {Z Z₁ : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hh : 0 ≤ hchild) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT : 1 ≤ T) (hshort : H - T ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hlower : s₀ * idealPrimarySize σ Z T / 4 ≤ ‖r targetTime‖ * ‖w targetTime‖) :
    ∀ τ ∈ Icc 0 H, primaryAmplitude δ hchild r w targetTime*Z τ ≤ 8*exp 6*δ*hchild/s₀ := by
  let A := primaryAmplitude δ hchild r w targetTime
  have hA : 0 ≤ A := primaryAmplitude_nonneg δ hchild r w targetTime hδ hh
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hIpos : 0 < idealPrimarySize σ Z T :=
    mul_pos (sqrt_pos.mpr (by positivity)) (hZpos T hT0)
  have htarget : 0 < ‖r targetTime‖*‖w targetTime‖ :=
    lt_of_lt_of_le (div_pos (mul_pos hs₀ hIpos) (by norm_num)) hlower
  have hid : A*(‖r targetTime‖*‖w targetTime‖) = δ*hchild :=
    primaryAmplitude_target_identity δ hchild r w targetTime htarget
  have hl : s₀*A*idealPrimarySize σ Z T ≤ 4*δ*hchild := by
    have hb := mul_le_mul_of_nonneg_left hlower hA
    rw [hid] at hb
    nlinarith only [hb]
  intro τ hτ
  have hroot : 1 ≤ sqrt (1+(σ^2*τ^2)^2) := one_le_sqrt.mpr (by nlinarith [sq_nonneg (σ^2*τ^2)])
  have hz : Z τ ≤ idealPrimarySize σ Z τ := by
    have hb := mul_le_mul_of_nonneg_right hroot (hZpos τ hτ.1).le
    simpa only [one_mul, idealPrimarySize] using hb
  have hi := equation30_horizon_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hT hshort hτ.1 hτ.2
  have hz' := hz.trans hi
  have h1 := mul_le_mul_of_nonneg_left hz' (mul_nonneg hs₀.le hA)
  have h2 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*exp (6:ℝ) by positivity)
  apply (le_div_iff₀ hs₀).mpr
  change A*Z τ*s₀ ≤ 8*exp 6*δ*hchild
  nlinarith only [h1, h2]

end EulerPacketMovingFrame
