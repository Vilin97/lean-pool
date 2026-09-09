/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketIdealSize
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import LeanPool.NavierStokesAndEuler.Euler.PacketSizeComparison
import Mathlib.Algebra.Order.Star.Real

/-!
The before-target part of the physical primary-size estimate.  The input
is the actual ray and velocity error already obtained from the physical
equations, and the comparison function solves the scalar reference ODE.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketGrowth EulerPacketFrameStability InnerProductSpace

theorem physical_ideal_size_comparison_order40 (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ Θ K e σ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hVrel : |scaledVelocity m v w t₀ a ε τ 1 / Z τ - 1| ≤ K * e * Θ ^ 29)
    (hratio : |scaledVelocity m v w t₀ a ε τ 0 / scaledVelocity m v w t₀ a ε τ 1 + Z₁ τ / Z τ|
      ≤ 10 * (K * e * Θ ^ 29)) :
    s₀*idealPrimarySize σ Z τ/4 ≤ ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ ∧
      ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ ≤ 8*s₀*idealPrimarySize σ Z τ := by
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hτ2 : τ^2 ≤ Θ^2 := (sq_le_sq₀ hτ0 hΘ0).mpr hτΘ
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    exact (mul_le_mul_of_nonneg_right hσ2 (sq_nonneg τ)).trans (by simpa using hτ2)
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_right hσ2 hτ0
    nlinarith only [hh, hτΘ, sq_nonneg (Θ-1), hΘ]
  have hzpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hslope := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ
  have hr₀ : |-Z₁ τ/Z τ| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |scaledVelocity m v w t₀ a ε τ 0/scaledVelocity m v w t₀ a ε τ 1-(-Z₁ τ/Z τ)|
      ≤ 10*(K*e*Θ^29) := by simpa only [neg_div, sub_neg_eq_add] using hratio
  obtain ⟨hl, hu⟩ := physical_size_comparison_order40 m v r w hs₀ hε hm hv hmv hrw
    hΘ hK he hεe hsmall hP₀ hQ₀ hr₀ hzpos hP hQ hN hVrel hr'
  constructor <;> dsimp only [idealPrimarySize] <;> nlinarith only [hl, hu]

/-- Every controlled neighboring primary before target is bounded by a
fixed multiple of the center's actual target size.  All comparisons use
the same genuine scalar ODE solution, including its initial slope. -/
theorem physical_before_target_size_bound {α : Type*} (center : α)
    (m v r w : α → ℝ → Space) {s₀ t₀ a ε T Θ K e σ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hT : 1 ≤ T) (hTΘ : T ≤ Θ) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hm : ∀ ξ τ, τ ∈ Icc 1 T → m ξ (physicalTime t₀ a ε τ) ≠ 0)
    (hv : ∀ ξ τ, τ ∈ Icc 1 T → v ξ (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ∀ ξ τ, τ ∈ Icc 1 T →
      ⟪m ξ (physicalTime t₀ a ε τ), v ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ∀ ξ τ, τ ∈ Icc 1 T →
      ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : ∀ ξ τ, τ ∈ Icc 1 T →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : ∀ ξ τ, τ ∈ Icc 1 T →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : ∀ ξ τ, τ ∈ Icc 1 T →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hVrel : ∀ ξ τ, τ ∈ Icc 1 T →
      |scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 1 / Z τ - 1| ≤ K * e * Θ ^ 29)
    (hratio : ∀ ξ τ, τ ∈ Icc 1 T →
      |scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 0 / scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 1 +
          Z₁
          τ / Z τ|
        ≤ 10 * (K * e * Θ ^ 29)) :
    ∀ ξ τ, τ ∈ Icc 1 T →
      ‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖ ≤
        64*(‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖) := by
  have hcomparison (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 1 T) :=
    physical_ideal_size_comparison_order40 (m ξ) (v ξ) (r ξ) (w ξ) hs₀ hε hσ hσsmall
      (hm ξ τ hτ) (hv ξ τ hτ) (hmv ξ τ hτ) (hrw ξ τ hτ)
      hΘ hK he hεe hsmall hτ.1 (hτ.2.trans hTΘ) hZ hfluxZ hZ0 hZ₁0
      (hP ξ τ hτ) (hQ ξ τ hτ) (hN ξ τ hτ) (hVrel ξ τ hτ) (hratio ξ τ hτ)
  have htarget := (hcomparison center T ⟨hT, le_rfl⟩).1
  intro ξ τ hτ
  have hcurrent := (hcomparison ξ τ hτ).2
  have hideal := equation30_ideal_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0
    (by linarith only [hτ.1] : 0 ≤ τ) hτ.2
  have hh := mul_le_mul_of_nonneg_left hideal hs₀.le
  nlinarith only [htarget, hcurrent, hh]

end EulerPacketMovingFrame
