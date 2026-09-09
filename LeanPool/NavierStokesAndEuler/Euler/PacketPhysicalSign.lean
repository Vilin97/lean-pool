/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameQuantitative
import LeanPool.NavierStokesAndEuler.Euler.PacketActualFrameEstimates
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrameRenewal
import Mathlib.Algebra.Order.Star.Real

/-!
The pressure numerator of the actual primary is positive.  The scale
condition `1 ≤ σ * Θ` is the source horizon condition; the smallness of the
matrix and ray errors is converted to smallness relative to `σ^2`.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketGrowth EulerPacketFrameStability
  EulerPacketFrameQuantitative InnerProductSpace

theorem controlled_pressure_ratio_lower
    {A : Fin 3 → Fin 3 → ℝ} {σ Θ K e τ P Q N r : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hσΘ : 1 ≤ σ * Θ) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5)
    (hratio : |r + Z₁ τ / Z τ| ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |A i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    σ^2/2 ≤ velocityNumerator A P Q N r 1 (velocityThird P Q N r 1) := by
  let ρ := 800*e*Θ^5
  let η := K*e*Θ^29
  let j := 147*e*Θ^4+1600*e*Θ^5
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hΘpos : 0 < Θ := by linarith only [hΘ]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hρ : ρ ≤ 1/2 := by
    have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
    dsimp [ρ]
    nlinarith only [hp, hsmall]
  have hη : η ≤ 1/2 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))
      (mul_nonneg hK0 he)
    dsimp [η]
    nlinarith only [hp, hsmall]
  have ht2 : τ^2 ≤ Θ^2 := (sq_le_sq₀ hτ0 hΘ0).mpr hτΘ
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 (sq_nonneg τ), ht2]
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 hτ0, hτΘ, hΘ, sq_nonneg (Θ-1)]
  obtain ⟨_, hp, hq, hn, hw, _, _⟩ := ray_geometric_bounds (ε := 0) (U := r) (V := 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hβ : |σ^2| ≤ 1 := by simpa only [abs_of_nonneg (sq_nonneg σ)] using hσ2
  have hJ : |velocityNumerator A P Q N r 1 (velocityThird P Q N r 1) -
      ((σ^2*τ^2+σ^2)*1+(-2*σ^2*τ)*r)| ≤ j*(|r|+|1|) := by
    have hh := velocity_numerator_error hΘ hρ0 (show 0 ≤ 3*e by positivity)
      hβ hA hp hq hn hP hQ hN hw
    dsimp [j, ρ] at *
    nlinarith only [hh]
  have hslope := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ
  have hr₀ : |-Z₁ τ/Z τ| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |r/1-(-Z₁ τ/Z τ)| ≤ 10*η := by
    simpa only [div_one, neg_div, sub_neg_eq_add] using hratio
  have herr := pressure_ratio_error hΘ hη0 hη hj (by norm_num : (0:ℝ) < 1) hQ₀ hr₀ hr' hJ
  simp only [div_one] at herr
  have herrorSmall : 10*j+20*Θ^2*η ≤ σ^2/2 := by
    have hp6 := scaled_power_le hΘ hK he (by decide : 6 ≤ 40)
    have hp7 := scaled_power_le hΘ hK he (by decide : 7 ≤ 40)
    have hp33 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 33 ≤ 40))
      (mul_nonneg hK0 he)
    have hs : (10*j+20*Θ^2*η)*Θ^2 ≤ 1/2 := by
      dsimp [j, η]
      nlinarith only [hp6, hp7, hp33, hsmall]
    have hστ : 1 ≤ σ^2*Θ^2 := by
      have hh := mul_le_mul hσΘ hσΘ (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ σ*Θ)
      nlinarith only [hh]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hΘpos)).mp
    nlinarith only [hs, hστ]
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hnum := equation30_ideal_numerator_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hideal : σ^2 ≤ σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ) := by
    apply (mul_le_mul_iff_right₀ hZpos).mp
    have hz : Z τ ≠ 0 := ne_of_gt hZpos
    have hid : (σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ))*Z τ =
        (σ^2*τ^2+σ^2)*Z τ+2*σ^2*τ*Z₁ τ := by field_simp
    nlinarith only [hid, hnum]
  linarith only [(abs_le.mp herr).1, herrorSmall, hideal]

/-- Source (33), stated for the actual physical ray and velocity. -/
theorem physical_pressure_positive_order40 (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ σ Θ K e : ℝ} {Z Z₁ : ℝ → ℝ}
    (ha : 0 < a) (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : 0 < scaledVelocity m v w t₀ a ε τ 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hσΘ : 1 ≤ σ * Θ) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hratio : |scaledVelocity m v w t₀ a ε τ 0 / scaledVelocity m v w t₀ a ε τ 1 + Z₁ τ / Z τ|
      ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |scaledAction M m v a ε (physicalTime t₀ a ε τ) i j -
      idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    s₀*a*scaledVelocity m v w t₀ a ε τ 1*(σ^2/2) ≤
        ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ ∧
      0 < ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
  have hρ : 800*e*Θ^5 ≤ 1/2 := by nlinarith only [hp, hsmall]
  have hNne : R 2 ≠ 0 := by
    have hh := (abs_le.mp hN).1
    change -(800*e*Θ^5) ≤ R 2-1 at hh
    linarith only [hh, hρ]
  have hpair := scaled_pairing_zero m v r w (ne_of_gt hs₀) (ne_of_gt hε) hm hv hmv hrw
  have hthird := thirdRatio_from_pairing R V hNne (ne_of_gt hV) hpair
  have hj := controlled_pressure_ratio_lower hσ hσsmall hΘ hK he hσΘ hτ hτΘ hsmall
    hZ hfluxZ hZ0 hZ₁0 hP hQ hN hratio hA
  rw [← hthird] at hj
  have hid := physical_pressure_ratio M m v r w (ne_of_gt ha) (ne_of_gt hs₀) (ne_of_gt hε)
    hm hv hmv (ne_of_gt hV)
  rw [hid]
  have hc : 0 < s₀*a*V 1 := mul_pos (mul_pos hs₀ ha) hV
  exact ⟨mul_le_mul_of_nonneg_left hj hc.le, mul_pos hc (lt_of_lt_of_le (by positivity) hj)⟩

end EulerPacketMovingFrame
