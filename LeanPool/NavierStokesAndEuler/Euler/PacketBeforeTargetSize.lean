/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketIdealSize
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameQuantitative
import LeanPool.NavierStokesAndEuler.Euler.PacketActualFrameEstimates

/-!
The before-target part of the physical primary-size estimate.  The input
is the actual ray and velocity error already obtained from the physical
equations, and the comparison function solves the scalar reference ODE.
-/

section

/-! Uniform comparison between actual and ideal physical primary sizes. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketFrameStability EulerPacketFrameQuantitative
  InnerProductSpace

theorem scalar_size_comparison {s₀ D D₀ E V Z : ℝ}
    (hs₀ : 0 ≤ s₀) (hD₀ : 1 ≤ D₀) (hD : |D - D₀| ≤ 1 / 2)
    (hElo : 1 ≤ E) (hEup : E ≤ 2) (hZ : 0 < Z) (hV : |V - Z| ≤ Z / 2) :
    s₀*Real.sqrt D₀*Z/4 ≤ s₀*Real.sqrt D*V*Real.sqrt E ∧
      s₀*Real.sqrt D*V*Real.sqrt E ≤ 8*s₀*Real.sqrt D₀*Z := by
  have hd := abs_le.mp hD
  have hv := abs_le.mp hV
  have hDp : 0 < D := by linarith only [hd.1, hD₀]
  have hD₀p : 0 ≤ D₀ := by linarith only [hD₀]
  have hVlo : Z/2 ≤ V := by linarith only [hv.1]
  have hVup : V ≤ 2*Z := by linarith only [hv.2, hZ]
  have hVp : 0 ≤ V := by linarith only [hVlo, hZ]
  have hrootD : Real.sqrt D₀/2 ≤ Real.sqrt D := by
    have hh : Real.sqrt D₀ ≤ 2*Real.sqrt D := Real.sqrt_le_iff.mpr
      ⟨by positivity, by linarith only [Real.sq_sqrt hDp.le, hd.1, hD₀]⟩
    linarith only [hh]
  have hrootD' : Real.sqrt D ≤ 2*Real.sqrt D₀ := Real.sqrt_le_iff.mpr
    ⟨by positivity, by linarith only [Real.sq_sqrt hD₀p, hd.2, hD₀]⟩
  have hrootE : 1 ≤ Real.sqrt E := Real.one_le_sqrt.mpr hElo
  have hrootE' : Real.sqrt E ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hEup]⟩
  have hlower := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hrootD hs₀) hVlo (by positivity) (by positivity))
    hrootE (by norm_num : (0:ℝ) ≤ 1) (by positivity)
  have hupper := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hrootD' hs₀) hVup hVp (by positivity))
    hrootE' (Real.sqrt_nonneg E) (by positivity)
  constructor <;> linarith only [hlower, hupper]

/-- The actual primary size lies between fixed multiples of its ideal
size under the same quantitative ray and relative-state estimates already
proved for propagation. -/
theorem physical_size_comparison_order40 (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ Θ K e P₀ Q₀ r₀ Z : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2) (hr₀ : |r₀| ≤ 4) (hZ : 0 < Z)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hVrel : |scaledVelocity m v w t₀ a ε τ 1 / Z - 1| ≤ K * e * Θ ^ 29)
    (hratio : |scaledVelocity m v w t₀ a ε τ 0 / scaledVelocity m v w t₀ a ε τ 1 - r₀| ≤ 10 * (K *
        e * Θ ^ 29))
        :
    s₀*Real.sqrt (1+P₀^2)*Z/4 ≤ ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ ∧
      ‖r (physicalTime t₀ a ε τ)‖*‖w (physicalTime t₀ a ε τ)‖ ≤ 8*s₀*Real.sqrt (1+P₀^2)*Z := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  let ρ := 800*e*Θ^5
  let η := K*e*Θ^29
  let A := K*e*Θ^40
  have hK0 : 0 ≤ K := by linarith
  have hΘ0 : 0 ≤ Θ := by linarith
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : 1000000*A ≤ 1 := by simpa only [A, mul_assoc] using hsmall
  have hp (n : ℕ) (hn : n ≤ 40) : e*Θ^n ≤ A := scaled_power_le hΘ hK he hn
  have hηA : η ≤ A := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))
      (mul_nonneg hK0 he)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ : ρ ≤ 1/2 := by have hh := hp 5 (by decide); dsimp [ρ]; linarith only [hh, hA]
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη : η ≤ 1/2 := by linarith only [hηA, hA]
  have he1 : e ≤ 1 := by have hh := hp 0 (by decide); norm_num at hh; linarith only [hh, hA]
  have hε1 : ε ≤ 1 := hεe.trans he1
  have hε2e : ε^2 ≤ e := by nlinarith only [hε, hε1, hεe]
  have hε4 : ε^2*Θ^4 ≤ A :=
    (mul_le_mul_of_nonneg_right hε2e (pow_nonneg hΘ0 4)).trans (hp 4 (by decide))
  have hVdiff : |V 1-Z| ≤ Z/2 := by
    have hrel : |V 1/Z-1| ≤ 1/2 := hVrel.trans hη
    have hid : V 1/Z-1 = (V 1-Z)/Z := by field_simp
    rw [hid, abs_div, abs_of_pos hZ] at hrel
    have hh := (div_le_iff₀ hZ).mp hrel
    linarith only [hh]
  have hVp : 0 < V 1 := by have hh := (abs_le.mp hVdiff).1; linarith only [hh, hZ]
  have hNne : R 2 ≠ 0 := by
    have hh := (abs_le.mp hN).1
    change -ρ ≤ R 2-1 at hh
    linarith only [hh, hρ]
  have hpair := scaled_pairing_zero m v r w (ne_of_gt hs₀) (ne_of_gt hε) hm hv hmv hrw
  have hthird := thirdRatio_from_pairing R V hNne (ne_of_gt hVp) hpair
  obtain ⟨hrabs, _, hwabs, _⟩ := third_ratio_error hΘ hρ0 hρ hη0 hη hP₀ hQ₀ hP hQ hN hr₀ hratio
  rw [← hthird] at hwabs
  have hE := velocity_direction_norm_bound (ε := ε) hΘ hrabs hwabs
  have hEup : velocityDirectionNormSq ε (V 0/V 1) (V 2/V 1) ≤ 2 := by
    linarith only [hE.2, hε4, hA]
  obtain ⟨_, _, _, _, _, _, hDD⟩ := ray_geometric_bounds (ε := ε) (U := V 0/V 1) (V := 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hDsmall : |rayDenominator ε (R 0) (R 1) (R 2)-(1+P₀^2)| ≤ 1/2 := by
    have hp7 := hp 7 (by decide)
    dsimp [ρ] at hDD
    linarith only [hDD, hp7, hε4, hA]
  have hb := scalar_size_comparison hs₀.le (show 1 ≤ 1+P₀^2 by linarith [sq_nonneg P₀])
    hDsmall hE.1 hEup hZ hVdiff
  have hid := physical_primary_size m v r w hs₀ (ne_of_gt hε) hm hv hmv hVp
  rw [hid]
  exact hb

end EulerPacketMovingFrame

end
end

end

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
    linarith only [hh, hτΘ, sq_nonneg (Θ-1), hΘ]
  have hzpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hslope := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ
  have hr₀ : |-Z₁ τ/Z τ| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |scaledVelocity m v w t₀ a ε τ 0/scaledVelocity m v w t₀ a ε τ 1-(-Z₁ τ/Z τ)|
      ≤ 10*(K*e*Θ^29) := by simpa only [neg_div, sub_neg_eq_add] using hratio
  obtain ⟨hl, hu⟩ := physical_size_comparison_order40 m v r w hs₀ hε hm hv hmv hrw
    hΘ hK he hεe hsmall hP₀ hQ₀ hr₀ hzpos hP hQ hN hVrel hr'
  constructor <;> dsimp only [idealPrimarySize] <;> linarith only [hl, hu]

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
  linarith only [htarget, hcurrent, hh]

end EulerPacketMovingFrame
