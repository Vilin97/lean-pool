/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameRenewal
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameQuantitative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Packet Target Compression
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketTargetCompression

open Real EulerPacketRay EulerPacketFrameRenewal EulerPacketFrameQuantitative

/-- The common `Θ^40` smallness regime guarantees every sign and
denominator condition used in the perturbed target compression estimate. -/
theorem target_compression_order40
    {β t Θ K e ε H P Q N : ℝ}
    (hβ : 0 < β) (hβupper : β ≤ 1) (ht : 0 < t) (htΘ : t ≤ Θ)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hH : 0 ≤ H)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * t ^ 2)
    (hP : |P - β * t ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * β * t| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    0 < rayDenominator ε P Q N ∧
      H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  let ρ := 800 * e * Θ ^ 5
  let M := K * e * Θ ^ 40
  have hΘpos : 0 < Θ := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hρsmall : ρ ≤ 1 / 2 := by
    have hh := hp 5 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hρΘ : ρ * Θ ≤ 1 := by
    have hh := hp 6 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hβtΘ : 1 ≤ β * t * Θ := by
    have hh := mul_le_mul_of_nonneg_left htΘ (mul_nonneg hβ.le ht.le)
    nlinarith only [hh, hscale]
  have hρQ : ρ ≤ β * t := by
    apply (mul_le_mul_iff_right₀ hΘpos).mp
    nlinarith only [hρΘ, hβtΘ]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos ht]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.le
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hh, htΘ, hΘ2]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q + 2 * β * t) (-2 * β * t)
    have hid : Q + 2 * β * t + -2 * β * t = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    change |Q + 2 * β * t| ≤ ρ at hQ
    nlinarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hεQ : |ε * Q| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hε]
    have hh := mul_le_mul hεe hQabs (abs_nonneg Q) he
    have hm := hp 2 (by decide)
    nlinarith only [hh, hm, hMb]
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hP).1
    change ρ ≤ 1 / 2 at hρsmall
    dsimp [ρ] at hρsmall
    nlinarith only [hh, hρsmall, hscale]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  exact ⟨hDpos, perturbed_target_compression hβ ht hε hH hscale hρ hρsmall hρQ hP hQ hN hεQ⟩

/-- The full parent matrix has strictly negative target-ray compression
once its shear contribution dominates the older-gradient error. -/
theorem full_target_compression_negative
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G t : ℝ}
    (ht : 0 < t) (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G)
    (hShear : H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t))
    (hdominates : 30 * G * t < H * ε) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N < 0 := by
  have hfull := parent_ray_compression (H := H) hD hB
  have hdom : 3 * G < H * ε / (10 * t) := (lt_div_iff₀ (by positivity : 0 < 10 * t)).mpr
    (by nlinarith only [hdominates])
  rw [neg_div] at hShear
  nlinarith only [hfull, hShear, hdom]

end EulerPacketTargetCompression
