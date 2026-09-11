/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameRenewal
import LeanPool.NavierStokesAndEuler.Euler.PacketFrameCoefficients
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameQuantitative
import Mathlib.Algebra.Order.Star.Real

/-! The source target-compression estimate for the actual next ray. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay EulerPacketFrameRenewal
  EulerPacketTargetCompression InnerProductSpace ContinuousLinearMap

theorem normalizedCompression_eq (M : Space →L[ℝ] Space) (m v r : ℝ → Space)
    {s₀ t₀ a ε τ : ℝ} (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hD : 0 < rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
      (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2)) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    normalizedCoupling M (r (physicalTime t₀ a ε τ)) (r (physicalTime t₀ a ε τ)) =
      quadraticForm3 (frameMatrix M (unit (m (physicalTime t₀ a ε τ)))
        (unit (v (physicalTime t₀ a ε τ)))) (R 0) (ε*R 1) (R 2)/rayDenominator ε (R 0) (R 1) (R 2)
            := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let p := unit (m (physicalTime t₀ a ε τ))
  let q := unit (v (physicalTime t₀ a ε τ))
  have hp : ⟪p,p⟫_ℝ = 1 := unit_inner_self hm
  have hq : ⟪q,q⟫_ℝ = 1 := unit_inner_self hv
  have hpq : ⟪p,q⟫_ℝ = 0 := unit_inner_zero hmv
  have hnum : ⟪r (physicalTime t₀ a ε τ),M (r (physicalTime t₀ a ε τ))⟫_ℝ =
      s₀^2*quadraticForm3 (frameMatrix M p q) (R 0) (ε*R 1) (R 2) := by
    have hf := frame_flux M p q (r (physicalTime t₀ a ε τ)) (r (physicalTime t₀ a ε τ)) hp hq hpq
    change (∑ i : Fin 3, movingRay m v r (physicalTime t₀ a ε τ) i *
      (∑ j : Fin 3, frameMatrix M p q i j*movingRay m v r (physicalTime t₀ a ε τ) j)) = _ at hf
    rw [← hf]
    simp_rw [← scaledRay_restore m v r hs₀ hε]
    norm_num [Fin.sum_univ_three, rayScale, quadraticForm3, Fin.ext_iff, R]
    ring
  have hnorm := scaledRay_norm_sq m v r hs₀ hε hm hv hmv
  have hden : ‖r (physicalTime t₀ a ε τ)‖*‖r (physicalTime t₀ a ε τ)‖ =
      s₀^2*rayDenominator ε (R 0) (R 1) (R 2) := by simpa only [pow_two] using hnorm
  rw [normalizedCoupling_eq, hnum, hden]
  have hDne := ne_of_gt hD
  dsimp only [R, p, q]
  field_simp

theorem physical_parent_compression (B M E : Space →L[ℝ] Space) (h : ℝ) (m v r : ℝ → Space)
    {s₀ t₀ a ε τ : ℝ} (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hD : 0 < rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
      (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2))
    (hparent : M = B + h • rankOne ℝ (unit (v (physicalTime t₀ a ε τ)))
      (unit (m (physicalTime t₀ a ε τ))) + E) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    normalizedCoupling M (r (physicalTime t₀ a ε τ)) (r (physicalTime t₀ a ε τ)) ≤
      h*ε*R 1*R 0/rayDenominator ε (R 0) (R 1) (R 2)+3*(‖B‖+‖E‖) := by
  have hp := unit_inner_self hm
  have hq := unit_inner_self hv
  have hpq := unit_inner_zero hmv
  rw [normalizedCompression_eq M m v r hs₀ hε hm hv hmv hD, hparent,
    frameMatrix_parent B E h _ _ hp hq hpq]
  apply parent_ray_compression hD
  intro i j
  exact (abs_add_le _ _).trans (add_le_add (frameMatrix_abs_le B _ _ hp hq hpq i j)
    (frameMatrix_abs_le E _ _ hp hq hpq i j))

theorem physical_target_compression (B M E : Space →L[ℝ] Space) (h : ℝ) (m v r : ℝ → Space)
    {s₀ t₀ a ε τ β Θ K e : ℝ} (hs₀ : s₀ ≠ 0) (hε : 0 < ε)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hparent : M = B + h • rankOne ℝ (unit (v (physicalTime t₀ a ε τ)))
      (unit (m (physicalTime t₀ a ε τ))) + E)
    (hβ : 0 < β) (hβupper : β ≤ 1) (hτ : 0 < τ) (hτΘ : τ ≤ Θ)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e) (hh : 0 ≤ h)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * τ ^ 2)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - β * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 + 2 * β * τ| ≤ 800 * e * Θ ^ 5)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5) :
    normalizedCoupling M (r (physicalTime t₀ a ε τ)) (r (physicalTime t₀ a ε τ)) ≤
      -(h*ε)/(10*τ)+3*(‖B‖+‖E‖) ∧
    (30*(‖B‖+‖E‖)*τ < h*ε →
      normalizedCoupling M (r (physicalTime t₀ a ε τ)) (r (physicalTime t₀ a ε τ)) < 0) := by
  have hs := target_compression_order40 hβ hβupper hτ hτΘ hΘ hK he hε.le hεe hh
    hsmall hscale hP hQ hN
  have hb := physical_parent_compression B M E h m v r hs₀ (ne_of_gt hε) hm hv hmv hs.1 hparent
  have hbound := hb.trans (add_le_add hs.2 (le_refl (3*(‖B‖+‖E‖))))
  refine ⟨hbound, ?_⟩
  intro hdom
  have hd : 3*(‖B‖+‖E‖) < h*ε/(10*τ) :=
    (lt_div_iff₀ (by positivity : 0 < 10*τ)).mpr (by nlinarith only [hdom])
  rw [neg_div] at hbound
  linarith only [hbound, hd]

end EulerPacketMovingFrame
