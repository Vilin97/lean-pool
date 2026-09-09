/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameRenewal
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketTargetCompression
import LeanPool.NavierStokesAndEuler.Euler.PacketFrameCoefficients

/-! The source target-compression estimate for the actual next ray. -/

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
