/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrameRenewal
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocitySystem

@[expose] public section

/-!
The quantified source frame-renewal bounds concern the actual normalized
physical vectors.  The third ratio is eliminated using actual tangency,
and the scalar estimate is transported through the checked exact formulas.
-/

noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketFrameStability
  EulerPacketFrameQuantitative InnerProductSpace

theorem thirdRatio_from_pairing (R V : Fin 3 → ℝ) (hN : R 2 ≠ 0) (hV : V 1 ≠ 0)
    (hpair : R 0*V 0+R 1*V 1+R 2*V 2 = 0) :
    V 2/V 1 = velocityThird (R 0) (R 1) (R 2) (V 0/V 1) 1 := by
  unfold velocityThird
  apply (eq_div_iff hN).mpr
  field_simp
  linarith only [hpair]

theorem physical_frame_renewal_order40 (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε σ y Θ K e : ℝ} {Z Z₁ : ℝ → ℝ}
    (ha : a ≠ 0) (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hm : m (physicalTime t₀ a ε (y⁻¹/σ)) ≠ 0)
    (hv : v (physicalTime t₀ a ε (y⁻¹/σ)) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε (y⁻¹/σ)),v (physicalTime t₀ a ε (y⁻¹/σ))⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε (y⁻¹/σ)),w (physicalTime t₀ a ε (y⁻¹/σ))⟫_ℝ = 0)
    (hV : 0 < scaledVelocity m v w t₀ a ε (y⁻¹/σ) 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hy : 0 < y) (hysmall : y ≤ 1/2)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e)
    (htΘ : y⁻¹/σ ≤ Θ) (hsmall : 1000000*K*e*Θ^40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |scaledRay m v r s₀ t₀ a ε (y⁻¹/σ) 0-(y⁻¹)^2| ≤ 800*e*Θ^5)
    (hQ : |scaledRay m v r s₀ t₀ a ε (y⁻¹/σ) 1+2*σ*y⁻¹| ≤ 800*e*Θ^5)
    (hN : |scaledRay m v r s₀ t₀ a ε (y⁻¹/σ) 2-1| ≤ 800*e*Θ^5)
    (hratio : |scaledVelocity m v w t₀ a ε (y⁻¹/σ) 0/scaledVelocity m v w t₀ a ε (y⁻¹/σ) 1+
      Z₁ (y⁻¹/σ)/Z (y⁻¹/σ)| ≤ 10*(K*e*Θ^29))
    (hA : ∀ i j, |scaledAction M m v a ε (physicalTime t₀ a ε (y⁻¹/σ)) i j-
      idealVelocityEntry (σ^2) i j| ≤ 3*e) :
    |normalizedCoupling M (r (physicalTime t₀ a ε (y⁻¹/σ))) (w (physicalTime t₀ a ε (y⁻¹/σ)))/a-1| ≤
      y^4+σ^2*y^2+8*σ*y^3+30000000*K*e*Θ^40 ∧
    |(y⁻¹)^2*normalizedTilt M (r (physicalTime t₀ a ε (y⁻¹/σ))) (w (physicalTime t₀ a ε
      (y⁻¹/σ)))-1| ≤
      1500*σ+30000000*K*e*Θ^40 := by
  let R := scaledRay m v r s₀ t₀ a ε (y⁻¹/σ)
  let V := scaledVelocity m v w t₀ a ε (y⁻¹/σ)
  have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
  have hρ : 800*e*Θ^5 ≤ 1/2 := by nlinarith only [hsmall, hp]
  have hNne : R 2 ≠ 0 := by
    have hh := (abs_le.mp hN).1
    change -(800*e*Θ^5) ≤ R 2-1 at hh
    linarith only [hh, hρ]
  have hr : r (physicalTime t₀ a ε (y⁻¹/σ)) ≠ 0 := by
    intro hz
    apply hNne
    simp only [R, scaledRay, movingRay, hz, inner_zero_right, zero_div]
  have hpair := scaled_pairing_zero m v r w (ne_of_gt hs₀) (ne_of_gt hε) hm hv hmv hrw
  have hthird := thirdRatio_from_pairing R V hNne (ne_of_gt hV) hpair
  have hform := physical_frame_formulas M m v r w ha hs₀ (ne_of_gt hε) hm hv hmv hr hV
  have hbound := frame_renewal_order40 hσ hσsmall hy hysmall hΘ hK he hε.le hεe htΘ hsmall
    hZ hfluxZ hZ0 hZ₁0 hP hQ hN hratio hA
  dsimp only at hbound hform
  rw [← hthird] at hbound
  constructor
  · rw [hform.1]
    exact hbound.1
  · rw [hform.2]
    simpa only [mul_div_assoc] using hbound.2

end EulerPacketMovingFrame
