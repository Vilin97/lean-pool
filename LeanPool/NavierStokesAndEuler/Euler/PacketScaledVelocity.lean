/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingVelocity
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocityAlgebra

@[expose] public section

/-!
The actual projected velocity equation after the source scaling, with its
pressure numerator and denominator identified exactly.  The first two rows
therefore feed the existing scalar-amplification estimates.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

def scaledVelocity (m v w : ℝ → Space) (t₀ a ε τ : ℝ) (i : Fin 3) : ℝ :=
  movingVelocity m v w (physicalTime t₀ a ε τ) i / velocityScale ε i

theorem scaledRay_restore (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) (i : Fin 3) :
    s₀*rayScale ε i*scaledRay m v r s₀ t₀ a ε τ i = movingRay m v r (physicalTime t₀ a ε τ) i := by
  unfold scaledRay
  field_simp [hs₀, rayScale_ne_zero hε i]

theorem scaledVelocity_restore (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : ε ≠ 0) (i : Fin 3) :
    velocityScale ε i*scaledVelocity m v w t₀ a ε τ i = movingVelocity m v w (physicalTime t₀ a ε
      τ) i := by
  unfold scaledVelocity
  field_simp [velocityScale_ne_zero hε i]

def scaledAction (M : Space →L[ℝ] Space) (m v : ℝ → Space) (a ε t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  scaledVelocityEntry a ε (frameMatrix M (unit (m t)) (unit (v t)))

def scaledTransport (B M : Space →L[ℝ] Space) (m v : ℝ → Space) (a ε t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  scaledVelocityEntry a ε (fun i j => frameMatrix M (unit (m t)) (unit (v t)) i j +
    frameSkew (frameMatrix B (unit (m t)) (unit (v t))) i j)

theorem movingDenominator_scaling (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) :
    movingDenominator m v r (physicalTime t₀ a ε τ) = s₀^2 *
      rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
        (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2) := by
  unfold movingDenominator
  simp_rw [← scaledRay_restore m v r hs₀ hε]
  exact scaling_denominator s₀ ε (scaledRay m v r s₀ t₀ a ε τ)

theorem movingFlux_scaling (M : Space →L[ℝ] Space) (m v r w : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (ha : a ≠ 0) (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) :
    movingFlux M m v r w (physicalTime t₀ a ε τ) = s₀*a*
      velocityNumerator (scaledAction M m v a ε (physicalTime t₀ a ε τ))
        (scaledRay m v r s₀ t₀ a ε τ 0) (scaledRay m v r s₀ t₀ a ε τ 1)
        (scaledRay m v r s₀ t₀ a ε τ 2)
        (scaledVelocity m v w t₀ a ε τ 0) (scaledVelocity m v w t₀ a ε τ 1)
        (scaledVelocity m v w t₀ a ε τ 2) := by
  unfold movingFlux
  simp_rw [← scaledRay_restore m v r hs₀ hε, ← scaledVelocity_restore m v w hε]
  exact scaling_flux ha s₀ ε _ _ _

theorem scaled_pairing_zero (m v r w : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ),v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ),w (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    scaledRay m v r s₀ t₀ a ε τ 0*scaledVelocity m v w t₀ a ε τ 0 +
      scaledRay m v r s₀ t₀ a ε τ 1*scaledVelocity m v w t₀ a ε τ 1 +
      scaledRay m v r s₀ t₀ a ε τ 2*scaledVelocity m v w t₀ a ε τ 2 = 0 := by
  have h := moving_pairing m v r w (physicalTime t₀ a ε τ) hm hv hmv
  rw [hrw] at h
  simp_rw [← scaledRay_restore m v r hs₀ hε, ← scaledVelocity_restore m v w hε] at h
  rw [scaling_pairing] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hs₀ hε)

theorem scaled_denominator_ne_zero (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ),v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hr : r (physicalTime t₀ a ε τ) ≠ 0) :
    rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
      (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2) ≠ 0 := by
  have h := movingDenominator_scaling m v r hs₀ hε (t₀ := t₀) (a := a) (τ := τ)
  rw [movingDenominator_eq m v r _ hm hv hmv] at h
  intro hz
  rw [hz, mul_zero] at h
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hr) h

/-- The actual three scaled velocity coordinates satisfy the exact projected
system, including the small middle-row pressure factor `ε²`. -/
theorem scaledVelocity_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r w : ℝ → Space} {s₀ t₀ a ε τ : ℝ} {S U : Set ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hm : HasDerivWithinAt m (-B.adjoint (m (physicalTime t₀ a ε τ))) S (physicalTime t₀ a ε τ))
    (hv : HasDerivWithinAt v (-B (v (physicalTime t₀ a ε τ)) +
      (2*⟪m (physicalTime t₀ a ε τ),B (v (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖m (physicalTime t₀ a ε τ)‖^2) • m (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hw : HasDerivWithinAt w (-M (w (physicalTime t₀ a ε τ)) +
      (2*⟪r (physicalTime t₀ a ε τ),M (w (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖r (physicalTime t₀ a ε τ)‖^2) • r (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hm0 : m (physicalTime t₀ a ε τ) ≠ 0) (hv0 : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ),v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hr0 : r (physicalTime t₀ a ε τ) ≠ 0) (i : Fin 3) :
    HasDerivWithinAt (fun σ => scaledVelocity m v w t₀ a ε σ i)
      (scaledVelocityRhs (scaledAction M m v a ε (physicalTime t₀ a ε τ))
        (scaledTransport B M m v a ε (physicalTime t₀ a ε τ)) ε
        (scaledRay m v r s₀ t₀ a ε τ) (scaledVelocity m v w t₀ a ε τ) i) U τ := by
  have h := ((movingVelocity_hasDerivWithinAt B M hm hv hw hm0 hv0 hmv i).comp τ
    (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap).div_const (velocityScale ε i)
  rw [movingFlux_scaling M m v r w ha hs₀ hε, movingDenominator_scaling m v r hs₀ hε] at h
  simp_rw [← scaledVelocity_restore m v w hε, ← scaledRay_restore m v r hs₀ hε] at h
  rw [scaling_velocity_rate ha hε hs₀ (scaled_denominator_ne_zero m v r hs₀ hε hm0 hv0 hmv hr0)] at
    h
  simpa only [scaledVelocityRhs, scaledTransport, scaledAction, scaledVelocity, Function.comp_def]
    using h

end EulerPacketMovingFrame
