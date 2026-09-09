/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalSize
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import LeanPool.NavierStokesAndEuler.Euler.PacketFrameRenewalAlgebra
import LeanPool.NavierStokesAndEuler.Euler.PacketOrientedCoordinates

/-!
The source's next-frame scalar formulas represent the actual normalized
physical ray and velocity.  Orientation, physical norms, and pressure
numerators are identified exactly before any quantitative estimate is used.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay EulerPacketFrameStability InnerProductSpace ContinuousLinearMap

theorem physical_pressure_ratio (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ : ℝ} (ha : a ≠ 0) (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : scaledVelocity m v w t₀ a ε τ 1 ≠ 0) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
    ⟪r (physicalTime t₀ a ε τ),M (w (physicalTime t₀ a ε τ))⟫_ℝ =
      s₀*a*V 1*velocityNumerator A (R 0) (R 1) (R 2) (V 0/V 1) 1 (V 2/V 1) := by
  rw [← movingFlux_eq M m v r w _ hm hv hmv, movingFlux_scaling M m v r w ha hs₀ hε,
    velocityNumerator_homogeneous _ _ _ _ _ _ _ hV]
  dsimp only
  ring

theorem physical_cross_ratio (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ : ℝ} (ha : a ≠ 0) (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : scaledVelocity m v w t₀ a ε τ 1 ≠ 0) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
    ⟪cross (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)),
        M (w (physicalTime t₀ a ε τ))⟫_ℝ =
      s₀*a*(V 1)^2*frameCrossNumerator ε (R 0) (R 1) (R 2) (V 0/V 1) (V 2/V 1)
        (rowAction A 0 (V 0/V 1) (V 2/V 1)) (rowAction A 1 (V 0/V 1) (V 2/V 1))
        (rowAction A 2 (V 0/V 1) (V 2/V 1)) := by
  let p := unit (m (physicalTime t₀ a ε τ))
  let q := unit (v (physicalTime t₀ a ε τ))
  have hp : ⟪p,p⟫_ℝ = 1 := unit_inner_self hm
  have hq : ⟪q,q⟫_ℝ = 1 := unit_inner_self hv
  have hpq : ⟪p,q⟫_ℝ = 0 := unit_inner_zero hmv
  have hact (i : Fin 3) : frameCoordinates p q (M (w (physicalTime t₀ a ε τ))) i =
      ∑ j : Fin 3, frameMatrix M p q i j*movingVelocity m v w (physicalTime t₀ a ε τ) j :=
    (frame_action M p q (w (physicalTime t₀ a ε τ)) hp hq hpq i).symm
  have hc : ⟪cross (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)),
      M (w (physicalTime t₀ a ε τ))⟫_ℝ =
      ∑ i : Fin 3, (_root_.crossProduct (movingRay m v r (physicalTime t₀ a ε τ))
        (movingVelocity m v w (physicalTime t₀ a ε τ))) i *
          (∑ j : Fin 3, frameMatrix M p q i j*movingVelocity m v w (physicalTime t₀ a ε τ) j) := by
    have h := cross_inner_coordinates p q (r (physicalTime t₀ a ε τ))
      (w (physicalTime t₀ a ε τ)) (M (w (physicalTime t₀ a ε τ))) hp hq hpq
    simp only [hact] at h
    have hR : frameCoordinates p q (r (physicalTime t₀ a ε τ)) =
        movingRay m v r (physicalTime t₀ a ε τ) := rfl
    have hW : frameCoordinates p q (w (physicalTime t₀ a ε τ)) =
        movingVelocity m v w (physicalTime t₀ a ε τ) := rfl
    rw [hR, hW] at h
    simpa only [Fin.sum_univ_three] using h
  rw [hc]
  have hR : movingRay m v r (physicalTime t₀ a ε τ) =
      fun j => s₀*rayScale ε j*scaledRay m v r s₀ t₀ a ε τ j :=
    funext fun j => (scaledRay_restore m v r hs₀ hε j).symm
  have hW : movingVelocity m v w (physicalTime t₀ a ε τ) =
      fun j => velocityScale ε j*scaledVelocity m v w t₀ a ε τ j :=
    funext fun j => (scaledVelocity_restore m v w hε j).symm
  rw [hR, hW]
  exact scaling_cross_flux ha s₀ ε (frameMatrix M p q)
    (scaledRay m v r s₀ t₀ a ε τ) (scaledVelocity m v w t₀ a ε τ) hV

/-- Exact source (34) quantities for the actual next normalized frame. -/
theorem physical_frame_formulas (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ : ℝ} (ha : a ≠ 0) (hs₀ : 0 < s₀) (hε : ε ≠ 0)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hr : r (physicalTime t₀ a ε τ) ≠ 0)
    (hV : 0 < scaledVelocity m v w t₀ a ε τ 1) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
    let D := rayDenominator ε (R 0) (R 1) (R 2)
    let E := velocityDirectionNormSq ε (V 0/V 1) (V 2/V 1)
    let J := velocityNumerator A (R 0) (R 1) (R 2) (V 0/V 1) 1 (V 2/V 1)
    let C := frameCrossNumerator ε (R 0) (R 1) (R 2) (V 0/V 1) (V 2/V 1)
      (rowAction A 0 (V 0/V 1) (V 2/V 1)) (rowAction A 1 (V 0/V 1) (V 2/V 1))
      (rowAction A 2 (V 0/V 1) (V 2/V 1))
    normalizedCoupling M (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ))/a =
        J/(Real.sqrt D*Real.sqrt E) ∧
      normalizedTilt M (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)) =
        C/(J*Real.sqrt E) := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
  let D := rayDenominator ε (R 0) (R 1) (R 2)
  let E := velocityDirectionNormSq ε (V 0/V 1) (V 2/V 1)
  let J := velocityNumerator A (R 0) (R 1) (R 2) (V 0/V 1) 1 (V 2/V 1)
  let C := frameCrossNumerator ε (R 0) (R 1) (R 2) (V 0/V 1) (V 2/V 1)
    (rowAction A 0 (V 0/V 1) (V 2/V 1)) (rowAction A 1 (V 0/V 1) (V 2/V 1))
    (rowAction A 2 (V 0/V 1) (V 2/V 1))
  change normalizedCoupling M (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ))/a =
      J/(Real.sqrt D*Real.sqrt E) ∧
    normalizedTilt M (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)) = C/(J*Real.sqrt E)
  have hs₀ne := ne_of_gt hs₀
  have hVne : V 1 ≠ 0 := ne_of_gt hV
  have hEpos : 0 < E := velocityDenominator_pos ε (V 0/V 1) (V 2/V 1)
  have hrootE : Real.sqrt E ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hEpos)
  have hDne : D ≠ 0 := scaled_denominator_ne_zero m v r hs₀ne hε hm hv hmv hr
  have hDpos : 0 < D := by
    have hD0 : 0 ≤ D := by dsimp [D, rayDenominator]; positivity
    exact lt_of_le_of_ne hD0 (Ne.symm hDne)
  have hrootD : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hDpos)
  have hrn : ‖r (physicalTime t₀ a ε τ)‖ = s₀*Real.sqrt D := by
    simpa only [abs_of_pos hs₀] using scaledRay_norm m v r hs₀ne hε hm hv hmv
  have hwn : ‖w (physicalTime t₀ a ε τ)‖ = V 1*Real.sqrt E := by
    simpa only [abs_of_pos hV, E, V, velocityDirectionNormSq, velocityDenominator] using
      scaledVelocity_norm_ratio m v w hε hm hv hmv hVne
  have hw : w (physicalTime t₀ a ε τ) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hwn
    exact (mul_ne_zero hVne hrootE) hwn.symm
  have hflux : ⟪r (physicalTime t₀ a ε τ),M (w (physicalTime t₀ a ε τ))⟫_ℝ = s₀*a*V 1*J :=
    physical_pressure_ratio M m v r w ha hs₀ne hε hm hv hmv hVne
  have hcross : ⟪cross (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)),
      M (w (physicalTime t₀ a ε τ))⟫_ℝ = s₀*a*(V 1)^2*C :=
    physical_cross_ratio M m v r w ha hs₀ne hε hm hv hmv hVne
  constructor
  · rw [normalizedCoupling_eq, hflux, hrn, hwn]
    field_simp
  · by_cases hJ : J = 0
    · have hz : normalizedCoupling M (r (physicalTime t₀ a ε τ)) (w (physicalTime t₀ a ε τ)) = 0 :=
        by
        rw [normalizedCoupling_eq, hflux, hJ, mul_zero, zero_div]
      simp only [normalizedTilt, hz, hJ, zero_mul, div_zero]
    · have hfluxne : ⟪r (physicalTime t₀ a ε τ),M (w (physicalTime t₀ a ε τ))⟫_ℝ ≠ 0 := by
        rw [hflux]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs₀ne ha) hVne) hJ
      rw [normalizedTilt_eq M _ _ hr hw hfluxne, hflux, hcross, hwn]
      field_simp

end EulerPacketMovingFrame
