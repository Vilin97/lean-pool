/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCoefficients
import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientMotion
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Actual shear motion, exposed for the compression scale guard. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
   InnerProductSpace ContinuousLinearMap

theorem physical_shear_motion_bound
    {B B₁ E : ℝ → Space →L[ℝ] Space} {m v : ℝ → Space}
    {c t₀ a ε Θ G d β : ℝ} {S : Set ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hsmall : 16 * (ε * Θ * (4 * G) ^ 2 + d) ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G ^ 2)
    (hE : ∀ t ∈ S, ‖E t‖ ≤ d)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a * β)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a / ε ^ 2) :
    let e := 16*(ε*Θ*(4*G)^2+d)
    ε ≤ e ∧ ∀ τ ∈ Icc 0 Θ, |ε^2*rescaledShear c m v t₀ a ε τ/a-1| ≤ e := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  let Bf := rescaledFrame B m v t₀ a ε
  let Ef := rescaledFrame E m v t₀ a ε
  let Hf := rescaledShear c m v t₀ a ε
  let Df : ℝ → Fin 3 → Fin 3 → ℝ := fun τ i j =>
    frameMatrixRate (B (physicalTime t₀ a ε τ)) (B₁ (physicalTime t₀ a ε τ))
      (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ))) i j*(ε/a)
  let H₁f : ℝ → ℝ := fun τ => -(Bf τ 0 0+Bf τ 1 1)*Hf τ*(ε/a)
  have ha0 : 0 < a := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hscale : |ε/a| ≤ 2*ε := by
    rw [abs_div, abs_of_pos hε, abs_of_pos ha0, div_le_iff₀ ha0]
    nlinarith only [mul_nonneg hε.le (sub_nonneg.mpr ha)]
  have hBF : ∀ τ ∈ Icc 0 Θ, ∀ i j, |Bf τ i j| ≤ 4*G := by
    intro τ hτ i j
    have ht := hmap hτ
    exact (frameMatrix_abs_le _ _ _ (unit_inner_self (hm0 _ ht))
      (unit_inner_self (hv0 _ ht)) (unit_inner_zero (hmv _ ht)) i j).trans
      ((hB _ ht).trans (by linarith))
  have hEF : ∀ τ ∈ Icc 0 Θ, ∀ i j, |Ef τ i j| ≤ d := by
    intro τ hτ i j
    have ht := hmap hτ
    exact (frameMatrix_abs_le _ _ _ (unit_inner_self (hm0 _ ht))
      (unit_inner_self (hv0 _ ht)) (unit_inner_zero (hmv _ ht)) i j).trans (hE _ ht)
  have hDF : ∀ τ ∈ Icc 0 Θ, ∀ i j,
      HasDerivWithinAt (fun s => Bf s i j) (Df τ i j) (Icc 0 Θ) τ := by
    intro τ hτ i j
    have ht := hmap hτ
    exact (frameMatrix_hasDerivWithinAt (hBd _ ht) (hmd _ ht) (hvd _ ht)
      (hm0 _ ht) (hv0 _ ht) (hmv _ ht) i j).comp τ
        (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap
  have hDFbound : ∀ τ ∈ Icc 0 Θ, ∀ i j, |Df τ i j| ≤ 2*ε*(4*G)^2 := by
    intro τ hτ i j
    have ht := hmap hτ
    have hrate := frameMatrixRate_abs_le (B (physicalTime t₀ a ε τ))
      (B₁ (physicalTime t₀ a ε τ)) _ _ (unit_inner_self (hm0 _ ht))
      (unit_inner_self (hv0 _ ht)) (unit_inner_zero (hmv _ ht)) i j
    have hnormsq : ‖B (physicalTime t₀ a ε τ)‖^2 ≤ G^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hB _ ht) 2
    have hrate' : |frameMatrixRate (B (physicalTime t₀ a ε τ)) (B₁ (physicalTime t₀ a ε τ))
        (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ))) i j| ≤ 13*G^2 := by
      linarith only [hrate, hnormsq, hB₁ _ ht]
    dsimp [Df]
    rw [abs_mul]
    calc
      _ ≤ (13*G^2)*(2*ε) := mul_le_mul hrate' hscale (abs_nonneg _) (by positivity)
      _ ≤ 2*ε*(4*G)^2 := by nlinarith only [mul_nonneg hε.le (sq_nonneg G)]
  have hHF : ∀ τ ∈ Icc 0 Θ, HasDerivWithinAt Hf (H₁f τ) (Icc 0 Θ) τ := by
    intro τ hτ
    have ht := hmap hτ
    exact (primaryShear_hasDerivWithinAt (B (physicalTime t₀ a ε τ)) c (hmd _ ht)
      (hvd _ ht) (hm0 _ ht) (hv0 _ ht) (hmv _ ht)).comp τ
        (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap
  have hHFbound : ∀ τ ∈ Icc 0 Θ, |H₁f τ| ≤ (4*ε*(4*G))*|Hf τ| := by
    intro τ hτ
    have ht := hmap hτ
    have hrate := primaryShear_rate_bound (B (physicalTime t₀ a ε τ)) c m v _
      (hm0 _ ht) (hv0 _ ht) (hmv _ ht)
    have hrate' : |-(Bf τ 0 0+Bf τ 1 1)*Hf τ| ≤ 2*G*|Hf τ| := by
      exact hrate.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB _ ht) (by norm_num)) (abs_nonneg _))
    dsimp [H₁f]
    rw [abs_mul]
    calc
      _ ≤ (2*G*|Hf τ|)*(2*ε) := mul_le_mul hrate' hscale (abs_nonneg _) (by positivity)
      _ ≤ (4*ε*(4*G))*|Hf τ| := by
        nlinarith only [mul_nonneg (mul_nonneg hε.le hG0) (abs_nonneg (Hf τ))]
  have herr := normalized_motion_errors_within ha hε hΘ (show 1 ≤ 4*G by linarith)
    hd hsmall hBF hEF (fun τ hτ => hDF τ hτ 0 1) (fun τ hτ => hDF τ hτ 2 1)
    (fun τ hτ => hDFbound τ hτ 0 1) (fun τ hτ => hDFbound τ hτ 2 1)
    hHF hHFbound hb0 hk0 hh0
  exact ⟨herr.1, fun τ hτ => (herr.2 τ hτ).2.2.1⟩

end EulerPacketMovingFrame
