/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension

/-! Ray control for the genuine within-interval packet equations. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerClosedIntervalDerivativeExtension

theorem ray_closeness_within
    {β Θ T e : ℝ} {A : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 < T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hsmall : 400 * e * Θ ^ 5 ≤ 1)
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (A t 0 0 * P t + A t 0 1 * Q t + A t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (A t 1 0 * P t + A t 1 1 * Q t + A t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t) (Icc 0 T) t)
    (hclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealRayEntry β i j| ≤ e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      norm3 (P t-β*t^2) (Q t+2*β*t) (N t-1) ≤ 200*e*Θ^5 ∧ 1/2 ≤ N t := by
  obtain ⟨P', hPeq, hP'⟩ := exists_extension hT0 hP
  obtain ⟨Q', hQeq, hQ'⟩ := exists_extension hT0 hQ
  obtain ⟨N', hNeq, hN'⟩ := exists_extension hT0 hN
  have hPe : ∀ t ∈ Icc 0 T, HasDerivAt P'
      (A t 0 0*P' t+A t 0 1*Q' t+A t 0 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hP' t ht
  have hQe : ∀ t ∈ Icc 0 T, HasDerivAt Q'
      (A t 1 0*P' t+A t 1 1*Q' t+A t 1 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hQ' t ht
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt N'
      (A t 2 0*P' t+A t 2 1*Q' t+A t 2 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hN' t ht
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hi : norm3 (P' 0) (Q' 0) (N' 0-1) ≤ e := by
    simpa only [hPeq h0, hQeq h0, hNeq h0] using hinitial
  have h := ray_closeness_of_coefficient_error hβ hβupper hΘ hT0.le hT he hsmall
    hAc hPe hQe hNe hclose hi
  intro t ht
  simpa only [hPeq ht, hQeq ht, hNeq ht] using h t ht

end EulerPacketMovingFrame
