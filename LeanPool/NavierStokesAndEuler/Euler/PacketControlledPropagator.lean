/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborControlled
public import LeanPool.NavierStokesAndEuler.Euler.PacketReferenceRatio
public import LeanPool.NavierStokesAndEuler.Euler.PacketVelocityPropagator

@[expose] public section

/-! The actual controlled velocity system has polynomial relative propagation. -/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketBridge EulerPacketExistence

/-- No initial velocity restriction is imposed.  The reference can have
any nonnegative initial slope, and the bound retains its ratio. -/
theorem controlled_velocity_propagator_within
    {σ Θ T e ε : ℝ} {Z Z₁ U V P Q N : ℝ → ℝ}
    {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 8000000*e*Θ^21 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0*P t+R t 0 1*Q t+R t 0 2*N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0*P t+R t 1 1*Q t+R t 1 2*N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0*P t+R t 2 1*Q t+R t 2 2*N t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j-idealRayEntry (σ^2) i j| ≤ 4*e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j-idealVelocityEntry (σ^2) i j| ≤ 3*e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j-idealUnprojectedEntry 0 j| ≤ 5*e ∧
      |C t 1 j-idealUnprojectedEntry 1 j| ≤ 5*e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0-1) ≤ e)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      |U t|+|V t| ≤ 40*Θ^8*(Z t/Z s)*(|U s|+|V s|) := by
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hgeom : 10000*e*Θ^5 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he
    nlinarith only [hsmall, hh, mul_nonneg he (pow_nonneg hΘ0 21)]
  have hcontrol := ray_controlled_velocity_error_within (sq_nonneg σ) hσ2 hΘ hT0 hT
    he hε hεe hgeom hRc hP hQ hN hRclose hAclose hCclose hrayInitial
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousWithinAt
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousWithinAt
  have hNne : ∀ t ∈ Icc 0 T, N t ≠ 0 := by
    intro t ht
    linarith only [(hcontrol t ht).1.2]
  obtain ⟨hU₁c, hV₁c⟩ := continuousOn_velocity_rhs (ε := ε) hAc hCc hPc hQc hNc hUc hVc hNne
  have hs : 40*(200000*e)*Θ^21 ≤ 1 := by nlinarith only [hsmall]
  have hprop := velocity_propagator_bound_within hσ hσsmall hΘ hT0 hT
    (show 0 ≤ 200000*e by positivity) hs (fun t _ => hF t) (fun t _ => hG t)
    (fun t _ => hfluxF t) (fun t _ => hfluxG t) hF0 hF₁0 hG₁0 hU hV hU₁c hV₁c
    (fun t ht => (hcontrol t ht).2 (U t) (V t))
  intro s t hstart hst ht
  have hratio := equation30_slope_ratio_dominates hσ hσsmall hZ₁0
    (fun x _ => hF x) hZ (fun x _ => hfluxF x) hfluxZ hF0 hF₁0 hZ0 rfl hstart hst
  have hcompare := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (show 0 ≤ 40*Θ^8 by positivity))
    (add_nonneg (abs_nonneg (U s)) (abs_nonneg (V s)))
  exact (hprop s t hstart hst ht).trans hcompare

end EulerPacketMovingFrame
