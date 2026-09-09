/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborStability

@[expose] public section

/-! Relative propagator estimates on arbitrary subintervals for actual velocity states. -/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketBridge EulerPacketPerturbation EulerClosedIntervalDerivativeExtension

theorem velocity_propagator_bound
    {σ Θ s t δ : ℝ} {F F₁ G G₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20*Θ^8*δ*(t-s) ≤ 1/2)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hG : ∀ x, 0 ≤ x → HasDerivAt G (G₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*F₁ u)
      (2*(1-σ^2*(σ^2*x^2))*F x) x)
    (hfluxG : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*G₁ u)
      (2*(1-σ^2*(σ^2*x^2))*G x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ x ∈ Icc s t, HasDerivAt U (U₁ x) x)
    (hV : ∀ x ∈ Icc s t, HasDerivAt V (V₁ x) x)
    (hU₁c : ContinuousOn U₁ (Icc s t)) (hV₁c : ContinuousOn V₁ (Icc s t))
    (herror : ∀ x ∈ Icc s t,
      |U₁ x-idealVelocityFirst (σ^2) x (U x) (V x)|+|V₁ x+U x| ≤ δ*(|U x|+|V x|)) :
    |U t|+|V t| ≤ 40*Θ^8*(F t/F s)*(|U s|+|V s|) := by
  let f : ℝ → ℝ := fun x => V₁ x+U x
  let g : ℝ → ℝ := fun x => -U₁ x+idealVelocityFirst (σ^2) x (U x) (V x)
  have hUc : ContinuousOn U (Icc s t) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc s t) := fun x hx => (hV x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc s t) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc s t) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ x ∈ Icc s t, HasDerivAt V (-U x+f x) x := by
    intro x hx
    exact (velocity_scalar_flux (β := σ^2) (hU x hx) (hV x hx)).1
  have hfluxY : ∀ x ∈ Icc s t, HasDerivAt (fun u => (1+(σ^2*u^2)^2)*(-U u))
      (2*(1-σ^2*(σ^2*x^2))*V x+(1+(σ^2*x^2)^2)*g x) x := by
    intro x hx
    exact (velocity_scalar_flux (β := σ^2) (hU x hx) (hV x hx)).2
  have hforcing : ∀ x ∈ Icc s t, |f x|+|g x| ≤ δ*(|V x|+|-U x|) := by
    intro x hx
    have hg : |g x| = |U₁ x-idealVelocityFirst (σ^2) x (U x) (V x)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    linarith only [herror x hx]
  have hb := equation30_perturbed_bound hσ hσsmall hΘ hs hst ht hδ hsmall
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hfc hgc hforcing t ⟨hst, le_rfl⟩
  simpa only [abs_neg, add_comm] using hb

theorem velocity_propagator_bound_within
    {σ Θ T e : ℝ} {F F₁ G G₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40*e*Θ^21 ≤ 1)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hG : ∀ x, 0 ≤ x → HasDerivAt G (G₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*F₁ u)
      (2*(1-σ^2*(σ^2*x^2))*F x) x)
    (hfluxG : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*G₁ u)
      (2*(1-σ^2*(σ^2*x^2))*G x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ x ∈ Icc 0 T, HasDerivWithinAt U (U₁ x) (Icc 0 T) x)
    (hV : ∀ x ∈ Icc 0 T, HasDerivWithinAt V (V₁ x) (Icc 0 T) x)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (herror : ∀ x ∈ Icc 0 T,
      |U₁ x-idealVelocityFirst (σ^2) x (U x) (V x)|+|V₁ x+U x| ≤ (e*Θ^12)*(|U x|+|V x|)) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      |U t|+|V t| ≤ 40*Θ^8*(F t/F s)*(|U s|+|V s|) := by
  obtain ⟨U', hUeq, hU'⟩ := exists_extension hT0 hU
  obtain ⟨V', hVeq, hV'⟩ := exists_extension hT0 hV
  intro s t hs hst ht
  have hsub : Icc s t ⊆ Icc 0 T := fun x hx => ⟨hs.trans hx.1, hx.2.trans ht⟩
  have hδ : 0 ≤ e*Θ^12 := by positivity
  have hspan : t-s ≤ Θ := by linarith only [ht, hT, hs]
  have hsmall' : 20*Θ^8*(e*Θ^12)*(t-s) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hspan (show 0 ≤ 20*e*Θ^20 by positivity)
    nlinarith only [hh, hsmall]
  have he' : ∀ x ∈ Icc s t,
      |U₁ x-idealVelocityFirst (σ^2) x (U' x) (V' x)|+|V₁ x+U' x| ≤
        (e*Θ^12)*(|U' x|+|V' x|) := by
    intro x hx
    simpa only [hUeq (hsub hx), hVeq (hsub hx)] using herror x (hsub hx)
  have hb := velocity_propagator_bound hσ hσsmall hΘ hs hst (ht.trans hT) hδ hsmall'
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 (fun x hx => hU' x (hsub hx))
    (fun x hx => hV' x (hsub hx)) (hU₁c.mono hsub) (hV₁c.mono hsub) he'
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
  simpa only [hUeq htT, hVeq htT, hUeq hsT, hVeq hsT] using hb

end EulerPacketMovingFrame
