/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketPerturbation
import Mathlib.Tactic.Positivity.Finset

/-!
Relative stability with an actual initial velocity discrepancy.  This keeps
the neighbor-data contribution in the Duhamel estimate rather than requiring
the perturbed velocity to have exactly the center initial data.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketBridge EulerPacketPerturbation
  EulerClosedIntervalDerivativeExtension

theorem velocity_difference_bound
    {σ Θ T e : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤
      20*Θ^8*F t*(|V 0-Z 0|+|U 0+Z₁ 0|)+800*e*Θ^29*F t*(|V 0|+|U 0|) := by
  let f : ℝ → ℝ := fun t => V₁ t+U t
  let g : ℝ → ℝ := fun t => -U₁ t+idealVelocityFirst (σ^2) t (U t) (V t)
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc 0 T) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ t ∈ Icc 0 T, HasDerivAt V (-U t+f t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ^2) (hU t ht) (hV t ht)).1
  have hfluxY : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*(-U s))
      (2*(1-σ^2*(σ^2*t^2))*V t+(1+(σ^2*t^2)^2)*g t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ^2) (hU t ht) (hV t ht)).2
  have hforcing : ∀ t ∈ Icc 0 T, |f t|+|g t| ≤ (e*Θ^12)*(|V t|+|-U t|) := by
    intro t ht
    have hg : |g t| = |U₁ t-idealVelocityFirst (σ^2) t (U t) (V t)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    linarith only [herror t ht]
  have hδ : 0 ≤ e*Θ^12 := by positivity
  have hs : 20*Θ^8*(e*Θ^12)*(T-0) ≤ 1/2 := by
    have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ 20*e*Θ^20 by positivity)
    nlinarith only [hsmall, hm]
  have hh := equation30_perturbed_difference_bound hσ hσsmall hΘ (by norm_num : (0:ℝ) ≤ 0)
    hT0 hT hδ hs hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hZ hfluxZ hfc hgc hforcing
  have habs (x y : ℝ) : |-x-y| = |x+y| := by rw [show -x-y = -(x+y) by ring, abs_neg]
  intro t ht
  have h := hh t ht
  simp only [hF0, div_one, habs, abs_neg] at h
  convert! h using 1
  ring

theorem velocity_difference_bound_within
    {σ Θ T e : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (U₁ t) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V (V₁ t) (Icc 0 T) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤
      20*Θ^8*F t*(|V 0-Z 0|+|U 0+Z₁ 0|)+800*e*Θ^29*F t*(|V 0|+|U 0|) := by
  obtain ⟨U', hUeq, hU'⟩ := exists_extension hT0 hU
  obtain ⟨V', hVeq, hV'⟩ := exists_extension hT0 hV
  have he' : ∀ t ∈ Icc 0 T,
      |U₁ t-idealVelocityFirst (σ^2) t (U' t) (V' t)|+|V₁ t+U' t| ≤
        (e*Θ^12)*(|U' t|+|V' t|) := by
    intro t ht
    simpa only [hUeq ht, hVeq ht] using herror t ht
  have hh := velocity_difference_bound hσ hσsmall hΘ hT0.le hT he hsmall hF hG hfluxF hfluxG
    hF0 hF₁0 hG₁0 hU' hV' hU₁c hV₁c hZ hfluxZ he'
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  intro t ht
  simpa only [hUeq ht, hVeq ht, hUeq h0, hVeq h0] using hh t ht

/-- Converting the retained initial discrepancy to the source's neighbor
normalization costs no additional power of `Θ`. -/
theorem neighbor_initial_error_bound
    {Θ e η lam Ft u₀ v₀ L : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam) (hFt : 0 ≤ Ft)
    (hi : |v₀ - 1| + |u₀ + lam| ≤ η)
    (hb : L ≤ 20 * Θ ^ 8 * Ft * (|v₀ - 1| + |u₀ + lam|) + 800 * e * Θ ^ 29 * Ft * (|v₀| + |u₀|)) :
    L ≤ (20*η*Θ^8+800*e*Θ^29*(1+lam+η))*Ft := by
  have hv := abs_add_le (v₀-1) 1
  have hu := abs_add_le (u₀+lam) (-lam)
  simp only [sub_add_cancel, abs_one, add_neg_cancel_right, abs_neg, abs_of_nonneg hlam] at hv hu
  have hnorm : |v₀|+|u₀| ≤ 1+lam+η := by linarith only [hv, hu, hi]
  have h1 := mul_le_mul_of_nonneg_left hi (show 0 ≤ 20*Θ^8*Ft by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 800*e*Θ^29*Ft by positivity)
  nlinarith only [hb, h1, h2]

end EulerPacketMovingFrame
