/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalNormBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFamily

@[expose] public section

/-!
Early physical amplitudes are exponentially small relative to the center
target amplitude.  The initial scalar slope cancels, including for
neighboring initial data controlled by the common reference.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay EulerPacketStage InnerProductSpace

theorem early_neighbor_state_bound {α : Type*} (center : α) (U V : α → ℝ → ℝ)
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1/σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδsmall : 4*exp 6*δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
      (2*(1-σ^2*(σ^2*t^2))*F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ ξ t, t ∈ Icc 0 T → |V ξ t-Z t|+|U ξ t+Z₁ t| ≤ δ*(1+lam)*F t) :
    0 < V center T ∧ ∀ ξ s, s ∈ Icc 0 1 →
      (|U ξ s|+|V ξ s|)/V center T ≤ 84*exp 9*Θ*exp (-(1/(4*σ))) := by
  have hcenter := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 (herror center)
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hTnot : ¬T ≤ 1 := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  refine ⟨hcenter.1, ?_⟩
  intro ξ s hs
  let U' : ℝ → ℝ := fun t => if t ≤ 1 then U ξ t else U center t
  let V' : ℝ → ℝ := fun t => if t ≤ 1 then V ξ t else V center t
  have he : ∀ t ∈ Icc 0 T, |V' t-Z t|+|U' t+Z₁ t| ≤ δ*(1+lam)*F t := by
    intro t ht
    by_cases h : t ≤ 1
    · simpa only [U', V', ite_eq_left h] using herror ξ t ht
    · simpa only [U', V', ite_eq_right h] using herror center t ht
  have hh := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 he
  simpa only [U', V', ite_eq_left hs.2, ite_eq_right hTnot] using hh.2 s hs

/-- The early part of source (36) for actual Euclidean norm products.
The estimate is uniform over neighboring labels and over the nonnegative
initial slope of the common scalar reference. -/
theorem early_physical_size_suppression {α : Type*} (center : α)
    (m v : ℝ → Space) (r w : α → ℝ → Space)
    {s₀ t₀ a ε σ Θ T lam δ ρ : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1/σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδsmall : 4*exp 6*δ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/2)
    (hm : ∀ τ ∈ Icc 0 T, m (physicalTime t₀ a ε τ) ≠ 0)
    (hv : ∀ τ ∈ Icc 0 T, v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ∀ τ ∈ Icc 0 T, ⟪m (physicalTime t₀ a ε τ),v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ∀ ξ τ, τ ∈ Icc 0 T → ⟪r ξ (physicalTime t₀ a ε τ),w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hP : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2| ≤ ρ)
    (hQ : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 1-(-2*σ^2*τ)| ≤ ρ)
    (hN : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1| ≤ ρ)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
      (2*(1-σ^2*(σ^2*t^2))*F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ ξ τ, τ ∈ Icc 0 T →
      |scaledVelocity m v (w ξ) t₀ a ε τ 1-Z τ|+
        |scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ| ≤ δ*(1+lam)*F τ) :
    0 < ‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖ ∧
    ∀ ξ τ, τ ∈ Icc 0 1 →
      (‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖)/
          (‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖) ≤
        8232*exp 9*Θ^5*exp (-(1/(4*σ))) := by
  have hstate := early_neighbor_state_bound center
    (fun ξ τ => scaledVelocity m v (w ξ) t₀ a ε τ 0)
    (fun ξ τ => scaledVelocity m v (w ξ) t₀ a ε τ 1)
    hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 herror
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hTT : T ∈ Icc 0 T := ⟨hTpos.le, le_rfl⟩
  have hNt : 1/2 ≤ scaledRay m v (r center) s₀ t₀ a ε T 2 := by
    have hh := (abs_le.mp (hN center T hTT)).1
    linarith only [hh, hρ]
  have htarget := physical_size_ge_second m v (r center) (w center) hs₀ (ne_of_gt hε)
    (hm T hTT) (hv T hTT) (hmv T hTT) hNt hstate.1.le
  have htargetpos : 0 < ‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖ :=
    lt_of_lt_of_le (div_pos (mul_pos hs₀ hstate.1) (by norm_num)) htarget
  refine ⟨htargetpos, ?_⟩
  intro ξ τ hτ
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans hT1⟩
  have hΘ2 : 1 ≤ Θ^2 := one_le_pow₀ hΘ
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hτ2 : τ^2 ≤ 1 := by nlinarith only [hτ.1, hτ.2]
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ σ^2*τ^2)]
    have hh := mul_le_mul hσ2 hτ2 (sq_nonneg τ) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hh, hΘ2]
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hh := mul_le_mul hσ2 hτ.2 hτ.1 (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hh, hΘ2]
  have hupper := physical_size_le_scaled_state m v (r ξ) (w ξ) hs₀ hε hε1
    (hm τ hτT) (hv τ hτT) (hmv τ hτT) (hrw ξ τ hτT) hΘ hρ0 hρ hP₀ hQ₀
    (hP ξ τ hτT) (hQ ξ τ hτT) (hN ξ τ hτT)
  have hstates := (div_le_iff₀ hstate.1).mp (hstate.2 ξ τ hτ)
  have hs := mul_le_mul_of_nonneg_left hstates (show 0 ≤ 49*s₀*Θ^4 by positivity)
  have ht := mul_le_mul_of_nonneg_left htarget
    (show 0 ≤ 8232*exp 9*Θ^5*exp (-(1/(4*σ))) by positivity)
  apply (div_le_iff₀ htargetpos).mpr
  nlinarith only [hupper, hs, ht]

end EulerPacketMovingFrame
