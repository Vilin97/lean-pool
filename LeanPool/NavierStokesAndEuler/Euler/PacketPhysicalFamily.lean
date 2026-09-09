/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborControlled
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.PacketBeforeTargetSize
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalNeighbor
import LeanPool.NavierStokesAndEuler.Euler.PacketScalarUniqueness
import Mathlib.Algebra.Order.Star.Real

/-!
Uniform neighboring amplification and before-target size control from the
actual physical equations.  The scalar reference is shared by uniqueness,
so its choice is independent of the physical label.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap

theorem physical_family_amplification_and_size {α : Type*} (center : α)
    {B B₁ : ℝ → Space →L[ℝ] Space} {M E : α → ℝ → Space →L[ℝ] Space}
    {m v : ℝ → Space} {r w : α → ℝ → Space}
    {c s₀ t₀ a ε σ Θ T G d lam : ℝ} {S : Set ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT0 : 1 ≤ T) (hT : T ≤ Θ)
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hs₀ : 0 < s₀) (hlam : 0 ≤ lam)
    (hsmall : 1000000 * neighborStabilityConstant * (16 * (ε * Θ * (4 * G) ^ 2 + d)) * Θ ^ 40 ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hMc : ∀ ξ, ContinuousOn (M ξ) S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hrd : ∀ ξ t, t ∈ S → HasDerivWithinAt (r ξ) (-(M ξ t).adjoint (r ξ t)) S t)
    (hwd : ∀ ξ t, t ∈ S → HasDerivWithinAt (w ξ) (-(M ξ t) (w ξ t) +
      (2 * ⟪r ξ t, (M ξ t) (w ξ t)⟫_ℝ / ‖r ξ t‖ ^ 2) • r ξ t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0) (hrw0 : ∀ ξ, ⟪r ξ t₀, w ξ t₀⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G ^ 2)
    (hE : ∀ ξ t, t ∈ S → ‖E ξ t‖ ≤ d)
    (hparent : ∀ ξ t, t ∈ S → M ξ t = B t +
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t)) + E ξ t)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a * σ ^ 2)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a / ε ^ 2)
    (hrInitial : ∀ ξ,
      norm3 (scaledRay m v (r ξ) s₀ t₀ a ε 0 0) (scaledRay m v (r ξ) s₀ t₀ a ε 0 1)
        (scaledRay m v (r ξ) s₀ t₀ a ε 0 2 - 1) ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d))
    (hvelocityInitial : ∀ ξ, |scaledVelocity m v (w ξ) t₀ a ε 0 1 - 1| +
      |scaledVelocity m v (w ξ) t₀ a ε 0 0 + lam| ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d)) :
    let e := 16*(ε*Θ*(4*G)^2+d)
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
        (2*(1-σ^2*(σ^2*t^2))*F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
        (2*(1-σ^2*(σ^2*t^2))*Z t) t) ∧
      (∀ ξ τ, τ ∈ Icc 0 T →
        norm3 (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1) ≤ 800*e*Θ^5 ∧
        1/2 ≤ scaledRay m v (r ξ) s₀ t₀ a ε τ 2 ∧
        ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0) ∧
      (∀ ξ τ, τ ∈ Icc 0 T →
        |scaledVelocity m v (w ξ) t₀ a ε τ 1-Z τ| +
          |scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧
      (∀ ξ τ, τ ∈ Icc 1 T →
        0 < scaledVelocity m v (w ξ) t₀ a ε τ 1 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 1/Z τ-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 0/scaledVelocity m v (w ξ) t₀ a ε τ 1+Z₁ τ/Z τ|
          ≤ 10*(neighborStabilityConstant*e*Θ^29)) ∧
      (∀ ξ τ, τ ∈ Icc 1 T →
        ‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖ ≤
          64*(‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖)) := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  have hTpos : 0 < T := by linarith only [hT0]
  have hall (ξ : α) := physical_neighbor_stage_references hσ hσsmall hTpos hT ha hε hΘ hG hd
    (ne_of_gt hs₀) hlam hsmall hmap (hMc ξ) hBd hmd hvd (hrd ξ) (hwd ξ) hm0 hv0 hmv (hrw0 ξ)
    hB hB₁ (hE ξ) (hparent ξ) hb0 hk0 hh0 (hrInitial ξ) (hvelocityInitial ξ)
  obtain ⟨_, F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, _, _⟩ := hall center
  have hcommon (ξ : α) :
      (∀ τ ∈ Icc 0 T,
        norm3 (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1) ≤ 800*e*Θ^5 ∧
        1/2 ≤ scaledRay m v (r ξ) s₀ t₀ a ε τ 2 ∧
        ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0) ∧
      (∀ τ ∈ Icc 0 T,
        |scaledVelocity m v (w ξ) t₀ a ε τ 1-Z τ| +
          |scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧
      (∀ τ ∈ Icc 1 T,
        0 < scaledVelocity m v (w ξ) t₀ a ε τ 1 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 1/Z τ-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 0/scaledVelocity m v (w ξ) t₀ a ε τ 1+Z₁ τ/Z τ|
          ≤ 10*(neighborStabilityConstant*e*Θ^29)) := by
    obtain ⟨hray, F', F₁', Z', Z₁', hF0', hF₁0', hZ0', hZ₁0', hF', hZ', hfluxF', hfluxZ', herr,
        hrel⟩ := hall ξ
    have hFeq := equation30_state_eq_of_initial hσ hσsmall (fun t _ => hF' t) (fun t _ => hF t)
      (fun t _ => hfluxF' t) (fun t _ => hfluxF t) (hF0'.trans hF0.symm) (hF₁0'.trans hF₁0.symm)
    have hZeq := equation30_state_eq_of_initial hσ hσsmall (fun t _ => hZ' t) (fun t _ => hZ t)
      (fun t _ => hfluxZ' t) (fun t _ => hfluxZ t) (hZ0'.trans hZ0.symm) (hZ₁0'.trans hZ₁0.symm)
    refine ⟨hray, ?_, ?_⟩
    · intro τ hτ
      simpa only [(hFeq τ hτ.1).1, (hZeq τ hτ.1).1, (hZeq τ hτ.1).2] using herr τ hτ
    · intro τ hτ
      have ht0 : 0 ≤ τ := by linarith only [hτ.1]
      simpa only [(hZeq τ ht0).1, (hZeq τ ht0).2] using hrel τ hτ
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ,
    (fun ξ => (hcommon ξ).1), (fun ξ => (hcommon ξ).2.1), (fun ξ => (hcommon ξ).2.2), ?_⟩
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hεe : ε ≤ e := by
    have hg : 1 ≤ (4*G)^2 := by nlinarith only [hG, sq_nonneg (G-1)]
    have hc : 1 ≤ Θ*(4*G)^2 := by
      simpa only [one_mul] using mul_le_mul hΘ hg
        (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hΘ] : 0 ≤ Θ)
    have hh := mul_le_mul_of_nonneg_left hc hε.le
    dsimp [e]
    nlinarith only [hh, hd, hε]
  have hK : 1 ≤ neighborStabilityConstant := (by
      norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  have hsub : Icc (1:ℝ) T ⊆ Icc 0 T := fun _ ht => ⟨by linarith only [ht.1], ht.2⟩
  have htime {τ : ℝ} (hτ : τ ∈ Icc 1 T) : physicalTime t₀ a ε τ ∈ S :=
    hmap ⟨(hsub hτ).1, hτ.2.trans hT⟩
  have hrays (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 1 T) :
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2| ≤ 800*e*Θ^5 ∧
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 1-(-2*σ^2*τ)| ≤ 800*e*Θ^5 ∧
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1| ≤ 800*e*Θ^5 := by
    have hh := ((hcommon ξ).1 τ (hsub hτ)).1
    unfold norm3 at hh
    have hqeq : scaledRay m v (r ξ) s₀ t₀ a ε τ 1-(-2*σ^2*τ) =
        scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ := by ring
    rw [hqeq]
    constructor
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1)]
    constructor
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1)]
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)]
  exact physical_before_target_size_bound center (fun _ => m) (fun _ => v) r w
    hs₀ hε hσ hσsmall hT0 hT hΘ hK he hεe hsmall
    (fun _ _ hτ => hm0 _ (htime hτ)) (fun _ _ hτ => hv0 _ (htime hτ))
    (fun _ _ hτ => hmv _ (htime hτ)) (fun ξ τ hτ => ((hcommon ξ).1 τ (hsub hτ)).2.2)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 (by rw [hZ₁0]; exact hlam)
    (fun ξ τ hτ => (hrays ξ τ hτ).1) (fun ξ τ hτ => (hrays ξ τ hτ).2.1)
    (fun ξ τ hτ => (hrays ξ τ hτ).2.2) (fun ξ τ hτ => ((hcommon ξ).2.2 τ hτ).2.1)
    (fun ξ τ hτ => ((hcommon ξ).2.2 τ hτ).2.2)

end EulerPacketMovingFrame
