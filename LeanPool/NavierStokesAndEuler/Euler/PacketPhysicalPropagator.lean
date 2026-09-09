/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalStage
public import LeanPool.NavierStokesAndEuler.Euler.PacketControlledPropagator
public import LeanPool.NavierStokesAndEuler.Euler.PacketTangentNorm

@[expose] public section

/-!
The arbitrary physical tangent propagator has polynomial loss relative to
the actual primary scalar profile.  All scaled coefficients and tangency
properties are derived from the physical ODEs and parent decomposition.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketStage EulerPacketPerturbation InnerProductSpace ContinuousLinearMap

theorem physical_tangent_propagator
    {B B₁ M E : ℝ → Space →L[ℝ] Space} {m v r w : ℝ → Space}
    {c s₀ t₀ a ε σ Θ T G d : ℝ} {S : Set ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hT0 : 0 < T) (hT : T ≤ Θ)
    (ha : 1/2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hs₀ : s₀ ≠ 0)
    (hsmall : 8000000*(16*(ε*Θ*(4*G)^2+d))*Θ^21 ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hMc : ContinuousOn M S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t)+
      (2*⟪m t,(B t) (v t)⟫_ℝ/‖m t‖^2) • m t) S t)
    (hrd : ∀ t ∈ S, HasDerivWithinAt r (-(M t).adjoint (r t)) S t)
    (hwd : ∀ t ∈ S, HasDerivWithinAt w (-(M t) (w t)+
      (2*⟪r t,(M t) (w t)⟫_ℝ/‖r t‖^2) • r t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t,v t⟫_ℝ = 0) (hrw0 : ⟪r t₀,w t₀⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G^2)
    (hE : ∀ t ∈ S, ‖E t‖ ≤ d)
    (hparent : ∀ t ∈ S, M t = B t+
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t))+E t)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a*σ^2)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a/ε^2)
    (hrInitial : norm3 (scaledRay m v r s₀ t₀ a ε 0 0) (scaledRay m v r s₀ t₀ a ε 0 1)
      (scaledRay m v r s₀ t₀ a ε 0 2-1) ≤ 16*(ε*Θ*(4*G)^2+d))
    {Z Z₁ : ℝ → ℝ}
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    ContinuousOn Z (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, 0 < Z t) ∧
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
        ‖w (physicalTime t₀ a ε t)‖ ≤
          (560*Θ^10/ε)*(Z t/Z s)*‖w (physicalTime t₀ a ε s)‖ := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  let Rp := scaledRay m v r s₀ t₀ a ε
  let Vp := scaledVelocity m v w t₀ a ε
  let Mf := rescaledFrame M m v t₀ a ε
  let Bf := rescaledFrame B m v t₀ a ε
  let Rmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledRayEntry a ε (Mf τ) (frameSkew (Bf τ))
  let Amat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledVelocityEntry a ε (Mf τ)
  let Cmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ =>
    scaledVelocityEntry a ε (fun i j => Mf τ i j+frameSkew (Bf τ) i j)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hΘ0 : 0 ≤ Θ := by linarith
  change 8000000*e*Θ^21 ≤ 1 at hsmall
  have heΘ : e ≤ e*Θ^21 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hΘ : 1 ≤ Θ^21) he
  have heSmall : e ≤ 1 := by nlinarith only [hsmall, heΘ, he]
  have hpow : e*Θ^5 ≤ e*Θ^21 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he
  have hsmallRay : 400*(4*e)*Θ^5 ≤ 1 := by
    nlinarith only [hsmall, hpow, mul_nonneg he (pow_nonneg hΘ0 5)]
  have ha0 : 0 < a := by linarith
  have hσsq : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have herr := physical_matrix_errors ha hε hΘ hG hd heSmall hmap hBd hmd hvd hm0 hv0 hmv
    hB hB₁ hE hparent hb0 hk0 hh0
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 Θ := fun _ ht => ⟨ht.1, ht.2.trans hT⟩
  have hmapT : MapsTo (physicalTime t₀ a ε) (Icc 0 T) S := fun _ ht => hmap (hsub ht)
  have hMf : ∀ i j, ContinuousOn (fun τ => Mf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B M hmapT hMc hmd hvd hm0 hv0 hmv
  have hBf : ∀ i j, ContinuousOn (fun τ => Bf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B B hmapT (fun t ht => (hBd t ht).continuousWithinAt)
      hmd hvd hm0 hv0 hmv
  have hSf := frameSkew_continuousOn hBf
  have hRmc : ∀ i j, ContinuousOn (fun τ => Rmat τ i j) (Icc 0 T) :=
    scaledRayEntry_continuousOn a ε hMf hSf
  have hAmc : ∀ i j, ContinuousOn (fun τ => Amat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε hMf
  have hCmc : ∀ i j, ContinuousOn (fun τ => Cmat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε (fun i j => (hMf i j).add (hSf i j))
  have hRode : ∀ i τ, τ ∈ Icc 0 T → HasDerivWithinAt (fun s => Rp s i)
      (∑ j : Fin 3, Rmat τ i j*Rp τ j) (Icc 0 T) τ := by
    intro i τ hτ
    have ht := hmapT hτ
    exact scaledRay_hasDerivWithinAt (B (physicalTime t₀ a ε τ)) (M (physicalTime t₀ a ε τ))
      (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT (hmd _ ht) (hvd _ ht) (hrd _ ht)
      (hm0 _ ht) (hv0 _ ht) (hmv _ ht) i
  have hP : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 0)
      (Rmat τ 0 0*Rp τ 0+Rmat τ 0 1*Rp τ 1+Rmat τ 0 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 0 τ hτ
  have hQ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 1)
      (Rmat τ 1 0*Rp τ 0+Rmat τ 1 1*Rp τ 1+Rmat τ 1 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 1 τ hτ
  have hN : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 2)
      (Rmat τ 2 0*Rp τ 0+Rmat τ 2 1*Rp τ 1+Rmat τ 2 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 2 τ hτ
  have hRclose : ∀ τ ∈ Icc 0 T, ∀ i j, |Rmat τ i j-idealRayEntry (σ^2) i j| ≤ 4*e :=
    fun τ hτ => (herr.2 τ (hsub hτ)).1
  have hnear := ray_closeness_within (sq_nonneg σ) hσsq hΘ hT0 hT
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) he) hsmallRay hRmc hP hQ hN hRclose
    (hrInitial.trans (show e ≤ 4*e by linarith))
  have hrnonzero : ∀ τ ∈ Icc 0 T, r (physicalTime t₀ a ε τ) ≠ 0 := by
    intro τ hτ hzero
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    apply hNne
    simp only [Rp, scaledRay, movingRay, hzero, inner_zero_right, zero_div]
  have hpair := rescaled_tangentPairing_zero M hmapT hrd hwd hrnonzero hrw0
  have hUV : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun s => Vp s 0)
        (velocityFirstRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
          T) τ ∧
      HasDerivWithinAt (fun s => Vp s 1)
        (velocitySecondRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
          T) τ := by
    intro τ hτ
    have ht := hmapT hτ
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    exact scaledVelocity_firstTwo_hasDerivWithinAt (B (physicalTime t₀ a ε τ))
      (M (physicalTime t₀ a ε τ)) (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT
      (hmd _ ht) (hvd _ ht) (hwd _ ht) (hm0 _ ht) (hv0 _ ht) (hmv _ ht)
      (hrnonzero τ hτ) (hpair τ hτ) hNne
  have hprop := controlled_velocity_propagator_within hσ hσsmall hΘ hT0 hT he hε.le herr.1 hsmall
    hRmc hAmc hCmc hP hQ hN (fun τ hτ => (hUV τ hτ).1) (fun τ hτ => (hUV τ hτ).2)
    hRclose (fun τ hτ => (herr.2 τ (hsub hτ)).2.1) (fun τ hτ => (herr.2 τ (hsub hτ)).2.2)
    hrInitial hZ hfluxZ hZ0 hZ₁0
  have hZpos := EulerPacketGrowth.equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  refine ⟨(fun τ hτ => (hZ τ hτ.1).continuousAt.continuousWithinAt),
    (fun τ hτ => hZpos τ hτ.1), ?_⟩
  intro s t hs hst ht
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
  have htimeS := hmapT hsT
  have htimeT := hmapT htT
  have hε1 : ε ≤ 1 := herr.1.trans heSmall
  have hρ0 : 0 ≤ 800*e*Θ^5 := by positivity
  have hρ : 800*e*Θ^5 ≤ 1/2 := by
    nlinarith only [hsmall, hpow, mul_nonneg he (pow_nonneg hΘ0 5)]
  have hrt : norm3 (Rp t 0-σ^2*t^2) (Rp t 1+2*σ^2*t) (Rp t 2-1) ≤ 800*e*Θ^5 := by
    nlinarith only [(hnear t htT).1]
  have hPt : |Rp t 0-σ^2*t^2| ≤ 800*e*Θ^5 := by
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 1+2*σ^2*t), abs_nonneg (Rp t 2-1)]
  have hQt : |Rp t 1-(-2*σ^2*t)| ≤ 800*e*Θ^5 := by
    rw [show Rp t 1-(-2*σ^2*t) = Rp t 1+2*σ^2*t by ring]
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 0-σ^2*t^2), abs_nonneg (Rp t 2-1)]
  have hNt : |Rp t 2-1| ≤ 800*e*Θ^5 := by
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 0-σ^2*t^2), abs_nonneg (Rp t 1+2*σ^2*t)]
  have htΘ : t ≤ Θ := ht.trans hT
  have ht2 : t^2 ≤ Θ^2 := (sq_le_sq₀ htT.1 hΘ0).mpr htΘ
  have hP₀ : |σ^2*t^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ σ^2*t^2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσsq (sq_nonneg t), ht2]
  have hQ₀ : |-2*σ^2*t| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg htT.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσsq htT.1, htΘ, hΘ, sq_nonneg (Θ-1)]
  have hfinish := physical_velocity_le_scaled_state m v r w hs₀ hε hε1
    (hm0 _ htimeT) (hv0 _ htimeT) (hmv _ htimeT) (hpair t htT) hΘ hρ0 hρ hP₀ hQ₀ hPt hQt hNt
  have hstart := scaled_pair_le_physical_norm m v w hε hε1 (hm0 _ htimeS) (hv0 _ htimeS) (hmv _
    htimeS)
  have hratio : 0 ≤ Z t/Z s := div_nonneg (hZpos t htT.1).le (hZpos s hs).le
  have h1 := mul_le_mul_of_nonneg_left (hprop s t hs hst ht) (show 0 ≤ 7*Θ^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hstart (show 0 ≤ 280*Θ^10*(Z t/Z s) by positivity)
  calc
    _ ≤ 7*Θ^2*(|Vp t 0|+|Vp t 1|) := hfinish
    _ ≤ 7*Θ^2*(40*Θ^8*(Z t/Z s)*(|Vp s 0|+|Vp s 1|)) := h1
    _ = 280*Θ^10*(Z t/Z s)*(|Vp s 0|+|Vp s 1|) := by ring
    _ ≤ 280*Θ^10*(Z t/Z s)*((2/ε)*‖w (physicalTime t₀ a ε s)‖) := h2
    _ = _ := by ring

end EulerPacketMovingFrame
