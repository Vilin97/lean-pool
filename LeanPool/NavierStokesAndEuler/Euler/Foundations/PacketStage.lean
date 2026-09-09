/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketExistence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Packet Stage
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketStage

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability
    EulerPacketExistence

/-- Absolute relative-stability constant obtained from the propagator
bound and the primary-solution lower comparison. -/
noncomputable def stabilityConstant : ℝ := 320000000 * exp 6

theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by
  have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
  unfold stabilityConstant
  nlinarith only [hh]

/-- The controlled velocity system has an exact scalar comparison
solution, constructed from the axioms rather than supplied as a hypothesis. -/
theorem controlled_stage_references
    {σ Θ T e ε lam : ℝ} {U V P Q N : ℝ → ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤
        160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧
        |V t / Z t - 1| ≤ stabilityConstant * e * Θ ^ 29 ∧
        |U t / V t + Z₁ t / Z t| ≤ 10 * (stabilityConstant * e * Θ ^ 29)) := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  obtain ⟨Z, Z₁, hZ0, hZ₁0, hZ, hfluxZ⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 lam
  have hK := stabilityConstant_ge
  have hΘ0 : 0 ≤ Θ := by linarith
  have hpow21 : Θ ^ 21 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hpow29 : Θ ^ 29 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hsmallODE : 8000000 * e * Θ ^ 21 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow21 he
    have hKmul := mul_nonneg (show 0 ≤ stabilityConstant - 8 by linarith)
      (mul_nonneg he (pow_nonneg hΘ0 40))
    nlinarith only [hsmall, hm, hKmul]
  have herror := controlled_velocity_relative_error hσ hσsmall hΘ hT0 hT he hε hεe hlam hsmallODE
    (fun t _ => hF t) (fun t _ => hG t) (fun t _ => hfluxF t) (fun t _ => hfluxG t)
    hF0 hF₁0 hG₁0 hRc hAc hCc hP hQ hN hU hV hRclose hAclose hCclose
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hrayInitial hU0 hV0 hZ0 hZ₁0
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, herror, ?_⟩
  intro t ht
  let δ := 160000000 * e * Θ ^ 29
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hrelSmall : 4 * exp 6 * δ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow29 (by positivity : 0 ≤ stabilityConstant * e)
    have hn : 0 ≤ stabilityConstant * e * Θ ^ 40 := by positivity
    dsimp [δ]
    unfold stabilityConstant at hm hn hsmall
    nlinarith only [hm, hn, hsmall]
  have herror' : |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t :=
    herror t ⟨by linarith [ht.1], ht.2⟩
  have hc := equation30_relative_state_consequences hσ hσsmall hlam ht.1 hδ hrelSmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 herror'
  refine ⟨hc.1, ?_, ?_⟩
  · dsimp [δ]
      at hc
    unfold stabilityConstant
    nlinarith only [hc.2.1]
  · dsimp [δ]
      at hc
    unfold stabilityConstant
    nlinarith only [hc.2.2]

/-- Early forward amplitudes are exponentially small relative to target
amplitude, with the initial slope cancelling from the estimate.  This is
the finite-ODE amplification mechanism underlying equation (36). -/
theorem early_forward_exponential_suppression
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ U V : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (_hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V T ∧ ∀ s ∈ Icc 0 1,
      (|U s| + |V s|) / V T ≤ 84 * exp 9 * Θ * exp (-(1 / (4 * σ))) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1 / σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hx : 1 ≤ σ * T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ * T := by positivity
  have hF₁0pos : 0 ≤ F₁ 0 := by rw [hF₁0]
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hσ hσsmall (fun t _ => hZ t)
    (fun t _ => hfluxZ t) hZ0 hZ₁0pos T hTpos.le
  have hc := equation30_relative_state_consequences hσ hσsmall hlam hT1 hδ hδsmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 (herror T ⟨hTpos.le, le_rfl⟩)
  have hVpos := hc.1
  have hVlower : Z T / 2 ≤ V T := by
    have hh := (abs_le.mp hc.2.1).1
    have hη : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hδsmall]
    have hratio : (1 : ℝ) / 2 ≤ V T / Z T := by nlinarith only [hh, hη]
    have hm := (le_div_iff₀ hZpos).mp hratio
    nlinarith only [hm]
  have hZlower := equation30_slope_uniform_lower hσ hσsmall hlam
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 T hT1
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ ^ 2 ≤ 1 / 16)
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := (equation30_post_inversion_lower hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos (σ * T) hx).1
  rw [mul_div_cancel_left₀ T hσne] at hpost
  have hFtarget : exp (1 / (4 * σ)) ≤ (σ * T) * F T := by
    have hh := (div_le_iff₀ hxpos).mp hpost
    nlinarith only [hgrowth, hh]
  have hexp6 : 0 < exp (6 : ℝ) := exp_pos _
  have hZscaled : (1 + lam) * F T ≤ 2 * exp 6 * Z T := by
    have hm := mul_le_mul_of_nonneg_left hZlower (by positivity : 0 ≤ 2 * exp (6 : ℝ))
    have hid : (2 * exp 6) * (((1 + lam) / (2 * exp 6)) * F T) = (1 + lam) * F T := by field_simp
    rw [hid] at hm
    nlinarith only [hm]
  have htarget : (1 + lam) * exp (1 / (4 * σ)) ≤ 4 * exp 6 * (σ * T) * V T := by
    have h₁ := mul_le_mul_of_nonneg_left hFtarget (by positivity : 0 ≤ 1 + lam)
    have h₂ := mul_le_mul_of_nonneg_left hZscaled hxpos.le
    have h₃ := mul_le_mul_of_nonneg_left hVlower (by positivity : 0 ≤ 4 * exp 6 * (σ * T))
    nlinarith only [h₁, h₂, h₃]
  refine ⟨hVpos, ?_⟩
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hT1⟩
  have hFpos := equation30_global_positive hσ hσsmall (fun t _ => hF t)
    (fun t _ => hfluxF t) hF0 hF₁0pos s hs.1
  have hFsmall := equation30_zero_slope_prefix_upper hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 s hs
  have hZstate := equation30_relative_propagator hσ hσsmall (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hs.1 hs.2
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 (fun t _ => hZ t) (fun t _ => hfluxZ t)
  simp only [hF0, hZ0, hZ₁0, one_pow, div_one, abs_one, abs_of_nonneg hlam, mul_one] at hZstate
  have hδ1 : δ ≤ 1 := by
    have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hm, hδsmall]
  have hUtri := abs_add_le (U s + Z₁ s) (-Z₁ s)
  have hVtri := abs_add_le (V s - Z s) (Z s)
  rw [abs_neg] at hUtri
  have hUid : U s + Z₁ s + -Z₁ s = U s := by ring
  have hVid : V s - Z s + Z s = V s := by ring
  rw [hUid] at hUtri
  rw [hVid] at hVtri
  have hnorm : |U s| + |V s| ≤ 21 * exp 3 * (1 + lam) := by
    have herr := herror s hsT
    have hmδ := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (1 + lam) * F s)
    have hmF := mul_le_mul_of_nonneg_right hFsmall (by positivity : 0 ≤ 21 * (1 + lam))
    nlinarith only [hUtri, hVtri, herr, hZstate, hmδ, hmF]
  have hscaled := mul_le_mul_of_nonneg_left htarget
    (by positivity : 0 ≤ 21 * exp 3 * exp (-(1 / (4 * σ))))
  have hexpCancel : exp (-(1 / (4 * σ))) * exp (1 / (4 * σ)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have hexp9 : exp (9 : ℝ) = exp 3 * exp 6 := by rw [← exp_add]; norm_num
  have hscaled' : 21 * exp 3 * (1 + lam) ≤ 84 * exp 9 * (σ * T) * exp (-(1 / (4 * σ))) * V T := by
    have hid : (21 * exp 3 * exp (-(1 / (4 * σ)))) * ((1 + lam) * exp (1 / (4 * σ))) =
        21 * exp 3 * (1 + lam) := by
      calc
        _ = (21 * exp 3 * (1 + lam)) * (exp (-(1 / (4 * σ))) * exp (1 / (4 * σ))) := by ring
        _ = _ := by rw [hexpCancel, mul_one]
    rw [hid] at hscaled
    rw [hexp9]
    nlinarith only [hscaled]
  have hxΘ : σ * T ≤ Θ := by
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hTpos.le
    nlinarith only [hm, hT]
  have hmΘ := mul_le_mul_of_nonneg_right hxΘ
    (by positivity : 0 ≤ 84 * exp 9 * exp (-(1 / (4 * σ))) * V T)
  apply (div_le_iff₀ hVpos).mpr
  nlinarith only [hnorm, hscaled', hmΘ]

end EulerPacketStage
