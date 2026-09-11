/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketIdealSize
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import LeanPool.NavierStokesAndEuler.Euler.PacketBeforeTargetSize
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
The primary size remains controlled on the short interval after target.
The actual scalar ODE gives the needed uniform logarithmic growth bound;
there is no separate post-target growth hypothesis.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth EulerPacketFrameStability InnerProductSpace

theorem equation30_short_size_comparison {σ s t : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * Z₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * Z x) x)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t - s ≤ 1) :
    idealPrimarySize σ Z t ≤ 2*exp 6*idealPrimarySize σ Z s := by
  let W : ℝ → ℝ := fun x => (1+σ^2*x^2)*Z x
  let W₁ : ℝ → ℝ := fun x => (2*σ^2*x)*Z x+(1+σ^2*x^2)*Z₁ x
  have hzpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  have hW (x : ℝ) (hx : 0 ≤ x) : HasDerivAt W (W₁ x) x := by
    convert! (((((hasDerivAt_id x).pow 2).const_mul (σ^2)).const_add 1).mul (hZ x hx)) using 1
    dsimp [W₁]
    ring
  have hWpos (x : ℝ) (hx : 0 ≤ x) : 0 < W x := mul_pos (by positivity) (hzpos x hx)
  have hderivBound (x : ℝ) (hx : 1 ≤ x) : |W₁ x| ≤ 6*W x := by
    have hx0 : 0 ≤ x := by linarith only [hx]
    have hlog := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 x hx
    have hzx := hzpos x hx0
    rw [abs_div, abs_of_pos hzx, div_le_iff₀ hzx] at hlog
    have ht := abs_add_le ((2*σ^2*x)*Z x) ((1+σ^2*x^2)*Z₁ x)
    rw [abs_of_nonneg (by positivity : 0 ≤ (2*σ^2*x)*Z x), abs_mul,
      abs_of_pos (by positivity : 0 < 1+σ^2*x^2)] at ht
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1+σ^2*x^2 by positivity)
    have hx2 : x ≤ x^2 := by nlinarith only [hx]
    have hcoef := mul_le_mul_of_nonneg_right hx2 (show 0 ≤ 2*σ^2*Z x by positivity)
    dsimp [W₁, W]
    linarith only [ht, hh, hcoef, hzx]
  have hcont : ContinuousOn W (Icc s t) := fun x hx =>
    (hW x (by linarith only [hs, hx.1])).continuousAt.continuousWithinAt
  have hright : ∀ x ∈ Ico s t, HasDerivWithinAt W (W₁ x) (Ici x) x :=
    fun x hx => (hW x (by linarith only [hs, hx.1])).hasDerivWithinAt
  have hs0 : 0 ≤ s := by linarith only [hs]
  have ht0 : 0 ≤ t := hs0.trans hst
  have hbound : ∀ x ∈ Ico s t, ‖W₁ x‖ ≤ 6*‖W x‖+0 := by
    intro x hx
    have hx1 : 1 ≤ x := hs.trans hx.1
    simpa only [Real.norm_eq_abs, abs_of_pos (hWpos x (by linarith only [hx1])), add_zero]
      using hderivBound x hx1
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hright
    (show ‖W s‖ ≤ W s by rw [Real.norm_eq_abs, abs_of_pos (hWpos s hs0)]) hbound t ⟨hst, le_rfl⟩
  rw [gronwallBound_ε0, Real.norm_eq_abs, abs_of_pos (hWpos t ht0)] at hg
  have hexp : exp (6*(t-s)) ≤ exp 6 := exp_le_exp.mpr (by linarith only [hshort])
  have hgrowth : W t ≤ W s*exp 6 := hg.trans (mul_le_mul_of_nonneg_left hexp (hWpos s hs0).le)
  have htWeight := (quadratic_weight_sqrt (show 0 ≤ σ^2*t^2 by positivity)).1
  have hsWeight := (quadratic_weight_sqrt (show 0 ≤ σ^2*s^2 by positivity)).2
  have hleft := mul_le_mul_of_nonneg_right htWeight (hzpos t ht0).le
  have hright' := mul_le_mul_of_nonneg_right hsWeight (hzpos s hs0).le
  have hrightExp := mul_le_mul_of_nonneg_right hright' (exp_pos (6:ℝ)).le
  dsimp [W] at hgrowth
  dsimp [idealPrimarySize]
  linarith only [hleft, hgrowth, hrightExp]

theorem equation30_horizon_size_comparison {σ T H τ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * Z₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * Z x) x)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) (hT : 1 ≤ T) (hshort : H - T ≤ 1)
    (hτ : 0 ≤ τ) (hτH : τ ≤ H) :
    idealPrimarySize σ Z τ ≤ 2*exp 6*idealPrimarySize σ Z T := by
  by_cases hpre : τ ≤ T
  · have hbound := equation30_ideal_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hτ hpre
    have hpos : 0 ≤ idealPrimarySize σ Z T := mul_nonneg (sqrt_nonneg _)
      (equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 T (by linarith only [hT])).le
    have he : 1 ≤ exp (6:ℝ) := one_le_exp_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right he hpos
    linarith only [hbound, hh]
  · exact equation30_short_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hT
      (le_of_not_ge hpre) (by linarith only [hshort, hτH])

theorem physical_horizon_size_bound {α : Type*} (center : α)
    (m v r w : α → ℝ → Space) {s₀ t₀ a ε T H Θ K e σ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hT : 1 ≤ T) (hTH : T ≤ H) (hHΘ : H ≤ Θ) (hshort : H - T ≤ 1)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hm : ∀ ξ τ, τ ∈ Icc 1 H → m ξ (physicalTime t₀ a ε τ) ≠ 0)
    (hv : ∀ ξ τ, τ ∈ Icc 1 H → v ξ (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ∀ ξ τ, τ ∈ Icc 1 H →
      ⟪m ξ (physicalTime t₀ a ε τ), v ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ∀ ξ τ, τ ∈ Icc 1 H →
      ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : ∀ ξ τ, τ ∈ Icc 1 H →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : ∀ ξ τ, τ ∈ Icc 1 H →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : ∀ ξ τ, τ ∈ Icc 1 H →
      |scaledRay (m ξ) (v ξ) (r ξ) s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hVrel : ∀ ξ τ, τ ∈ Icc 1 H →
      |scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 1 / Z τ - 1| ≤ K * e * Θ ^ 29)
    (hratio : ∀ ξ τ, τ ∈ Icc 1 H →
      |scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 0 / scaledVelocity (m ξ) (v ξ) (w ξ) t₀ a ε τ 1 +
          Z₁
          τ / Z τ|
        ≤ 10 * (K * e * Θ ^ 29)) :
    ∀ ξ τ, τ ∈ Icc 1 H →
      ‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖ ≤
        64*exp 6*(‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖) := by
  have hcomparison (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 1 H) :=
    physical_ideal_size_comparison_order40 (m ξ) (v ξ) (r ξ) (w ξ) hs₀ hε hσ hσsmall
      (hm ξ τ hτ) (hv ξ τ hτ) (hmv ξ τ hτ) (hrw ξ τ hτ)
      hΘ hK he hεe hsmall hτ.1 (hτ.2.trans hHΘ) hZ hfluxZ hZ0 hZ₁0
      (hP ξ τ hτ) (hQ ξ τ hτ) (hN ξ τ hτ) (hVrel ξ τ hτ) (hratio ξ τ hτ)
  have htarget := (hcomparison center T ⟨hT, hTH⟩).1
  intro ξ τ hτ
  have hcurrent := (hcomparison ξ τ hτ).2
  have hideal := equation30_horizon_size_comparison hσ hσsmall hZ hfluxZ hZ0 hZ₁0 hT hshort
    (by linarith only [hτ.1] : 0 ≤ τ) hτ.2
  have hh := mul_le_mul_of_nonneg_left hideal hs₀.le
  have ht := mul_le_mul_of_nonneg_left htarget (exp_pos (6:ℝ)).le
  linarith only [ht, hcurrent, hh]

end EulerPacketMovingFrame
