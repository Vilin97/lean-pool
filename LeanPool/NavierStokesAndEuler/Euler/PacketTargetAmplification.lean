/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalNormBounds

@[expose] public section

/-!
Actual target amplification and the resulting exponential gain for
bounded history sizes and the packet amplitude chosen at target.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketGrowth InnerProductSpace

theorem equation30_target_exp_le {σ T Θ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hTtarget : 1/σ ≤ T) (hTΘ : T ≤ Θ)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    exp (1/(4*σ)) ≤ Θ*Z T := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hx : 1 ≤ σ*T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ*T := by positivity
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ^2 ≤ 1/16)
    (fun t ht => hZ t ht.1) (fun t ht => hfluxZ t ht.1) hZ0 hZ₁0
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := equation30_post_inversion_lower hσ hσsmall hZ hfluxZ hZ0 hZ₁0 (σ*T) hx
  rw [mul_div_cancel_left₀ T (ne_of_gt hσ)] at hpost
  have hraw : exp (1/(4*σ)) ≤ (σ*T)*Z T := by
    have hh := (div_le_iff₀ hxpos).mp hpost.1
    nlinarith only [hgrowth, hh]
  have hcoeff : σ*T ≤ Θ := by
    have hh := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith only [hσsmall]) hTpos.le
    nlinarith only [hh, hTΘ]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hpost.2.le)

theorem physical_target_exponential_lower (m v r w : ℝ → Space)
    {s₀ t₀ a ε σ T Θ : ℝ} {Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : ε ≠ 0) (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hTtarget : 1/σ ≤ T) (hTΘ : T ≤ Θ)
    (hm : m (physicalTime t₀ a ε T) ≠ 0) (hv : v (physicalTime t₀ a ε T) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε T),v (physicalTime t₀ a ε T)⟫_ℝ = 0)
    (hN : 1/2 ≤ scaledRay m v r s₀ t₀ a ε T 2)
    (hV : |scaledVelocity m v w t₀ a ε T 1/Z T-1| ≤ 1/2)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    0 < ‖r (physicalTime t₀ a ε T)‖*‖w (physicalTime t₀ a ε T)‖ ∧
      s₀*exp (1/(4*σ)) ≤ 4*Θ*(‖r (physicalTime t₀ a ε T)‖*‖w (physicalTime t₀ a ε T)‖) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hΘpos : 0 < Θ := hTpos.trans_le hTΘ
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 T hTpos.le
  have hVlower : Z T/2 ≤ scaledVelocity m v w t₀ a ε T 1 := by
    have hh := (abs_le.mp hV).1
    have hr : 1/2 ≤ scaledVelocity m v w t₀ a ε T 1/Z T := by linarith only [hh]
    have hb := (le_div_iff₀ hZpos).mp hr
    nlinarith only [hb]
  have hVpos : 0 < scaledVelocity m v w t₀ a ε T 1 := by linarith only [hVlower, hZpos]
  have hsize := physical_size_ge_second m v r w hs₀ hε hm hv hmv hN hVpos.le
  have hsizepos : 0 < ‖r (physicalTime t₀ a ε T)‖*‖w (physicalTime t₀ a ε T)‖ :=
    lt_of_lt_of_le (by positivity) hsize
  have hexp := equation30_target_exp_le hσ hσsmall hTtarget hTΘ hZ hfluxZ hZ0 hZ₁0
  have h1 := mul_le_mul_of_nonneg_left hexp hs₀.le
  have h2 := mul_le_mul_of_nonneg_left hVlower (show 0 ≤ 2*s₀*Θ by positivity)
  have h3 := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 4*Θ by positivity)
  exact ⟨hsizepos, by nlinarith only [h1, h2, h3]⟩

/-- A bounded physical history size, or the numerator used to choose a
packet amplitude, gains the actual target's exponential factor. -/
theorem ratio_bound_from_target_growth {s₀ Θ x target value bound : ℝ}
    (hs₀ : 0 < s₀) (hΘ : 0 < Θ) (hbound : 0 ≤ bound) (hvalue : value ≤ bound)
    (hgrowth : s₀*exp x ≤ 4*Θ*target) :
    0 < target ∧ value/target ≤ (4*Θ*bound/s₀)*exp (-x) := by
  have hleft : 0 < s₀*exp x := mul_pos hs₀ (exp_pos x)
  have htarget : 0 < target := by
    by_contra hn
    have hnon : target ≤ 0 := le_of_not_gt hn
    have hmul : 4*Θ*target ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hnon
    linarith only [hleft, hgrowth, hmul]
  have hexp : exp x*exp (-x) = 1 := by rw [← exp_add]; simp
  have hscaled : s₀ ≤ 4*Θ*target*exp (-x) := by
    have hh := mul_le_mul_of_nonneg_right hgrowth (exp_pos (-x)).le
    simpa only [mul_assoc, hexp, mul_one] using hh
  have hb : bound ≤ ((4*Θ*bound/s₀)*exp (-x))*target := by
    calc
      bound = (bound/s₀)*s₀ := by field_simp
      _ ≤ (bound/s₀)*(4*Θ*target*exp (-x)) :=
        mul_le_mul_of_nonneg_left hscaled (div_nonneg hbound hs₀.le)
      _ = _ := by ring
  exact ⟨htarget, (div_le_iff₀ htarget).mpr (hvalue.trans hb)⟩

end EulerPacketMovingFrame
