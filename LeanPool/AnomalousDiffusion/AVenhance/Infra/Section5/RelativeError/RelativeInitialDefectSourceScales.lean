/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpointScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds

/-! Scalar absorption of the positive half-cell source estimate. All amplitude
parameters are nonnegative; the zero-amplitude case is included. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section5.RelativeError

/-- Square-root time absorption at an abstract relative amplitude. -/
theorem relative_initial_source_time_absorb {b ν L C K E S : ℝ}
    (hb : 0 ≤ b) (hν : 0 ≤ ν) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hscale : b * ν * L ^ 2 ≤ K * E ^ 2) :
    2 * Real.sqrt b * (C * Real.sqrt ν * L * S) ≤
      (2 * C * Real.sqrt K) * E * S := by
  have hroot : Real.sqrt b * Real.sqrt ν * L ≤ Real.sqrt K * E := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ = b * ν * L ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hb, Real.sq_sqrt hν]
      _ ≤ K * E ^ 2 := hscale
      _ = _ := by rw [mul_pow, Real.sq_sqrt hK]
  calc
    _ = (2 * C * S) * (Real.sqrt b * Real.sqrt ν * L) := by ring
    _ ≤ (2 * C * S) * (Real.sqrt K * E) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by ring

/-- The temperature spatial rate cancels the previous-scale diffusivity
power exactly; no estimate of the temperature itself is involved. -/
theorem relative_initial_diffusivity_rate_cancel {e γ ν C a : ℝ}
    (he : 0 < e) (hν : ν ≤ C * (a * e ^ (2 + γ))) :
    ν * (e ^ (-(1 + γ / 2))) ^ 2 ≤ C * a := by
  have heq : e ^ (2 + γ) * (e ^ (-(1 + γ / 2))) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le, ← Real.rpow_add he]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 + γ) + (-(1 + γ / 2)) * (2 : ℝ) = 0 by ring, Real.rpow_zero]
  calc
    _ ≤ (C * (a * e ^ (2 + γ))) * (e ^ (-(1 + γ / 2))) ^ 2 :=
      mul_le_mul_of_nonneg_right hν (sq_nonneg _)
    _ = C * a * (e ^ (2 + γ) * (e ^ (-(1 + γ / 2))) ^ 2) := by ring
    _ = C * a := by rw [heq, mul_one]

/-- The first half-cell lies strictly inside the unit time interval. -/
theorem relative_initial_half_cell_lt_one {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) : AVenhance.tauPP β I.Λ m / 2 < 1 := by
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have hδ := AVenhance.Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hp : 0 ≤ 2 - β + 2 * AVenhance.delta β := by linarith only [I.beta_lt, hδ]
  have hr := Real.rpow_le_one he.le he1 hp
  have hτ := (AVenhance.Infra.Ingredients.tauPP_bounds
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2
  have hle : AVenhance.tauPP β I.Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) :=
    hτ.trans (by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hr
        (by positivity : 0 ≤ (2 : ℝ) ^ (-25 : ℤ))))
  have hsmall : (2 : ℝ) ^ (-25 : ℤ) < 2 := by norm_num
  exact (div_lt_one (by norm_num : (0 : ℝ) < 2)).mpr (hle.trans_lt hsmall)

end AVenhance.Infra.Section5.RelativeError
