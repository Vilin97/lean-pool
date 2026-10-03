/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! # Scale arithmetic for `e.tildethetam.to.Tm.A`

Abstract-real lemmas: the corrector sup-norm `a ε_m³ / (2π κ_m)` times
`ε_{m-1}^{-(1+γ/2)}` is at most `K² ε_{m-1}^δ` once `a ε_m²/κ_m ≤ K ε_m^{-γ}` and
`ε_m ≤ K ε_{m-1}^q` (the exponent identity `q(1-γ) - 1 - γ/2 = 4δ`, `e.tildethetam.to.Tm.A`). -/

@[expose] public section

open Real

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- `γ < 1` on the range. -/
theorem gamma_lt_one_of_range {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : gamma β < 1 := by
  rw [Infra.Numeric.gamma_eq_beta_fraction hβ]
  have h : 0 < 5 * β - 4 := by linarith
  rw [div_lt_one h]
  nlinarith

/-- The explicit corrector sup-norm constant, rewritten in terms of `a ε² / κ`. -/
theorem chi_const_eq {a e κ : ℝ} (ha : 0 < a) (he : 0 < e) (hκ : 0 < κ) :
    (4 * Real.pi ^ 2 * κ / e ^ 2)⁻¹ * |2 * Real.pi * a * e| = (a * e ^ 2 / κ) * e / (2 * Real.pi)
        := by
  have hpi := Real.pi_pos
  rw [abs_of_pos (by positivity)]
  field_simp
  norm_num

/-- The scale bound: `c ≤ (a e_m²/κ) e_m / 2π`, `a e_m²/κ ≤ K e_m^{-γ}`, `e_m ≤ K e^q`
give `c e^{-(1+γ/2)} ≤ K² e^δ`. -/
theorem ansatz_scale_bound {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) {K e em A : ℝ}
    (hK : 1 ≤ K) (he : 0 < e) (he1 : e ≤ 1) (hem : 0 < em) (hA0 : 0 ≤ A)
    (hA : A ≤ K * em ^ (-gamma β)) (hemK : em ≤ K * e ^ q β) :
    A * em / (2 * Real.pi) * e ^ (-(1 + gamma β / 2)) ≤ K ^ 2 * e ^ delta β := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hg1 := gamma_lt_one_of_range hβ hβ'
  have hg0 := Infra.Ingredients.gamma_pos hβ hβ'
  have hK0 : 0 < K := by linarith
  have hd := Infra.Ingredients.delta_pos hβ hβ'
  -- step 1: `A em / 2π ≤ K em^{1-γ}`
  have h1 : A * em / (2 * Real.pi) ≤ K * em ^ (1 - gamma β) := by
    have hrw : em ^ (1 - gamma β) = em ^ (-gamma β) * em := by
      rw [show 1 - gamma β = -gamma β + 1 by ring, Real.rpow_add hem, Real.rpow_one]
    rw [hrw]
    calc A * em / (2 * Real.pi) ≤ A * em := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg hA0 hem.le]
      _ ≤ K * em ^ (-gamma β) * em := mul_le_mul_of_nonneg_right hA hem.le
      _ = K * (em ^ (-gamma β) * em) := by ring
  -- step 2: `em^{1-γ} ≤ K * e^{q(1-γ)}`
  have h2 : em ^ (1 - gamma β) ≤ K * e ^ (q β * (1 - gamma β)) := by
    have hexp : 0 ≤ 1 - gamma β := by linarith
    calc em ^ (1 - gamma β) ≤ (K * e ^ q β) ^ (1 - gamma β) :=
          Real.rpow_le_rpow hem.le hemK hexp
      _ = K ^ (1 - gamma β) * e ^ (q β * (1 - gamma β)) := by
          rw [Real.mul_rpow hK0.le (Real.rpow_nonneg he.le _), ← Real.rpow_mul he.le]
      _ ≤ K ^ (1 : ℝ) * e ^ (q β * (1 - gamma β)) := by
          gcongr
          · linarith
      _ = K * e ^ (q β * (1 - gamma β)) := by rw [Real.rpow_one]
  -- step 3: exponent bookkeeping
  have h3 : e ^ (q β * (1 - gamma β)) * e ^ (-(1 + gamma β / 2)) ≤ e ^ delta β := by
    rw [← Real.rpow_add he]
    have hid := Infra.Numeric.four_delta_identity hβ
    have : q β * (1 - gamma β) + -(1 + gamma β / 2) = 4 * delta β := by linarith
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hep : 0 ≤ e ^ (-(1 + gamma β / 2)) := Real.rpow_nonneg he.le _
  calc A * em / (2 * Real.pi) * e ^ (-(1 + gamma β / 2))
      ≤ (K * (K * e ^ (q β * (1 - gamma β)))) * e ^ (-(1 + gamma β / 2)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
    _ = K ^ 2 * (e ^ (q β * (1 - gamma β)) * e ^ (-(1 + gamma β / 2))) := by ring
    _ ≤ K ^ 2 * e ^ delta β := by gcongr

end AVenhance.Infra.Section5.Integration
