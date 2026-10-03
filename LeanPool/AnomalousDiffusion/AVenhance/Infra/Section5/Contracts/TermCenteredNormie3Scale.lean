/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffScalar

/-! # Abstract-real scale arithmetic for the centered `normie3` bound

Pure real-variable facts (no `nlinarith` near transcendentals):

* `n3_scale1`: `y (1 + ψ/κ) ≤ M₁ ρ ε^δ` from `ψ/κ ≤ K y^{-γ}`, `y ≤ K x^q`,
  `1 + γ/2 + δ ≤ q (1 - γ)` (the exponent identity `q(1-γ) - 1 - γ/2 = 4δ`), `ρ = x^{1+γ/2}`;
* `n3_exp_scale`: `(1 + ψ/κ) ρ⁻² e^{-ρN/(4096 c₂)} ≲ x^δ`;
* `n3_arith_final`: assembly of the four terms into `C ε^δ √κ B`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance

/-- The exponent inequality `1 + γ/2 + δ ≤ q (1 - γ)` (indeed `1 + γ/2 + 4δ = q(1-γ)`). -/
theorem n3_exponent {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    1 + gamma β / 2 + delta β ≤ q β * (1 - gamma β) := by
  have hid := Infra.Numeric.four_delta_identity hβ
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  linarith

theorem n3_scale1 {x y ψκ K q γ δ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hyK : y ≤ K * x ^ q) (hK : 1 ≤ K) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hψκ : ψκ ≤ K * y ^ (-γ)) (hexp : 1 + γ / 2 + δ ≤ q * (1 - γ)) :
    y * (1 + ψκ) ≤ ((1 + K) * K) * (x ^ (1 + γ / 2) * x ^ δ) := by
  have hK0 : 0 < K := by linarith
  have hyy : y * y ^ (-γ) = y ^ (1 - γ) := by
    rw [show 1 - γ = 1 + -γ by ring, Real.rpow_add hy, Real.rpow_one]
  have h1 : y ≤ y ^ (1 - γ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show 1 - γ ≤ 1 by linarith)
    simpa using this
  have h2 : y ^ (1 - γ) ≤ K * x ^ (q * (1 - γ)) := by
    have hexp0 : 0 ≤ 1 - γ := by linarith
    calc y ^ (1 - γ) ≤ (K * x ^ q) ^ (1 - γ) := Real.rpow_le_rpow hy.le hyK hexp0
      _ = K ^ (1 - γ) * x ^ (q * (1 - γ)) := by
          rw [Real.mul_rpow hK0.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
      _ ≤ K ^ (1 : ℝ) * x ^ (q * (1 - γ)) := by
          gcongr
          · linarith
      _ = K * x ^ (q * (1 - γ)) := by rw [Real.rpow_one]
  have h3 : x ^ (q * (1 - γ)) ≤ x ^ (1 + γ / 2) * x ^ δ := by
    rw [← Real.rpow_add hx]
    exact Real.rpow_le_rpow_of_exponent_ge hx hx1 hexp
  have h4 : y * (1 + ψκ) ≤ y + K * y ^ (1 - γ) := by
    calc y * (1 + ψκ) = y + y * ψκ := by ring
      _ ≤ y + y * (K * y ^ (-γ)) := by gcongr
      _ = y + K * (y * y ^ (-γ)) := by ring
      _ = y + K * y ^ (1 - γ) := by rw [hyy]
  calc y * (1 + ψκ) ≤ y + K * y ^ (1 - γ) := h4
    _ ≤ (1 + K) * y ^ (1 - γ) := by nlinarith [h1]
    _ ≤ (1 + K) * (K * x ^ (q * (1 - γ))) := by gcongr
    _ ≤ (1 + K) * (K * (x ^ (1 + γ / 2) * x ^ δ)) := by gcongr
    _ = _ := by ring

theorem n3_exp_scale {γ δ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ) {K c₂ : ℝ}
    (hK : 1 ≤ K) (hc₂ : 0 < c₂) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y ψκ : ℝ, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 → ψκ ≤ K * y ^ (-γ) →
      (1 / (4096 * c₂ * K)) * x ^ (-(2 * δ)) ≤ (x ^ (1 + γ / 2) / c₂ * y⁻¹) / 4096 →
      (1 + ψκ) * (((x ^ (1 + γ / 2)) ^ 2)⁻¹ *
        Real.exp (-(x ^ (1 + γ / 2) / c₂) * y⁻¹ / 4096)) ≤ M * x ^ δ := by
  have hK0 : 0 < K := by linarith
  obtain ⟨M0, hM0, hM⟩ := sb_exp_decay_le (q := 3 * (1 + γ / 2)) (δ := δ)
    (c := 1 / (8192 * c₂ * K)) (by positivity) hδ (by positivity)
  refine ⟨(1 + K) * (8192 * c₂) * M0, by positivity, ?_⟩
  intro x y ψκ hx hx1 hy hy1 hψκ hZ
  set ρ : ℝ := x ^ (1 + γ / 2) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hx _
  set u : ℝ := (ρ / c₂ * y⁻¹) / 4096 with hu
  have hu0 : 0 < u := by positivity
  have hE : Real.exp (-(ρ / c₂) * y⁻¹ / 4096) = Real.exp (-u) := by
    congr 1
    rw [hu]
    ring
  rw [hE]
  have hyinv : y⁻¹ = 4096 * c₂ * u / ρ := by
    rw [hu]
    field_simp
  have hy1' : 1 ≤ y⁻¹ := by
    rw [one_le_inv₀ hy]
    exact hy1
  have hpow : y ^ (-γ) ≤ y⁻¹ := by
    have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show -1 ≤ -γ by linarith)
    simpa [Real.rpow_neg_one] using this
  have h1 : 1 + ψκ ≤ (1 + K) * y⁻¹ := by
    calc 1 + ψκ ≤ 1 + K * y ^ (-γ) := by linarith
      _ ≤ 1 * y⁻¹ + K * y⁻¹ := by
          have := mul_le_mul_of_nonneg_left hpow hK0.le
          linarith
      _ = (1 + K) * y⁻¹ := by ring
  have hexp0 : 0 < Real.exp (-u) := Real.exp_pos _
  have h2 : (1 + ψκ) * ((ρ ^ 2)⁻¹ * Real.exp (-u)) ≤
      ((1 + K) * y⁻¹) * ((ρ ^ 2)⁻¹ * Real.exp (-u)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have hu2 : u ≤ 2 * Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have h3 : u * Real.exp (-u) ≤ 2 * Real.exp (-(u / 2)) := by
    calc u * Real.exp (-u) ≤ (2 * Real.exp (u / 2)) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right hu2 hexp0.le
      _ = 2 * (Real.exp (u / 2) * Real.exp (-u)) := by ring
      _ = 2 * Real.exp (-(u / 2)) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hρ3 : (ρ ^ 3)⁻¹ = (x ^ (3 * (1 + γ / 2)))⁻¹ := by
    have : ρ ^ 3 = x ^ (3 * (1 + γ / 2)) := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      congr 1
      push_cast
      ring
    rw [this]
  have h4 : Real.exp (-(u / 2)) * (x ^ (3 * (1 + γ / 2)))⁻¹ ≤ M0 * x ^ δ := by
    refine hM x (u / 2) hx ?_
    have : 1 / (8192 * c₂ * K) * x ^ (-(2 * δ)) =
        (1 / (4096 * c₂ * K)) * x ^ (-(2 * δ)) / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  calc (1 + ψκ) * ((ρ ^ 2)⁻¹ * Real.exp (-u))
      ≤ ((1 + K) * y⁻¹) * ((ρ ^ 2)⁻¹ * Real.exp (-u)) := h2
    _ = ((1 + K) * (4096 * c₂)) * ((u * Real.exp (-u)) * (ρ ^ 3)⁻¹) := by
        rw [hyinv]
        field_simp
    _ ≤ ((1 + K) * (4096 * c₂)) * ((2 * Real.exp (-(u / 2))) * (ρ ^ 3)⁻¹) := by
        gcongr
    _ = ((1 + K) * (8192 * c₂)) * (Real.exp (-(u / 2)) * (x ^ (3 * (1 + γ / 2)))⁻¹) := by
        rw [hρ3]
        ring
    _ ≤ ((1 + K) * (8192 * c₂)) * (M0 * x ^ δ) := by gcongr
    _ = _ := by ring

/-- Assembly of the four terms of the time-integrated centered bound of `normie3`.  With
`G = 4ψ(1 + ψ/κ)`, the coefficients `144 C_d y G (c₀ x⁻¹)`, `144 C_d y G c₁` (twice) and the
exponential remainder `144 C_d (c₂ B ρ⁻²) G E` give `C ε^δ √κ B`. -/
theorem n3_arith_final {x y κ ν ψ B A K Cd c₀ c₁ c₂ M₁ M₂ ρ d E D₀ D₁ D₂ R : ℝ}
    (hK : 1 ≤ K) (hκ : 0 < κ) (hν : 0 < ν) (hνK : ν ≤ K) (hψ : 0 ≤ ψ)
    (hψκ : ψ ^ 2 ≤ K * κ * ν) (hx : 0 < x) (hρ : 0 < ρ) (hρx : ρ ≤ x)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (_hA : 0 ≤ A) (hCd : 0 ≤ Cd)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hM₁ : 0 ≤ M₁) (_hM₂ : 0 ≤ M₂)
    (hy : 0 ≤ y) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hD₀b : Real.sqrt ν * D₀ ≤ A * B)
    (hD₁b : Real.sqrt ν * D₁ ≤ A * (A / ρ) * B)
    (hD₂b : Real.sqrt ν * D₂ ≤ A * (A / ρ) * B)
    (hΛ₁ : y * (1 + R) ≤ M₁ * (ρ * d))
    (hΛ₂ : (1 + R) * ((ρ ^ 2)⁻¹ * E) ≤ M₂ * d) :
    2 * ((144 * Cd * y * (4 * ψ * (1 + R)) * (c₀ * x⁻¹)) * D₀ +
      (144 * Cd * y * (4 * ψ * (1 + R)) * c₁) * D₁ +
      (144 * Cd * y * (4 * ψ * (1 + R)) * c₁) * D₂ +
      144 * Cd * (c₂ * B * (ρ ^ 2)⁻¹) * (4 * ψ * (1 + R)) * E) ≤
    (1152 * Cd * (c₀ * M₁ * Real.sqrt K * A + 2 * c₁ * M₁ * Real.sqrt K * A ^ 2 +
      c₂ * M₂ * K)) * d * Real.sqrt κ * B := by
  have hK0 : 0 ≤ K := by linarith
  have hsK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
  have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hsκ0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have hsν0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have hsνK : Real.sqrt ν ≤ Real.sqrt K := Real.sqrt_le_sqrt hνK
  have hS0 : 0 ≤ Real.sqrt K * Real.sqrt κ := mul_nonneg hsK0 hsκ0
  have hψs : ψ ≤ Real.sqrt K * Real.sqrt κ * Real.sqrt ν := by
    have hsq : (Real.sqrt K * Real.sqrt κ * Real.sqrt ν) ^ 2 = K * κ * ν := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hκ.le, Real.sq_sqrt hν.le]
    exact abs_le_of_sq_le_sq' (by rw [hsq]; exact hψκ) (by positivity) |>.2
  have hψK : ψ ≤ K * Real.sqrt κ := by
    calc ψ ≤ Real.sqrt K * Real.sqrt κ * Real.sqrt ν := hψs
      _ ≤ Real.sqrt K * Real.sqrt κ * Real.sqrt K := by gcongr
      _ = (Real.sqrt K * Real.sqrt K) * Real.sqrt κ := by ring
      _ = K * Real.sqrt κ := by rw [hsK]
  have key : ∀ D W : ℝ, 0 ≤ D → Real.sqrt ν * D ≤ W →
      ψ * D ≤ Real.sqrt K * Real.sqrt κ * W := by
    intro D W hD hW
    calc ψ * D ≤ (Real.sqrt K * Real.sqrt κ * Real.sqrt ν) * D :=
          mul_le_mul_of_nonneg_right hψs hD
      _ = Real.sqrt K * Real.sqrt κ * (Real.sqrt ν * D) := by ring
      _ ≤ Real.sqrt K * Real.sqrt κ * W := mul_le_mul_of_nonneg_left hW hS0
  have k0 := key D₀ _ hD₀ hD₀b
  have k1 := key D₁ _ hD₁ hD₁b
  have k2 := key D₂ _ hD₂ hD₂b
  have hρx' : ρ * x⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hx]
    exact hρx
  have hyx : y * (1 + R) * x⁻¹ ≤ M₁ * d := by
    calc y * (1 + R) * x⁻¹ ≤ (M₁ * (ρ * d)) * x⁻¹ :=
          mul_le_mul_of_nonneg_right hΛ₁ (inv_nonneg.2 hx.le)
      _ = (M₁ * d) * (ρ * x⁻¹) := by ring
      _ ≤ (M₁ * d) * 1 := mul_le_mul_of_nonneg_left hρx' (by positivity)
      _ = M₁ * d := mul_one _
  have hy0 : 0 ≤ y * (1 + R) := by positivity
  -- term 0
  have t0 : (144 * Cd * y * (4 * ψ * (1 + R)) * (c₀ * x⁻¹)) * D₀ ≤
      576 * Cd * c₀ * M₁ * Real.sqrt K * A * d * Real.sqrt κ * B := by
    have e1 : (144 * Cd * y * (4 * ψ * (1 + R)) * (c₀ * x⁻¹)) * D₀ =
        (576 * Cd * c₀) * ((y * (1 + R) * x⁻¹) * (ψ * D₀)) := by ring
    rw [e1]
    have e2 : (y * (1 + R) * x⁻¹) * (ψ * D₀) ≤
        (M₁ * d) * (Real.sqrt K * Real.sqrt κ * (A * B)) :=
      mul_le_mul hyx k0 (by positivity) (by positivity)
    calc (576 * Cd * c₀) * ((y * (1 + R) * x⁻¹) * (ψ * D₀))
        ≤ (576 * Cd * c₀) * ((M₁ * d) * (Real.sqrt K * Real.sqrt κ * (A * B))) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  -- terms 1, 2
  have t12 : ∀ D W : ℝ, 0 ≤ D → Real.sqrt ν * D ≤ A * (A / ρ) * B →
      (144 * Cd * y * (4 * ψ * (1 + R)) * c₁) * D ≤
      576 * Cd * c₁ * M₁ * Real.sqrt K * A ^ 2 * d * Real.sqrt κ * B := by
    intro D _ hD hDb
    have kD := key D _ hD hDb
    have e1 : (144 * Cd * y * (4 * ψ * (1 + R)) * c₁) * D =
        (576 * Cd * c₁) * ((y * (1 + R)) * (ψ * D)) := by ring
    rw [e1]
    have e2 : (y * (1 + R)) * (ψ * D) ≤
        (M₁ * (ρ * d)) * (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B)) :=
      mul_le_mul hΛ₁ kD (by positivity) (by positivity)
    have e3 : (M₁ * (ρ * d)) * (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B)) =
        M₁ * Real.sqrt K * A ^ 2 * d * Real.sqrt κ * B := by
      field_simp
    calc (576 * Cd * c₁) * ((y * (1 + R)) * (ψ * D))
        ≤ (576 * Cd * c₁) * ((M₁ * (ρ * d)) *
            (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B))) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by rw [e3]; ring
  have t1 := t12 D₁ 0 hD₁ hD₁b
  have t2 := t12 D₂ 0 hD₂ hD₂b
  -- term 3
  have t3 : 144 * Cd * (c₂ * B * (ρ ^ 2)⁻¹) * (4 * ψ * (1 + R)) * E ≤
      576 * Cd * c₂ * M₂ * K * d * Real.sqrt κ * B := by
    have hE' : 0 ≤ (ρ ^ 2)⁻¹ * E := by positivity
    have e1 : 144 * Cd * (c₂ * B * (ρ ^ 2)⁻¹) * (4 * ψ * (1 + R)) * E =
        (576 * Cd * c₂ * B) * (ψ * ((1 + R) * ((ρ ^ 2)⁻¹ * E))) := by ring
    rw [e1]
    have e2 : ψ * ((1 + R) * ((ρ ^ 2)⁻¹ * E)) ≤ (K * Real.sqrt κ) * (M₂ * d) :=
      mul_le_mul hψK hΛ₂ (by positivity) (by positivity)
    calc (576 * Cd * c₂ * B) * (ψ * ((1 + R) * ((ρ ^ 2)⁻¹ * E)))
        ≤ (576 * Cd * c₂ * B) * ((K * Real.sqrt κ) * (M₂ * d)) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  have hrhs : (1152 * Cd * (c₀ * M₁ * Real.sqrt K * A + 2 * c₁ * M₁ * Real.sqrt K * A ^ 2 +
      c₂ * M₂ * K)) * d * Real.sqrt κ * B =
      2 * (576 * Cd * c₀ * M₁ * Real.sqrt K * A * d * Real.sqrt κ * B) +
      2 * (576 * Cd * c₁ * M₁ * Real.sqrt K * A ^ 2 * d * Real.sqrt κ * B) +
      2 * (576 * Cd * c₁ * M₁ * Real.sqrt K * A ^ 2 * d * Real.sqrt κ * B) +
      2 * (576 * Cd * c₂ * M₂ * K * d * Real.sqrt κ * B) := by ring
  rw [hrhs]
  linarith

end AVenhance.Infra.Section5.Contracts
end
