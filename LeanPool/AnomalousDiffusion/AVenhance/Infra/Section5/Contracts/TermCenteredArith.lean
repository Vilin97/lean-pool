/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Abstract-real arithmetic of the centered ergodic estimates

Proved real-variable estimates for the centered ergodic argument -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

theorem sd_arith_final {x y κ ν ψ B A K Cd c₀ c₁ c₂ cfl M ρ e d D₀ D₁ D₂ E : ℝ}
    (hK : 1 ≤ K) (hκ : 0 < κ) (hν : 0 < ν) (hνK : ν ≤ K) (hψ : 0 ≤ ψ)
    (hψκ : ψ ^ 2 ≤ K * κ * ν)
    (hx : 0 < x) (hy : 0 < y) (hρ : 0 < ρ) (hyx : y ≤ K * x) (hyρ : y ≤ K * ρ)
    (he : 0 ≤ e) (hed : e ≤ d) (hB : 0 ≤ B) (hA : 0 ≤ A) (hCd : 0 ≤ Cd)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hcfl : 0 ≤ cfl) (hM : 0 ≤ M)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hD₀b : Real.sqrt ν * D₀ ≤ A * B)
    (hD₁b : Real.sqrt ν * D₁ ≤ A * (A / ρ) * B)
    (hD₂b : Real.sqrt ν * D₂ ≤ A * (A / ρ) * B)
    (hE : 0 ≤ E) (hEb : (ρ ^ 2)⁻¹ * E ≤ M * d) :
    2 * ((144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ) * D₀ +
      144 * Cd * y * (c₁ * ψ * e) * D₁ + 144 * Cd * y * (c₁ * ψ * e) * D₂ +
      144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E)) ≤
    (2 * (144 * Cd * c₀ * K + cfl) * Real.sqrt K * A +
      576 * Cd * c₁ * A ^ 2 * K * Real.sqrt K + 288 * Cd * c₂ * M * K) *
        d * Real.sqrt κ * B := by
  have _hM0 : 0 ≤ M := hM
  have hK0 : 0 ≤ K := by linarith
  have hsK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hK
  have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hsκ0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have hsν0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have hsνK : Real.sqrt ν ≤ Real.sqrt K := Real.sqrt_le_sqrt hνK
  have hS0 : 0 ≤ Real.sqrt K * Real.sqrt κ := mul_nonneg hsK0 hsκ0
  -- ψ ≤ √K √κ √ν
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
  have hyx' : y / x ≤ K := by rw [div_le_iff₀ hx]; exact hyx
  have hyρ' : y / ρ ≤ K := by rw [div_le_iff₀ hρ]; exact hyρ
  have hP : 0 ≤ 144 * Cd * c₀ * K + cfl := by positivity
  have hψe : 0 ≤ ψ * e := mul_nonneg hψ he
  -- term 0
  have h0a : y * (c₀ * ψ * e / x) ≤ K * (c₀ * ψ * e) := by
    have : y * (c₀ * ψ * e / x) = (y / x) * (c₀ * ψ * e) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hyx' (by positivity)
  have h0b : 144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ ≤
      (144 * Cd * c₀ * K + cfl) * (ψ * e) := by
    have h1 : 144 * Cd * y * (c₀ * ψ * e / x) = 144 * Cd * (y * (c₀ * ψ * e / x)) := by ring
    have h2 : 144 * Cd * (y * (c₀ * ψ * e / x)) ≤ 144 * Cd * (K * (c₀ * ψ * e)) :=
      mul_le_mul_of_nonneg_left h0a (by positivity)
    linarith [h1, h2]
  have h0c : (144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ) * D₀ ≤
      (144 * Cd * c₀ * K + cfl) * (ψ * e) * D₀ := mul_le_mul_of_nonneg_right h0b hD₀
  have h0d : (144 * Cd * c₀ * K + cfl) * (ψ * e) * D₀ ≤
      (144 * Cd * c₀ * K + cfl) * d * (Real.sqrt K * Real.sqrt κ * (A * B)) := by
    have e1 : (144 * Cd * c₀ * K + cfl) * (ψ * e) * D₀ =
        ((144 * Cd * c₀ * K + cfl) * e) * (ψ * D₀) := by ring
    rw [e1]
    have e2 : ((144 * Cd * c₀ * K + cfl) * e) * (ψ * D₀) ≤
        ((144 * Cd * c₀ * K + cfl) * e) * (Real.sqrt K * Real.sqrt κ * (A * B)) :=
      mul_le_mul_of_nonneg_left k0 (mul_nonneg hP he)
    have e3 : ((144 * Cd * c₀ * K + cfl) * e) * (Real.sqrt K * Real.sqrt κ * (A * B)) ≤
        ((144 * Cd * c₀ * K + cfl) * d) * (Real.sqrt K * Real.sqrt κ * (A * B)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hed hP)
        (mul_nonneg hS0 (mul_nonneg hA hB))
    exact e2.trans e3
  -- terms 1, 2
  have h12a : y * (A / ρ) ≤ K * A := by
    have : y * (A / ρ) = (y / ρ) * A := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hyρ' hA
  have h12b : 144 * Cd * y * (c₁ * ψ * e) * D₁ + 144 * Cd * y * (c₁ * ψ * e) * D₂ ≤
      144 * Cd * c₁ * e * y * (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B) +
        Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B)) := by
    have e1 : 144 * Cd * y * (c₁ * ψ * e) * D₁ + 144 * Cd * y * (c₁ * ψ * e) * D₂ =
        (144 * Cd * c₁ * e * y) * (ψ * D₁ + ψ * D₂) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left (add_le_add k1 k2)
      (by positivity)
  have h12c : 144 * Cd * c₁ * e * y * (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B) +
        Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B)) ≤
      288 * Cd * c₁ * A ^ 2 * K * Real.sqrt K * d * Real.sqrt κ * B := by
    have e1 : 144 * Cd * c₁ * e * y * (Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B) +
        Real.sqrt K * Real.sqrt κ * (A * (A / ρ) * B)) =
        (288 * Cd * c₁ * e * Real.sqrt K * Real.sqrt κ * A * B) * (y * (A / ρ)) := by ring
    rw [e1]
    have hpos : 0 ≤ 288 * Cd * c₁ * e * Real.sqrt K * Real.sqrt κ * A * B := by positivity
    have e2 := mul_le_mul_of_nonneg_left h12a hpos
    have e3 : (288 * Cd * c₁ * e * Real.sqrt K * Real.sqrt κ * A * B) * (K * A) ≤
        (288 * Cd * c₁ * d * Real.sqrt K * Real.sqrt κ * A * B) * (K * A) := by
      have hX : 0 ≤ 288 * Cd * c₁ * Real.sqrt K * Real.sqrt κ * A * B := by positivity
      have h := mul_le_mul_of_nonneg_left hed hX
      have r1 : 288 * Cd * c₁ * e * Real.sqrt K * Real.sqrt κ * A * B =
          (288 * Cd * c₁ * Real.sqrt K * Real.sqrt κ * A * B) * e := by ring
      have r2 : 288 * Cd * c₁ * d * Real.sqrt K * Real.sqrt κ * A * B =
          (288 * Cd * c₁ * Real.sqrt K * Real.sqrt κ * A * B) * d := by ring
      rw [r1, r2]
      exact mul_le_mul_of_nonneg_right h (by positivity)
    have e4 : (288 * Cd * c₁ * d * Real.sqrt K * Real.sqrt κ * A * B) * (K * A) =
        288 * Cd * c₁ * A ^ 2 * K * Real.sqrt K * d * Real.sqrt κ * B := by ring
    linarith
  -- term 3
  have h3 : 144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E) ≤
      144 * Cd * c₂ * B * (K * Real.sqrt κ) * (M * d) := by
    have hpos : 0 ≤ 144 * Cd * c₂ * B := by positivity
    have e1 : 144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E) =
        (144 * Cd * c₂ * B) * (ψ * ((ρ ^ 2)⁻¹ * E)) := by ring
    have hE' : 0 ≤ (ρ ^ 2)⁻¹ * E := by positivity
    have e2 : ψ * ((ρ ^ 2)⁻¹ * E) ≤ (K * Real.sqrt κ) * (M * d) :=
      mul_le_mul hψK hEb hE' (by positivity)
    rw [e1, show 144 * Cd * c₂ * B * (K * Real.sqrt κ) * (M * d) =
      (144 * Cd * c₂ * B) * ((K * Real.sqrt κ) * (M * d)) by ring]
    exact mul_le_mul_of_nonneg_left e2 hpos
  -- assemble
  have hfinal0 : 2 * (144 * Cd * c₀ * K + cfl) * d * (Real.sqrt K * Real.sqrt κ * (A * B)) =
      2 * (144 * Cd * c₀ * K + cfl) * Real.sqrt K * A * d * Real.sqrt κ * B := by ring
  have hfinal3 : 2 * (144 * Cd * c₂ * B * (K * Real.sqrt κ) * (M * d)) =
      288 * Cd * c₂ * M * K * d * Real.sqrt κ * B := by ring
  have hfinal1 : 2 * (288 * Cd * c₁ * A ^ 2 * K * Real.sqrt K * d * Real.sqrt κ * B) =
      576 * Cd * c₁ * A ^ 2 * K * Real.sqrt K * d * Real.sqrt κ * B := by ring
  have hrhs : (2 * (144 * Cd * c₀ * K + cfl) * Real.sqrt K * A +
      576 * Cd * c₁ * A ^ 2 * K * Real.sqrt K + 288 * Cd * c₂ * M * K) *
        d * Real.sqrt κ * B =
      2 * (144 * Cd * c₀ * K + cfl) * Real.sqrt K * A * d * Real.sqrt κ * B +
      576 * Cd * c₁ * A ^ 2 * K * Real.sqrt K * d * Real.sqrt κ * B +
      288 * Cd * c₂ * M * K * d * Real.sqrt κ * B := by ring
  rw [hrhs]
  have hsplit : 2 * ((144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ) * D₀ +
      144 * Cd * y * (c₁ * ψ * e) * D₁ + 144 * Cd * y * (c₁ * ψ * e) * D₂ +
      144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E)) =
      2 * ((144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ) * D₀) +
      2 * (144 * Cd * y * (c₁ * ψ * e) * D₁ + 144 * Cd * y * (c₁ * ψ * e) * D₂) +
      2 * (144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E)) := by ring
  rw [hsplit]
  linarith

end AVenhance.Infra.Section5.Contracts
end
