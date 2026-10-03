/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExpratScaling
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffScalar

/-! # Abstract-real scale arithmetic for the `twistie1` source contract

Pure real lemmas (no objects) for `e.monster.est.5` (`enhance.tex` 7371–7460):

* `se_main_scale`: the main term `ε_m^{2-γ} √κ_{m-1} ε_{m-1}^{-(2+γ)}` is `≲ ε_{m-1}^δ √κ_m`,
  from the diffusivity upper bound `κ_{m-1} ≲ ε_{m-1}^{β+γ}`, the lower bound `ε_m^{β+γ} ≲ κ_m`
      and the
  supergeometric comparison `ε_m ≃ ε_{m-1}^q`; the exponent is `8δ` (`se_exponent_ge`). -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance

/-- The exponent of the main term is `8 δ ≥ δ`. -/
theorem se_exponent_ge {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    delta β ≤ (1 - q β) * (β + gamma β) / 2 + q β * (2 - gamma β) - (2 + gamma β) := by
  have h8 := Infra.Section3.exprat_source_exponent_eq_eight_delta hβ
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd := Infra.Ingredients.delta_pos hβ hβ'
  have hγq : gamma β * (q β + 1) = (q β - 1) * β := by
    unfold gamma
    have : q β + 1 ≠ 0 := by linarith
    field_simp
  have hE : (1 - q β) * (β + gamma β) / 2 + q β * (2 - gamma β) - (2 + gamma β) =
      (2 - β) * (q β - 1) - q β * gamma β := by
    linear_combination (-1 / 2 : ℝ) * hγq
  rw [hE, h8]
  linarith

/-- `√κ_{m-1} ≤ C x^s ε_m^{-s} √κ_m`, then the main scale estimate. -/
theorem se_main_scale {x εm κm κp K Ca β γ q δ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hεm : 0 < εm)
    (hκm : 0 < κm) (hK : 1 ≤ K) (hCa : 0 ≤ Ca) (hγ2 : γ ≤ 2)
    (hβγ : 0 ≤ β + γ) (hlow : x ^ q ≤ 2 * εm) (hup : εm ≤ K * x ^ q)
    (hκpA : κp ≤ Ca * x ^ (β + γ)) (hκmL : εm ^ (β + γ) ≤ K * κm)
    (hexp : δ ≤ (1 - q) * (β + γ) / 2 + q * (2 - γ) - (2 + γ)) :
    εm ^ (2 - γ) * Real.sqrt κp * x ^ (-(2 + γ)) ≤
      (K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ ((β + γ) / 2))) * x ^ δ * Real.sqrt κm := by
  set s : ℝ := (β + γ) / 2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hK0 : 0 < K := by linarith
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx0 q
  -- `√κp ≤ √Ca x^s`
  have h1 : Real.sqrt κp ≤ Real.sqrt Ca * x ^ s := by
    calc Real.sqrt κp ≤ Real.sqrt (Ca * x ^ (β + γ)) := Real.sqrt_le_sqrt hκpA
      _ = Real.sqrt Ca * Real.sqrt (x ^ (β + γ)) := Real.sqrt_mul hCa _
      _ = Real.sqrt Ca * x ^ s := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
          congr 1; rw [hs]; ring
  -- `εm^s ≤ √K √κm`
  have h2 : εm ^ s ≤ Real.sqrt K * Real.sqrt κm := by
    calc εm ^ s = Real.sqrt (εm ^ (β + γ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hεm.le]
          congr 1; rw [hs]; ring
      _ ≤ Real.sqrt (K * κm) := Real.sqrt_le_sqrt hκmL
      _ = _ := Real.sqrt_mul hK0.le _
  -- `εm^{-s} ≤ 2^s x^{-q s}`
  have h3 : εm ^ (-s) ≤ 2 ^ s * x ^ (-(q * s)) := by
    have hxe : x ^ q / 2 ≤ εm := by linarith
    have hpos : 0 < x ^ q / 2 := by positivity
    calc εm ^ (-s) ≤ (x ^ q / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hpos hxe (by linarith)
      _ = 2 ^ s * x ^ (-(q * s)) := by
          have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos (by norm_num) s
          have hxs : (0 : ℝ) < x ^ (q * s) := Real.rpow_pos_of_pos hx0 _
          rw [Real.rpow_neg hpos.le, Real.div_rpow hxq.le (by norm_num), ← Real.rpow_mul hx0.le,
            Real.rpow_neg hx0.le]
          field_simp
  have h4 : εm ^ (2 - γ) ≤ K ^ (2 - γ) * x ^ (q * (2 - γ)) := by
    calc εm ^ (2 - γ) ≤ (K * x ^ q) ^ (2 - γ) := Real.rpow_le_rpow hεm.le hup (by linarith)
      _ = _ := by rw [Real.mul_rpow hK0.le hxq.le, ← Real.rpow_mul hx0.le]
  have hεs : εm ^ (-s) * εm ^ s = 1 := by
    rw [← Real.rpow_add hεm, neg_add_cancel, Real.rpow_zero]
  have hsqκp : Real.sqrt κp ≤
      Real.sqrt Ca * Real.sqrt K * x ^ s * (2 ^ s * x ^ (-(q * s))) * Real.sqrt κm := by
    have hsCa := Real.sqrt_nonneg Ca
    have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx0.le _
    have h2s : (0 : ℝ) ≤ 2 ^ s := Real.rpow_nonneg (by norm_num) s
    have hε0 : 0 ≤ εm ^ (-s) := Real.rpow_nonneg hεm.le _
    calc Real.sqrt κp ≤ Real.sqrt Ca * x ^ s := h1
      _ = Real.sqrt Ca * x ^ s * (εm ^ (-s) * εm ^ s) := by rw [hεs]; ring
      _ ≤ Real.sqrt Ca * x ^ s * ((2 ^ s * x ^ (-(q * s))) * (Real.sqrt K * Real.sqrt κm)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul h3 h2 (Real.rpow_nonneg hεm.le _) (by positivity)
      _ = _ := by ring
  have hE : x ^ (q * (2 - γ) + (s - q * s - (2 + γ))) ≤ x ^ δ := by
    apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1
    rw [hs]
    nlinarith [hexp]
  have hxpow : x ^ (q * (2 - γ)) * (x ^ s * x ^ (-(q * s))) * x ^ (-(2 + γ)) =
      x ^ (q * (2 - γ) + (s - q * s - (2 + γ))) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1; ring
  have hxne : ∀ y : ℝ, 0 ≤ x ^ y := fun y => Real.rpow_nonneg hx0.le y
  have hsK := Real.sqrt_nonneg K
  have hsκ := Real.sqrt_nonneg κm
  have hsCa := Real.sqrt_nonneg Ca
  calc εm ^ (2 - γ) * Real.sqrt κp * x ^ (-(2 + γ))
      ≤ (K ^ (2 - γ) * x ^ (q * (2 - γ))) *
        (Real.sqrt Ca * Real.sqrt K * x ^ s * (2 ^ s * x ^ (-(q * s))) * Real.sqrt κm) *
        x ^ (-(2 + γ)) := by
        apply mul_le_mul_of_nonneg_right _ (hxne _)
        exact mul_le_mul h4 hsqκp (Real.sqrt_nonneg _) (by positivity)
    _ = (K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ s)) *
        (x ^ (q * (2 - γ)) * (x ^ s * x ^ (-(q * s))) * x ^ (-(2 + γ))) * Real.sqrt κm := by ring
    _ = (K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ s)) *
        x ^ (q * (2 - γ) + (s - q * s - (2 + γ))) * Real.sqrt κm := by rw [hxpow]
    _ ≤ (K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ s)) * x ^ δ * Real.sqrt κm := by
        gcongr

/-- Part A of the final chain: the main (ergodic `1/N`) term. -/
theorem se_partA {x εm κm κp K Ca A' CB1 Aj Bm CE u c7 U β γ q δ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hεm : 0 < εm) (hκm : 0 < κm) (hK : 1 ≤ K) (hCa : 0 ≤ Ca) (hγ2 : γ ≤ 2)
    (hβγ : 0 ≤ β + γ) (hlow : x ^ q ≤ 2 * εm) (hup : εm ≤ K * x ^ q)
    (hκpA : κp ≤ Ca * x ^ (β + γ)) (hκmL : εm ^ (β + γ) ≤ K * κm)
    (hexp : δ ≤ (1 - q) * (β + γ) / 2 + q * (2 - γ) - (2 + γ))
    (hCB1 : 0 ≤ CB1) (hAj : 0 ≤ Aj) (hBm : 0 ≤ Bm) (hCE : 0 ≤ CE) (hc7 : 0 ≤ c7)
    (hu : u ≤ K * εm ^ (-γ))
    (hU : Real.sqrt U ≤ c7 * (CB1 * Aj * Bm * (A' ^ 2 * x ^ (-(2 + γ)))) * Real.sqrt κp) :
    4 * CE * εm * (εm * u) * Real.sqrt U ≤
      (4 * CE * K * c7 * CB1 * Aj * A' ^ 2 *
        (K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ ((β + γ) / 2)))) * x ^ δ *
        Real.sqrt κm * Bm := by
  have hmain := se_main_scale hx0 hx1 hεm hκm hK hCa hγ2 hβγ hlow hup hκpA hκmL hexp
  have hxn : 0 ≤ x ^ (-(2 + γ)) := Real.rpow_nonneg hx0.le _
  have hsκp := Real.sqrt_nonneg κp
  have hK0 : 0 < K := by linarith
  have hεe : εm * (εm * u) ≤ K * εm ^ (2 - γ) := by
    have : εm * εm * εm ^ (-γ) = εm ^ (2 - γ) := by
      rw [show (2 - γ) = 2 + (-γ) by ring, Real.rpow_add hεm]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    calc εm * (εm * u) = εm * εm * u := by ring
      _ ≤ εm * εm * (K * εm ^ (-γ)) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = K * (εm * εm * εm ^ (-γ)) := by ring
      _ = K * εm ^ (2 - γ) := by rw [this]
  have hsU := Real.sqrt_nonneg U
  have hpos : 0 ≤ 4 * CE := by positivity
  calc 4 * CE * εm * (εm * u) * Real.sqrt U
      = (4 * CE) * (εm * (εm * u)) * Real.sqrt U := by ring
    _ ≤ (4 * CE) * (K * εm ^ (2 - γ)) * (c7 * (CB1 * Aj * Bm * (A' ^ 2 * x ^ (-(2 + γ)))) *
          Real.sqrt κp) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hεe hpos) hU hsU (by positivity)
    _ = (4 * CE * K * c7 * CB1 * Aj * A' ^ 2 * Bm) *
          (εm ^ (2 - γ) * Real.sqrt κp * x ^ (-(2 + γ))) := by ring
    _ ≤ (4 * CE * K * c7 * CB1 * Aj * A' ^ 2 * Bm) *
          ((K ^ (2 - γ) * (Real.sqrt Ca * Real.sqrt K * 2 ^ ((β + γ) / 2))) * x ^ δ *
            Real.sqrt κm) := by
        apply mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by ring

/-- Part B of the final chain: the exponentially small term. -/
theorem se_partB {x εm κm κp K A' CB1 Aj Bm CE u M₁ c8 Ev β γ q δ : ℝ} (hx0 : 0 < x)
    (hεm : 0 < εm) (hεm1 : εm ≤ 1) (hK : 1 ≤ K) (hγ1 : γ ≤ 1)
    (hκpK : κp ≤ K)
    (hCB1 : 0 ≤ CB1) (hAj : 0 ≤ Aj) (hBm : 0 ≤ Bm) (hCE : 0 ≤ CE) (hA' : 0 ≤ A')
    (hu0 : 0 ≤ u) (hu : u ≤ K * εm ^ (-γ)) (hM₁ : 0 ≤ M₁) (hEv : 0 ≤ Ev)
    (hdec : Ev * (x ^ (3 + 3 * γ / 2 + q * β))⁻¹ ≤ M₁ * x ^ δ)
    (hc8 : x ^ (q * β) ≤ c8 * Real.sqrt κm) :
    CE * (2048 * 40 * (κp * CB1) * (Aj * Bm) * (A' / x ^ (1 + γ / 2)) ^ 3) *
        (εm * u) * Ev ≤
      (CE * 2048 * 40 * K * CB1 * Aj * A' ^ 3 * K * M₁ * c8) * x ^ δ * Real.sqrt κm * Bm := by
  have hGχ : εm * u ≤ K := by
    have h1 : εm * εm ^ (-γ) = εm ^ (1 - γ) := by
      rw [show (1 - γ) = 1 + (-γ) by ring, Real.rpow_add hεm, Real.rpow_one]
    have h2 : εm ^ (1 - γ) ≤ 1 := Real.rpow_le_one hεm.le hεm1 (by linarith)
    calc εm * u ≤ εm * (K * εm ^ (-γ)) := mul_le_mul_of_nonneg_left hu hεm.le
      _ = K * (εm * εm ^ (-γ)) := by ring
      _ = K * εm ^ (1 - γ) := by rw [h1]
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = K := mul_one K
  have hL3 : (A' / x ^ (1 + γ / 2)) ^ 3 = A' ^ 3 * (x ^ (3 + 3 * γ / 2))⁻¹ := by
    rw [div_pow, ← Real.rpow_natCast (x ^ (1 + γ / 2)) 3, ← Real.rpow_mul hx0.le]
    rw [show (1 + γ / 2) * ((3 : ℕ) : ℝ) = 3 + 3 * γ / 2 by push_cast; ring]
    ring
  have hxP : (x ^ (3 + 3 * γ / 2))⁻¹ = (x ^ (3 + 3 * γ / 2 + q * β))⁻¹ * x ^ (q * β) := by
    rw [Real.rpow_add hx0 (3 + 3 * γ / 2) (q * β), mul_inv, mul_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hx0 _).ne', mul_one]
  have hxs0 : 0 ≤ (x ^ (3 + 3 * γ / 2 + q * β))⁻¹ := by positivity
  have hxqb0 : 0 ≤ x ^ (q * β) := Real.rpow_nonneg hx0.le _
  have hCEn : 0 ≤ CE * 2048 * 40 := by positivity
  rw [hL3]
  calc CE * (2048 * 40 * (κp * CB1) * (Aj * Bm) * (A' ^ 3 * (x ^ (3 + 3 * γ / 2))⁻¹)) *
        (εm * u) * Ev
      ≤ CE * (2048 * 40 * (K * CB1) * (Aj * Bm) * (A' ^ 3 * (x ^ (3 + 3 * γ / 2))⁻¹)) * K * Ev := by
        gcongr
    _ = (CE * 2048 * 40 * K * CB1 * Aj * A' ^ 3 * K * Bm) *
          (Ev * (x ^ (3 + 3 * γ / 2 + q * β))⁻¹ * x ^ (q * β)) := by
        rw [hxP]; ring
    _ ≤ (CE * 2048 * 40 * K * CB1 * Aj * A' ^ 3 * K * Bm) *
          ((M₁ * x ^ δ) * (c8 * Real.sqrt κm)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hdec hc8 hxqb0 (by positivity)
    _ = _ := by ring

/-- `x^{qβ} ≲ √κ_m`, from `ε_m^{2β} ≤ K κ_{m-1} κ_m`, `κ_{m-1} ≤ K` and `x^q ≤ 2 ε_m`. -/
theorem se_kappa_lower {x εm κm κp K q β : ℝ} (hx0 : 0 < x) (hεm : 0 < εm) (hκm : 0 < κm)
    (hK : 1 ≤ K) (hβ : 0 < β) (hlow : x ^ q ≤ 2 * εm)
    (hκpK : κp ≤ K) (h2 : εm ^ (2 * β) ≤ K * κp * κm) :
    x ^ (q * β) ≤ 2 ^ β * K * Real.sqrt κm := by
  have hK0 : 0 < K := by linarith
  have h1 : εm ^ β ≤ K * Real.sqrt κm := by
    have e : εm ^ β = Real.sqrt (εm ^ (2 * β)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hεm.le]
      congr 1; ring
    rw [e]
    calc Real.sqrt (εm ^ (2 * β)) ≤ Real.sqrt (K ^ 2 * κm) := by
          apply Real.sqrt_le_sqrt
          calc εm ^ (2 * β) ≤ K * κp * κm := h2
            _ ≤ K * K * κm := by gcongr
            _ = K ^ 2 * κm := by ring
      _ = K * Real.sqrt κm := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK0.le]
  calc x ^ (q * β) = (x ^ q) ^ β := by rw [Real.rpow_mul hx0.le]
    _ ≤ (2 * εm) ^ β := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hlow hβ.le
    _ = 2 ^ β * εm ^ β := Real.mul_rpow (by norm_num) hεm.le
    _ ≤ 2 ^ β * (K * Real.sqrt κm) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
    _ = 2 ^ β * K * Real.sqrt κm := by ring

/-- `r N ≥ x^{-p} / (2^{15} A' K)` for the composed radius `r = (16 L)⁻¹ / 2^{11}`,
`L = A'/x^{1+γ/2}`, `N = ε_m⁻¹`, `ε_m ≤ K x^q`, `p = q - 1 - γ/2`. -/
theorem se_radius_freq {x εm K A' q γ : ℝ} (hx0 : 0 < x) (hεm : 0 < εm) (hK : 1 ≤ K)
    (hA' : 1 ≤ A') (hup : εm ≤ K * x ^ q) :
    (1 / (2 ^ 15 * A' * K)) * x ^ (-(q - 1 - γ / 2)) ≤
      (16 * (A' / x ^ (1 + γ / 2)))⁻¹ / 2 ^ 11 * εm⁻¹ := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 < A' := by linarith
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx0 q
  have hxg : 0 < x ^ (1 + γ / 2) := Real.rpow_pos_of_pos hx0 _
  have hinv : (K * x ^ q)⁻¹ ≤ εm⁻¹ := inv_anti₀ hεm hup
  have hr : (16 * (A' / x ^ (1 + γ / 2)))⁻¹ / 2 ^ 11 = x ^ (1 + γ / 2) / (2 ^ 15 * A') := by
    field_simp
    norm_num
  have hexp : x ^ (-(q - 1 - γ / 2)) = x ^ (1 + γ / 2) / x ^ q := by
    rw [← Real.rpow_sub hx0]; congr 1; ring
  rw [hr]
  calc (1 / (2 ^ 15 * A' * K)) * x ^ (-(q - 1 - γ / 2))
      = x ^ (1 + γ / 2) / (2 ^ 15 * A') * (K * x ^ q)⁻¹ := by
        rw [hexp]; field_simp
    _ ≤ x ^ (1 + γ / 2) / (2 ^ 15 * A') * εm⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)

/-- `c ≤ x^{-p}` for `x ≤ Λ⁻¹` and `c^{1/p} ≤ Λ`. -/
theorem se_rpow_neg_ge {x Λ p c : ℝ} (hx0 : 0 < x) (hxΛ : x ≤ Λ⁻¹) (hΛ : 0 < Λ) (hp : 0 < p)
    (hc : 0 ≤ c) (hΛc : c ^ (1 / p) ≤ Λ) : c ≤ x ^ (-p) := by
  have h1 : c ≤ Λ ^ p := by
    calc c = (c ^ (1 / p)) ^ p := by
          rw [← Real.rpow_mul hc, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
      _ ≤ Λ ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hc _) hΛc hp.le
  have h2 : x ^ p ≤ (Λ⁻¹) ^ p := Real.rpow_le_rpow hx0.le hxΛ hp.le
  have h3 : Λ ^ p = ((Λ⁻¹) ^ p)⁻¹ := by
    rw [Real.inv_rpow hΛ.le, inv_inv]
  have h4 : ((Λ⁻¹) ^ p)⁻¹ ≤ (x ^ p)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hx0 p) h2
  rw [Real.rpow_neg hx0.le]
  exact h1.trans (h3 ▸ h4)

/-- The coefficient radius and the flow radius are dominated by the common rate `L =
    A'/x^{1+γ/2}`. -/
theorem se_rate_le {x γ δ A' : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hA' : 2 ^ 10 ≤ A')
    (hδγ : 2 * δ ≤ γ / 2) (hδ : 0 ≤ δ) :
    2 ^ 10 / x ≤ A' / x ^ (1 + γ / 2) ∧ (2 ^ 10 / x) / x ^ (2 * δ) ≤ A' / x ^ (1 + γ / 2) := by
  have hxg : 0 < x ^ (1 + γ / 2) := Real.rpow_pos_of_pos hx0 _
  have hxd : 0 < x ^ (2 * δ) := Real.rpow_pos_of_pos hx0 _
  have h1 : x ^ (1 + γ / 2) ≤ x := by
    calc x ^ (1 + γ / 2) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      _ = x := Real.rpow_one x
  have h2 : x ^ (1 + γ / 2) ≤ x * x ^ (2 * δ) := by
    rw [← Real.rpow_one_add' hx0.le (by linarith : 1 + 2 * δ ≠ 0)]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hA0 : (0 : ℝ) < 2 ^ 10 := by norm_num
  constructor
  · rw [div_le_div_iff₀ hx0 hxg]
    nlinarith [mul_le_mul hA' h1 hxg.le (by linarith)]
  · rw [div_div, div_le_div_iff₀ (by positivity) hxg]
    nlinarith [mul_le_mul hA' h2 hxg.le (by linarith)]

theorem se_L_sq {x γ A' : ℝ} (hx0 : 0 < x) :
    (A' / x ^ (1 + γ / 2)) ^ 2 = A' ^ 2 * x ^ (-(2 + γ)) := by
  rw [div_pow, ← Real.rpow_natCast (x ^ (1 + γ / 2)) 2, ← Real.rpow_mul hx0.le,
    show (1 + γ / 2) * ((2 : ℕ) : ℝ) = 2 + γ by push_cast; ring, Real.rpow_neg hx0.le]
  ring

end AVenhance.Infra.Section5.Contracts
end
