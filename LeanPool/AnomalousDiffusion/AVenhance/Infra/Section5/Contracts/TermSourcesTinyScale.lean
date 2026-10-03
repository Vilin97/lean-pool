/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Abstract-real scale arithmetic for the `tiny` source contract

Pure real lemmas (no project definitions).  The smallness `x^{δ N_*}` of the last increment
(`x = ε_{m-1}`) beats the polynomial losses `r² L²` of the coefficient jets and of the analytic
radius, and the loss `√κ_{m-1}/√κ_m ≲ ε_m^{-β}` coming from the lower bound
`ε_m^{2β} ≤ K κ_m κ_{m-1}` (`a_m² ε_m⁴/κ_m ≤ K κ_{m-1}`). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

/-- `√κ_{m-1} · Y x^E ≤ C x^δ √κ_m`, from `E ≥ δ + q β`, `x^q ≤ 2 ε_m`, `ε_m^{2β} ≤ K κ_{m-1} κ_m`
and `κ_{m-1} ≤ K`. -/
theorem sc_Z_core {x εm κm κp K Y δ q β E : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hεm : 0 < εm)
    (hκm : 0 < κm) (hκp : 0 < κp) (hK : 1 ≤ K) (hκpK : κp ≤ K) (hβ : 0 < β)
    (hpow : x ^ q ≤ 2 * εm) (hε : εm ^ (2 * β) ≤ K * κp * κm) (hE : δ + q * β ≤ E)
    (hY : 0 ≤ Y) :
    Real.sqrt κp * (Y * x ^ E) ≤ (Y * 2 ^ β * K * Real.sqrt K) * x ^ δ * Real.sqrt κm := by
  have hxE : x ^ E ≤ x ^ δ * x ^ (q * β) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hE
  have hxqb : x ^ (q * β) ≤ 2 ^ β * εm ^ β := by
    rw [Real.rpow_mul hx0.le, ← Real.mul_rpow (by norm_num) hεm.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hpow hβ.le
  have hεβ : εm ^ β ≤ Real.sqrt K * Real.sqrt κp * Real.sqrt κm := by
    have h2 : εm ^ β = Real.sqrt (εm ^ (2 * β)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hεm.le]
      congr 1; ring
    rw [h2, ← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hε
  have hsk : Real.sqrt κp ≤ Real.sqrt K := Real.sqrt_le_sqrt hκpK
  have hsk0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hxd : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  have hp2 : (0 : ℝ) ≤ 2 ^ β := Real.rpow_nonneg (by norm_num) _
  have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by linarith)
  calc Real.sqrt κp * (Y * x ^ E)
      ≤ Real.sqrt κp * (Y * (x ^ δ * (2 ^ β * εm ^ β))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hY
        exact hxE.trans (mul_le_mul_of_nonneg_left hxqb hxd)
    _ ≤ Real.sqrt κp * (Y * (x ^ δ * (2 ^ β * (Real.sqrt K * Real.sqrt κp * Real.sqrt κm)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hY
        apply mul_le_mul_of_nonneg_left _ hxd
        exact mul_le_mul_of_nonneg_left hεβ hp2
    _ = Y * 2 ^ β * x ^ δ * Real.sqrt K * (Real.sqrt κp * Real.sqrt κp) * Real.sqrt κm := by ring
    _ = Y * 2 ^ β * x ^ δ * Real.sqrt K * κp * Real.sqrt κm := by
        rw [Real.mul_self_sqrt hκp.le]
    _ ≤ Y * 2 ^ β * x ^ δ * Real.sqrt K * K * Real.sqrt κm := by
        gcongr
    _ = _ := by ring

theorem sc_rpow_sq {x : ℝ} (hx0 : 0 < x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (2 * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  norm_num
  rw [mul_comm]

/-- The product of the polynomial losses and the smallness `(C x^{2δ})^{N/2}` is a single power
of `x`. -/
theorem sc_Z_chain {x δ γ Cs Cs' F N : ℝ} (hx0 : 0 < x) (hCs : 0 ≤ Cs) :
    (2 * ((2 ^ 10 / x) / x ^ (2 * δ))) ^ 2 * (Cs ^ 3 * x ^ (2 * δ)) ^ (N / 2) * F *
        (Cs' * x ^ (-(1 + γ / 2))) ^ 2 =
      2 ^ 22 * Cs' ^ 2 * F * (Cs ^ 3) ^ (N / 2) * x ^ (δ * N - 4 - 4 * δ - γ) := by
  have hr : (2 ^ 10 / x) / x ^ (2 * δ) = 2 ^ 10 * x ^ (-(1 + 2 * δ)) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one]
    field_simp
  have hr2 : ((2 ^ 10 / x) / x ^ (2 * δ)) ^ 2 = 2 ^ 20 * x ^ (-(2 + 4 * δ)) := by
    rw [hr, mul_pow, sc_rpow_sq hx0]
    norm_num
    congr 1
    ring
  have hL2 : (Cs' * x ^ (-(1 + γ / 2))) ^ 2 = Cs' ^ 2 * x ^ (-(2 + γ)) := by
    rw [mul_pow, sc_rpow_sq hx0]
    congr 2
    ring
  have hA : (Cs ^ 3 * x ^ (2 * δ)) ^ (N / 2) = (Cs ^ 3) ^ (N / 2) * x ^ (δ * N) := by
    rw [Real.mul_rpow (pow_nonneg hCs 3) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
    congr 2
    ring
  rw [mul_pow, hr2, hL2, hA]
  have hx : x ^ (-(2 + 4 * δ)) * x ^ (δ * N) * x ^ (-(2 + γ)) = x ^ (δ * N - 4 - 4 * δ - γ) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  calc _ = 2 ^ 22 * Cs' ^ 2 * F * (Cs ^ 3) ^ (N / 2) *
        (x ^ (-(2 + 4 * δ)) * x ^ (δ * N) * x ^ (-(2 + γ))) := by ring
    _ = _ := by rw [hx]

/-- The coefficient constant: `c ≤ C_c (κ_{m-1} C_B)² r⁴` for `r ≥ 1`. -/
theorem sc_c_le {b K r : ℝ} (hr : 1 ≤ r) :
    16 * b ^ 2 + 2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * K ^ 2 * (14336 * b ^ 2 * r ^ 4)) ≤
      (16 + 2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * K ^ 2 * 14336)) * (b ^ 2 * r ^ 4) := by
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr
  have h1 : 16 * b ^ 2 ≤ 16 * (b ^ 2 * r ^ 4) := by
    have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg b)
    linarith
  have h2 : 2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * K ^ 2 * (14336 * b ^ 2 * r ^ 4)) =
      2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * K ^ 2 * 14336) * (b ^ 2 * r ^ 4) := by ring
  rw [h2]
  linarith

/-- `√(7 c) ≤ √(7 C_c) b r²` from `c ≤ C_c b² r⁴`. -/
theorem sc_sqrt7_le {c Cc b r : ℝ} (hb : 0 ≤ b) (_hr : 0 ≤ r) (h : c ≤ Cc * (b ^ 2 * r ^ 4)) :
    Real.sqrt (7 * c) ≤ Real.sqrt (7 * Cc) * b * r ^ 2 := by
  have h7 : 7 * c ≤ 7 * Cc * (b ^ 2 * r ^ 4) := by linarith
  calc Real.sqrt (7 * c) ≤ Real.sqrt (7 * Cc * (b ^ 2 * r ^ 4)) := Real.sqrt_le_sqrt h7
    _ = Real.sqrt (7 * Cc) * b * r ^ 2 := by
        have : b ^ 2 * r ^ 4 = (b * r ^ 2) ^ 2 := by ring
        rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
        ring

/-- The final scalar chain for the nondivergence energy. -/
theorem sc_final_chain {x κp B CB CZ Y Cc c G A F L' r S E δ : ℝ} {sk : ℝ}
    (hκp : 0 < κp) (hCB : 0 ≤ CB) (hB : 0 ≤ B) (hG0 : 0 ≤ G) (hr : 0 ≤ r)
    (hcle : c ≤ Cc * ((κp * CB) ^ 2 * r ^ 4))
    (hsum : Real.sqrt (c * S) ≤ Real.sqrt (7 * c) * (G / Real.sqrt κp))
    (hG : G = B * A * F * L' ^ 2)
    (hchain : r ^ 2 * A * F * L' ^ 2 = Y * E)
    (hZ : Real.sqrt κp * (Y * E) ≤ CZ * x ^ δ * sk) :
    Real.sqrt (c * S) ≤ Real.sqrt (7 * Cc) * CB * B * (CZ * x ^ δ * sk) := by
  have hs0 : 0 < Real.sqrt κp := Real.sqrt_pos.2 hκp
  have hss : Real.sqrt κp * Real.sqrt κp = κp := Real.mul_self_sqrt hκp.le
  have hdiv : κp / Real.sqrt κp = Real.sqrt κp := by
    rw [div_eq_iff hs0.ne']; exact hss.symm
  have hsq7 := sc_sqrt7_le (c := c) (Cc := Cc) (b := κp * CB) (r := r)
    (mul_nonneg hκp.le hCB) hr hcle
  refine hsum.trans ?_
  calc Real.sqrt (7 * c) * (G / Real.sqrt κp)
      ≤ (Real.sqrt (7 * Cc) * (κp * CB) * r ^ 2) * (G / Real.sqrt κp) :=
        mul_le_mul_of_nonneg_right hsq7 (div_nonneg hG0 hs0.le)
    _ = Real.sqrt (7 * Cc) * CB * r ^ 2 * G * (κp / Real.sqrt κp) := by ring
    _ = Real.sqrt (7 * Cc) * CB * B * (Real.sqrt κp * (r ^ 2 * A * F * L' ^ 2)) := by
        rw [hdiv, hG]; ring
    _ = Real.sqrt (7 * Cc) * CB * B * (Real.sqrt κp * (Y * E)) := by rw [hchain]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hZ
        have : 0 ≤ Real.sqrt (7 * Cc) := Real.sqrt_nonneg _
        positivity

end AVenhance.Infra.Section5.Contracts
