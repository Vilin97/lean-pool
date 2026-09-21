/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corridor-width optimization (rpow algebra)

This file isolates the pure real-analysis optimization that turns the two-error
bound

  `Var[F] ≤ C₀·(Θ³·(ℓ/L)^{d-2} + Θ/ℓ)·Msq²`      (`4 ≤ ℓ ≤ L`)

together with the deterministic bound `Var[F] ≤ 4·Msq²` into the `min`-form of
the scalar block variance estimate `e.scalar.block.variance`:

  `Var[F] ≤ C·Msq²·min{1, Θ²·L^{-(d-2)/(d-1)}}`.

The optimal corridor width is `ℓ₀ = (L^{d-2}/Θ²)^{1/(d-1)}`, put here in the
resolved normal form `ℓ₀ = L^β·Θ^{-2/(d-1)}` with `β = (d-2)/(d-1)`.  The two
balancing identities and the bound `Θ^{1+2/(d-1)} ≤ Θ²` are the whole content.

The `rpow` algebra (`exists_optimal_width`) is separated from the numeric
regime combination (`scalar_opt`) so each declaration elaborates at default
heartbeats.  No probability appears.
-/

namespace Homogenization

open Real

/-- **Optimal corridor width.**  For `Θ, L ≥ 1` there is a width `ℓ₀ ∈ (0, L]`
whose two corridor error terms are both bounded by `X := Θ²·L^{-(d-2)/(d-1)}`.
This packages all of the `rpow` balance algebra. -/
theorem exists_optimal_width {d : ℕ} (hd : 3 ≤ d) {Θ L : ℝ}
    (hΘ : 1 ≤ Θ) (hL : 1 ≤ L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ℓ₀ ≤ L ∧
      Θ ^ 3 * (ℓ₀ / L) ^ (d - 2) ≤ Θ ^ 2 * L ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) ∧
      Θ * ℓ₀⁻¹ ≤ Θ ^ 2 * L ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) := by
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set n1 : ℝ := (d : ℝ) - 1 with hn1def
  set n2 : ℝ := (d : ℝ) - 2 with hn2def
  have hn1pos : (0 : ℝ) < n1 := by rw [hn1def]; linarith
  have hn2pos : (0 : ℝ) < n2 := by rw [hn2def]; linarith
  have hn2ge1 : (1 : ℝ) ≤ n2 := by rw [hn2def]; linarith
  have hn1 : n1 = n2 + 1 := by rw [hn1def, hn2def]; ring
  have hn1ne : n1 ≠ 0 := ne_of_gt hn1pos
  have hn2p1 : n2 + 1 ≠ 0 := by positivity
  set β : ℝ := n2 / n1 with hβdef
  have hβpos : (0 : ℝ) < β := div_pos hn2pos hn1pos
  have hβle1 : β ≤ 1 := by rw [hβdef, div_le_one hn1pos, hn1]; linarith
  set X : ℝ := Θ ^ 2 * L ^ (-n2 / n1) with hXdef
  have hnegβ : -n2 / n1 = -β := by rw [hβdef]; ring
  have hXeq : X = Θ ^ 2 * L ^ (-β) := by rw [hXdef, hnegβ]
  have hLβnn : (0 : ℝ) ≤ L ^ (-β) := (Real.rpow_pos_of_pos hL0 _).le
  -- `Θ^{1+2/n1} ≤ Θ²`
  have hexp_le : Θ ^ (1 + 2 / n1) ≤ Θ ^ 2 := by
    have h1 : (2 : ℝ) / n1 ≤ 1 := by rw [div_le_one hn1pos, hn1]; linarith
    have h2 : Θ ^ (1 + 2 / n1) ≤ Θ ^ ((2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hΘ (by push_cast; linarith)
    rwa [Real.rpow_natCast] at h2
  set ℓ₀ : ℝ := L ^ β * Θ ^ (-(2 / n1)) with hℓ₀def
  have hℓ₀pos : (0 : ℝ) < ℓ₀ := by
    rw [hℓ₀def]; exact mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hΘ0 _)
  -- Claim A : Θ·ℓ₀⁻¹ = Θ^{1+2/n1}·L^{-β}
  have hClaimA : Θ * ℓ₀⁻¹ = Θ ^ (1 + 2 / n1) * L ^ (-β) := by
    have hℓ₀inv : ℓ₀⁻¹ = L ^ (-β) * Θ ^ (2 / n1) := by
      rw [hℓ₀def, mul_inv, ← Real.rpow_neg hL0.le, ← Real.rpow_neg hΘ0.le, neg_neg]
    rw [hℓ₀inv, Real.rpow_add hΘ0, Real.rpow_one]; ring
  -- Claim B : Θ³·(ℓ₀/L)^{d-2} = Θ^{1+2/n1}·L^{-β}
  have hcast : ((d - 2 : ℕ) : ℝ) = n2 := by
    rw [hn2def, Nat.cast_sub (show 2 ≤ d by omega)]; norm_num
  have hClaimB : Θ ^ 3 * (ℓ₀ / L) ^ (d - 2) = Θ ^ (1 + 2 / n1) * L ^ (-β) := by
    rw [← Real.rpow_natCast (ℓ₀ / L) (d - 2), hcast]
    have hfrac : ℓ₀ / L = L ^ (β - 1) * Θ ^ (-(2 / n1)) := by
      rw [hℓ₀def, show L ^ (β - 1) = L ^ β / L by rw [Real.rpow_sub hL0, Real.rpow_one]]
      ring
    rw [hfrac, Real.mul_rpow (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hΘ0.le _),
      ← Real.rpow_mul hL0.le, ← Real.rpow_mul hΘ0.le]
    have hLexp : (β - 1) * n2 = -β := by rw [hβdef, hn1]; field_simp; ring
    have hΘexp : Θ ^ 3 * Θ ^ (-(2 / n1) * n2) = Θ ^ (1 + 2 / n1) := by
      rw [← Real.rpow_natCast Θ 3, ← Real.rpow_add hΘ0]
      congr 1
      push_cast; rw [hn1]; field_simp; ring
    rw [hLexp]
    calc Θ ^ 3 * (L ^ (-β) * Θ ^ (-(2 / n1) * n2))
        = (Θ ^ 3 * Θ ^ (-(2 / n1) * n2)) * L ^ (-β) := by ring
      _ = Θ ^ (1 + 2 / n1) * L ^ (-β) := by rw [hΘexp]
  -- `ℓ₀ ≤ L`
  have hℓ₀leL : ℓ₀ ≤ L := by
    have h1 : Θ ^ (-(2 / n1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hΘ (neg_nonpos_of_nonneg (by positivity))
    have h2 : L ^ β ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hβle1
    calc ℓ₀ = L ^ β * Θ ^ (-(2 / n1)) := hℓ₀def
      _ ≤ L ^ β * 1 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hL0.le _)
      _ = L ^ β := mul_one _
      _ ≤ L ^ (1 : ℝ) := h2
      _ = L := Real.rpow_one L
  refine ⟨ℓ₀, hℓ₀pos, hℓ₀leL, ?_, ?_⟩
  · rw [hXeq, hClaimB]
    exact mul_le_mul_of_nonneg_right hexp_le hLβnn
  · rw [hXeq, hClaimA]
    exact mul_le_mul_of_nonneg_right hexp_le hLβnn

/-- **Corridor-width optimization.**  From the deterministic bound and the
two-error bound (free `ℓ ∈ [4, L]`), the scalar block variance obeys the
`min`-form with `β = (d-2)/(d-1)` and a `Θ²` upper factor. -/
theorem scalar_opt {d : ℕ} (hd : 3 ≤ d) {Θ L Msq V C₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀)
    (hdet : V ≤ 4 * Msq ^ 2)
    (htwo : ∀ ℓ : ℝ, 4 ≤ ℓ → ℓ ≤ L →
      V ≤ C₀ * (Θ ^ 3 * (ℓ / L) ^ (d - 2) + Θ * ℓ⁻¹) * Msq ^ 2) :
    V ≤ (16 + 2 * C₀) * Msq ^ 2 *
        min 1 (Θ ^ 2 * L ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1))) := by
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hMsq2 : (0 : ℝ) ≤ Msq ^ 2 := sq_nonneg _
  obtain ⟨ℓ₀, hℓ₀pos, hℓ₀leL, hBle, hAle⟩ := exists_optimal_width hd hΘ hL
  set X : ℝ := Θ ^ 2 * L ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) with hXdef
  have hXpos : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hMX : (0 : ℝ) ≤ Msq ^ 2 * X := mul_nonneg hMsq2 hXpos.le
  clear_value X
  rcases le_total 1 X with hX1 | hX1
  · rw [min_eq_left hX1, mul_one]
    have hge : 4 * Msq ^ 2 ≤ (16 + 2 * C₀) * Msq ^ 2 := by
      have h2 : (0 : ℝ) ≤ 2 * C₀ * Msq ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hC₀) hMsq2
      nlinarith [hMsq2, h2]
    linarith [hdet, hge]
  · rw [min_eq_right hX1]
    rcases le_or_gt 4 ℓ₀ with hℓ₀4 | hℓ₀4
    · have hb := htwo ℓ₀ hℓ₀4 hℓ₀leL
      have hsum : Θ ^ 3 * (ℓ₀ / L) ^ (d - 2) + Θ * ℓ₀⁻¹ ≤ 2 * X := by
        linarith [hAle, hBle]
      have hstep : V ≤ C₀ * (2 * X) * Msq ^ 2 :=
        hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum hC₀) hMsq2)
      have hge : C₀ * (2 * X) * Msq ^ 2 ≤ (16 + 2 * C₀) * Msq ^ 2 * X := by
        nlinarith [hMX]
      linarith [hstep, hge]
    · have hquarter : (1 : ℝ) / 4 ≤ X := by
        have hΘℓ : Θ * ℓ₀⁻¹ * ℓ₀ = Θ := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hℓ₀pos), mul_one]
        have hypos : (0 : ℝ) < Θ * ℓ₀⁻¹ := mul_pos hΘ0 (inv_pos.2 hℓ₀pos)
        have hinv : (1 : ℝ) / 4 ≤ Θ * ℓ₀⁻¹ := by
          nlinarith [hΘℓ, hΘ,
            mul_nonneg hypos.le (by linarith [hℓ₀4] : (0:ℝ) ≤ 4 - ℓ₀)]
        linarith [hinv, hAle]
      have hA : 4 * Msq ^ 2 ≤ 16 * Msq ^ 2 * X := by
        nlinarith [mul_nonneg hMsq2 (by linarith [hquarter] : (0:ℝ) ≤ X - 1 / 4)]
      have hB : 16 * Msq ^ 2 * X ≤ (16 + 2 * C₀) * Msq ^ 2 * X := by
        nlinarith [mul_nonneg hC₀ hMX]
      linarith [hdet, hA, hB]

end Homogenization
