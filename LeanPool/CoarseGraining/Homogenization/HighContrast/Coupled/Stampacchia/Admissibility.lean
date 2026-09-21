/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The De Giorgi admissibility algebra

The scalar inequality feeding `deGiorgi_levelVolume_tendsto_zero`'s `hKcond`.
With `α = q/2`, `β = α − 1`, `B = 4^α`, `Crec = C_F²·E₀²`, `K = Cd·L·E₀`,
`Ld = L^d`, and the critical-exponent relation `d·β = 2·α` (equivalently
`q = 2d/(d−2)`), the powers of `L` and `E₀` cancel and the admissibility
condition reduces to a choice of `Cd ≥ C_F·B^{1/(2β)}`.
-/

namespace Homogenization

open scoped NNReal

/-- **Admissibility algebra.**  Given the critical relation `(d:ℝ)·β = 2·α`
(with `α, β > 0`, `β = α − 1`), `B = 4^α`, and `Cd ≥ C_F·B^{1/(2β)}` with
`Cd > 0`, `C_F ≥ 0`, `E₀ > 0`, `L > 0`, the De Giorgi leading constant is
admissible:
`((C_F²·E₀²)/(Cd·L·E₀)²)^α · B · (L^d)^β ≤ B^{−(1/β)}`. -/
theorem deGiorgi_admissible
    {d : ℕ} {C_F E₀ L Cd α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβeq : β = α - 1) (hB : (d : ℝ) * β = 2 * α)
    (hCF : 0 ≤ C_F) (hE₀ : 0 < E₀) (hL : 0 < L) (hCd : 0 < Cd)
    (hchoice : C_F * ((4 : ℝ) ^ α) ^ (1 / (2 * β)) ≤ Cd) :
    (((C_F ^ 2 * E₀ ^ 2) / (Cd * L * E₀) ^ 2) ^ α) * ((4 : ℝ) ^ α) * ((L ^ d) ^ β)
      ≤ ((4 : ℝ) ^ α) ^ (-(1 / β)) := by
  set B : ℝ := (4 : ℝ) ^ α with hBdef
  have hBpos : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  -- Abbreviate `t := C_F / Cd`.
  set t : ℝ := C_F / Cd with htdef
  have ht0 : 0 ≤ t := div_nonneg hCF hCd.le
  -- Step 1: `Crec/K² = t² / L²`.
  have hK2 : (Cd * L * E₀) ^ 2 = Cd ^ 2 * L ^ 2 * E₀ ^ 2 := by ring
  have hCd0 : Cd ≠ 0 := hCd.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hE00 : E₀ ≠ 0 := hE₀.ne'
  have hstep1 : (C_F ^ 2 * E₀ ^ 2) / (Cd * L * E₀) ^ 2 = t ^ 2 / L ^ 2 := by
    rw [hK2, htdef, div_pow]
    field_simp
  rw [hstep1]
  -- Step 2: `(t²/L²)^α = t^{2α} · L^{-2α}`.
  have hL2 : (0 : ℝ) ≤ L ^ 2 := by positivity
  have ht2 : (0 : ℝ) ≤ t ^ 2 := by positivity
  have hdiv : (t ^ 2 / L ^ 2) ^ α = (t ^ 2) ^ α / (L ^ 2) ^ α :=
    Real.div_rpow ht2 hL2 α
  -- `(t²)^α = t^{2α}`, `(L²)^α = L^{2α}`.
  have hLd : ((L ^ d) ^ β) = L ^ ((d : ℝ) * β) := by
    rw [← Real.rpow_natCast L d, ← Real.rpow_mul hL.le]
  have hL2a : ((L ^ 2) ^ α) = L ^ (2 * α) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
    norm_num
  have ht2a : ((t ^ 2) ^ α) = t ^ (2 * α) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0]
    norm_num
  -- Assemble the `L`-cancellation.
  rw [hdiv, hLd, hL2a, ht2a, hB]
  -- Goal: `t^{2α} / L^{2α} * B * L^{2α} ≤ B^{−1/β}`.
  have hLα_pos : (0 : ℝ) < L ^ (2 * α) := Real.rpow_pos_of_pos hL _
  have hcollapse :
      t ^ (2 * α) / L ^ (2 * α) * B * L ^ (2 * α) = B * t ^ (2 * α) := by
    have hne : L ^ (2 * α) ≠ 0 := hLα_pos.ne'
    field_simp
  rw [hcollapse]
  -- Step 3: `t ≤ B^{-1/(2β)}`, hence `B · t^{2α} ≤ B^{-1/β}`.
  have hBpow : (0 : ℝ) < B ^ (1 / (2 * β)) := Real.rpow_pos_of_pos hBpos _
  have ht_le : t ≤ B ^ (-(1 / (2 * β))) := by
    have h1 : t * B ^ (1 / (2 * β)) ≤ 1 := by
      rw [htdef, div_mul_eq_mul_div, div_le_one hCd]
      exact hchoice
    rw [Real.rpow_neg hBpos.le, ← one_div]
    exact (le_div_iff₀ hBpow).mpr h1
  -- Raise to `2α`.
  have h2α : (0 : ℝ) < 2 * α := by positivity
  have htpow : t ^ (2 * α) ≤ (B ^ (-(1 / (2 * β)))) ^ (2 * α) :=
    Real.rpow_le_rpow ht0 ht_le h2α.le
  have hRHSpow : (B ^ (-(1 / (2 * β)))) ^ (2 * α) = B ^ (-(1 / β) - 1) := by
    rw [← Real.rpow_mul hBpos.le]
    congr 1
    -- `-(1/(2β)) · 2α = -(1/β) - 1`, using `α = β + 1`.
    have hαβ : α = β + 1 := by rw [hβeq]; ring
    rw [hαβ]
    field_simp
    ring
  calc B * t ^ (2 * α)
      ≤ B * (B ^ (-(1 / (2 * β)))) ^ (2 * α) :=
        mul_le_mul_of_nonneg_left htpow hBpos.le
    _ = B * B ^ (-(1 / β) - 1) := by rw [hRHSpow]
    _ = B ^ (1 + (-(1 / β) - 1)) := by
        rw [Real.rpow_add hBpos, Real.rpow_one]
    _ = B ^ (-(1 / β)) := by congr 1; ring

end Homogenization
