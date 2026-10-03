/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Interpolation and exponent algebra for Lemma r.LeBron (abstract reals)

All `Real.rpow` algebra used by `lebron_step` lives here, in statements about plain real numbers. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem

/-- Interpolation between a sup bound and a Hölder-`1/4` bound:
`x ≤ 2A` and `x ≤ S h^{1/4}` give `x ≤ (2A)^{1-4μ} S^{4μ} h^μ` for `0 < μ ≤ 1/4`. -/
theorem interpolate_holder {μ x A S h : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 4)
    (hS0 : 0 ≤ S) (hx0 : 0 ≤ x) (hh : 0 ≤ h) (hx1 : x ≤ 2 * A) (hx2 : x ≤ S * h ^ ((1 : ℝ) / 4)) :
    x ≤ (2 * A) ^ (1 - 4 * μ) * S ^ (4 * μ) * h ^ μ := by
  have hA : 0 ≤ 2 * A := hx0.trans hx1
  have hh4 : 0 ≤ h ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hh _
  have e1 : (0 : ℝ) ≤ 1 - 4 * μ := by linarith
  have e2 : (0 : ℝ) ≤ 4 * μ := by linarith
  have hx_eq : x = x ^ (1 - 4 * μ) * x ^ (4 * μ) := by
    rw [← Real.rpow_add' hx0 (by linarith), show 1 - 4 * μ + 4 * μ = (1 : ℝ) by ring,
      Real.rpow_one]
  have hs1 : x ^ (1 - 4 * μ) ≤ (2 * A) ^ (1 - 4 * μ) := Real.rpow_le_rpow hx0 hx1 e1
  have hs2 : x ^ (4 * μ) ≤ (S * h ^ ((1 : ℝ) / 4)) ^ (4 * μ) := Real.rpow_le_rpow hx0 hx2 e2
  have hs3 : (S * h ^ ((1 : ℝ) / 4)) ^ (4 * μ) = S ^ (4 * μ) * h ^ μ := by
    rw [Real.mul_rpow hS0 hh4, ← Real.rpow_mul hh]
    congr 2
    ring
  calc x = x ^ (1 - 4 * μ) * x ^ (4 * μ) := hx_eq
    _ ≤ (2 * A) ^ (1 - 4 * μ) * (S * h ^ ((1 : ℝ) / 4)) ^ (4 * μ) :=
        mul_le_mul hs1 hs2 (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hA _)
    _ = (2 * A) ^ (1 - 4 * μ) * S ^ (4 * μ) * h ^ μ := by rw [hs3]; ring

/-- The Hölder exponent of Lemma r.LeBron: `μ = δ/(8δ+4P)`. -/
def lebronMu (δ P : ℝ) : ℝ := δ / (8 * δ + 4 * P)

theorem lebronMu_pos {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) : 0 < lebronMu δ P := by
  unfold lebronMu; positivity

theorem lebronMu_le {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) : lebronMu δ P ≤ 1 / 4 := by
  unfold lebronMu
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The exponent bookkeeping: `δ(1-4μ) - 2μP = δ/2`. -/
theorem lebronMu_exponent {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) :
    δ * (1 - 4 * lebronMu δ P) - 2 * lebronMu δ P * P = δ / 2 := by
  unfold lebronMu
  have : 8 * δ + 4 * P ≠ 0 := by positivity
  field_simp
  ring

/-- Power algebra: `(ε^δ)^{1-4μ} (ε^{-P/2})^{4μ} = ε^{δ(1-4μ) - 2μP}`. -/
theorem rpow_mix {ε δ P μ : ℝ} (hε : 0 < ε) :
    (ε ^ δ) ^ (1 - 4 * μ) * (ε ^ (-(P / 2))) ^ (4 * μ) = ε ^ (δ * (1 - 4 * μ) - 2 * μ * P) := by
  rw [← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
  congr 1
  ring

/-- The assembled real-number step: from a sup bound `x ≤ 2 C₈ ε^δ N` and a Hölder bound
`x ≤ S₀ ε^{-P/2} N h^{1/4}` conclude `x ≤ K ε^{δ/2} N h^μ`, `K = (2C₈)^{1-4μ} S₀^{4μ}`. -/
theorem holder_step {ε δ P x C₈ S₀ N h : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hC₈ : 0 ≤ C₈) (hS₀ : 0 ≤ S₀) (hN : 0 ≤ N) (hh : 0 ≤ h) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 2 * (C₈ * ε ^ δ * N))
    (hx2 : x ≤ S₀ * ε ^ (-(P / 2)) * N * h ^ ((1 : ℝ) / 4)) :
    x ≤ ((2 * C₈) ^ (1 - 4 * lebronMu δ P) * S₀ ^ (4 * lebronMu δ P)) *
      ε ^ (δ / 2) * N * h ^ lebronMu δ P := by
  set μ := lebronMu δ P with hμ
  have hμ0 : 0 < μ := lebronMu_pos hδ hP
  have hμ1 : μ ≤ 1 / 4 := lebronMu_le hδ hP
  have hint := interpolate_holder hμ0 hμ1 (by positivity) hx0 hh hx1 hx2
  have e1 : (0 : ℝ) ≤ 1 - 4 * μ := by linarith
  have e2 : (0 : ℝ) ≤ 4 * μ := by linarith
  have hεδ : 0 ≤ ε ^ δ := Real.rpow_nonneg hε.le _
  have hεP : 0 ≤ ε ^ (-(P / 2)) := Real.rpow_nonneg hε.le _
  have h1 : (2 * (C₈ * ε ^ δ * N)) ^ (1 - 4 * μ) =
      (2 * C₈) ^ (1 - 4 * μ) * (ε ^ δ) ^ (1 - 4 * μ) * N ^ (1 - 4 * μ) := by
    rw [show 2 * (C₈ * ε ^ δ * N) = (2 * C₈) * ε ^ δ * N by ring,
      Real.mul_rpow (by positivity) hN, Real.mul_rpow (by positivity) hεδ]
  have h2 : (S₀ * ε ^ (-(P / 2)) * N) ^ (4 * μ) =
      S₀ ^ (4 * μ) * (ε ^ (-(P / 2))) ^ (4 * μ) * N ^ (4 * μ) := by
    rw [Real.mul_rpow (by positivity) hN, Real.mul_rpow hS₀ hεP]
  have hNN : N ^ (1 - 4 * μ) * N ^ (4 * μ) = N := by
    rcases hN.eq_or_lt with h0 | hpos
    · subst h0
      have : (0 : ℝ) ^ (1 - 4 * μ) * (0 : ℝ) ^ (4 * μ) = 0 := by
        rcases e1.eq_or_lt with a | a
        · rw [← a]; rcases e2.eq_or_lt with b | b
          · linarith
          · rw [Real.zero_rpow b.ne']; simp
        · rw [Real.zero_rpow a.ne']; simp
      exact this
    · rw [← Real.rpow_add hpos, show 1 - 4 * μ + 4 * μ = (1 : ℝ) by ring, Real.rpow_one]
  have hmix := rpow_mix (ε := ε) (δ := δ) (P := P) (μ := μ) hε
  rw [lebronMu_exponent hδ hP] at hmix
  -- the interpolated bound, reorganised
  have hsplit : (2 * (C₈ * ε ^ δ * N)) ^ (1 - 4 * μ) * (S₀ * ε ^ (-(P / 2)) * N) ^ (4 * μ) * h ^ μ
      = ((2 * C₈) ^ (1 - 4 * μ) * S₀ ^ (4 * μ)) * ((ε ^ δ) ^ (1 - 4 * μ) *
        (ε ^ (-(P / 2))) ^ (4 * μ)) * (N ^ (1 - 4 * μ) * N ^ (4 * μ)) * h ^ μ := by
    rw [h1, h2]; ring
  rw [hsplit, hmix, hNN] at hint
  calc x ≤ _ := hint
    _ = _ := by ring

/-- `1/√κ ≤ c^{-1/2} E^{-P/2}` from `c E^P ≤ κ`. -/
theorem one_div_sqrt_le {c E P κ : ℝ} (hc : 0 < c) (hE : 0 < E) (hκ : c * E ^ P ≤ κ) :
    1 / Real.sqrt κ ≤ (1 / Real.sqrt c) * E ^ (-(P / 2)) := by
  have hEP : 0 < E ^ P := Real.rpow_pos_of_pos hE P
  have h1 : Real.sqrt c * E ^ (P / 2) ≤ Real.sqrt κ := by
    have : Real.sqrt (c * E ^ P) = Real.sqrt c * E ^ (P / 2) := by
      rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow (E ^ P), ← Real.rpow_mul hE.le]
      congr 2
      ring
    rw [← this]
    exact Real.sqrt_le_sqrt hκ
  have hpos : 0 < Real.sqrt c * E ^ (P / 2) :=
    mul_pos (Real.sqrt_pos.2 hc) (Real.rpow_pos_of_pos hE _)
  calc 1 / Real.sqrt κ ≤ 1 / (Real.sqrt c * E ^ (P / 2)) := one_div_le_one_div_of_le hpos h1
    _ = (1 / Real.sqrt c) * E ^ (-(P / 2)) := by
      rw [Real.rpow_neg hE.le]
      field_simp

end AVenhance.Infra.FullTheorem
