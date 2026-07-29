/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.LocallyUniformEulerProduct

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_logDeriv_primeIdealFactor {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun P : HeightOneSpectrum (𝓞 K) ↦
        logDeriv (primeIdealFactor K P) s) := by
  let ε : ℝ := (s.re - 1) / 2
  let σ : ℝ := (s.re + 1) / 2
  have hε : 0 < ε := by grind
  have hσ : 1 < σ := by grind
  rw [← summable_norm_iff]
  apply ((summable_primeIdealNorm_rpow K hσ).mul_left (2 / ε)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro P
  let q := primeIdealNorm K P
  let x := inverseNormPower q s
  have hq : 1 < q := one_lt_primeIdealNorm K P
  have hx : ‖x‖ < 1 / 2 :=
    norm_inverseNormPower_primeIdeal_lt_half K P hs
  have hdenLower : 1 / 2 ≤ ‖1 - x‖ := by
    calc
      1 / 2 ≤ 1 - ‖x‖ := by linarith
      _ ≤ ‖1 - x‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) x
  rw [logDeriv_primeIdealFactor K P (zero_lt_one.trans hs),
    norm_neg, norm_div, norm_mul]
  have hlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    calc
      ‖Complex.log (q : ℂ)‖ =
          ‖((Real.log (q : ℝ) : ℝ) : ℂ)‖ := by simp
      _ = Real.log q := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast
            (Nat.le_of_lt hq)))]
  rw [hlog, show ‖x‖ = (q : ℝ) ^ (-s.re) by
    exact norm_inverseNormPower q (Nat.zero_lt_of_lt hq) s]
  calc
    Real.log q * (q : ℝ) ^ (-s.re) / ‖1 - x‖ ≤
        Real.log q * (q : ℝ) ^ (-s.re) / (1 / 2) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · simp_all
    _ = 2 * (Real.log q * (q : ℝ) ^ (-s.re)) := by ring
    _ ≤ 2 * (((q : ℝ) ^ ε / ε) * (q : ℝ) ^ (-s.re)) := by
      gcongr
      exact Real.log_le_rpow_div (by positivity) hε
    _ = (2 / ε) * (q : ℝ) ^ (-σ) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add (by positivity)]
      grind

end NumberField.Odlyzko
