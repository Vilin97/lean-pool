/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleParameters
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexamplePointwise

/-!
# The asymptotic error budget in the negative endpoint example

For the explicit choice `A_N = 2⁻⁴⁰ log N`, the stationary error is a
small fixed fraction of the harmonic main term, the packet-scale error decays
geometrically, and the two-fold oscillatory error is `O((log N)⁻²)`.  This
module proves that their sum eventually fits below the unused half of the
main-term lower bound.
-/

open Filter

namespace QuadraticCarleson


private theorem nat_le_two_pow (N : ℕ) : N ≤ 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hone : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by omega)
      rw [pow_succ]
      omega

/-- The first packet scale already beats the reciprocal linear scale. -/
theorem nat_mul_packetScale_one_le_one (N : ℕ) :
    (N : ℝ) * packetScale N 1 ≤ 1 := by
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast nat_le_two_pow N
  have hpowpos : 0 < (2 : ℝ) ^ N := by positivity
  unfold packetScale
  simp only [Nat.mul_one, zpow_neg, zpow_natCast]
  calc
    (N : ℝ) * ((2 : ℝ) ^ N)⁻¹ ≤
        (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hpowpos.le)
    _ = 1 := mul_inv_cancel₀ hpowpos.ne'

private theorem offSupportOscillatoryConstant_nonneg :
    0 ≤ offSupportOscillatoryConstant := by
  unfold offSupportOscillatoryConstant
  positivity

private theorem eventually_log_cube_dominates_oscillatory_constant :
    ∀ᶠ N : ℕ in atTop,
      4096 * offSupportOscillatoryConstant * ((2 : ℝ) ^ 40) ^ 2 ≤
        Real.log (N : ℝ) ^ 3 := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcube : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hlog
  exact hcube.eventually_ge_atTop _

/-- With the explicit amplitude and height, all analytic errors eventually
fit below the gap between the proved `1/4` main-term constant and the chosen
`1/8` operator level. -/
theorem eventually_paper_negative_endpoint_error_budget :
    ∀ᶠ N : ℕ in atTop,
      14 * paperAmplitude N / N + 28 * packetScale N 1 +
          128 * offSupportOscillatoryConstant /
            ((N : ℝ) * paperAmplitude N ^ 2) ≤
        Real.log N / (4 * N) -
          counterexampleHeight negativeEndpointHeightConstant N := by
  have hlog_atTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
      hlog_atTop.eventually_ge_atTop 896,
      eventually_log_cube_dominates_oscillatory_constant]
      with N hN hlog896 hcube
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) hlog896
  have hA : 0 < paperAmplitude N := by
    unfold paperAmplitude
    positivity
  have hamp : 14 * paperAmplitude N / N ≤
      Real.log N / (32 * N) := by
    have hcoef : (14 : ℝ) / (2 : ℝ) ^ 40 ≤ 1 / 32 := by norm_num
    calc
      14 * paperAmplitude N / N =
          ((14 : ℝ) / (2 : ℝ) ^ 40) *
            (Real.log N / N) := by
        unfold paperAmplitude
        ring
      _ ≤ (1 / 32 : ℝ) * (Real.log N / N) := by
        exact mul_le_mul_of_nonneg_right hcoef (div_nonneg hlog.le hNr.le)
      _ = Real.log N / (32 * N) := by ring
  have hpacket : 28 * packetScale N 1 ≤
      Real.log N / (32 * N) := by
    have hscaled : (N : ℝ) * packetScale N 1 ≤ 1 :=
      nat_mul_packetScale_one_le_one N
    apply (le_div_iff₀ (mul_pos (by norm_num) hNr)).mpr
    nlinarith [packetScale_pos N 1]
  have hoscNumerator :
      128 * offSupportOscillatoryConstant / paperAmplitude N ^ 2 ≤
        Real.log N / 32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    unfold paperAmplitude
    have hden : (0 : ℝ) < (2 : ℝ) ^ 40 := by positivity
    have heq :
        Real.log N / 32 * (Real.log N / (2 : ℝ) ^ 40) ^ 2 =
          Real.log N ^ 3 / (32 * ((2 : ℝ) ^ 40) ^ 2) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hden))).mpr
    nlinarith
  have hosc :
      128 * offSupportOscillatoryConstant /
          ((N : ℝ) * paperAmplitude N ^ 2) ≤
        Real.log N / (32 * N) := by
    have heqLeft :
        128 * offSupportOscillatoryConstant /
            ((N : ℝ) * paperAmplitude N ^ 2) =
          (128 * offSupportOscillatoryConstant / paperAmplitude N ^ 2) / N := by
      field_simp [hNr.ne', hA.ne']
    rw [heqLeft]
    have heqRight : Real.log N / (32 * N) = (Real.log N / 32) / N := by ring
    rw [heqRight]
    exact (div_le_div_iff_of_pos_right hNr).mpr hoscNumerator
  rw [negativeEndpointHeightConstant, counterexampleHeight]
  have htarget :
      Real.log N / (4 * N) - (1 / 8 * Real.log N / N) =
        4 * (Real.log N / (32 * N)) := by ring
  rw [htarget]
  have hq : 0 ≤ Real.log N / (32 * N) := by positivity
  nlinarith

end QuadraticCarleson
