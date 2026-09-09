/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Packet Scale Geometry
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace EulerPacketScaleGeometry

open Real EulerScale

/-- The activation-time interval in (38) follows from the two frame
invariants in (24), with the numerical constants stated in the source. -/
theorem activation_time_bounds
    {a β H x X : ℝ} (ha : 1 / 2 ≤ a) (ha₂ : a ≤ 2)
    (hH : 0 < H) (hx : 0 < x) (hX : 0 ≤ X)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    (3 * X * x / sqrt H) / 6 ≤ X / sqrt (β * a * H) ∧
      X / sqrt (β * a * H) ≤ 2 * (3 * X * x / sqrt H) / 3 := by
  have ha₀ : 0 < a := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hroot : 0 < sqrt (β * a * H) := sqrt_pos.2 (by positivity)
  have hrootH : 0 < sqrt H := sqrt_pos.2 hH
  have hs := sq_sqrt (show 0 ≤ β * a * H by positivity)
  have hsH := sq_sqrt hH.le
  have hprodLow : 1 / 4 ≤ β * x ^ 2 * a := by
    have hh := mul_le_mul hβx ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by positivity : 0 ≤ β * x ^ 2)
    nlinarith only [hh]
  have hprodUp : β * x ^ 2 * a ≤ 4 := by
    have hh := mul_le_mul hβx₂ ha₂ ha₀.le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have hlo : sqrt H ≤ 2 * x * sqrt (β * a * H) := by
    have hh := mul_le_mul_of_nonneg_right hprodLow hH.le
    have hhroot : 0 ≤ 2 * x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  have hup : x * sqrt (β * a * H) ≤ 2 * sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hprodUp hH.le
    have hhroot : 0 ≤ x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  constructor
  · have hid : 3 * X * x / sqrt H / 6 = X * x / (2 * sqrt H) := by ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity) hroot).2
    have hh := mul_le_mul_of_nonneg_left hup hX
    nlinarith only [hh]
  · have hid : 2 * (3 * X * x / sqrt H) / 3 = 2 * X * x / sqrt H := by ring
    rw [hid]
    apply (div_le_div_iff₀ hroot hrootH).2
    have hh := mul_le_mul_of_nonneg_left hlo hX
    nlinarith only [hh]

/-- A sufficiently small next time width makes the packet horizons nest. -/
theorem nested_horizon_of_width_ratio
    {t Δ W Wnext : ℝ} (hW : 0 ≤ W)
    (hΔ : Δ ≤ 2 * W / 3) (hnext : Wnext ≤ W / 2) :
    t + Δ + 2 * Wnext ≤ t + 2 * W := by linarith

/-- Powers of a shifted stage index divided by a larger predecessor
power vanish, a basic consequence of the quadratic recurrence geometry. -/
theorem stage_power_div_predecessor_power_tendsto_zero
    (J : ℕ) (hJ : 2 ≤ J) (A B : ℕ) (hAB : A < B) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ A /
      ((J - 1 + n : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add
    (stage_inv_tendsto_zero (J - 1))).pow A).mul
    ((stage_inv_tendsto_zero (J - 1)).pow (B - A))
  simp only [add_zero, one_pow, zero_pow (show B - A ≠ 0 by omega), mul_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by
    exact_mod_cast (show 0 < J - 1 + n by omega)
  have hj : (((J + n : ℕ) : ℝ)) = ((J - 1 + n : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show J + n = (J - 1 + n) + 1 by omega)
  have hi : 1 + (((J - 1 + n : ℕ) : ℝ))⁻¹ =
      (((J - 1 + n : ℕ) : ℝ) + 1) / ((J - 1 + n : ℕ) : ℝ) := by field_simp
  have hpw : ((J - 1 + n : ℕ) : ℝ) ^ B =
      ((J - 1 + n : ℕ) : ℝ) ^ A * ((J - 1 + n : ℕ) : ℝ) ^ (B - A) := by
    rw [← pow_add, show A + (B - A) = B by omega]
  dsimp only
  rw [hj, hi, hpw, div_pow]
  field_simp [hp.ne']
  simp only [one_div, ← mul_pow, inv_mul_cancel₀ hp.ne', one_pow]

/-- Exponential decay on any polynomially rescaled quadratic scale
absorbs every fixed polynomial in the scale and the stage index. -/
theorem polynomial_exponential_decay_summable
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A p q : ℕ) (C b : ℝ) (hC : 0 < C) (hb : 0 < b) :
    Summable (fun n => C * ((J + n : ℕ) : ℝ) ^ p * (x n) ^ q *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  let e : ℕ → ℝ := fun n => log C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
    have h := (((polynomial_over_growth_summable J hJ x hx0 hx A).tendsto_atTop_zero.const_mul
      (log C)).add ((polynomial_stage_log_over_growth_summable J hJ x hx0 hx
          A).tendsto_atTop_zero.const_mul (p : ℝ))).add
      ((polynomial_log_over_growth_tendsto_zero J hJ x hx0 hx A).const_mul (q : ℝ))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
    dsimp [e]
    field_simp [(hxp n).ne', hj.ne']
  have hh := perturbed_exponential_decay_summable J hJ x hx0 hx A b hb e
    (by simpa only [rpow_natCast] using he)
  apply hh.congr
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  simp only [rpow_natCast, e, exp_add, exp_log hC, exp_nat_mul,
    exp_log hj, exp_log (hxp n)]
  ring

/-- The ratio of a stage to any fixed predecessor tends to one. -/
theorem stage_div_shifted_tendsto_one (J d : ℕ) (hJ : d < J) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) /
      ((J - d + n : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := (stage_inv_tendsto_zero (J - d)).const_mul (d : ℝ)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add h
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  have hj : ((J + n : ℕ) : ℝ) = ((J - d + n : ℕ) : ℝ) + d := by
    exact_mod_cast (show J + n = (J - d + n) + d by omega)
  dsimp only
  rw [hj]
  field_simp

/-- A real power below a predecessor's natural power has vanishing
ratio; this includes the source's support exponent `7/2`. -/
theorem stage_rpow_div_shifted_power_tendsto_zero
    (J d B : ℕ) (hJ : d < J) (A : ℝ) (hAB : A < B) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ A /
      ((J - d + n : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  have hjtop : Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm] using tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat J)
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hAB)).comp hjtop
  have hh := ((stage_div_shifted_tendsto_one J d hJ).pow B).mul hp
  simp only [one_pow, mul_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hprev : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  dsimp only [Function.comp_def]
  rw [neg_sub, rpow_sub hj, rpow_natCast, div_pow]
  field_simp

/-- Polynomial logarithms are negligible relative to `x/j^A`, for every
nonnegative real exponent `A`. -/
theorem polynomial_log_relative_tendsto_zero
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A C p q : ℝ) (_hA : 0 ≤ A) :
    Tendsto (fun n => (C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)) /
      (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp (n : ℕ) : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hpoly : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (polynomial_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    · intro n
      exact div_nonneg (rpow_nonneg (hjp n).le A) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogx : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log (x n) / x n) atTop (𝓝 0) := by
    have hb := (polynomial_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply squeeze_zero_norm' _ hb
    apply Eventually.of_forall
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (rpow_nonneg (hjp n).le A),
      abs_of_pos (hxp n)]
    apply div_le_div_of_nonneg_right _ (hxp n).le
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogj : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log ((J + n : ℕ) : ℝ) / x n)
      atTop (𝓝 0) := by
    have hb := (polynomial_stage_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · intro n
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact div_nonneg (mul_nonneg (rpow_nonneg (hjp n).le A) (log_nonneg hj1)) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      apply mul_le_mul_of_nonneg_right _ (log_nonneg hj1)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hh := ((hpoly.const_mul C).add (hlogj.const_mul p)).add (hlogx.const_mul q)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  field_simp [(hxp n).ne', (rpow_pos_of_pos (hjp n) A).ne']

/-- Explicit positive logarithmic errors from older stages are absorbed
by the source's negative exponential scale. No smallness guard is assumed. -/
theorem source_scale_exponential_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C p q : ℝ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) :
    Summable (fun n => exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) := by
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x hx0 hx
  let e : ℕ → ℝ := fun n => c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
    C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
    have hh := ((stage_rpow_div_shifted_power_tendsto_zero J d B hJ A hAB).const_mul c).add
      (polynomial_log_relative_tendsto_zero J hJ1 x hx0 hx A C p q hA)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
    have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
    dsimp only [e]
    field_simp [(hxp n).ne', (rpow_pos_of_pos hj A).ne', hp.ne']
    ring
  have hh := perturbed_exponential_decay_summable J hJ1 x hx0 hx A b hb e he
  simpa only [e, add_assoc] using hh

end EulerPacketScaleGeometry
