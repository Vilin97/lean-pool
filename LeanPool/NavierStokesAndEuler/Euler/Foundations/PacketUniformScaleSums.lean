/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Complex.Exponential
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

/-!
# Packet Uniform Scale Sums
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleSums

open Real EulerScale

/-- Once the initial stage dominates the fixed polynomial exponent,
the rescaled quadratic sequence grows by at least a factor two at every step. -/
theorem polynomial_scale_doubles
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) (n : ℕ) :
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤ x (n + 1) / ((J + (n + 1) : ℕ) : ℝ) ^ A := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hJj : (J : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show J ≤ J + n by omega)
  have hJ₀ : (0 : ℝ) ≤ J := by positivity
  have hpower : (2 : ℝ) ^ (A + 1) ≤ ((J + n : ℕ) : ℝ) ^ 2 :=
    hJA.trans (pow_le_pow_left₀ hJ₀ hJj 2)
  have hn : ((J + (n + 1) : ℕ) : ℝ) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
  have hden : (((J + n : ℕ) : ℝ) + 1) ^ A ≤ (2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A := by
    have hh := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (J + n : ℕ) + 1)
      (by linarith : ((J + n : ℕ) : ℝ) + 1 ≤ 2 * ((J + n : ℕ) : ℝ)) A
    simpa only [mul_pow] using hh
  rw [hx, hn]
  calc
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
        (((J + n : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ A) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (hxp n).le (pow_nonneg hj.le A))
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ A)).2
      simpa only [pow_succ, mul_comm] using hpower
    _ = (((J + n : ℕ) : ℝ) ^ 2 * x n) / ((2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (hxp n).le)
      (by positivity : 0 < (((J + n : ℕ) : ℝ) + 1) ^ A) hden

/-- The entire positive exponent sequence is bounded below by its first
term times `2^n`, uniformly in the initial scale. -/
theorem polynomial_scale_geometric_lower
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, (2 : ℝ) ^ n * (x 0 / (J : ℝ) ^ A) ≤ x n / ((J + n : ℕ) : ℝ) ^ A := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
      have hd := polynomial_scale_doubles J A hJ hJA x hx0 hx n
      rw [pow_succ]
      nlinarith only [hh, hd]

/-- A simple exact comparison between binary growth and the stage count. -/
theorem stage_count_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      push_cast
      rw [pow_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith only [ih, hn]

/-- Every term of the source exponential series is bounded by one
explicit geometric series whose ratio depends only on the first scale. -/
theorem source_exponential_geometric_majorant
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A)) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) * exp (-b * (x 0 / (J : ℝ) ^ A)) ^ n := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hd := polynomial_scale_geometric_lower J A hJ hJA x hx0 hx n
  have hn := mul_le_mul_of_nonneg_right (stage_count_le_two_pow n)
    (div_nonneg hx0.le (pow_nonneg hJp.le A))
  have he : -b * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
      -b * (x 0 / (J : ℝ) ^ A) + (n : ℝ) * (-b * (x 0 / (J : ℝ) ^ A)) := by
    have hh := mul_le_mul_of_nonpos_left (hn.trans hd) (neg_nonpos.mpr hb.le)
    nlinarith only [hh]
  have hh := exp_le_exp.mpr he
  simpa only [exp_add, exp_nat_mul] using hh

/-- The full exponential-cost sum has an explicit upper bound tending
to zero as the initial scale increases. This makes the uniform small-sum
choice in the source quantitative. -/
theorem source_exponential_tsum_bound
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) / (1 - exp (-b * (x 0 / (J : ℝ) ^ A))) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let r := exp (-b * (x 0 / (J : ℝ) ^ A))
  have hr₀ : 0 ≤ r := (exp_pos _).le
  have hr : |r| < 1 := by
    rw [abs_of_nonneg hr₀]
    apply exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hb) (div_pos hx0 (pow_pos hJp A))
  have hgeom := (summable_geometric_of_abs_lt_one hr).mul_left r
  have hsum := exponential_decay_summable J hJ x hx0 hx A b hb
  have hh := hsum.tsum_le_tsum (source_exponential_geometric_majorant J A hJ hJA x hx0 hx b hb)
      hgeom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr] at hh
  simpa only [r, div_eq_mul_inv] using hh

/-- The explicit geometric-series bound vanishes as `x₀` tends to infinity. -/
theorem source_exponential_bound_tendsto_zero (J A : ℕ) (hJ : 1 ≤ J)
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A)) /
      (1 - exp (-b * (X / (J : ℝ) ^ A)))) atTop (𝓝 0) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hh := EulerPacketBaseScales.base_exponential_decay 1 0 (b / (J : ℝ) ^ A) 0 0
    (div_pos hb (pow_pos hJp A))
  simp only [rpow_zero, one_mul, pow_zero, mul_one] at hh
  have hh' : Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A))) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    congr 1
    ring
  have hd := hh'.div (tendsto_const_nhds.sub hh') (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, zero_div] at hd
  convert! hd using 1

end EulerPacketUniformScaleSums
