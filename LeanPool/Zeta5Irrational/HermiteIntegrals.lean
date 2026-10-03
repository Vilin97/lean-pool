/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Hermite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The rational integrals in Hermite's formula

* `∫₀^∞ g₄(y)/y dy = π/a`;
* `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for `n > 0` (separate closed forms for `n ≠ a` and
  `n = a`).
The antiderivatives (a rational function plus arctan terms) are verified by differentiation.
-/

public section

open Filter Topology Set MeasureTheory

namespace Zeta5Irrational

/-- `g₄(y) / y` as a rational function (continuous at `0`). -/
@[expose] noncomputable def h4 (a y : ℝ) : ℝ :=
  2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4) / (y ^ 2 + a ^ 2) ^ 5

lemma g4_div_eq_h4 (a : ℝ) {y : ℝ} (hy : y ≠ 0) : g4 a y / y = h4 a y := by
  unfold g4 h4;
  field_simp

lemma abs_h4_le {a : ℝ} (ha : 0 < a) (y : ℝ) : |h4 a y| ≤ 20 / (y ^ 2 + a ^ 2) := by
  unfold h4
  have hden : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 + a ^ 2) ^ 5),
    div_le_div_iff₀ (by positivity) hden]
  have h1 :
    |2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| ≤
      2 * a ^ 4 * (10 * (y ^ 2 + a ^ 2) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 4)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le];
    constructor <;>
      nlinarith [sq_nonneg (a ^ 2 - y ^ 2), sq_nonneg y, sq_nonneg a,
        mul_nonneg (sq_nonneg a) (sq_nonneg y)]
  have h2 : a ^ 4 ≤ (y ^ 2 + a ^ 2) ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg a, mul_nonneg (sq_nonneg y) (sq_nonneg a)]
  calc
    |2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| * (y ^ 2 + a ^ 2) ≤
        2 * a ^ 4 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) :=
      by gcongr
    _ ≤ 2 * (y ^ 2 + a ^ 2) ^ 2 * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) := by gcongr
    _ = 20 * (y ^ 2 + a ^ 2) ^ 5 := by ring

lemma integrableOn_of_le_inv_sq {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {C : ℝ}
    (hC : ∀ y, 0 < y → |f y| ≤ C / (y ^ 2 + a ^ 2)) : IntegrableOn f (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => (C * (1 + 1 / a ^ 2)) * (1 + y ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul _).integrableOn
  refine hg.mono' hf ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have h1 := hC y hy
    have h2 : C / (y ^ 2 + a ^ 2) < 0 := div_neg_of_neg_of_pos hneg (by positivity)
    linarith [abs_nonneg (f y)]
  calc
    |f y| ≤ C / (y ^ 2 + a ^ 2) := hC y hy
    _ = C * (1 / (y ^ 2 + a ^ 2)) := by ring
    _ ≤ C * ((1 + 1 / a ^ 2) * (1 / (1 + y ^ 2))) := by gcongr; exact inv_sq_add_le ha y
    _ = _ := by ring

/-- The limit `arctan (y / c) → π/2` as `y → ∞`, for `c > 0`. -/
lemma tendsto_arctan_div_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.arctan (y / c)) atTop (𝓝 (Real.pi / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const hc)

/-! ### `∫₀^∞ g₄(y)/y dy = π / a` -/

/-- Antiderivative of `h₄`. -/
noncomputable def A1 (a y : ℝ) : ℝ :=
  2 / a * Real.arctan (y / a) +
    2 * y * (12 * a ^ 6 + 14 * a ^ 4 * y ^ 2 + 11 * a ^ 2 * y ^ 4 + 3 * y ^ 6) /
      (3 * (a ^ 2 + y ^ 2) ^ 4)

lemma hasDerivAt_A1 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (A1 a) (h4 a y) y := by
  have h1 := ((hasDerivAt_id y).div_const a).arctan.const_mul (2 / a)
  have hne : 3 * (a ^ 2 + y ^ 2) ^ 4 ≠ 0 := by positivity
  have hnum :=
    ((hasDerivAt_id y).const_mul 2).mul
      (((((hasDerivAt_pow 2 y).const_mul (14 * a ^ 4)).const_add (12 * a ^ 6)).add
            ((hasDerivAt_pow 4 y).const_mul (11 * a ^ 2))).add
        ((hasDerivAt_pow 6 y).const_mul 3))
  have h2 := hnum.div ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 4).const_mul 3) hne
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A1, id, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [h4, id, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring

lemma tendsto_A1_atTop {a : ℝ} (ha : 0 < a) : Tendsto (A1 a) atTop (𝓝 (Real.pi / a)) := by
  have h1 :
    Tendsto (fun y : ℝ => 2 / a * Real.arctan (y / a)) atTop (𝓝 (2 / a * (Real.pi / 2))) :=
    (tendsto_arctan_div_atTop ha).const_mul _
  have hφ :
    Tendsto
      (fun u : ℝ =>
        2 * u * (12 * a ^ 6 * u ^ 6 + 14 * a ^ 4 * u ^ 4 + 11 * a ^ 2 * u ^ 2 + 3) /
          (3 * (a ^ 2 * u ^ 2 + 1) ^ 4))
      (𝓝 0) (𝓝 0) := by
    have :
      ContinuousAt
        (fun u : ℝ =>
          2 * u * (12 * a ^ 6 * u ^ 6 + 14 * a ^ 4 * u ^ 4 + 11 * a ^ 2 * u ^ 2 + 3) /
            (3 * (a ^ 2 * u ^ 2 + 1) ^ 4))
        0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    simpa using this.tendsto
  have h2 :
    Tendsto
      (fun y : ℝ =>
        2 * y * (12 * a ^ 6 + 14 * a ^ 4 * y ^ 2 + 11 * a ^ 2 * y ^ 4 + 3 * y ^ 6) /
          (3 * (a ^ 2 + y ^ 2) ^ 4))
      atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := h1.add h2
  unfold A1
  convert this using 2
  field_simp
  ring

lemma continuous_g4 (a : ℝ) (ha : 0 < a) : Continuous (g4 a) := by
  unfold g4
  exact
    (by fun_prop :
          Continuous fun y : ℝ => 2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
      (by fun_prop) (fun y => by positivity)

lemma integrableOn_h4 {a : ℝ} (ha : 0 < a) : IntegrableOn (h4 a) (Ioi 0) := by
  have hcont : Continuous (h4 a) := by
    unfold h4
    exact
      (by fun_prop :
            Continuous fun y : ℝ => 2 * a ^ 4 * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
        (by fun_prop) (fun y => by positivity)
  exact integrableOn_of_le_inv_sq ha hcont.aestronglyMeasurable (fun y _ => abs_h4_le ha y)

/-- `∫₀^∞ g₄(y)/y dy = π/a`. -/
lemma integral_h4 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, h4 a y = Real.pi / a := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A1 a) (f' := h4 a)
      (fun y _ => hasDerivAt_A1 ha y) (integrableOn_h4 ha) (tendsto_A1_atTop ha)
  rw [h]; simp [A1]

/-! ### `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` -/

/-- The integrand `g₄(y) · y/(y² + n²)`. -/
@[expose] noncomputable def k4 (a n y : ℝ) : ℝ :=
  g4 a y * (y / (y ^ 2 + n ^ 2))

lemma abs_k4_le {a n : ℝ} (ha : 0 < a) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    |k4 a n y| ≤ 5 * a / n / (y ^ 2 + a ^ 2) := by
  unfold k4
  have h1 := abs_g4_le ha hy.le
  have h2 : y / (y ^ 2 + n ^ 2) ≤ 1 / (2 * n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (y - n)]
  have h3 : 0 ≤ y / (y ^ 2 + n ^ 2) := by positivity
  rw [abs_mul, abs_of_nonneg h3]
  calc
    |g4 a y| * (y / (y ^ 2 + n ^ 2)) ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 * (1 / (2 * n)) := by
      gcongr
    _ ≤ 10 * a ^ 3 / (a ^ 2 * (y ^ 2 + a ^ 2)) * (1 / (2 * n)) := by
      gcongr;
      nlinarith [sq_nonneg y]
    _ = 5 * a / n / (y ^ 2 + a ^ 2) := by field_simp; ring

lemma integrableOn_k4 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) : IntegrableOn (k4 a n) (Ioi 0) := by
  have hcont : Continuous (k4 a n) := by
    unfold k4
    exact
      (continuous_g4 a ha).mul
        ((by fun_prop : Continuous fun y : ℝ => y).div (by fun_prop) (fun y => by positivity))
  exact integrableOn_of_le_inv_sq ha hcont.aestronglyMeasurable (fun y hy => abs_k4_le ha hn hy)

/-- Antiderivative of `k4 a n` for `n ≠ a`; `D = a² - n²`. -/
noncomputable def A2 (a n y : ℝ) : ℝ :=
  (2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5 *
        Real.arctan (y / a) -
      (10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5 *
        Real.arctan (y / n) +
    (y ^ 7 * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4)) +
            y ^ 5 * (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
          y ^ 3 * (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
        y * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) /
      (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4)

lemma hasDerivAt_A2 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) (y : ℝ) :
    HasDerivAt (A2 a n) (k4 a n y) y := by
  have hD : a ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    have : (a - n) * (a + n) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hne (by linarith)
    · linarith
  have h1 :=
    ((hasDerivAt_id y).div_const a).arctan.const_mul
      ((2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5)
  have h2 :=
    ((hasDerivAt_id y).div_const n).arctan.const_mul
      ((10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5)
  have hne3 : 3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4 ≠ 0 := by positivity
  have hnum :=
    ((((hasDerivAt_pow 7 y).mul_const
                  (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4))).add
              ((hasDerivAt_pow 5 y).mul_const
                (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6))).add
          ((hasDerivAt_pow 3 y).mul_const
            (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6))).add
      ((hasDerivAt_id y).mul_const (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2)))
  have h3 :=
    hnum.div
      ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 4).const_mul (3 * (a ^ 2 - n ^ 2) ^ 4)) hne3
  have h := (h1.sub h2).add h3
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A2, id, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [k4, g4, id, Pi.add_apply, Pi.pow_apply]
    have hyn : y ^ 2 + n ^ 2 ≠ 0 := by positivity
    have hya : a ^ 2 + y ^ 2 ≠ 0 := by positivity
    field_simp
    ring

lemma tendsto_A2_atTop {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) :
    Tendsto (A2 a n) atTop (𝓝 (Real.pi * a ^ 4 / (a + n) ^ 5)) := by
  have hD : a ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    have : (a - n) * (a + n) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hne (by linarith)
    · linarith
  have h1 :=
    (tendsto_arctan_div_atTop ha).const_mul
      ((2 * a ^ 9 + 20 * a ^ 7 * n ^ 2 + 10 * a ^ 5 * n ^ 4) / (a ^ 2 - n ^ 2) ^ 5)
  have h2 :=
    (tendsto_arctan_div_atTop hn).const_mul
      ((10 * a ^ 8 * n + 20 * a ^ 6 * n ^ 3 + 2 * a ^ 4 * n ^ 5) / (a ^ 2 - n ^ 2) ^ 5)
  have hφ :
    Tendsto
      (fun u : ℝ =>
        u *
            (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4) +
                  u ^ 2 *
                    (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
                u ^ 4 *
                  (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
              u ^ 6 * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) /
          (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 * u ^ 2 + 1) ^ 4))
      (𝓝 0) (𝓝 0) := by
    have :
      ContinuousAt
        (fun u : ℝ =>
          u *
              (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4) +
                    u ^ 2 *
                      (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 -
                        2 * a ^ 4 * n ^ 6) +
                  u ^ 4 *
                    (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 +
                      10 * a ^ 6 * n ^ 6) +
                u ^ 6 * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) /
            (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 * u ^ 2 + 1) ^ 4))
        0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
          one_pow, mul_one, mul_eq_zero, pow_eq_zero_iff, false_or]
        positivity)
    simpa using this.tendsto
  have h3 :
    Tendsto
      (fun y : ℝ =>
        (y ^ 7 * (3 * (2 * a ^ 8 + 12 * a ^ 6 * n ^ 2 + 2 * a ^ 4 * n ^ 4)) +
                y ^ 5 *
                  (22 * a ^ 10 + 122 * a ^ 8 * n ^ 2 + 2 * a ^ 6 * n ^ 4 - 2 * a ^ 4 * n ^ 6) +
              y ^ 3 *
                (28 * a ^ 12 + 146 * a ^ 10 * n ^ 2 - 40 * a ^ 8 * n ^ 4 + 10 * a ^ 6 * n ^ 6) +
            y * (3 * (8 * a ^ 14 + 8 * a ^ 12 * n ^ 2))) /
          (3 * (a ^ 2 - n ^ 2) ^ 4 * (a ^ 2 + y ^ 2) ^ 4))
      atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := (h1.sub h2).add h3
  unfold A2
  convert this using 2
  have hsum : a + n ≠ 0 := by positivity
  have hdiff : a - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hDf : a ^ 2 - n ^ 2 = (a - n) * (a + n) := by ring
  rw [hDf]
  field_simp
  ring

/-- `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for `n ≠ a`. -/
lemma integral_k4_ne {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (hne : n ≠ a) :
    ∫ y in Ioi 0, k4 a n y = Real.pi * a ^ 4 / (a + n) ^ 5 := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A2 a n) (f' := k4 a n)
      (fun y _ => hasDerivAt_A2 ha hn hne y) (integrableOn_k4 ha hn) (tendsto_A2_atTop ha hn hne)
  rw [h]; simp [A2]

/-- Antiderivative of `k4 a a`. -/
noncomputable def A2e (a y : ℝ) : ℝ :=
  Real.arctan (y / a) / (16 * a) +
    y *
        (-15 * a ^ 8 + 730 * a ^ 6 * y ^ 2 + 32 * a ^ 4 * y ^ 4 + 70 * a ^ 2 * y ^ 6 +
          15 * y ^ 8) /
      (240 * (a ^ 2 + y ^ 2) ^ 5)

lemma hasDerivAt_A2e {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (A2e a) (k4 a a y) y := by
  have h1 := ((hasDerivAt_id y).div_const a).arctan.div_const (16 * a)
  have hne : 240 * (a ^ 2 + y ^ 2) ^ 5 ≠ 0 := by positivity
  have hnum :=
    (hasDerivAt_id y).mul
      (((((((hasDerivAt_pow 2 y).const_mul (730 * a ^ 6)).const_add (-15 * a ^ 8)).add
                ((hasDerivAt_pow 4 y).const_mul (32 * a ^ 4))).add
            ((hasDerivAt_pow 6 y).const_mul (70 * a ^ 2))).add
        ((hasDerivAt_pow 8 y).const_mul 15)))
  have h2 := hnum.div ((((hasDerivAt_pow 2 y).const_add (a ^ 2)).pow 5).const_mul 240) hne
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [A2e, id, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [k4, g4, id, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    have hya : a ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hya' : y ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring

lemma tendsto_A2e_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (A2e a) atTop (𝓝 (Real.pi * a ^ 4 / (a + a) ^ 5)) := by
  have h1 := (tendsto_arctan_div_atTop ha).div_const (16 * a)
  have hφ :
    Tendsto
      (fun u : ℝ =>
        u *
            (-15 * a ^ 8 * u ^ 8 + 730 * a ^ 6 * u ^ 6 + 32 * a ^ 4 * u ^ 4 + 70 * a ^ 2 * u ^ 2 +
              15) /
          (240 * (a ^ 2 * u ^ 2 + 1) ^ 5))
      (𝓝 0) (𝓝 0) := by
    have :
      ContinuousAt
        (fun u : ℝ =>
          u *
              (-15 * a ^ 8 * u ^ 8 + 730 * a ^ 6 * u ^ 6 + 32 * a ^ 4 * u ^ 4 +
                  70 * a ^ 2 * u ^ 2 +
                15) /
            (240 * (a ^ 2 * u ^ 2 + 1) ^ 5))
        0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    simpa using this.tendsto
  have h2 :
    Tendsto
      (fun y : ℝ =>
        y *
            (-15 * a ^ 8 + 730 * a ^ 6 * y ^ 2 + 32 * a ^ 4 * y ^ 4 + 70 * a ^ 2 * y ^ 6 +
              15 * y ^ 8) /
          (240 * (a ^ 2 + y ^ 2) ^ 5))
      atTop (𝓝 0) := by
    refine (hφ.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp]
    field_simp
  have := h1.add h2
  unfold A2e
  convert this using 2
  field_simp
  ring

/-- `∫₀^∞ g₄(y) y/(y² + a²) dy = π a⁴/(2a)⁵`. -/
lemma integral_k4_eq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi 0, k4 a a y = Real.pi * a ^ 4 / (a + a) ^ 5 := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := A2e a) (f' := k4 a a)
      (fun y _ => hasDerivAt_A2e ha y) (integrableOn_k4 ha ha) (tendsto_A2e_atTop ha)
  rw [h]; simp [A2e]

/-- `∫₀^∞ g₄(y) y/(y² + n²) dy = π a⁴/(a + n)⁵` for all `n > 0`. -/
lemma integral_k4 {a n : ℝ} (ha : 0 < a) (hn : 0 < n) :
    ∫ y in Ioi 0, k4 a n y = Real.pi * a ^ 4 / (a + n) ^ 5 := by
  rcases eq_or_ne n a with rfl | hne
  · exact integral_k4_eq ha
  · exact integral_k4_ne ha hn hne

end Zeta5Irrational
