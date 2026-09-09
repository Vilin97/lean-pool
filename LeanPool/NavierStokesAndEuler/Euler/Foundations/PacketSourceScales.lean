/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Packet Source Scales
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketSourceScales

open Real EulerScale EulerPacketScaleGeometry

/-- A fixed polynomial majorant for the dimensionless stage horizon. -/
noncomputable def sourceTheta (J : ℕ) (C : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * (1 + ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)

/-- The source upper bound for the square-root inverse parent shear. -/
noncomputable def sourceEpsilon (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The older gradient bound expressed using the quadratic recurrence. -/
noncomputable def sourceOlderGradient (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + exp (x n / (((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7))

/-- The inverse fourth root of the preceding packet frequency. -/
noncomputable def sourcePriorError (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / (4 * ((J - 1 + n : ℕ) : ℝ) ^ 4))

/-- The neighbor error with the support, frequency, and shear scales of (37). -/
noncomputable def sourceNeighborError (J : ℕ) (c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ) +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4 +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)

/-- The full coefficient error entering the normalized ray and velocity equations. -/
noncomputable def sourceCoefficientError (J : ℕ) (C c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  16 * (sourceEpsilon J x n * sourceTheta J C x n * sourceOlderGradient J x n ^ 2 +
    sourcePriorError J x n + sourceNeighborError J c x n)

/-- The horizon majorant is bounded by a single monomial. -/
theorem sourceTheta_bounds {J : ℕ} (hJ : 1 ≤ J) {C : ℝ} (hC : 1 ≤ C)
    {x : ℕ → ℝ} (hx : ∀ n, 1 ≤ x n) (n : ℕ) :
    1 ≤ sourceTheta J C x n ∧
      sourceTheta J C x n ≤ 2 * C * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjx : 1 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) (one_le_pow₀ (hx n))
  unfold sourceTheta
  have hC₀ : 0 ≤ C := by linarith
  constructor
  · nlinarith only [hC, hjx, mul_nonneg hC₀ (by nlinarith only [hjx] :
      0 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)]
  · have hh := mul_le_mul_of_nonneg_left hjx hC₀
    nlinarith only [hh]

/-- The explicit logarithmic scale comparison also allows an arbitrary
fixed polynomial prefactor. -/
theorem polynomial_source_scale_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C : ℝ) (p q : ℕ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) (hC : 0 < C) :
    Summable (fun n => C * ((J + n : ℕ) : ℝ) ^ p * (x n) ^ q *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
        c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))) := by
  have hh := source_scale_exponential_summable J d B hJ x hx0 hx A b c (log C) p q hA hAB hb
  have hxp := quadratic_growth_pos J (by omega) x hx0 hx
  apply hh.congr
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  simp only [exp_add, exp_log hC, exp_nat_mul, exp_log hj, exp_log (hxp n)]
  ring

/-- Every polynomially weighted neighbor error in (25) is summable. -/
theorem source_neighbor_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    Summable (fun n => sourceNeighborError J c x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x (by linarith) hx
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hC₀ : 0 < C := by linarith
  have hsum := polynomial_source_scale_summable J 1 4 (by omega) x (by linarith) hx
    (7 / 2) 1 (2 * c) ((2 * C) ^ A) (2 * A) (2 * A)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (exp_pos _).le (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC
        hx1 n).1) A)
  · intro n
    have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hp : (1 : ℝ) ≤ (J - 1 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 1 + n by omega)
    have hp4 : ((J - 1 + n : ℕ) : ℝ) ^ 4 ≤ ((J - 1 + n : ℕ) : ℝ) ^ 7 :=
      pow_le_pow_right₀ hp (by decide)
    have herr : sourceNeighborError J c x n ≤
        exp (-(x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
          2 * c * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 4)) := by
      unfold sourceNeighborError
      apply exp_le_exp.mpr
      have hd := div_le_div_of_nonneg_left (mul_nonneg hc (hxp n).le)
        (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 4) hp4
      simp only [div_eq_mul_inv] at hd ⊢
      nlinarith only [hd]
    have hθ := pow_le_pow_left₀ (by linarith [(sourceTheta_bounds hJ1 hC hx1 n).1] :
      0 ≤ sourceTheta J C x n) (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul herr hθ (pow_nonneg (by linarith [(sourceTheta_bounds hJ1 hC hx1 n).1]) A)
      (exp_pos _).le
    convert! hh using 1
    simp only [neg_one_mul, mul_pow, ← pow_mul]
    ring

/-- Multiplying any decaying source exponential by a fixed horizon power
preserves summability. -/
theorem theta_weighted_source_exponential_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C a b c : ℝ) (hC : 1 ≤ C) (ha : 0 ≤ a) (haB : a < B) (hb : 0 < b) (A : ℕ) :
    Summable (fun n => sourceTheta J C x n ^ A *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
        c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := polynomial_source_scale_summable J d B hJ x (by linarith) hx a b c
    ((2 * C) ^ A) (2 * A) (2 * A) ha haB hb (by positivity)
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A)
        (exp_pos _).le
  · intro n
    have hθ := pow_le_pow_left₀ (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1)
      (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul_of_nonneg_right hθ (exp_pos
      (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) + c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))).le
    convert! hh using 1
    simp only [mul_pow, ← pow_mul]

/-- The parent-frequency error is summable with every horizon power. -/
theorem source_prior_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) :
    Summable (fun n => sourcePriorError J x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := theta_weighted_source_exponential_summable J 0 5 (by omega) x hx0 hx
    C 4 (1 / 4) 0 hC (by norm_num) (by norm_num) (by norm_num) A
  simp only [rpow_ofNat, zero_mul, add_zero] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (exp_pos _).le (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC
        hx1 n).1) A)
  · intro n
    have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by exact_mod_cast (show 0 < J - 1 + n by omega)
    have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
        exact_mod_cast (show J - 1 + n ≤ J + n by omega)
    have hpow := pow_le_pow_left₀ hp.le hpj 4
    have hd := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < 4 * ((J - 1 + n : ℕ) : ℝ) ^ 4)
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
    have he : sourcePriorError J x n ≤ exp (-(1 / 4) * (x n / ((J + n : ℕ) : ℝ) ^ 4)) := by
      unfold sourcePriorError
      apply exp_le_exp.mpr
      convert! neg_le_neg hd using 1 <;> ring
    have hh := mul_le_mul_of_nonneg_right he
      (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A)
    simpa only [mul_comm] using hh

/-- The source shear/older-gradient product has an explicit decaying
exponential majorant at every normal stage after the two base exceptions. -/
theorem source_shear_gradient_bound
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    sourceEpsilon J x n * sourceOlderGradient J x n ^ 2 ≤
      8 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7) +
        2 * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9)) := by
  have ho : (1 : ℝ) ≤ (J - 2 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 2 + n by omega)
  have hop : ((J - 2 + n : ℕ) : ℝ) ≤ ((J - 1 + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 2 + n ≤ J - 1 + n by omega)
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := lt_of_lt_of_le (by
      linarith : (0 : ℝ) < (J - 2 + n : ℕ)) hop
  have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 1 + n ≤ J + n by omega)
  have hpow := pow_le_pow_left₀ hp.le hpj 7
  have hd := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < 2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
  have he : sourceEpsilon J x n ≤ 2 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply exp_le_exp.mpr
    convert! neg_le_neg hd using 1 <;> ring
  have hden : ((J - 2 + n : ℕ) : ℝ) ^ 9 ≤
      ((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one ho) hop 2)
      (by positivity : 0 ≤ ((J - 2 + n : ℕ) : ℝ) ^ 7)
    simpa only [← pow_add] using hh
  have hdG := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < ((J - 2 + n : ℕ) : ℝ) ^ 9) hden
  have hg : sourceOlderGradient J x n ≤ 2 * exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) := by
    have hle := exp_le_exp.mpr hdG
    have h1 : 1 ≤ exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) :=
      one_le_exp_iff.mpr (div_nonneg (hx n) (by positivity))
    unfold sourceOlderGradient
    linarith
  have hg₀ : 0 ≤ sourceOlderGradient J x n := by unfold sourceOlderGradient; positivity
  have hh := mul_le_mul he (pow_le_pow_left₀ hg₀ hg 2) (sq_nonneg _) (by positivity)
  convert! hh using 1
  rw [exp_add, show (2 : ℝ) * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) =
    x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 + x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 by ring, exp_add]
  ring

/-- The change of the parent shear and older coefficients obeys every
polynomial smallness regime required by the ray analysis. -/
theorem source_shear_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) :
    Summable (fun n => sourceEpsilon J x n * sourceTheta J C x n *
      sourceOlderGradient J x n ^ 2 * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := (theta_weighted_source_exponential_summable J 2 9 (by omega) x hx0 hx
    C 7 (1 / 2) 2 hC (by norm_num) (by norm_num) (by norm_num) (A + 1)).mul_left 8
  simp only [rpow_ofNat] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    have hθ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold sourceEpsilon sourceOlderGradient
    positivity
  · intro n
    have hh := mul_le_mul_of_nonneg_right
      (source_shear_gradient_bound J hJ x (fun m => le_trans zero_le_one (hx1 m)) n)
      (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) (A + 1))
    convert! hh using 1 <;> simp only [pow_succ] <;> ring

/-- The complete error specified by the logarithmic scales is summable
after multiplication by any fixed horizon power. -/
theorem source_coefficient_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    Summable (fun n => sourceCoefficientError J C c x n * sourceTheta J C x n ^ A) := by
  have hh := (((source_shear_error_summable J hJ x hx0 hx C hC A).add
    (source_prior_error_summable J hJ x hx0 hx C hC A)).add
    (source_neighbor_error_summable J hJ x hx0 hx C c hC hc A)).mul_left 16
  convert! hh using 1
  ext n
  unfold sourceCoefficientError
  ring

/-- In particular the actual source scales eventually satisfy the
quantitative `Θ^40` guard needed by the complete ODE frame analysis. -/
theorem source_coefficient_error_eventually_small
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c K : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) :
    ∀ᶠ n in atTop, 1000000 * K * sourceCoefficientError J C c x n * sourceTheta J C x n ^ 40 ≤ 1 :=
        by
  have hh := (source_coefficient_error_summable J hJ x hx0 hx C c hC hc
      40).tendsto_atTop_zero.const_mul
    (1000000 * K)
  simp only [mul_zero] at hh
  have hh' := hh.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh'] with n hn
  nlinarith only [hn]

end EulerPacketSourceScales
