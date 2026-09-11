/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleSums
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The literal sequences in (37), including the polynomial initial shear and
frequency.  Their first two exceptional stages are retained explicitly.
-/

section

/-!
Pointwise bounds for the literal scale expressions in (37)--(39).  They
exhibit a finite list of exponential costs to which the existing uniform
scale-choice theorem applies.  The estimates here contain no field data.
-/

section

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
  · linarith only [hC, hjx, mul_nonneg hC₀ (by linarith only [hjx] :
      0 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)]
  · have hh := mul_le_mul_of_nonneg_left hjx hC₀
    linarith only [hh]

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
      linarith only [hd]
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
  linarith only [hn]

end EulerPacketSourceScales

end
end

end

section

/-!
# Packet Source Time
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketSourceTime

open Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales

/-- The preceding two shear logarithms are exactly those obtained by
substituting the quadratic recurrence into (37). -/
theorem preceding_scale_identities {p q x X Y : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hx : x = p ^ 2 * X) (hX : X = q ^ 2 * Y) :
    X / p ^ 5 = x / p ^ 7 ∧ Y / q ^ 5 = x / (p ^ 2 * q ^ 7) := by
  constructor
  · rw [hx]
    field_simp
  · rw [hx, hX]
    field_simp

/-- A frame normalization `a≤2` gives the explicit source epsilon bound. -/
theorem epsilon_of_shear_bound {a L : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    sqrt (a / exp L) ≤ 2 * exp (-L / 2) := by
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  rw [sqrt_div ha, ← exp_half]
  have hid : -L / 2 = -(L / 2) := by ring
  rw [hid, exp_neg]
  change sqrt a / exp (L / 2) ≤ 2 / exp (L / 2)
  exact div_le_div_of_nonneg_right hs (exp_pos (L / 2)).le

/-- The current time width in (37), after exact substitution of the scales. -/
noncomputable def sourceTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 *
    exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The following time width, using `x_j=j²x_{j-1}` twice. -/
noncomputable def sourceNextTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))

/-- The exact quotient of consecutive time widths. -/
noncomputable def sourceTimeRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) +
      x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- Exact cancellation computes the consecutive time-width quotient. -/
theorem source_time_ratio_identity (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    sourceNextTimeWidth J x n = sourceTimeRatio J x n * sourceTimeWidth J x n := by
  unfold sourceNextTimeWidth sourceTimeRatio sourceTimeWidth
  rw [exp_add]
  have hc : exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) = 1 := by
    rw [← exp_add]
    convert! exp_zero using 1
    ring_nf
  linear_combination -(3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 *
    (x n) ^ 2 * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) * hc

/-- Consecutive time-width ratios are summable, so they tend to zero. -/
theorem source_time_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (sourceTimeRatio J x) := by
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) 4 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, pow_zero, mul_one] at hsum
  apply hsum.of_nonneg_of_le
  · intro n; unfold sourceTimeRatio; positivity
  · intro n
    have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hj]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ((J + n : ℕ) : ℝ))
    have hh' := mul_le_mul_of_nonneg_right hh (exp_pos
      (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))).le
    unfold sourceTimeRatio
    have hid : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) + (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by
          ring
    rw [hid] at hh' ⊢
    convert! hh' using 1
    ring

/-- The actual next time width is eventually at most half of the current width. -/
theorem source_time_width_eventually_contracts
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ᶠ n in atTop, sourceNextTimeWidth J x n ≤ sourceTimeWidth J x n / 2 := by
  have hh := (source_time_ratio_summable J hJ x hx0 hx).tendsto_atTop_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hh] with n hn
  rw [source_time_ratio_identity]
  have hW : 0 ≤ sourceTimeWidth J x n := by unfold sourceTimeWidth; positivity
  have hb := mul_le_mul_of_nonneg_right hn hW
  linarith only [hb]

/-- The extra normalized horizon length has the explicit polynomial/exponential
bound asserted after (39). -/
theorem source_extra_time_bound
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) * sourceNextTimeWidth J x n ≤
      48 * ((J + n : ℕ) : ℝ) ^ 6 * (x n) ^ 2 *
        exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) +
          (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hroot : sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) ≤
      2 * exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
    rw [sqrt_mul ha, ← exp_half]
    have hh := mul_le_mul_of_nonneg_right hs (exp_pos ((x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) / 2)).le
    convert! hh using 1
    congr 2
    ring
  have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by nlinarith only [hj]
  have hW : 0 ≤ sourceNextTimeWidth J x n := by unfold sourceNextTimeWidth; positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by
      norm_num : (0 : ℝ) ≤ 2)) hW
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 12 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5)))
  unfold sourceNextTimeWidth at hh
  have hpE : x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by ring
  have hnE : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) := by ring
  rw [hpE, hnE] at hh hp'
  rw [exp_add]
  change 2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
    (3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) ≤ _
  rw [hnE]
  refine hh.trans ?_
  convert! hp' using 1 <;> ring

/-- Every horizon power times the extra normalized length is summable. -/
theorem source_extra_time_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2) :
    Summable (fun n => 2 * sqrt (a n * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      sourceNextTimeWidth J x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) (48 * (2 * C) ^ A) (6 + 2 * A) (2 + 2 * A)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  simp only [rpow_ofNat] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    have hθ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold sourceNextTimeWidth
    positivity
  · intro n
    have hθ₀ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    have hθ := pow_le_pow_left₀ hθ₀ (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul (source_extra_time_bound J hJ1 x n (ha n) (ha₂ n)) hθ
      (pow_nonneg hθ₀ A) (by positivity)
    convert! hh using 1
    simp only [mul_pow, pow_add, ← pow_mul]
    ring

/-- The parent-shear square is negligible relative to the newly chosen shear. -/
theorem source_parent_shear_square_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (2 * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) /
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5)) := by
  have hh := source_scale_exponential_summable J 1 7 (by omega) x (by linarith) hx
    5 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hh
  apply hh.congr
  intro n
  rw [← exp_sub]
  congr 1
  ring

/-- The good-interval pressure costs of the source are summable. -/
theorem source_good_interval_cost_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (-x n / ((J + n : ℕ) : ℝ) ^ 3) *
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5) *
      exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hsum := source_scale_exponential_summable J 1 5 (by omega) x (by linarith) hx
    3 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hsum
  have hx1 := quadratic_growth_one_le J (by omega) x hx0 hx
  apply hsum.of_nonneg_of_le
  · intro n; positivity
  · intro n
    have hp : (1 : ℝ) ≤ (J - 1 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 1 + n by omega)
    have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
        exact_mod_cast (show J - 1 + n ≤ J + n by omega)
    have hd₁ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_left₀ (by linarith) hpj 5)
    have hd₂ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hd₁ hd₂ ⊢
    linarith only [hd₁, hd₂]

end EulerPacketSourceTime

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceScaleBounds

open Real EulerPacketSourceScales EulerPacketSourceTime

/-- Monomial cost, given by `C * ((J + n : ℕ) : ℝ)^p * (x n)^q * exp (-b * (x n / ((J + n : ℕ) :
ℝ)^a) + c * (x n / ((J - d + n : ℕ) : ℝ)^B))`. -/
def monomialCost (J d B : ℕ) (a b c C : ℝ) (p q : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * ((J + n : ℕ) : ℝ)^p * (x n)^q *
    exp (-b * (x n / ((J + n : ℕ) : ℝ)^a) +
      c * (x n / ((J - d + n : ℕ) : ℝ)^B))

theorem monomialCost_nonneg (J d B : ℕ) (a b c C : ℝ) (p q : ℕ)
    (x : ℕ → ℝ) (n : ℕ) (hC : 0 ≤ C) (hx : 0 ≤ x n) :
    0 ≤ monomialCost J d B a b c C p q x n := by
  unfold monomialCost
  positivity

theorem monomialCost_eq_exp (J d B : ℕ) (a b c C : ℝ) (p q : ℕ)
    (x : ℕ → ℝ) (n : ℕ) (hJ : 1 ≤ J) (hC : 0 < C) (hx : 0 < x n) :
    monomialCost J d B a b c C p q x n =
      exp (-b * (x n / ((J + n : ℕ) : ℝ)^a) +
        c * (x n / ((J - d + n : ℕ) : ℝ)^B) +
        log C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)) := by
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  simp only [monomialCost, exp_add, exp_log hC, exp_nat_mul, exp_log hj, exp_log hx]
  ring

theorem theta_weighted_monomial_bound
    (J d B : ℕ) (a b c D C : ℝ) (p q A : ℕ) (x : ℕ → ℝ) (n : ℕ)
    (hJ : 1 ≤ J) (hC : 1 ≤ C) (hD : 0 ≤ D) (hx : ∀ n, 1 ≤ x n) :
    monomialCost J d B a b c D p q x n * sourceTheta J C x n^A ≤
      monomialCost J d B a b c (D*(2*C)^A) (p+2*A) (q+2*A) x n := by
  have hθ := pow_le_pow_left₀ (le_trans zero_le_one (sourceTheta_bounds hJ hC hx n).1)
    (sourceTheta_bounds hJ hC hx n).2 A
  have hh := mul_le_mul_of_nonneg_left hθ
    (monomialCost_nonneg J d B a b c D p q x n hD (le_trans zero_le_one (hx n)))
  convert! hh using 1
  simp only [monomialCost, mul_pow, pow_add, ← pow_mul]
  ring

theorem sourcePriorError_bound (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (n : ℕ)
    (hx : 0 ≤ x n) :
    sourcePriorError J x n ≤ exp (-(1/4)*(x n/((J+n : ℕ) : ℝ)^4)) := by
  have hp : (0 : ℝ) < (J-1+n : ℕ) := by exact_mod_cast (show 0 < J-1+n by omega)
  have hpj : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hd := div_le_div_of_nonneg_left hx
    (show 0 < 4*((J-1+n : ℕ) : ℝ)^4 by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hpj 4) (by norm_num : (0:ℝ) ≤ 4))
  apply exp_le_exp.mpr
  change -x n/(4*((J-1+n : ℕ) : ℝ)^4) ≤ _
  convert! neg_le_neg hd using 1 <;> ring

theorem sourceNeighborError_bound (J : ℕ) (hJ : 3 ≤ J) (c : ℝ) (hc : 0 ≤ c)
    (x : ℕ → ℝ) (n : ℕ) (hx : 0 ≤ x n) :
    sourceNeighborError J c x n ≤
      exp (-(x n/((J+n : ℕ) : ℝ)^(7/2 : ℝ)) +
        (2*c)*(x n/((J-1+n : ℕ) : ℝ)^4)) := by
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hd := div_le_div_of_nonneg_left (mul_nonneg hc hx)
    (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^4)
    (pow_le_pow_right₀ hp (by decide : 4 ≤ 7))
  unfold sourceNeighborError
  apply exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hd ⊢
  linarith only [hd]

/-- The complete coefficient error is controlled by three explicit costs,
with exactly the preceding-stage powers and the real support exponent 7/2. -/
theorem sourceCoefficientError_bound (J : ℕ) (hJ : 3 ≤ J) (C c : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ) :
    sourceCoefficientError J C c x n * sourceTheta J C x n^A ≤
      monomialCost J 2 9 7 (1/2) 2 (128*(2*C)^(A+1)) (2*(A+1)) (2*(A+1)) x n +
      monomialCost J 0 5 4 (1/4) 0 (16*(2*C)^A) (2*A) (2*A) x n +
      monomialCost J 1 4 (7/2) 1 (2*c) (16*(2*C)^A) (2*A) (2*A) x n := by
  have hJ1 : 1 ≤ J := by omega
  have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx n).1
  have hxp : ∀ n, 0 ≤ x n := fun n => le_trans zero_le_one (hx n)
  have hs := mul_le_mul_of_nonneg_right
    (source_shear_gradient_bound J hJ x hxp n) (pow_nonneg hθ (A+1))
  have hs16 := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 16)
  have hsm := theta_weighted_monomial_bound J 2 9 7 (1/2) 2 128 C 0 0 (A+1) x n hJ1 hC
    (by norm_num) hx
  have hshear : 16*(sourceEpsilon J x n*sourceTheta J C x n*sourceOlderGradient J x n^2) *
      sourceTheta J C x n^A ≤
      monomialCost J 2 9 7 (1/2) 2 (128*(2*C)^(A+1)) (2*(A+1)) (2*(A+1)) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hsm)
    convert! hs16 using 1 <;> simp only [monomialCost, rpow_ofNat, pow_zero, mul_one, pow_succ] <;>
        ring
  have hp := mul_le_mul_of_nonneg_right
    (sourcePriorError_bound J hJ x n (hxp n)) (pow_nonneg hθ A)
  have hp16 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 16)
  have hpm := theta_weighted_monomial_bound J 0 5 4 (1/4) 0 16 C 0 0 A x n hJ1 hC
    (by norm_num) hx
  have hprior : 16*sourcePriorError J x n*sourceTheta J C x n^A ≤
      monomialCost J 0 5 4 (1/4) 0 (16*(2*C)^A) (2*A) (2*A) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hpm)
    simpa only [monomialCost, rpow_ofNat, zero_mul, add_zero, pow_zero, mul_one, mul_assoc] using
        hp16
  have hn := mul_le_mul_of_nonneg_right
    (sourceNeighborError_bound J hJ c hc x n (hxp n)) (pow_nonneg hθ A)
  have hn16 := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ) ≤ 16)
  have hnm := theta_weighted_monomial_bound J 1 4 (7/2) 1 (2*c) 16 C 0 0 A x n hJ1 hC
    (by norm_num) hx
  have hneighbor : 16*sourceNeighborError J c x n*sourceTheta J C x n^A ≤
      monomialCost J 1 4 (7/2) 1 (2*c) (16*(2*C)^A) (2*A) (2*A) x n := by
    apply le_trans _ (by simpa only [Nat.zero_add] using hnm)
    simpa only [monomialCost, neg_one_mul, pow_zero, mul_one, mul_assoc] using hn16
  have hh := add_le_add (add_le_add hshear hprior) hneighbor
  convert! hh using 1
  unfold sourceCoefficientError
  ring

theorem sourceExtraTime_bound (J : ℕ) (hJ : 1 ≤ J) (C : ℝ) (hC : 1 ≤ C)
    (A : ℕ) (x : ℕ → ℝ) (hx : ∀ n, 1 ≤ x n) (n : ℕ)
    (a : ℝ) (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2*sqrt (a*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J x n *
      sourceTheta J C x n^A ≤
      monomialCost J 1 7 5 (1/2) (1/2) (48*(2*C)^A) (6+2*A) (2+2*A) x n := by
  have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ hC hx n).1
  have hh := mul_le_mul_of_nonneg_right (source_extra_time_bound J hJ x n ha ha₂) (pow_nonneg hθ A)
  have hm := theta_weighted_monomial_bound J 1 7 5 (1/2) (1/2) 48 C 6 2 A x n hJ hC (by norm_num) hx
  apply le_trans hh
  simpa only [monomialCost, rpow_ofNat] using hm

theorem sourceTimeRatio_bound (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) :
    sourceTimeRatio J x n ≤ monomialCost J 1 7 5 (1/2) (1/2) 4 4 0 x n := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  have hp : (((J+n : ℕ) : ℝ)+1)^2 ≤ 4*((J+n : ℕ) : ℝ)^2 := by nlinarith only [hj]
  have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ((J+n : ℕ) : ℝ))
  have he := mul_le_mul_of_nonneg_right hh
    (exp_pos (-x n/(2*((J+n : ℕ) : ℝ)^5)+x n/(2*((J-1+n : ℕ) : ℝ)^7))).le
  have hexp : exp (-x n/(2*((J+n : ℕ) : ℝ)^5)+x n/(2*((J-1+n : ℕ) : ℝ)^7)) =
      exp (-(1/2)*(x n/((J+n : ℕ) : ℝ)^5)+(1/2)*(x n/((J-1+n : ℕ) : ℝ)^7)) := by
    congr 1
    ring
  rw [hexp] at he
  convert! he using 1 <;> simp only [sourceTimeRatio, monomialCost, rpow_ofNat, pow_zero, mul_one]
  · rw [hexp]
  · ring

theorem sourceParentSquareRatio_eq (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5) =
      monomialCost J 1 7 5 1 2 1 0 0 x n := by
  rw [← exp_sub]
  simp only [monomialCost, pow_zero, mul_one, one_mul, neg_one_mul, rpow_ofNat]
  congr 1
  ring

theorem sourceGoodCost_bound (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (n : ℕ) (hx : 0 ≤ x n) :
    exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5) *
      exp (x n/((J-1+n : ℕ) : ℝ)^7) ≤ monomialCost J 1 5 3 1 2 1 0 0 x n := by
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hpj : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hd₁ := div_le_div_of_nonneg_left hx (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^5)
    (pow_le_pow_left₀ (le_trans zero_le_one hp) hpj 5)
  have hd₂ := div_le_div_of_nonneg_left hx (by positivity : 0 < ((J-1+n : ℕ) : ℝ)^5)
    (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))
  rw [← exp_add, ← exp_add]
  simp only [monomialCost, pow_zero, mul_one, one_mul, neg_one_mul, rpow_ofNat]
  apply exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hd₁ hd₂ ⊢
  linarith only [hd₁, hd₂]

end EulerPacketSourceScaleBounds

end
end

end

section

/-!
A common choice of the starting stage and base scale for the concrete
coefficient, time-width, and pressure costs in the outer construction.
-/

section

/-!
# Packet Uniform Scale Choice
-/

section

/-!
# Packet Uniform Log Bounds
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformLogBounds

open Real EulerScale EulerPacketUniformScaleSums

/-- Every fixed polynomial logarithm is bounded by a simple product of
the stage and the square root of the scale. -/
theorem polynomial_log_bound {j X C p q : ℝ} (hj : 1 ≤ j) (hX : 1 ≤ X) :
    C + p * log j + q * log X ≤ (|C| + |p| + 2 * |q|) * j * sqrt X := by
  have hjp : 0 < j := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ sqrt X := one_le_sqrt.mpr hX
  have hsj : 1 ≤ j * sqrt X := one_le_mul_of_one_le_of_one_le hj hs
  have hlj : 0 ≤ log j := log_nonneg hj
  have hlX : 0 ≤ log X := log_nonneg hX
  have hljb : log j ≤ j := (log_le_sub_one_of_pos hjp).trans (by linarith)
  have hlXb : log X ≤ 2 * sqrt X := by
    have hh := log_le_sub_one_of_pos (sqrt_pos.mpr hXp)
    rw [log_sqrt hXp.le] at hh
    linarith
  have hCb : C ≤ |C| * j * sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hsj (abs_nonneg C)
    linarith only [hh, le_abs_self C]
  have hp₁ := mul_le_mul_of_nonneg_right (le_abs_self p) hlj
  have hp₂ := mul_le_mul_of_nonneg_left hljb (abs_nonneg p)
  have hp₃ := mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg p) hjp.le)
  have hq₁ := mul_le_mul_of_nonneg_right (le_abs_self q) hlX
  have hq₂ := mul_le_mul_of_nonneg_left hlXb (abs_nonneg q)
  have hq₃ := mul_le_mul_of_nonneg_right hj (mul_nonneg (by
      positivity : 0 ≤ 2 * |q|) (sqrt_nonneg X))
  linarith only [hCb, hp₁, hp₂, hp₃, hq₁, hq₂, hq₃]

/-- A single explicit lower bound on the initial scale absorbs the
polynomial logarithms at every subsequent quadratic stage. -/
theorem polynomial_logs_uniformly_absorbed
    (J A : ℕ) (hJ : 1 ≤ J)
    (hJA : (2 : ℝ) ^ (2 * A + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C p q b : ℝ) (hb : 0 < b)
    (hlarge : (2 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * A + 2) ≤ x 0) :
    ∀ n, C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
  let S := |C| + |p| + 2 * |q|
  let L := 2 * S / b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hgeom := polynomial_scale_geometric_lower J (2 * A + 2) hJ
    (by simpa only [show 2 * A + 2 + 1 = 2 * A + 3 by omega] using hJA) x (by linarith) hx
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hstart : L ^ 2 ≤ x 0 / (J : ℝ) ^ (2 * A + 2) := by
    apply (le_div_iff₀ (pow_pos hJp _)).2
    exact hlarge
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hone
    (div_nonneg (le_trans zero_le_one hx0) (pow_nonneg hJp.le (2 * A + 2)))
  have hscale : L ^ 2 ≤ x n / ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
    linarith only [hstart, hbase, hgeom n]
  have hsquare := (le_div_iff₀ (pow_pos hj (2 * A + 2))).mp hscale
  have hroot : L * ((J + n : ℕ) : ℝ) ^ (A + 1) ≤ sqrt (x n) := by
    have hp : (((J + n : ℕ) : ℝ) ^ (A + 1)) ^ 2 = ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hs := sq_sqrt (le_trans zero_le_one (hx1 n))
    have hn : 0 ≤ L * ((J + n : ℕ) : ℝ) ^ (A + 1) := by positivity
    nlinarith only [hsquare, hp, hs, hn, sqrt_nonneg (x n)]
  have hlog := polynomial_log_bound (C := C) (p := p) (q := q) hj1 (hx1 n)
  have hlogmul := mul_le_mul_of_nonneg_right hlog (pow_nonneg hj.le A)
  have hrootmul := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg (div_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)) (sqrt_nonneg (x n)))
  have hLS : (b / 2) * L = S := by dsimp [L]; field_simp
  have hid : (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) =
      ((b / 2) * x n) / ((J + n : ℕ) : ℝ) ^ A := by ring
  rw [hid]
  apply (le_div_iff₀ (pow_pos hj A)).2
  have hmul : S * ((J + n : ℕ) : ℝ) ^ (A + 1) * sqrt (x n) ≤ (b / 2) * x n := by
    calc
      _ = (L * ((J + n : ℕ) : ℝ) ^ (A + 1)) * ((b / 2) * sqrt (x n)) := by rw [← hLS]; ring
      _ ≤ sqrt (x n) * ((b / 2) * sqrt (x n)) := hrootmul
      _ = (b / 2) * (sqrt (x n)) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt (le_trans zero_le_one (hx1 n))]
  rw [pow_succ] at hmul
  dsimp only [S] at hmul
  linarith only [hlogmul, hmul]

end EulerPacketUniformLogBounds

end
end

end

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleChoice

open Real EulerScale EulerPacketScaleGeometry EulerPacketUniformScaleSums
    EulerPacketUniformLogBounds

/-- One sufficiently large initial stage makes every predecessor-log
coefficient small, uniformly over all subsequent stages. -/
theorem exists_uniform_stage_choice (d B N : ℕ) (a c b : ℝ)
    (haB : a < B) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ d < J ∧ (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2 ∧
      ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4 := by
  have hh := (stage_rpow_div_shifted_power_tendsto_zero (d + 1) d B (by omega) a haB).const_mul c
  simp only [mul_zero] at hh
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hh.eventually_le_const (by positivity : (0 : ℝ) < b / 4))
  let R : ℕ := 2 ^ (2 * N + 3) + 3
  let J : ℕ := (d + 1) + M + R
  have hR3 : 3 ≤ R := Nat.le_add_left 3 _
  have hJ3 : 3 ≤ J := by dsimp [J]; omega
  have hdJ : d < J := by dsimp [J]; omega
  have hpJ : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) := by
    exact_mod_cast (show 2 ^ (2 * N + 3) ≤ J by dsimp [J, R]; omega)
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  refine ⟨J, hJ3, hdJ, by nlinarith only [hpJ, hJr], ?_⟩
  intro n
  have h := hM (M + R + n) (by omega)
  have hj : d + 1 + (M + R + n) = J + n := by dsimp [J]; omega
  have hp : d + 1 - d + (M + R + n) = J - d + n := by dsimp [J]; omega
  simpa only [hj, hp] using h

/-- For a stage chosen above, one explicit lower bound on the initial
scale controls all logarithmic scale errors at once. -/
theorem uniform_source_exponent_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    ∀ n, -b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      -(b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ N) := by
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hlog := polynomial_logs_uniformly_absorbed J N hJ hJN x hx0 hx C p q (b / 2)
    (by positivity) (by convert! hlarge using 1; ring)
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
  have hxn : 0 < x n := by linarith [hx1 n]
  have hpow : ((J + n : ℕ) : ℝ) ^ a ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 haN
  have hscales := div_le_div_of_nonneg_left hxn.le (rpow_pos_of_pos hj a) hpow
  have hcm := mul_le_mul_of_nonneg_right (hcoeff n)
    (div_nonneg hxn.le (rpow_nonneg hj.le a))
  have hct : c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) ≤
      (b / 4) * (x n / ((J + n : ℕ) : ℝ) ^ a) := by
    convert! hcm using 1
    field_simp [(rpow_pos_of_pos hj a).ne', hp.ne']
  have hscaleB := mul_le_mul_of_nonneg_left hscales hb.le
  have hl := hlog n
  linarith only [hct, hscaleB, hl]

/-- The complete logarithmic source cost has a uniform geometric-series
bound after choosing the stage and then the initial scale. -/
theorem uniform_source_cost_tsum_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤
      exp (-(b / 2) * (x 0 / (J : ℝ) ^ N)) /
        (1 - exp (-(b / 2) * (x 0 / (J : ℝ) ^ N))) := by
  have hmajor := fun n => exp_le_exp.mpr
    (uniform_source_exponent_bound J d B N hJ hdJ hJN x hx0 hx a b c C p q haN hb hcoeff hlarge n)
  have hsum := exponential_decay_summable J hJ x (by linarith) hx N (b / 2) (by positivity)
  have hcost := hsum.of_nonneg_of_le (fun _ => (exp_pos _).le) hmajor
  have hh := hcost.tsum_le_tsum hmajor hsum
  have hpower : (2 : ℝ) ^ (N + 1) ≤ (J : ℝ) ^ 2 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : N + 1 ≤ 2 * N + 3)).trans hJN
  exact hh.trans (source_exponential_tsum_bound J N hJ hpower x (by
      linarith) hx (b / 2) (by positivity))

/-- The source's order of parameter choice is valid: first one chooses
the stage `J`, then the base scale `x₀`, and the whole infinite sum is
arbitrarily small. This includes the real support exponent `7/2`. -/
theorem source_uniform_small_sum_choice
    (d B N : ℕ) (a b c C p q : ℝ) (haB : a < B) (haN : a ≤ N) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) →
        (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
          c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
          C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤ δ := by
  obtain ⟨J, hJ3, hdJ, hJN, hcoeff⟩ := exists_uniform_stage_choice d B N a c b haB hb
  have hJ : 1 ≤ J := by omega
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hh := source_exponential_bound_tendsto_zero J N hJ (b / 2) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (hh.eventually_le_const hδ)
  let L := (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2)
  let X₀ := max 1 (max L Y)
  have hX₀ : 1 ≤ X₀ := le_max_left _ _
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx0 hx
  have hx1 : 1 ≤ x 0 := hX₀.trans hx0
  have hlarge : L ≤ x 0 := (le_trans (le_max_left L Y) (le_max_right 1 (max L Y))).trans hx0
  have hYx : Y ≤ x 0 := (le_trans (le_max_right L Y) (le_max_right 1 (max L Y))).trans hx0
  exact (uniform_source_cost_tsum_bound J d B N hJ hdJ hJN x hx1 hx a b c C p q
    haN hb hcoeff hlarge).trans (hY (x 0) hYx)

end EulerPacketUniformScaleChoice

end
end

end

section

/-!
# Packet Finite Scale Choice
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketFiniteScaleChoice

open Real EulerPacketUniformScaleChoice EulerPacketUniformScaleSums

/-- Every finite collection of scale inequalities allows the same
choices of `J` and then `x₀`. Thus the source's different coefficient,
neighbor, time, and pressure-cost requirements can be imposed together. -/
theorem finite_source_uniform_small_sum_choice
    {ι : Type*} [Finite ι] (d B N : ι → ℕ) (a b c C p q : ι → ℝ)
    (haB : ∀ i, a i < B i) (haN : ∀ i, a i ≤ N i) (hb : ∀ i, 0 < b i) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) → ∀ i,
        (∑' n, exp (-(b i) * (x n / ((J + n : ℕ) : ℝ) ^ (a i)) +
          c i * (x n / ((J - d i + n : ℕ) : ℝ) ^ (B i)) +
          C i + p i * log ((J + n : ℕ) : ℝ) + q i * log (x n))) ≤ δ := by
  classical
  let := Fintype.ofFinite ι
  classical
  choose Ji hJi3 hJid hJiN hJiC using fun i =>
    exists_uniform_stage_choice (d i) (B i) (N i) (a i) (c i) (b i) (haB i) (hb i)
  let J := max 3 (Finset.univ.sup Ji)
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJ1 : 1 ≤ J := by omega
  have hJiLe (i : ι) : Ji i ≤ J :=
    (Finset.le_sup (f := Ji) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hdJ (i : ι) : d i < J := lt_of_lt_of_le (hJid i) (hJiLe i)
  have hJN (i : ι) : (2 : ℝ) ^ (2 * N i + 3) ≤ (J : ℝ) ^ 2 := by
    exact (hJiN i).trans (pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast hJiLe i) 2)
  have hcoeff (i : ι) (n : ℕ) :
      c i * (((J + n : ℕ) : ℝ) ^ (a i) / ((J - d i + n : ℕ) : ℝ) ^ (B i)) ≤ b i / 4 := by
    have hh := hJiC i (J - Ji i + n)
    have hj : Ji i + (J - Ji i + n) = J + n := by have hi := hJiLe i; omega
    have hp : Ji i - d i + (J - Ji i + n) = J - d i + n := by
      have hi := hJiLe i
      have hid := hJid i
      omega
    simpa only [hj, hp] using hh
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hboth : ∀ᶠ X : ℝ in atTop, ∀ i : ι,
      (4 * (|C i| + |p i| + 2 * |q i|) / b i) ^ 2 * (J : ℝ) ^ (2 * N i + 2) ≤ X ∧
      exp (-(b i / 2) * (X / (J : ℝ) ^ N i)) /
        (1 - exp (-(b i / 2) * (X / (J : ℝ) ^ N i))) ≤ δ := by
    apply eventually_all.2
    intro i
    have hi := source_exponential_bound_tendsto_zero J (N i) hJ1 (b i / 2)
      (div_pos (hb i) (by norm_num))
    exact (eventually_ge_atTop _).and (hi.eventually_le_const hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hboth
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hx1 : 1 ≤ x 0 := (le_max_left 1 X).trans hx0
  have hall := hX (x 0) ((le_max_right 1 X).trans hx0) i
  exact (uniform_source_cost_tsum_bound J (d i) (B i) (N i) hJ1 (hdJ i) (hJN i)
    x hx1 hx (a i) (b i) (c i) (C i) (p i) (q i) (haN i) (hb i) (hcoeff i) hall.1).trans hall.2

end EulerPacketFiniteScaleChoice

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceScaleChoice

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
   EulerPacketFiniteScaleChoice EulerPacketSourceScaleBounds

open scoped Topology

/-- Cost spec data, collecting `d`, `B`, `N`, `a`, `b`, `c` and their compatibility conditions. -/
structure CostSpec where
  /-- D of `CostSpec`, of type `ℕ`. -/
  d : ℕ
  /-- Bound parameter of `CostSpec`, of type `ℕ`. -/
  B : ℕ
  /-- Truncation order of `CostSpec`, of type `ℕ`. -/
  N : ℕ
  /-- A of `CostSpec`, of type `ℝ`. -/
  a : ℝ
  /-- B of `CostSpec`, of type `ℝ`. -/
  b : ℝ
  /-- C of `CostSpec`, of type `ℝ`. -/
  c : ℝ
  /-- Bound coefficient of `CostSpec`, of type `ℝ`. -/
  C : ℝ
  /-- P of `CostSpec`, of type `ℕ`. -/
  p : ℕ
  /-- Q of `CostSpec`, of type `ℕ`. -/
  q : ℕ
  d_le_two : d ≤ 2
  a_nonneg : 0 ≤ a
  a_lt_B : a < B
  a_le_N : a ≤ N
  b_pos : 0 < b
  C_pos : 0 < C

/-- Cost, given by `monomialCost J s.d s.B s.a s.b s.c s.C s.p s.q x`. -/
def CostSpec.cost (s : CostSpec) (J : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  monomialCost J s.d s.B s.a s.b s.c s.C s.p s.q x

/-- A finite list of literal exponential costs has summable, uniformly
small terms and a small total, using one fixed stage and then one base scale. -/
theorem finite_uniform_choice {ι : Type*} [Finite ι] (s : ι → CostSpec) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n+1) = ((J+n : ℕ) : ℝ)^2*x n) →
        ∀ i, Summable ((s i).cost J x) ∧
          (∑' n, (s i).cost J x n) ≤ δ ∧ ∀ n, (s i).cost J x n ≤ δ := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨J, hJ, hchoice⟩ := finite_source_uniform_small_sum_choice
    (fun i => (s i).d) (fun i => (s i).B) (fun i => (s i).N)
    (fun i => (s i).a) (fun i => (s i).b) (fun i => (s i).c)
    (fun i => log (s i).C) (fun i => ((s i).p : ℝ)) (fun i => ((s i).q : ℝ))
    (fun i => (s i).a_lt_B) (fun i => (s i).a_le_N) (fun i => (s i).b_pos)
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice δ hδ
  refine ⟨max 8 X₀, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hstart : X₀ ≤ x 0 := (le_max_right _ _).trans hx0
  have hxp := quadratic_growth_pos J (by omega) x (lt_of_lt_of_le zero_lt_one (hX₀.trans hstart)) hx
  have hdJ : (s i).d < J := lt_of_le_of_lt (s i).d_le_two (by omega)
  have hsum : Summable ((s i).cost J x) :=
    polynomial_source_scale_summable J (s i).d (s i).B hdJ x (hxp 0) hx
      (s i).a (s i).b (s i).c (s i).C (s i).p (s i).q
      (s i).a_nonneg (s i).a_lt_B (s i).b_pos (s i).C_pos
  have hbound : (∑' n, (s i).cost J x n) ≤ δ := by
    convert! hX x hstart hx i using 1
    apply tsum_congr
    intro n
    exact monomialCost_eq_exp J (s i).d (s i).B (s i).a (s i).b (s i).c (s i).C
      (s i).p (s i).q x n (by omega) (s i).C_pos (hxp n)
  refine ⟨hsum, hbound, ?_⟩
  intro n
  apply le_trans (hsum.le_tsum n ?_) hbound
  intro m hm
  exact monomialCost_nonneg J (s i).d (s i).B (s i).a (s i).b (s i).c (s i).C
    (s i).p (s i).q x m (s i).C_pos.le (hxp m).le

/-- Source cost data, collecting `elems`. -/
inductive SourceCost
  | shear | prior | neighbor | extra | width | parent | good
  deriving DecidableEq

instance : Fintype SourceCost where
  elems := {.shear, .prior, .neighbor, .extra, .width, .parent, .good}
  complete c := by cases c <;> simp

/-- Source cost spec used in packet source scale choice. -/
def sourceCostSpec (C c : ℝ) (hC : 1 ≤ C) (A : ℕ) : SourceCost → CostSpec
  | .shear => {
      d := 2, B := 9, N := 7, a := 7, b := 1/2, c := 2,
      C := 128*(2*C)^(A+1), p := 2*(A+1), q := 2*(A+1),
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .prior => {
      d := 0, B := 5, N := 4, a := 4, b := 1/4, c := 0,
      C := 16*(2*C)^A, p := 2*A, q := 2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .neighbor => {
      d := 1, B := 4, N := 4, a := 7/2, b := 1, c := 2*c,
      C := 16*(2*C)^A, p := 2*A, q := 2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .extra => {
      d := 1, B := 7, N := 5, a := 5, b := 1/2, c := 1/2,
      C := 48*(2*C)^A, p := 6+2*A, q := 2+2*A,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by positivity }
  | .width => {
      d := 1, B := 7, N := 5, a := 5, b := 1/2, c := 1/2,
      C := 4, p := 4, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }
  | .parent => {
      d := 1, B := 7, N := 5, a := 5, b := 1, c := 2,
      C := 1, p := 0, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }
  | .good => {
      d := 1, B := 5, N := 3, a := 3, b := 1, c := 2,
      C := 1, p := 0, q := 0,
      d_le_two := by norm_num, a_nonneg := by norm_num, a_lt_B := by norm_num,
      a_le_N := by norm_num, b_pos := by norm_num, C_pos := by norm_num }

/-- Small series data, collecting `nonneg`, `summable`, `total_le`. -/
structure SmallSeries (f : ℕ → ℝ) (δ : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ f n
  summable : Summable f
  total_le : (∑' n, f n) ≤ δ

theorem SmallSeries.term_le {f : ℕ → ℝ} {δ : ℝ} (h : SmallSeries f δ) (n : ℕ) : f n ≤ δ :=
  (h.summable.le_tsum n (fun m _ => h.nonneg m)).trans h.total_le

theorem SmallSeries.weaken {f : ℕ → ℝ} {δ η : ℝ} (h : SmallSeries f δ) (hle : δ ≤ η) :
    SmallSeries f η := ⟨h.nonneg, h.summable, h.total_le.trans hle⟩

theorem SmallSeries.mono {f g : ℕ → ℝ} {δ : ℝ} (h : SmallSeries f δ)
    (hg : ∀ n, 0 ≤ g n) (hle : ∀ n, g n ≤ f n) : SmallSeries g δ := by
  have hs := h.summable.of_nonneg_of_le hg hle
  exact ⟨hg, hs, (hs.tsum_le_tsum hle h.summable).trans h.total_le⟩

/-- Coefficient cost, given by `sourceCoefficientError J C c x n * sourceTheta J C x n^A`. -/
def coefficientCost (J : ℕ) (C c : ℝ) (A : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  sourceCoefficientError J C c x n * sourceTheta J C x n^A

/-- Extra time cost, given by `2*sqrt (a n*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J
x n * sourceTheta J C x n^A`. -/
def extraTimeCost (J : ℕ) (C : ℝ) (A : ℕ) (x a : ℕ → ℝ) (n : ℕ) : ℝ :=
  2*sqrt (a n*exp (x n/((J-1+n : ℕ) : ℝ)^7))*sourceNextTimeWidth J x n *
    sourceTheta J C x n^A

/-- Parent square ratio, given by `exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5)`. -/
def parentSquareRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (2*x n/((J-1+n : ℕ) : ℝ)^7)/exp (x n/((J+n : ℕ) : ℝ)^5)

/-- Good cost, given by `exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5) * exp (x
n/((J-1+n : ℕ) : ℝ)^7)`. -/
def goodCost (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n/((J+n : ℕ) : ℝ)^3)*exp (x n/((J+n : ℕ) : ℝ)^5) *
    exp (x n/((J-1+n : ℕ) : ℝ)^7)

/-- Uniform bounds data, collecting `coefficient`, `extraTime`, `width`, `parent`, `good`. -/
structure UniformBounds (J : ℕ) (C c : ℝ) (A : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop where
  coefficient : SmallSeries (coefficientCost J C c A x) δ
  extraTime : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ n, a n ≤ 2) →
    SmallSeries (extraTimeCost J C A x a) δ
  width : SmallSeries (sourceTimeRatio J x) δ
  parent : SmallSeries (parentSquareRatio J x) δ
  good : SmallSeries (goodCost J x) δ

/-- One fixed choice of the starting stage makes all the actual normal-stage
coefficient, time, shear-separation and good-interval pressure series small.
The initial scale is chosen afterwards, and every later stage is covered. -/
theorem source_uniform_choice (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n+1) = ((J+n : ℕ) : ℝ)^2*x n) → UniformBounds J C c A x δ := by
  obtain ⟨J, hJ, hchoice⟩ := finite_uniform_choice (sourceCostSpec C c hC A)
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice (δ/3) (by positivity)
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx0 hx
  have hJ1 : 1 ≤ J := by omega
  have hx1 : ∀ n, 1 ≤ x n := quadratic_growth_one_le J hJ1 x
    (by linarith only [hX₀, hx0]) hx
  have hxp : ∀ n, 0 ≤ x n := fun n => le_trans zero_le_one (hx1 n)
  let f := fun i : SourceCost => (sourceCostSpec C c hC A i).cost J x
  have hsmall (i : SourceCost) : SmallSeries (f i) (δ/3) := by
    have hh := hX x hx0 hx i
    refine ⟨?_, hh.1, hh.2.1⟩
    intro n
    exact monomialCost_nonneg J _ _ _ _ _ _ _ _ x n
      (sourceCostSpec C c hC A i).C_pos.le (hxp n)
  have hweak (i : SourceCost) : SmallSeries (f i) δ :=
    (hsmall i).weaken (by linarith only [hδ])
  have hsum : SmallSeries (fun n => f .shear n+f .prior n+f .neighbor n) δ := by
    have hs := ((hsmall .shear).summable.add (hsmall .prior).summable).add (hsmall
        .neighbor).summable
    refine ⟨fun n => add_nonneg (add_nonneg ((hsmall .shear).nonneg n)
      ((hsmall .prior).nonneg n)) ((hsmall .neighbor).nonneg n), hs, ?_⟩
    rw [Summable.tsum_add ((hsmall .shear).summable.add (hsmall .prior).summable)
        (hsmall .neighbor).summable,
      Summable.tsum_add (hsmall .shear).summable (hsmall .prior).summable]
    linarith only [(hsmall .shear).total_le, (hsmall .prior).total_le, (hsmall .neighbor).total_le]
  refine ⟨hsum.mono ?_ ?_, ?_, (hweak .width).mono ?_ ?_,
    (hweak .parent).mono ?_ ?_, (hweak .good).mono ?_ ?_⟩
  · intro n
    have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold coefficientCost sourceCoefficientError sourceEpsilon sourceOlderGradient
        sourcePriorError sourceNeighborError
    positivity
  · intro n
    exact sourceCoefficientError_bound J hJ C c hC hc A x hx1 n
  · intro a ha ha₂
    apply (hweak .extra).mono
    · intro n
      have hθ : 0 ≤ sourceTheta J C x n := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
      unfold extraTimeCost sourceNextTimeWidth
      positivity
    · intro n
      exact sourceExtraTime_bound J hJ1 C hC A x hx1 n (a n) (ha n) (ha₂ n)
  · intro n
    unfold sourceTimeRatio
    positivity
  · intro n
    exact sourceTimeRatio_bound J hJ1 x n
  · intro n
    unfold parentSquareRatio
    positivity
  · intro n
    exact (sourceParentSquareRatio_eq J x n).le
  · intro n
    unfold goodCost
    positivity
  · intro n
    exact sourceGoodCost_bound J hJ x n (hxp n)

/-- The sequence in (37), now constructed rather than supplied. -/
def scaleSequence (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X
  | n+1 => ((J+n : ℕ) : ℝ)^2*scaleSequence J X n

@[simp] theorem scaleSequence_zero (J : ℕ) (X : ℝ) : scaleSequence J X 0 = X := rfl

theorem scaleSequence_succ (J : ℕ) (X : ℝ) (n : ℕ) :
    scaleSequence J X (n+1) = ((J+n : ℕ) : ℝ)^2*scaleSequence J X n := rfl

/-- In particular the explicit sequence allows the same simultaneous choice;
no recurrence or asymptotic conclusion remains as an input. -/
theorem explicit_sequence_uniform_choice (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → UniformBounds J C c A (scaleSequence J X) δ := by
  obtain ⟨J, hJ, hchoice⟩ := source_uniform_choice C c hC hc A
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨X₀, hX₀, hX⟩ := hchoice δ hδ
  exact ⟨X₀, hX₀, fun X hX' => hX (scaleSequence J X) hX' (scaleSequence_succ J X)⟩

end EulerPacketSourceScaleChoice

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceScaleSequence

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleChoice EulerPacketBaseScales

open scoped Topology

/-- Shear, given by `exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^5)`. -/
def shear (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^5)

/-- Frequency, given by `exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^2)`. -/
def frequency (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^2)

/-- Spike, given by `exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^3)`. -/
def spike (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^3)

/-- Support scale, given by `exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ))`. -/
def supportScale (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ))

/-- Previous shear as an element of `ℕ → ℝ | 0 => X^1000 | n+1 => shear J X n`. -/
def previousShear (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X^1000
  | n+1 => shear J X n

/-- Previous frequency as an element of `ℕ → ℝ | 0 => X^D | n+1 => frequency J X n`. -/
def previousFrequency (J D : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X^D
  | n+1 => frequency J X n

/-- Older shear as an element of `ℕ → ℝ | 0 => 1 | n+1 => previousShear J X n`. -/
def olderShear (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => previousShear J X n

/-- Time width, given by `3*scaleSequence J X (n+1)*scaleSequence J X n/sqrt (previousShear J X
n)`. -/
def timeWidth (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  3*scaleSequence J X (n+1)*scaleSequence J X n/sqrt (previousShear J X n)

theorem previousShear_pos (J : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < previousShear J X n := by
  cases n with
  | zero => exact pow_pos hX 1000
  | succ n => exact exp_pos _

theorem previousFrequency_pos (J D : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < previousFrequency J D X n := by
  cases n with
  | zero => exact pow_pos hX D
  | succ n => exact exp_pos _

theorem previousShear_succ_eq (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousShear J X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^7) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have he : J-1+(n+1) = J+n := by omega
  simp only [previousShear, shear, scaleSequence_succ, he]
  congr 1
  field_simp [hj.ne']

theorem previousFrequency_succ_eq (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousFrequency J D X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^4) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have he : J-1+(n+1) = J+n := by omega
  simp only [previousFrequency, frequency, scaleSequence_succ, he]
  congr 1
  field_simp [hj.ne']

theorem olderShear_succ_succ_eq (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (n : ℕ) :
    olderShear J X (n+1+1) = exp (scaleSequence J X (n+1+1)/
      (((J-1+(n+1+1) : ℕ) : ℝ)^2*((J-2+(n+1+1) : ℕ) : ℝ)^7)) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have hj1 : (0 : ℝ) < (J+(n+1) : ℕ) := by exact_mod_cast (show 0 < J+(n+1) by omega)
  have he1 : J-1+(n+1+1) = J+(n+1) := by omega
  have he2 : J-2+(n+1+1) = J+n := by omega
  simp only [olderShear, previousShear, shear, scaleSequence_succ, he1, he2]
  congr 1
  field_simp [hj.ne', hj1.ne']

/-- A fixed positive linear exponential eventually dominates each actual
polynomial base shear or frequency. -/
theorem eventually_pow_le_exp (D : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ X : ℝ in atTop, X^D ≤ exp (X/r) := by
  have hh := base_exponential_decay 1 (D : ℝ) (1/r) 0 0 (by positivity)
  have hlim : Tendsto (fun X : ℝ => X^D*exp (-(X/r))) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    simp only [rpow_natCast, pow_zero, mul_one]
    congr 1
    ring_nf
  filter_upwards [hlim.eventually_le_const zero_lt_one] with X hX
  have hm := mul_le_mul_of_nonneg_right hX (exp_pos (X/r)).le
  simpa only [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] using hm

theorem previousShear_le_normal (J : ℕ) (hJ : 1 ≤ J) (X : ℝ)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    previousShear J X n ≤ exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7) := by
  cases n with
  | zero => simpa only [previousShear, scaleSequence_zero, Nat.add_zero] using hbase
  | succ n => exact (previousShear_succ_eq J hJ X n).le

theorem previousFrequency_le_normal (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    previousFrequency J D X n ≤ exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4) := by
  cases n with
  | zero => simpa only [previousFrequency, scaleSequence_zero, Nat.add_zero] using hbase
  | succ n => exact (previousFrequency_succ_eq J D hJ X n).le

theorem olderShear_le_normal (J : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    1+olderShear J X n ≤ sourceOlderGradient J (scaleSequence J X) n := by
  cases n with
  | zero =>
    change 1+1 ≤ 1+exp (X/(((J-1 : ℕ) : ℝ)^2*((J-2 : ℕ) : ℝ)^7))
    have hh : 1 ≤ exp (X/(((J-1 : ℕ) : ℝ)^2*((J-2 : ℕ) : ℝ)^7)) :=
      one_le_exp (by positivity)
    linarith only [hh]
  | succ n =>
    cases n with
    | zero =>
      have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      have he1 : J-1+1 = J := by omega
      have he2 : J-2+1 = J-1 := by omega
      change 1+X^1000 ≤ 1+exp (scaleSequence J X 1/
        (((J-1+1 : ℕ) : ℝ)^2*((J-2+1 : ℕ) : ℝ)^7))
      rw [show scaleSequence J X 1 = (J : ℝ)^2*X by
          simp only [scaleSequence_succ, scaleSequence_zero, Nat.add_zero], he1, he2]
      have he : (J : ℝ)^2*X/((J : ℝ)^2*((J-1 : ℕ) : ℝ)^7) = X/((J-1 : ℕ) : ℝ)^7 := by
        field_simp [hJp.ne']
      rw [he]
      linarith only [hbase]
    | succ n =>
      rw [olderShear_succ_succ_eq J (by omega) X n]
      exact le_rfl

theorem timeWidth_pos (J : ℕ) (hJ : 1 ≤ J) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < timeWidth J X n := by
  have hxp := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact div_pos (mul_pos (mul_pos (by norm_num) (hxp (n+1))) (hxp n))
    (sqrt_pos.mpr (previousShear_pos J hX n))

theorem timeWidth_succ_eq (J : ℕ) (X : ℝ) (n : ℕ) :
    timeWidth J X (n+1) = sourceNextTimeWidth J (scaleSequence J X) n := by
  simp only [timeWidth, previousShear, shear, scaleSequence_succ, ← exp_half]
  have hj : ((J+(n+1) : ℕ) : ℝ) = ((J+n : ℕ) : ℝ)+1 := by push_cast; ring
  rw [hj]
  unfold sourceNextTimeWidth
  rw [div_eq_mul_inv, ← exp_neg]
  have he : -(scaleSequence J X n/((J+n : ℕ) : ℝ)^5/2) =
      -scaleSequence J X n/(2*((J+n : ℕ) : ℝ)^5) := by ring
  rw [he]
  ring

theorem sourceTimeWidth_eq (J : ℕ) (X : ℝ) (n : ℕ) :
    sourceTimeWidth J (scaleSequence J X) n =
      3*scaleSequence J X (n+1)*scaleSequence J X n/
        sqrt (exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7)) := by
  rw [scaleSequence_succ, ← exp_half, div_eq_mul_inv, ← exp_neg]
  unfold sourceTimeWidth
  have he : -(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7/2) =
      -scaleSequence J X n/(2*((J-1+n : ℕ) : ℝ)^7) := by ring
  rw [he]
  ring

/-- The actual polynomial-base time width is no smaller than the normal-form
one, once the explicit polynomial/exponential comparison holds. -/
theorem sourceTimeWidth_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    sourceTimeWidth J (scaleSequence J X) n ≤ timeWidth J X n := by
  rw [sourceTimeWidth_eq]
  have hxp := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg (by norm_num) (hxp (n+1)).le) (hxp n).le)
    (sqrt_pos.mpr (previousShear_pos J hX n))
    (sqrt_le_sqrt (previousShear_le_normal J hJ X hbase n))

end EulerPacketSourceScaleSequence
