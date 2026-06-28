/-
Copyright (c) 2026 M. Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: M. Samarakkody
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# The Isoperimetric Inequality

This file formalises basic properties of classical Fourier series needed on the way to
the isoperimetric inequality.  In particular we prove:

* **Parseval's theorem** – `Parsevals_thm`
* **Wirtinger's inequality** – `Wirtingers_inequality`

## Main results

### Parseval's theorem (`Parsevals_thm`)
Given a Fourier series `f(x) = a₀/2 + ∑_{n≥1} (aₙ cos(nx) + bₙ sin(nx))`,
under suitable integrability and summability hypotheses,
```
(1/π) ∫_{-π}^{π} f(x)² dx = (1/2) a₀² + ∑_{n≥1} (aₙ² + bₙ²).
```

### Wirtinger's inequality (`Wirtingers_inequality`)
Given the same Fourier series, the Parseval identity applied to the derivative series yields
```
(1/π) ∫_{-π}^{π} (f'(x))² dx = ∑_{n≥1} n² (aₙ² + bₙ²).
```
This is the continuous analogue of the discrete Wirtinger inequality, and reflects that
differentiation weights each Fourier mode by its frequency `n`.

## Notation

Throughout, `a : ℕ → ℝ` and `b : ℕ → ℝ` are the cosine and sine Fourier coefficients,
and the series is indexed over `ℕ+` (positive natural numbers).
-/

open Real
open scoped BigOperators Topology MeasureTheory Filter

namespace IsoperimetricInequality

noncomputable section

-- The Fourier coefficients
variable (a : ℕ → ℝ) (b : ℕ → ℝ)

/-- The classical Fourier series as a function of `x`:
`f(x) = a₀/2 + ∑_{n=1}^∞ (aₙ cos(nx) + bₙ sin(nx))`. -/
def fourierSeries (x : ℝ) : ℝ :=
    (1/2) * a 0 + ∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))

/-- The `N`-th partial sum of the Fourier series:
`S_N(x) = a₀/2 + ∑_{n=1}^N (aₙ cos(nx) + bₙ sin(nx))`. -/
def fourierPartialSum (x : ℝ) (N : ℕ) : ℝ :=
  (1/2) * a 0 + ∑ n ∈ Finset.range N, (a (n + 1) * cos ((n + 1 : ℝ) * x)
  + b (n + 1) * sin ((n + 1 : ℝ) * x))


/-- The oscillatory sum part of the Fourier series (without the constant term):
`S(x) = ∑_{n=1}^∞ (aₙ cos(nx) + bₙ sin(nx))`. -/
def fourierSum (x : ℝ) : ℝ :=
    ∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))

/-- The Fourier series decomposes as `f(x) = a₀/2 + S(x)`,
where `S(x)` is the oscillatory sum part. -/
lemma fourierSeries_eq (x : ℝ) :
  fourierSeries a b x = (1/2) * a 0 + fourierSum a b x := by rfl


/-- Expansion of `(f(x))²` as `(a₀/2)² + a₀·S(x) + S(x)²`,
where `S(x) = fourierSum a b x`. -/
lemma fourierSeries_sq (x : ℝ) :
  --(hsum : Summable fun n : ℕ+ => (a n * cos (n * x) + b n * sin (n * x))) :
  (fourierSeries a b x)^2 = (a 0)^2 / 4 +
  a 0 * (∑' n : ℕ+ , (a n * cos (n * x) + b n * sin (n * x))) +
  (∑' n : ℕ+ , (a n * cos (n * x) + b n * sin (n * x)))^2 := by
  unfold fourierSeries
  ring

/-- Expands `(∑ aₙ cos(nx) + bₙ sin(nx))²` into
`(∑ aₙ cos)² + 2·(∑ aₙ cos)(∑ bₙ sin) + (∑ bₙ sin)²`
using linearity of the infinite sum. -/
lemma expand_square (x : ℝ)
    (hc : Summable fun n : ℕ+ => a n * cos (n * x))
    (hs : Summable fun n : ℕ+ => b n * sin (n * x)) :
    (∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x)))^2 =
    (∑' n : ℕ+, a n * cos (n * x))^2 +
    2 * (∑' n : ℕ+, a n * cos (n * x)) * (∑' n : ℕ+, b n * sin (n * x)) +
    (∑' n : ℕ+, b n * sin (n * x))^2 := by
  rw [hc.tsum_add hs]
  ring

/-- Expands the square of the sine partial sum into a double sum:
`(∑ bₙ sin(nx))² = ∑ₙ ∑ₘ bₙ bₘ sin(nx) sin(mx)`. -/
lemma expand_sin_sq (x : ℝ)
    (hs : Summable fun n : ℕ+ => b n * sin (n * x))
    -- The product family (n,m) ↦ bₙ sin(nx) · bₘ sin(mx) is summable
    (hprod : Summable fun z : ℕ+ × ℕ+ =>
      (b z.1 * sin (z.1 * x)) * (b z.2 * sin (z.2 * x)))
    -- Each inner sum is summable (needed for converting paired → iterated tsum)
    (hinner : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (b n * sin (n * x)) * (b m * sin (m * x))) :
    (∑' n : ℕ+, b n * sin (n * x))^2 =
    ∑' n : ℕ+, ∑' m : ℕ+, b n * b m * sin (n * x) * sin (m * x) := by
  -- Step 1: Rewrite x² as x * x
  rw [sq]
  -- Step 2: Product of tsums → tsum over pairs
  rw [hs.tsum_mul_tsum hs hprod]
  -- Step 3: Paired tsum → iterated tsum
  rw [hprod.tsum_prod' hinner]
  -- Step 4: Show the terms match pointwise
  congr 1; ext n; congr 1; ext m
  ring

/-- Expands the square of the cosine partial sum into a double sum:
`(∑ aₙ cos(nx))² = ∑ₙ ∑ₘ aₙ aₘ cos(nx) cos(mx)`. -/
lemma expand_cos_sq (x : ℝ)
    (hs1 : Summable fun n : ℕ+ => a n * cos (n * x))
    -- The product family (n,m) ↦ aₙ cos(nx) · aₘ cos(mx) is summable
    (hprod1 : Summable fun z : ℕ+ × ℕ+ =>
      (a z.1 * cos (z.1 * x)) * (a z.2 * cos (z.2 * x)))
    -- Each inner sum is summable (needed for converting paired → iterated tsum)
    (hinner : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (a n * cos (n * x)) * (a m * cos (m * x))) :
    (∑' n : ℕ+, a n * cos (n * x))^2 =
    ∑' n : ℕ+, ∑' m : ℕ+, a n * a m * cos (n * x) * cos (m * x) := by
  -- Step 1: Rewrite x² as x * x
  rw [sq]
  -- Step 2: Product of tsums → tsum over pairs
  rw [hs1.tsum_mul_tsum hs1 hprod1]
  -- Step 3: Paired tsum → iterated tsum
  rw [hprod1.tsum_prod' hinner]
  -- Step 4: Show the terms match pointwise
  congr 1; ext n; congr 1; ext m
  ring


/-- Full expansion of `(f(x))²` into a constant term, cross terms, and double sums,
combining `fourierSeries_sq`, `expand_square`, `expand_cos_sq`, and `expand_sin_sq`. -/
theorem fourier_series_sq_expanded (x : ℝ)
    (hc : Summable fun n : ℕ+ => a n * cos (n * x))
    (hs : Summable fun n : ℕ+ => b n * sin (n * x))
    (hprod_cos : Summable fun z : ℕ+ × ℕ+ =>
      (a z.1 * cos (z.1 * x)) * (a z.2 * cos (z.2 * x)))
    (hinner_cos : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (a n * cos (n * x)) * (a m * cos (m * x)))
    (hprod_sin : Summable fun z : ℕ+ × ℕ+ =>
      (b z.1 * sin (z.1 * x)) * (b z.2 * sin (z.2 * x)))
    (hinner_sin : ∀ n : ℕ+, Summable fun m : ℕ+ =>
      (b n * sin (n * x)) * (b m * sin (m * x))) :
    (fourierSeries a b x)^2 = (a 0)^2 / 4 +
    a 0 * (∑' n : ℕ+, (a n * cos (n * x) + b n * sin (n * x))) +
    ((∑' n : ℕ+, ∑' m : ℕ+, a n * a m * cos (n * x) * cos (m * x)) +
    2 * (∑' n : ℕ+, a n * cos (n * x)) * (∑' n : ℕ+, b n * sin (n * x)) +
    (∑' n : ℕ+, ∑' m : ℕ+, b n * b m * sin (n * x) * sin (m * x))) := by
  -- Step 1: Expand (a₀/2 + S)² into a₀²/4 + a₀·S + S²
  rw [fourierSeries_sq]
  -- Step 2: Expand S² into C² + 2·C·S_sin + S_sin²
  rw [expand_square a b x hc hs]
  -- Step 3: Expand C² into double sum
  rw [expand_cos_sq a x hc hprod_cos hinner_cos]
  -- Step 4: Expand S_sin² into double sum
  rw [expand_sin_sq b x hs hprod_sin hinner_sin]

/-- `∫_{-π}^{π} (1/4) a₀² dx = (1/2) a₀² π`. -/
lemma integration_of_const :
    ∫ _x in (-π)..π, (1 / 4) * (a 0)^2 = (1 / 2) * (a 0)^2 * π := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

/-- `∫_{-π}^{π} cos(n·x) dx = 0` for any positive integer `n : ℕ+`. -/
private lemma integral_cos_pnat (n : ℕ+) :
    ∫ x in (-π)..π, cos ((n : ℝ) * x) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have h_sin : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
  have key : (n : ℝ) * ∫ x in (-π)..π, cos ((n : ℝ) * x) = 0 := by
    rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
    simp [mul_neg, sin_neg, h_sin]
  exact (mul_eq_zero.mp key).resolve_left hn

/-- `∫_{-π}^{π} sin(n·x) dx = 0` for any positive integer `n : ℕ+`. -/
private lemma integral_sin_pnat (n : ℕ+) :
    ∫ x in (-π)..π, sin ((n : ℝ) * x) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.pos.ne'
  have key : (n : ℝ) * ∫ x in (-π)..π, sin ((n : ℝ) * x) = 0 := by
    rw [intervalIntegral.mul_integral_comp_mul_left, integral_sin]
    simp [mul_neg, cos_neg]
  exact (mul_eq_zero.mp key).resolve_left hn

/-- Orthogonality of individual Fourier terms:
`∫_{-π}^{π} (aₙ cos(nx) + bₙ sin(nx)) dx = 0` for each `n : ℕ+`. -/
private lemma integral_fourierTerm (n : ℕ+) :
    ∫ x in (-π)..π, (a n * cos ((n : ℝ) * x) + b n * sin ((n : ℝ) * x)) = 0 := by
  have hc : Continuous (fun x => a n * cos ((n : ℝ) * x)) :=
    continuous_const.mul (continuous_cos.comp (continuous_const.mul continuous_id))
  have hs : Continuous (fun x => b n * sin ((n : ℝ) * x)) :=
    continuous_const.mul (continuous_sin.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_add (hc.intervalIntegrable (-π) π) (hs.intervalIntegrable (-π) π),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_pnat n, integral_sin_pnat n, mul_zero, mul_zero, add_zero]

/-- The cross term integrates to zero over `[-π, π]`:
`∫_{-π}^{π} a₀ · (∑_{n≥1} aₙ cos(nx) + bₙ sin(nx)) dx = 0`. -/
lemma integration_of_cos_sin
    (hF_int : ∀ n : ℕ+, IntervalIntegrable
      (fun x => a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x))
      MeasureTheory.volume (-π) π)
    (hF_sum : Summable (fun n : ℕ+ =>
      ∫ x in (-π)..π, ‖a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)‖)) :
    ∫ x in (-π)..π, a 0 * fourierSum a b x = 0 := by
  -- Factor out the constant a 0
  rw [intervalIntegral.integral_const_mul]
  -- It suffices to show ∫ fourierSum = 0
  suffices h : ∫ x in (-π)..π, fourierSum a b x = 0 by simp [h]
  simp only [fourierSum]
  -- Interchange ∫ and ∑' (by summability of norms via dominated convergence)
  have hswap : ∫ x in (-π)..π,
        ∑' n : ℕ+, (a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)) =
        ∑' n : ℕ+, ∫ x in (-π)..π,
          (a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)) := by
    have h_le : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    -- Convert interval integrals to restricted integrals over Ioc (-π) π
    simp_rw [intervalIntegral.integral_of_le h_le]
    symm
    -- Apply integral_tsum_of_summable_integral_norm with μ = volume.restrict (Ioc (-π) π)
    apply MeasureTheory.integral_tsum_of_summable_integral_norm
    · intro n; exact (hF_int n).1
    · simp_rw [← intervalIntegral.integral_of_le h_le]; exact hF_sum
  rw [hswap]
  -- Each term integrates to zero by orthogonality of trig functions
  simp_rw [integral_fourierTerm a b, tsum_zero]

/-- Orthogonality of cosines: `∫_{-π}^{π} cos(nx) cos(mx) dx = 0` for `n ≠ m`. -/
lemma integration_cos_cos_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, cos (n  * x) * cos (m * x) = 0 := by
  -- (n-m) ≠ 0 in ℝ
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- sin((n-m)π) = 0  (integer multiple of π)
  have hnm_sin : sin (((n : ℝ) - m) * π) = 0 := by
    rw [sub_mul, sin_sub]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- ∫ cos((n-m)x) = 0
  have int_nm : ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
      simp [mul_neg, sin_neg, hnm_sin]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ cos((n+m)x) = 0  (n+m : ℕ+ so use integral_cos_pnat)
  have int_np : ∫ x in (-π)..π, cos (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_cos_pnat (n + m)
  -- Product-to-sum: cos(nx)cos(mx) = ½cos((n-m)x) + ½cos((n+m)x)
  have prod_sum : ∀ x : ℝ, cos ((n : ℝ) * x) * cos ((m : ℝ) * x) =
      (1/2) * cos (((n : ℝ) - m) * x) + (1/2) * cos (((n : ℝ) + m) * x) := fun x => by
    have h1 := cos_sub ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := cos_add ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← sub_mul, ← add_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_nm, int_np]; simp

/-- Orthogonality of sines: `∫_{-π}^{π} sin(nx) sin(mx) dx = 0` for `n ≠ m`. -/
lemma integration_sin_sin_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, sin (n  * x) * sin (m * x) = 0 := by
  -- (n-m) ≠ 0 in ℝ
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- sin((n-m)π) = 0  (integer multiple of π)
  have hnm_sin : sin (((n : ℝ) - m) * π) = 0 := by
    rw [sub_mul, sin_sub]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- sin((n+m)x) = 0 (integer multiple of π)
  have hnm1_sin : sin (((n : ℝ) + m) * π) = 0 := by
    rw [add_mul, sin_add]
    have h1 : sin ((n : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (n : ℕ)
    have h2 : sin ((m : ℝ) * π) = 0 := by exact_mod_cast sin_nat_mul_pi (m : ℕ)
    simp [h1, h2]
  -- ∫ cos((n-m)x) = 0
  have int_nm : ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, cos (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_cos]
      simp [mul_neg, sin_neg, hnm_sin]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ cos((n+m)x) = 0  (n+m : ℕ+ so use integral_cos_pnat)
  have int_np : ∫ x in (-π)..π, cos (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_cos_pnat (n + m)
  -- Product-to-sum: sin(nx)sin(mx) = ½cos((n-m)x) - ½cos((n+m)x)
  have prod_sum : ∀ x : ℝ, sin ((n : ℝ) * x) * sin ((m : ℝ) * x) =
      (1/2) * cos (((n : ℝ) - m) * x) - (1/2) * cos (((n : ℝ) + m) * x) := fun x => by
    have h1 := cos_sub ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := cos_add ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← sub_mul, ← add_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_nm, int_np]; simp

/-- Cross orthogonality: `∫_{-π}^{π} cos(nx) sin(mx) dx = 0` for `n ≠ m`. -/
lemma integration_sin_cos_zero (n m : ℕ+) (h : n ≠ m) :
    ∫ x in (-π)..π, cos (n * x) * sin (m * x) = 0 := by
  have hnm_ne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  -- ∫ sin((n-m)x) = 0
  have int_sin_nm : ∫ x in (-π)..π, sin (((n : ℝ) - m) * x) = 0 := by
    have key : ((n : ℝ) - m) * ∫ x in (-π)..π, sin (((n : ℝ) - m) * x) = 0 := by
      rw [intervalIntegral.mul_integral_comp_mul_left, integral_sin]
      simp [mul_neg, cos_neg]
    exact (mul_eq_zero.mp key).resolve_left hnm_ne
  -- ∫ sin((n+m)x) = 0
  have int_sin_np : ∫ x in (-π)..π, sin (((n : ℝ) + m) * x) = 0 := by
    have h_cast : ((n : ℝ) + m) = ((n + m : ℕ+) : ℝ) := by push_cast; ring
    rw [h_cast]; exact integral_sin_pnat (n + m)
  -- Product-to-sum: cos(nx)sin(mx) = ½sin((n+m)x) - ½sin((n-m)x)
  have prod_sum : ∀ x : ℝ, cos ((n : ℝ) * x) * sin ((m : ℝ) * x) =
      (1/2) * sin (((n : ℝ) + m) * x) - (1/2) * sin (((n : ℝ) - m) * x) := fun x => by
    have h1 := sin_add ((n : ℝ) * x) ((m : ℝ) * x)
    have h2 := sin_sub ((n : ℝ) * x) ((m : ℝ) * x)
    simp only [← add_mul, ← sub_mul] at h1 h2
    linarith
  simp_rw [prod_sum]
  have hc1 : IntervalIntegrable (fun x => (1/2 : ℝ) * sin (((n : ℝ) + m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * sin (((n : ℝ) - m) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_sin_np, int_sin_nm]; simp

/-- Self-orthogonality of cosines:
`∫_{-π}^{π} cos(nx) cos(mx) dx = π` when `n = m`. -/
lemma integration_cos_cos_pi (n m : ℕ+) (h : n = m) :
    ∫ x in (-π)..π, cos (n * x) * cos (m * x) = π := by
  subst h
  -- cos²(nx) = ½(1 + cos(2nx))
  have half_angle : ∀ x : ℝ,  cos ((n : ℝ) * x) * cos ((n : ℝ) * x) =
      1/2 + (1/2) * cos ((2 * (n : ℝ)) * x) := fun x => by
    have h := cos_sq ((n : ℝ) * x)
    rw [sq, show 2 * ((n : ℝ) * x) = 2 * (n : ℝ) * x from by ring] at h
    linarith
  simp_rw [half_angle]
  -- ∫ cos(2nx) = 0 since 2n : ℕ+
  have int_cos2n : ∫ x in (-π)..π, (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x) = 0 := by
    have h_cast : 2 * (n : ℝ) = ((2 * n : ℕ+) : ℝ) := by push_cast; ring
    rw [intervalIntegral.integral_const_mul, h_cast, integral_cos_pnat]
    simp
  have hc1 : IntervalIntegrable (fun _ => (1/2 : ℝ)) MeasureTheory.volume (-π) π :=
    intervalIntegrable_const
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const, int_cos2n]
  simp only [smul_eq_mul, sub_neg_eq_add, add_zero]
  linarith


/-- Self-orthogonality of sines:
`∫_{-π}^{π} sin(nx) sin(mx) dx = π` when `n = m`. -/
lemma integration_sin_sin_pi (n m : ℕ+) (h : n = m) :
    ∫ x in (-π)..π, sin (n * x) * sin (m * x) = π := by
  subst h
  -- sin(nx)sin(nx) = ½(1 - cos(2nx))
  have half_angle : ∀ x : ℝ, sin ((n : ℝ) * x) * sin ((n : ℝ) * x) =
      1/2 - (1/2) * cos ((2 * (n : ℝ)) * x) := fun x => by
    have h1 := sin_sq_add_cos_sq ((n : ℝ) * x)
    have h2 := cos_sq ((n : ℝ) * x)
    rw [show 2 * ((n : ℝ) * x) = 2 * (n : ℝ) * x from by ring] at h2
    rw [← sq]
    linarith
  simp_rw [half_angle]
  -- ∫ cos(2nx) = 0 since 2n : ℕ+
  have int_cos2n : ∫ x in (-π)..π, (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x) = 0 := by
    have h_cast : 2 * (n : ℝ) = ((2 * n : ℕ+) : ℝ) := by push_cast; ring
    rw [intervalIntegral.integral_const_mul, h_cast, integral_cos_pnat]
    simp
  have hc1 : IntervalIntegrable (fun _ => (1/2 : ℝ)) MeasureTheory.volume (-π) π :=
    intervalIntegrable_const
  have hc2 : IntervalIntegrable (fun x => (1/2 : ℝ) * cos ((2 * (n : ℝ)) * x))
      MeasureTheory.volume (-π) π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const, int_cos2n]
  simp only [smul_eq_mul, sub_neg_eq_add, sub_zero]
  linarith

/-- **Parseval's theorem**: Given square-integrability and suitable summability hypotheses,
`(1/π) ∫_{-π}^{π} f(x)² dx = (1/2) a₀² + ∑_{n≥1} (aₙ² + bₙ²)`. -/
theorem Parsevals_thm
    -- Integrability of a₀·S(x) over [-π, π]
    (hfS_int : IntervalIntegrable (fun x => a 0 * fourierSum a b x)
      MeasureTheory.volume (-π) π)
    -- Integrability of S(x)² over [-π, π]
    (hfSq_int : IntervalIntegrable (fun x => (fourierSum a b x)^2)
      MeasureTheory.volume (-π) π)
    -- Each Fourier term is integrable
    (hF_int : ∀ n : ℕ+, IntervalIntegrable
      (fun x => a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x))
      MeasureTheory.volume (-π) π)
    -- L¹ summability (for integral/sum interchange in cross term)
    (hF_sum : Summable (fun n : ℕ+ =>
      ∫ x in (-π)..π, ‖a n * cos ((n : ℕ+) * x) + b n * sin ((n : ℕ+) * x)‖))
    -- ∫ S(x)² = π · ∑ₙ (aₙ² + bₙ²)  (orthogonality of the Fourier basis)
    (h_int_sq : ∫ x in (-π)..π, (fourierSum a b x)^2 =
      π * ∑' n : ℕ+, ((a n)^2 + (b n)^2)) :
    (1/π) * ∫ x in (-π)..π, (fourierSeries a b x)^2 =
    (1/2) * (a 0)^2 + ∑' n : ℕ+, ((a n)^2 + (b n)^2) := by
  -- Step 1: pointwise expand f(x)² = (a₀/2)² + a₀·S(x) + S(x)²
  have hpt : ∀ x : ℝ, (fourierSeries a b x)^2 =
      (1/4 : ℝ) * (a 0)^2 + a 0 * fourierSum a b x + (fourierSum a b x)^2 := fun x => by
    simp only [fourierSeries_eq]; ring
  simp_rw [hpt]
  -- Step 2: establish integrability of the sub-expressions
  have h_const_int : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ) * (a 0) ^ 2)
      MeasureTheory.volume (-π) π := intervalIntegrable_const
  have h_sum_int : IntervalIntegrable
      (fun x => (1 / 4 : ℝ) * (a 0) ^ 2 + a 0 * fourierSum a b x)
      MeasureTheory.volume (-π) π := h_const_int.add hfS_int
  -- Step 3: split the integral linearly into three pieces
  rw [intervalIntegral.integral_add h_sum_int hfSq_int,
      intervalIntegral.integral_add h_const_int hfS_int]
  -- Step 3: evaluate each piece
  --   ∫ (1/4)·a₀²  = (1/2)·a₀²·π   (integration_of_const)
  --   ∫ a₀·S(x)    = 0              (orthogonality, integration_of_cos_sin)
  --   ∫ S(x)²      = π·∑ₙ(aₙ²+bₙ²) (h_int_sq)
  rw [integration_of_const, integration_of_cos_sin a b hF_int hF_sum, h_int_sq]
  -- Step 4: arithmetic — (1/π)·((1/2)·a₀²·π + 0 + π·∑…) = (1/2)·a₀² + ∑…
  simp only [add_zero]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]


/-- Each Fourier term is bounded in norm:
`‖aₙ cos(nx) + bₙ sin(nx)‖ ≤ ‖aₙ‖ + ‖bₙ‖` for all `x : ℝ`. -/
lemma term_bound (n : ℕ) (x : ℝ) :
    ‖a (n + 1) * cos ((n + 1 : ℝ) * x) + b (n + 1) * sin ((n + 1 : ℝ) * x)‖
    ≤ ‖a (n + 1)‖ + ‖b (n + 1)‖ := by
  calc ‖a (n + 1) * cos ((n + 1 : ℝ) * x) + b (n + 1) * sin ((n + 1 : ℝ) * x)‖
      ≤ ‖a (n + 1) * cos ((n + 1 : ℝ) * x)‖ + ‖b (n + 1) * sin ((n + 1 : ℝ) * x)‖ :=
        norm_add_le _ _
    _ = ‖a (n + 1)‖ * ‖cos ((n + 1 : ℝ) * x)‖ + ‖b (n + 1)‖ * ‖sin ((n + 1 : ℝ) * x)‖ := by
        simp [norm_mul]
    _ ≤ ‖a (n + 1)‖ * 1 + ‖b (n + 1)‖ * 1 := by
        gcongr
        · exact abs_cos_le_one _
        · exact abs_sin_le_one _
    _ = ‖a (n + 1)‖ + ‖b (n + 1)‖ := by ring

/-- **Weierstrass M-test for Fourier series**: If `∑ (‖aₙ‖ + ‖bₙ‖)` converges, then the
Fourier partial sums converge uniformly to `fourierSeries a b` on all of `ℝ`. -/
lemma fourierSeries_uniformlyConvergence
    (hsumab : Summable (fun n => ‖a n‖ + ‖b n‖)) :
    TendstoUniformly
      (fun N x => fourierPartialSum a b x N)
      (fourierSeries a b)
      Filter.atTop := by
  unfold fourierPartialSum
  -- Summability of the shifted bound sequence
  have hshift : Summable (fun n => ‖a (n + 1)‖ + ‖b (n + 1)‖) :=
    summable_pnat_iff_summable_succ.mp (summable_pnat_iff_summable_nat.mpr hsumab)
  -- Weierstrass M-test: partial sums converge uniformly to the ℕ-indexed tsum
  have hcore := tendstoUniformly_tsum_nat hshift (term_bound a b)
  -- Use metric characterisation: reduce to dist bound on partial sums
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hcore) ε hε] with N hN
  intro x
  -- fourierSeries a b x = 1/2 * a 0 + ∑' n : ℕ, f(n+1)   (reindex ℕ+ → ℕ)
  have heq : fourierSeries a b x =
      1 / 2 * a 0 + ∑' n : ℕ, (a (n + 1) * cos ((↑n + 1) * x)
      + b (n + 1) * sin ((↑n + 1) * x)) := by
    simp only [fourierSeries]
    congr 1
    -- reindex: ∑' n : ℕ+, f n = ∑' n : ℕ, f (succPNat n)
    rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
    congr 1; ext n
    simp [Nat.succPNat, Nat.cast_succ]
  rw [heq, dist_add_left]
  exact hN x


/-- If `∑ (‖aₙ‖ + ‖bₙ‖)` converges, then the Fourier series `fourierSeries a b` is
continuous on all of `ℝ`. -/
lemma fourierSeries_continuous
    (hsumab : Summable (fun n => ‖a n‖ + ‖b n‖)) :
    Continuous (fourierSeries a b) := by
  apply (fourierSeries_uniformlyConvergence a b hsumab).continuous
  apply Filter.Eventually.frequently
  apply Filter.eventually_atTop.mpr
  refine ⟨0, fun N _ => ?_⟩
  unfold fourierPartialSum
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro n _
  exact (continuous_const.mul (continuous_cos.comp (continuous_const.mul continuous_id))).add
        (continuous_const.mul (continuous_sin.comp (continuous_const.mul continuous_id)))

/-- The Fourier series `f(x) = (1/2)a₀ + ∑ (aₙ cos nx + bₙ sin nx)`
is integrable on `[-π, π]` whenever `∑ (‖aₙ‖ + ‖bₙ‖)` converges. -/
lemma fourierSeries_integrable (hsumab : Summable (fun n => ‖a n‖ + ‖b n‖)) :
  IntervalIntegrable (fourierSeries a b)
    MeasureTheory.volume (-Real.pi) Real.pi := by
      exact (fourierSeries_continuous a b hsumab).continuousOn
      |>.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])

/-- The formal derivative series: `d/dx [aₙ cos nx + bₙ sin nx] = -n aₙ sin nx + n bₙ cos nx`. -/
noncomputable def fourierDeriv (a b : ℕ → ℝ) (x : ℝ) :=
  ∑' n , (- n * a n * sin (n * x) + n * b n * cos (n * x))


/-- If `∑ n * (‖aₙ‖ + ‖bₙ‖)` converges, then the derivative series is summable at each `x`. -/
lemma fourierDeriv_summable (hab' : Summable (fun n : ℕ => (n : ℝ) * (‖a n‖ + ‖b n‖))) (x : ℝ) :
    Summable (fun n : ℕ => -(n : ℝ) * a n * sin (↑n * x) + ↑n * b n * cos (↑n * x)) := by
  exact Summable.of_norm_bounded hab' fun (n : ℕ) => by
    calc ‖-(n : ℝ) * a n * sin (↑n * x) + ↑n * b n * cos (↑n * x)‖
        ≤ ‖-(n : ℝ) * a n * sin (↑n * x)‖ + ‖↑n * b n * cos (↑n * x)‖ := norm_add_le _ _
      _ = ↑n * ‖a n‖ * ‖sin (↑n * x)‖ + ↑n * ‖b n‖ * ‖cos (↑n * x)‖ := by
            simp [norm_mul, norm_neg]
      _ ≤ ↑n * ‖a n‖ * 1 + ↑n * ‖b n‖ * 1 := by
            gcongr
            · exact abs_sin_le_one _
            · exact abs_cos_le_one _
      _ = ↑n * (‖a n‖ + ‖b n‖) := by ring

/-- If `∑ n * (‖aₙ‖ + ‖bₙ‖)` converges, the partial sums of the derivative series converge
uniformly to `fourierDeriv a b` (Weierstrass M-test applied to the derivative). -/
lemma fourierDeriv_uniformConvergence
    (hab' : Summable (fun n : ℕ => (n : ℝ) * (‖a n‖ + ‖b n‖))) :
    TendstoUniformly
      (fun N x => ∑ n ∈ Finset.range N,
        (-(n : ℝ) * a n * sin (n * x) + (n : ℝ) * b n * cos (n * x)))
      (fourierDeriv a b)
      Filter.atTop := by
  change TendstoUniformly
    (fun N x => ∑ n ∈ Finset.range N,
      (-(n : ℝ) * a n * sin ((n : ℝ) * x) + (n : ℝ) * b n * cos ((n : ℝ) * x)))
    (fun x => ∑' n : ℕ, (-(n : ℝ) * a n * sin ((n : ℝ) * x) + (n : ℝ) * b n * cos ((n : ℝ) * x)))
    Filter.atTop
  apply tendstoUniformly_tsum_nat hab'
  intro n x
  calc ‖-(n : ℝ) * a n * sin ((n : ℝ) * x) + (n : ℝ) * b n * cos ((n : ℝ) * x)‖
      ≤ ‖-(n : ℝ) * a n * sin ((n : ℝ) * x)‖ + ‖(n : ℝ) * b n * cos ((n : ℝ) * x)‖ :=
          norm_add_le _ _
    _ = ↑n * ‖a n‖ * ‖sin ((n : ℝ) * x)‖ + ↑n * ‖b n‖ * ‖cos ((n : ℝ) * x)‖ := by
          simp [norm_mul, norm_neg]
    _ ≤ ↑n * ‖a n‖ * 1 + ↑n * ‖b n‖ * 1 := by
          gcongr
          · exact abs_sin_le_one _
          · exact abs_cos_le_one _
    _ = ↑n * (‖a n‖ + ‖b n‖) := by ring

/-- Each Fourier term is differentiable:
`d/dx [aₙ cos(nx) + bₙ sin(nx)] = -n aₙ sin(nx) + n bₙ cos(nx)`. -/
lemma hasDerivAt_term (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun x => a n * cos (n * x) + b n * sin (n * x))
      (-(n : ℝ) * a n * sin (n * x) + (n : ℝ) * b n * cos (n * x))
      x := by
  have h1 : HasDerivAt (fun x => a n * cos (n * x))
                       (-(n : ℝ) * a n * sin (n * x)) x := by
    have := ((hasDerivAt_id x).const_mul (n : ℝ)).cos
    simp at this
    exact this.const_mul (a n) |>.congr_deriv (by ring)
  have h2 : HasDerivAt (fun x => b n * sin (n * x))
                       ((n : ℝ) * b n * cos (n * x)) x := by
    have := ((hasDerivAt_id x).const_mul (n : ℝ)).sin
    simp at this
    exact this.const_mul (b n) |>.congr_deriv (by ring)
  exact h1.add h2

/-- The `N`-th partial sum is differentiable, with derivative equal to the partial sum of
term-wise derivatives. -/
lemma hasDerivAt_partialSum (N : ℕ) (x : ℝ) :
    HasDerivAt
      (fun x => fourierPartialSum a b x N)
      (∑ n ∈ Finset.range N,
        (-(↑(n + 1) : ℝ) * a (n + 1) * sin (↑(n + 1) * x)
          + ↑(n + 1) * b (n + 1) * cos (↑(n + 1) * x)))
      x := by
  unfold fourierPartialSum
  -- Strip the constant: reduces goal to HasDerivAt (fun x => ∑ ...) (∑ ...) x
  apply HasDerivAt.const_add
  -- HasDerivAt.sum produces: HasDerivAt (∑ n ∈ s, fun x => f n x) D p  (Pi.sum form)
  have hsum : HasDerivAt
      (∑ n ∈ Finset.range N,
        fun x => a (n + 1) * cos ((↑(n + 1) : ℝ) * x) + b (n + 1) * sin ((↑(n + 1) : ℝ) * x))
      (∑ n ∈ Finset.range N,
        (-(↑(n + 1) : ℝ) * a (n + 1) * sin ((↑(n + 1) : ℝ) * x)
          + ↑(n + 1) * b (n + 1) * cos ((↑(n + 1) : ℝ) * x)))
      x :=
    HasDerivAt.sum fun n _ => hasDerivAt_term a b (n + 1) x
  -- Bridge the form: goal has `fun x => ∑ ...`, hsum has `∑ n, fun x => ...`.
  exact hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (by intro y; simp [Finset.sum_apply, Nat.cast_succ]))

/-- Term-by-term differentiation: `HasDerivAt (fourierSeries a b) (fourierDeriv a b x) x`
whenever `∑ n * (‖aₙ‖ + ‖bₙ‖)` and `∑ (‖aₙ‖ + ‖bₙ‖)` both converge. -/
lemma fourierSeries_hasDerivAt (hab' : Summable (fun n : ℕ => (n : ℝ) * (‖a n‖ + ‖b n‖)))
    (hab : Summable (fun n => ‖a n‖ + ‖b n‖)) (x : ℝ) :
    HasDerivAt (fourierSeries a b) (fourierDeriv a b x) x := by
  -- Uniform convergence of the (n+1)-shifted derivative partial sums.
  -- Key identity: ∑ n ∈ range N, D(n+1, x) = ∑ n ∈ range (N+1), D(n, x)
  -- since D(0, x) = 0 (via Finset.sum_range_succ'). The N ↦ N+1 shift
  -- preserves atTop convergence via Filter.Tendsto.eventually.
  have hderiv_unif : TendstoUniformly
      (fun N x => ∑ n ∈ Finset.range N,
        (-(↑(n + 1) : ℝ) * a (n + 1) * sin (↑(n + 1) * x)
          + ↑(n + 1) * b (n + 1) * cos (↑(n + 1) * x)))
      (fourierDeriv a b) Filter.atTop := by
    have key : ∀ N x,
        ∑ n ∈ Finset.range N,
          (-(↑(n + 1) : ℝ) * a (n + 1) * sin (↑(n + 1) * x)
            + ↑(n + 1) * b (n + 1) * cos (↑(n + 1) * x)) =
        ∑ n ∈ Finset.range (N + 1),
          (-(↑n : ℝ) * a n * sin (↑n * x) + ↑n * b n * cos (↑n * x)) :=
      fun N x => by symm; rw [Finset.sum_range_succ']; simp
    simp_rw [key]
    exact fun u hu =>
      (Filter.tendsto_atTop_atTop.mpr fun M => ⟨M - 1, fun N hN => by omega⟩).eventually
        (fourierDeriv_uniformConvergence a b hab' u hu)
  exact hasDerivAt_of_tendstoUniformly hderiv_unif
    (Filter.Eventually.of_forall (hasDerivAt_partialSum a b))
    (fun y => (fourierSeries_uniformlyConvergence a b hab).tendsto_at y) x

/-- If `∑ n * (‖aₙ‖ + ‖bₙ‖)` and `∑ (‖aₙ‖ + ‖bₙ‖)` both converge, then the Fourier series
`fourierSeries a b` is differentiable on all of `ℝ`, with derivative `fourierDeriv a b`. -/
lemma fourierSeries_differentiable (hab' : Summable (fun n : ℕ => (n : ℝ) * (‖a n‖ + ‖b n‖)))
  (hab : Summable (fun n => ‖a n‖ + ‖b n‖)) :
    Differentiable ℝ (fourierSeries a b) :=
  fun x => (fourierSeries_hasDerivAt a b hab' hab x).differentiableAt

/-- The derivative of the Fourier series equals the ℕ⁺-indexed derivative series. -/
lemma FourierSerise_derivative (hab' : Summable (fun n : ℕ => (n : ℝ) * (‖a n‖ + ‖b n‖)))
  (hab : Summable (fun n => ‖a n‖ + ‖b n‖))
  (x : ℝ) :
    deriv (fourierSeries a b) x =
      ∑' n : ℕ+, (-(a n) * (n : ℝ) * Real.sin ((n : ℝ) * x) +
      b n * (n : ℝ) * Real.cos ((n : ℝ) * x)) := by
  rw [(fourierSeries_hasDerivAt a b hab' hab x).deriv]
  simp only [fourierDeriv]
  rw [(fourierDeriv_summable a b hab' x).tsum_eq_zero_add]
  simp only [Nat.cast_zero, neg_zero, zero_mul, zero_add]
  rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
  congr 1; ext n
  simp [Nat.succPNat, Nat.cast_succ]
  ring

/-- **Wirtinger's inequality**: `(1/pi) * int (f'(x))^2 = sum n^2 * (a n^2 + b n^2)`.
The integral formula `h_int_sq` is the Parseval identity for the derivative series,
mirroring the `h_int_sq` hypothesis in `Parsevals_thm`. -/
theorem Wirtingers_inequality
    (h_int_sq : ∫ x in (-π)..π, (deriv (fourierSeries a b) x) ^ 2 =
        π * ∑' n : ℕ+, ((n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2))) :
    (1/π) * ∫ x in (-π)..π, (deriv (fourierSeries a b) x) ^ 2 =
        ∑' n : ℕ+, ((n : ℝ)^2 * ((a n)^2 + (b n)^2)) := by
  rw [h_int_sq]
  field_simp [Real.pi_ne_zero]

end

end IsoperimetricInequality
