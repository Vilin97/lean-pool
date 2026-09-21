/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! # Strong Entropy -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Quantitative concavity from row entropy

The extra row-entropy regularizer is not merely strictly concave.  On the
probability cube it supplies a uniform quadratic Jensen gap.  This is the
bridge from objective accuracy to coordinate accuracy in the executable
optimizer.
-/

/-- On `[0,1]`, `x log x` is one-strongly convex. -/
theorem strongConvexOn_mul_log_Icc :
    StrongConvexOn (Set.Icc (0 : ℝ) 1) 1
      (fun x : ℝ ↦ x * Real.log x) := by
  rw [strongConvexOn_iff_convex]
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun x : ℝ ↦ x * Real.log x - x ^ 2 / 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    · exact (Real.continuous_mul_log.sub
        (continuous_id.pow 2 |>.div_const 2)).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      convert (Real.hasDerivAt_mul_log hx0).sub
        ((hasDerivAt_pow 2 x).div_const 2) |>.hasDerivWithinAt using 1 <;>
        ring
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      convert (((hasDerivAt_const x 1).add
        (Real.hasDerivAt_log hx0)).sub (hasDerivAt_id x)).hasDerivWithinAt
          using 1
      · funext u
        norm_num
        ring
    · intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < x := hx.1
      have hxle : x ≤ 1 := hx.2.le
      have hinv : 1 ≤ x⁻¹ := by
        have hdiv : 1 ≤ 1 / x := (le_div_iff₀ hxpos).2 (by simpa using hxle)
        simpa only [one_div] using hdiv
      linarith
  convert hconv using 1
  funext x
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- Scalar quadratic Jensen bonus for `negMulLog`. -/
theorem negMulLog_segment_gap_quadratic
    {t x y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 - t) * Real.negMulLog x + t * Real.negMulLog y +
        ((1 - t) * t / 2) * (x - y) ^ 2 ≤
      Real.negMulLog ((1 - t) * x + t * y) := by
  have hstrong := strongConvexOn_mul_log_Icc.2
    (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    (Set.mem_Icc.mpr ⟨hy0, hy1⟩)
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, one_div] at hstrong
  change (1 - t) * (-x * Real.log x) + t * (-y * Real.log y) +
      (1 - t) * t / 2 * (x - y) ^ 2 ≤
    -((1 - t) * x + t * y) * Real.log ((1 - t) * x + t * y)
  rw [Real.norm_eq_abs, sq_abs] at hstrong
  linarith

/-- Summing the scalar bonus gives a Frobenius-square Jensen gap for total
row entropy. -/
theorem totalRowEntropy_segment_quadratic
    {ι : Type*} [Fintype ι]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {X Y : Matrix ι ι ℝ}
    (hX0 : Matrix.Nonnegative X) (hX1 : ∀ i j, X i j ≤ 1)
    (hY0 : Matrix.Nonnegative Y) (hY1 : ∀ i j, Y i j ≤ 1) :
    (1 - t) * totalRowEntropy X + t * totalRowEntropy Y +
        ((1 - t) * t / 2) * (∑ i, ∑ j, (X i j - Y i j) ^ 2) ≤
      totalRowEntropy (matrixSegment t X Y) := by
  simp only [totalRowEntropy, shannonEntropy]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa only [matrixSegment, mul_assoc] using
    negMulLog_segment_gap_quadratic ht0 ht1
      (hX0 i j) (hX1 i j) (hY0 i j) (hY1 i j)

/-- Strong-concavity form of the regularized Bethe segment inequality. -/
theorem regularizedBetheObjective_segment_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A : Matrix ι ι ℝ) {X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y) :
    (1 - t) * regularizedBetheObjective τ A X +
        t * regularizedBetheObjective τ A Y +
        τ * (((1 - t) * t / 2) *
          (∑ i, ∑ j, (X i j - Y i j) ^ 2)) ≤
      regularizedBetheObjective τ A (matrixSegment t X Y) := by
  have hbethe := betheObjective_segment_lower hcard A X Y hX hY ht0 ht1
  have hsegment : betheMatrixSegment t X Y = matrixSegment t X Y := by
    ext i j
    rfl
  rw [hsegment] at hbethe
  have hentropy := totalRowEntropy_segment_quadratic ht0 ht1
    hX.nonnegative (fun i j ↦ hX.entry_le_one i j)
    hY.nonnegative (fun i j ↦ hY.entry_le_one i j)
  have hscaled := mul_le_mul_of_nonneg_left hentropy hτ
  rw [regularizedBetheObjective, regularizedBetheObjective,
    regularizedBetheObjective]
  nlinarith

/-- Objective suboptimality controls squared distance from any exact
regularized maximizer.  The fixedValue `τ/4` comes from the midpoint case. -/
theorem regularizedBetheMaximizer_distance_sq_le_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    {τ : ℝ} (hτ : 0 ≤ τ) {A X Y : Matrix ι ι ℝ}
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    (hmax : ∀ Z, IsDoublyStochastic Z →
      regularizedBetheObjective τ A Z ≤
        regularizedBetheObjective τ A X) :
    (τ / 4) * (∑ i, ∑ j, (X i j - Y i j) ^ 2) ≤
      regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A Y := by
  have hmidDS := matrixSegment_doublyStochastic
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) hX hY
  have hupper := hmax _ hmidDS
  have hlower := regularizedBetheObjective_segment_quadratic
    hcard hτ (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) A hX hY
  norm_num at hlower
  nlinarith

end BeyondBethe
