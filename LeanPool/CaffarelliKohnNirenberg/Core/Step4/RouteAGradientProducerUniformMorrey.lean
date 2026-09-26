/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Inclusions

/-!
# Route AGradient Producer Uniform Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! # Lowering the second Morrey exponent on a parabolic ball

The vector Morrey membership of `def:parabolic-morrey` is defined on a metric
ball of finite radius.  A function whose Morrey seminorm is finite at an
exponent pair `(P, τ)` also has finite seminorm at any pair `(P, τ')` with
`τ' ≤ τ`, because the ball sits inside a fixed parabolic cylinder and the
bounded-support Morrey inclusion is available there.  The results here expose
that monotonicity directly on the metric-ball formulation, which is the shape
consumed downstream. -/

/-- Parabolic Morrey inclusion on a ball of finite radius: if a vector field has
finite Morrey seminorm for the exponent pair `(P, τ)` on `Metric.ball z₀ R`,
then it has finite seminorm for `(P, τ')` whenever `P ≤ τ' ≤ τ`.  This is the
ball-level form of `def:parabolic-morrey`, obtained from the bounded-support
inclusion for the cylinder containing the ball. -/
theorem morreyVecMem_ball_of_exponent_le
    {P τ τ' : ℝ} (hP : 1 ≤ P) (hPτ' : P ≤ τ') (hτ'τ : τ' ≤ τ)
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    {u : ParabolicPoint → Vec3}
    (hu : morreyVecMem P τ (Metric.ball z₀ R) u) :
    morreyVecMem P τ' (Metric.ball z₀ R) u := by
  intro i
  set f : ParabolicPoint → ℝ := (Metric.ball z₀ R).indicator (fun z => u z i) with hf
  have hPτ : P ≤ τ := le_trans hPτ' hτ'τ
  have hfinτ : morreyNorm P τ f < ∞ := by
    rw [hf]
    exact (morreyNorm_le_morreyBallNorm (le_trans zero_le_one hP) hPτ _).trans_lt (hu i)
  have hsupp : ∀ w ∉ parabolicCylinder z₀.1 (z₀.2 + R ^ 2) (2 * R), f w = 0 := by
    intro w hw
    rw [hf]
    exact Set.indicator_of_notMem
      (fun hm => hw (metricBall_subset_parabolicCylinder_doubled z₀ hR hm)) _
  have hbs := morreyNorm_bounded_support (p := P) (q := τ) (q' := τ')
    (f := f) (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R) hP hPτ hPτ' hτ'τ
    (by positivity : (0 : ℝ) < 2 * R) hsupp
  have hdiff : 0 ≤ 5 * (1 / τ' - 1 / τ) := by
    have hle : 1 / τ ≤ 1 / τ' :=
      one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (le_trans hP hPτ')) hτ'τ
    linarith only [hle]
  have hfinτ' : morreyNorm P τ' f < ∞ :=
    hbs.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hdiff ENNReal.ofReal_ne_top) hfinτ)
  have hbridge := morreyBallNorm_le_two_rpow_mul_morreyNorm hP hPτ' f
  have hdiff' : 0 ≤ 5 * (1 / P - 1 / τ') := by
    have hle : 1 / τ' ≤ 1 / P :=
      one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hP) hPτ'
    linarith only [hle]
  exact hbridge.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hdiff' (by norm_num)) hfinτ')

/-- Parabolic Morrey inclusion on a ball of finite radius at the base exponent
`P = 3`: a vector field with finite Morrey seminorm for `(3, τ)` on
`Metric.ball z₀ R` has finite seminorm for `(3, 25 / 3)` whenever
`25 / 3 ≤ τ`.  This is `def:parabolic-morrey` at the exponent used by the
gradient producer. -/
theorem morreyVecMem_ball_three_base_of_le
    {τ : ℝ} (hτ : 25 / 3 ≤ τ)
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    {u : ParabolicPoint → Vec3}
    (hu : morreyVecMem 3 τ (Metric.ball z₀ R) u) :
    morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u :=
  morreyVecMem_ball_of_exponent_le (P := 3) (τ := τ) (τ' := 25 / 3)
    (by norm_num) (by norm_num) hτ hR hu

end CKN.Core.Step4
