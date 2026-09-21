/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Stage 2, Route C: quantitative `ell_p` convexity

This file isolates the Clarkson / Ball--Carlen--Lieb route to
`O3.belowGeometry`.  The key point of the investigation is that Mathlib's
abstract `UniformConvexSpace` class exposes only an existential modulus.  The
exact quantitative input needed here is therefore recorded explicitly below,
but only as a proposition carrier, never as an assumption or an axiom.
-/

open scoped BigOperators

namespace O3.Stage2RouteC

/-- The literal O3 norm is definitionally the finite `PiLp` norm after the
standard `ENNReal.ofReal` exponent conversion. -/
theorem lpNorm_eq_piLpNorm {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : O3.Point d) :
    O3.lpNorm p x =
      ‖(WithLp.toLp (ENNReal.ofReal p) x :
        PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖ := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [PiLp.norm_eq_sum]
  · simp [O3.lpNorm, O3.lpPower, ENNReal.toReal_ofReal (zero_le_one.trans hp)]
  · simpa [ENNReal.toReal_ofReal (zero_le_one.trans hp)] using (zero_lt_one.trans_le hp)

/-- Homogeneity of the literal O3 norm, obtained without changing norms by
transporting to Mathlib's finite `PiLp` norm. -/
theorem lpNorm_smul {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (a : ℝ) (x : O3.Point d) :
    O3.lpNorm p (a • x) = |a| * O3.lpNorm p x := by
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLpNorm hp, lpNorm_eq_piLpNorm hp]
  change ‖a • (WithLp.toLp (ENNReal.ofReal p) x :
      PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖ =
    |a| * ‖(WithLp.toLp (ENNReal.ofReal p) x :
      PiLp (ENNReal.ofReal p) (fun _ : Fin d ↦ ℝ))‖
  exact norm_smul a _

/-- At the endpoint `p = 2`, the transport reduces the literal O3 norm to the
usual finite sum of coordinate squares. -/
theorem lpNorm_two_sq {d : ℕ} (x : O3.Point d) :
    (O3.lpNorm 2 x) ^ (2 : ℕ) = ∑ i, (x i) ^ (2 : ℕ) := by
  rw [lpNorm_eq_piLpNorm (p := (2 : ℝ)) (by norm_num)]
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [htwo]
  change ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin d ↦ ℝ))‖ ^ (2 : ℕ) =
    ∑ i, (x i) ^ (2 : ℕ)
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Endpoint sanity check: BCL is the parallelogram identity at `p = 2`.
This covers arbitrary dimension and all zero cases. -/
theorem ballCarlenLieb_at_two {d : ℕ} (u v : O3.Point d) :
    (O3.lpNorm 2 (u + v)) ^ (2 : ℕ) +
        ((2 : ℝ) - 1) * (O3.lpNorm 2 (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm 2 u) ^ (2 : ℕ) + (O3.lpNorm 2 v) ^ (2 : ℕ)) := by
  simp_rw [lpNorm_two_sq]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, one_mul, ← Finset.sum_add_distrib]
  have hcoord : ∀ i : Fin d,
      (u i + v i) ^ (2 : ℕ) + (u i - v i) ^ (2 : ℕ) =
        2 * ((u i) ^ (2 : ℕ) + (v i) ^ (2 : ℕ)) := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hcoord i)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- In one dimension the literal `ell_p` norm is absolute value for every
positive real exponent. -/
theorem lpNorm_fin_one {p : ℝ} (hp : 0 < p) (x : O3.Point 1) :
    O3.lpNorm p x = |x 0| := by
  simp only [O3.lpNorm, O3.lpPower, Fin.sum_univ_one]
  rw [← Real.rpow_mul (abs_nonneg (x 0))]
  have hp0 : p ≠ 0 := hp.ne'
  rw [mul_one_div_cancel hp0, Real.rpow_one]

/-- One-dimensional sanity check for the whole real range `1 < p ≤ 2`.
The exact coefficient follows from a scalar square identity. -/
theorem ballCarlenLieb_fin_one {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (u v : O3.Point 1) :
    (O3.lpNorm p (u + v)) ^ (2 : ℕ) +
        (p - 1) * (O3.lpNorm p (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm p u) ^ (2 : ℕ) + (O3.lpNorm p v) ^ (2 : ℕ)) := by
  simp_rw [lpNorm_fin_one (zero_lt_one.trans hp)]
  simp only [Pi.add_apply, Pi.sub_apply, sq_abs]
  nlinarith [sq_nonneg (u 0 - v 0)]

/-- The exact Ball--Carlen--Lieb inequality needed by Route C.  This is a
transparent proposition describing the first missing quantitative input; it is
not registered as a theorem and is not used as a hidden hypothesis of the O3
target. -/
noncomputable def BallCarlenLiebStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (u v : O3.Point d),
    (O3.lpNorm p (u + v)) ^ (2 : ℕ) +
        (p - 1) * (O3.lpNorm p (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm p u) ^ (2 : ℕ) + (O3.lpNorm p v) ^ (2 : ℕ))

/-- Exact midpoint form of `(p-1)`-strong convexity for the squared `ell_p`
norm.  It is the quantitative form that an unspecified uniform-convexity
modulus cannot supply. -/
noncomputable def ExactMidpointStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (x y : O3.Point d),
    (1 / 2 : ℝ) * (O3.lpNorm p ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (O3.lpNorm p x) ^ (2 : ℕ)) +
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (O3.lpNorm p y) ^ (2 : ℕ)) -
        (1 / 4 : ℝ) * ((p - 1) / 2) * (O3.lpNorm p (x - y)) ^ (2 : ℕ)

/-- The exact BCL inequality implies the exact midpoint strong-convexity
inequality with no loss in the coefficient. -/
theorem ballCarlenLieb_implies_exactMidpoint
    (hBCL : BallCarlenLiebStatement) : ExactMidpointStatement := by
  intro p hp hp2 d x y
  have hp1 : 1 ≤ p := hp.le
  have havg :
      (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnormAvg :
      O3.lpNorm p ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) =
        (1 / 2 : ℝ) * O3.lpNorm p (x + y) := by
    rw [havg, lpNorm_smul hp1]
    norm_num
  have h := hBCL p hp hp2 d x y
  rw [hnormAvg]
  nlinarith

end O3.Stage2RouteC
