/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Operator-valued Cauchy formula on a centered circle

This file proves the circle model of the operator-valued Cauchy formula used
in the Crouzeix--Palencia argument.  If a circle has radius strictly larger
than the norm of an element `A` in a complex Banach algebra, then the
normalized contour integral of its resolvent is the identity.  Multiplying
the integrand by a polynomial recovers polynomial evaluation at `A`.

The resolvent identity is proved directly from the uniformly convergent
Laurent expansion

`R_A(z) = sum n, z^(-(n + 1)) • A^n`.

Thus no holomorphic-functional-calculus theorem is hidden in the result.
The present hypotheses describe the centered disk model `‖A‖ < R`; they do
not replace the separate smooth-domain or numerical-range approximation
needed for the full Crouzeix--Palencia capstone.

## Main declarations

* `normalized_circleIntegral_resolvent_eq_one` -- the normalized resolvent
  integral is the identity.
* `circleIntegral_resolvent_eq_two_pi_I_smul_one` -- the same identity in
  the unnormalized form used by double-layer mass calculations.
* `circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt` --
  the corresponding identity on a circle with arbitrary center.
* `normalized_circleIntegral_zpow_smul_resolvent_eq_pow` -- the monomial
  operator Cauchy formula.
* `normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero` -- every strictly
  negative Laurent mode of the centered resolvent integral vanishes.
* `normalized_circleIntegral_eval_smul_resolvent_eq_aeval` -- the polynomial
  operator Cauchy formula.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts

open Complex Set spectrum TopologicalSpace
open scoped Real Interval

universe u

variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]

private theorem smul_resolvent_eq_one_add_mul (A : B) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    z • resolvent A z = 1 + A * resolvent A z := by
  have hmul : (z • (1 : B) - A) * resolvent A z = 1 := by
    have hunit : z • (1 : B) - A = (hz.unit : B) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hz.unit_spec.symm
    calc
      (z • (1 : B) - A) * resolvent A z =
          (hz.unit : B) * (↑((hz.unit)⁻¹) : B) := by
            rw [hunit, spectrum.resolvent_eq hz]
      _ = 1 := Units.mul_inv _
  rw [sub_mul, smul_mul_assoc, one_mul] at hmul
  exact eq_add_of_sub_eq hmul

variable [CompleteSpace B]

private theorem resolvent_eq_tsum_inv_pow_smul_pow (A : B) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    resolvent A z = ∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have hz' : ‖A‖ < 0 := by simpa only [norm_zero] using hz
    exact (not_lt_of_ge (norm_nonneg A)) hz'
  let zu : ℂˣ := Units.mk0 z hz0
  have hscale : z • resolvent A z = resolvent (z⁻¹ • A) (1 : ℂ) := by
    simpa [zu, Units.smul_def] using
      (spectrum.units_smul_resolvent_self (r := zu) (a := A))
  have hsmall : ‖z⁻¹ • A‖ < 1 := by
    rw [norm_smul, norm_inv]
    rw [inv_mul_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz
  have hseries : resolvent (z⁻¹ • A) (1 : ℂ) = ∑' n : ℕ, (z⁻¹ • A) ^ n := by
    unfold resolvent
    rw [Algebra.algebraMap_eq_smul_one, one_smul]
    exact NormedRing.inverse_one_sub _ hsmall
  calc
    resolvent A z = z⁻¹ • (z • resolvent A z) := by
      rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
    _ = z⁻¹ • resolvent (z⁻¹ • A) (1 : ℂ) := congrArg _ hscale
    _ = z⁻¹ • ∑' n : ℕ, (z⁻¹ • A) ^ n := congrArg _ hseries
    _ = ∑' n : ℕ, z⁻¹ • (z⁻¹ • A) ^ n := (tsum_const_smul'' _).symm
    _ = ∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n := by
      congr 1
      funext n
      rw [smul_pow, smul_smul]
      congr 1
      ring

omit [CompleteSpace B] in
private theorem circleIntegrable_zpow_smul_one {R : ℝ} (n : ℕ) :
    CircleIntegrable (fun z : ℂ => z ^ n • (1 : B)) 0 R := by
  exact ((continuous_pow n).smul continuous_const).continuousOn.circleIntegrable'

private theorem circleIntegral_zpow_smul_one_eq_zero {R : ℝ} (n : ℕ) :
    circleIntegral (fun z : ℂ => z ^ n • (1 : B)) 0 R = 0 := by
  rw [circleIntegral.integral_smul_const]
  have hne : (n : ℤ) ≠ -1 := by omega
  rw [show circleIntegral (fun z : ℂ => z ^ n) 0 R = 0 by
    simpa only [sub_zero, zpow_natCast] using
      (circleIntegral.integral_sub_zpow_of_ne hne 0 0 R)]
  exact zero_smul _ _

variable [NormOneClass B]

/-- The normalized resolvent integral on a centered circle enclosing `A` is
the identity.  The strict norm bound supplies a uniformly convergent Laurent
series on the whole circle. -/
theorem normalized_circleIntegral_resolvent_eq_one_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R = (1 : B) := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hderiv : Continuous (deriv (circleMap 0 R)) :=
    (contDiff_circleMap 0 R).continuous_deriv (n := 2) (by norm_num)
  have hcircle_ne : ∀ t, circleMap 0 R t ≠ 0 := fun _ =>
    circleMap_ne_center hRpos.ne'
  have hinv : Continuous (fun t => (circleMap 0 R t)⁻¹) :=
    Continuous.inv₀ (continuous_circleMap 0 R) hcircle_ne
  let term : ℕ → C(ℝ, B) := fun n =>
    ⟨fun t => deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n), by
      exact hderiv.smul ((hinv.pow (n + 1)).smul continuous_const)⟩
  have hratio : ‖A‖ / R < 1 := (div_lt_one hRpos).mpr hR
  have hterm_norm (n : ℕ) :
      ‖(term n).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ ≤
        (‖A‖ / R) ^ n := by
    apply (ContinuousMap.norm_le _
      (pow_nonneg (div_nonneg (norm_nonneg A) hRpos.le) n)).2
    intro t
    change ‖deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n)‖ ≤ (‖A‖ / R) ^ n
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hRpos,
      norm_I, mul_one, norm_smul, norm_pow, norm_inv, norm_circleMap_zero,
      abs_of_pos hRpos]
    calc
      R * (R⁻¹ ^ (n + 1) * ‖A ^ n‖) ≤
          R * (R⁻¹ ^ (n + 1) * ‖A‖ ^ n) := by
        gcongr
        exact norm_pow_le A n
      _ = (‖A‖ / R) ^ n := by
        rw [pow_succ]
        calc
          R * (R⁻¹ ^ n * R⁻¹ * ‖A‖ ^ n) =
              (R * R⁻¹) * (R⁻¹ ^ n * ‖A‖ ^ n) := by ring
          _ = R⁻¹ ^ n * ‖A‖ ^ n := by rw [mul_inv_cancel₀ hRpos.ne', one_mul]
          _ = (‖A‖ * R⁻¹) ^ n := by rw [mul_pow]; ring
          _ = (‖A‖ / R) ^ n := by rw [div_eq_mul_inv]
  have hsum : Summable fun n =>
      ‖(term n).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_norm
      (summable_geometric_of_lt_one (div_nonneg (norm_nonneg A) hRpos.le) hratio)
  have hinterchange := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  have hpoint (t : ℝ) :
      (∑' n : ℕ, term n t) =
        deriv (circleMap 0 R) t • resolvent A (circleMap 0 R t) := by
    have hzt : ‖A‖ < ‖circleMap 0 R t‖ := by
      simpa only [norm_circleMap_zero, abs_of_pos hRpos] using hR
    rw [show (∑' n : ℕ, term n t) =
        ∑' n : ℕ, deriv (circleMap 0 R) t •
          ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n) by rfl]
    rw [tsum_const_smul'']
    congr 1
    exact (resolvent_eq_tsum_inv_pow_smul_pow A hzt).symm
  have hcircle : circleIntegral (resolvent A) 0 R =
      ∑' n : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term n t := by
    unfold circleIntegral
    rw [hinterchange]
    apply intervalIntegral.integral_congr
    intro t _
    exact (hpoint t).symm
  have hterm_as_circle (n : ℕ) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term n t) =
        circleIntegral (fun z : ℂ => z⁻¹ ^ (n + 1) • A ^ n) 0 R := by
    rfl
  have hterm_zero :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term 0 t) =
        (2 * (Real.pi : ℂ) * I) • (1 : B) := by
    rw [hterm_as_circle]
    simp only [zero_add, pow_one, pow_zero]
    rw [circleIntegral.integral_smul_const]
    rw [show circleIntegral (fun z : ℂ => z⁻¹) 0 R = 2 * (Real.pi : ℂ) * I by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hRpos.ne']
  have hterm_vanish (n : ℕ) (hn : n ≠ 0) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term n t) = 0 := by
    rw [hterm_as_circle, circleIntegral.integral_smul_const]
    have hne : (Int.negSucc n) ≠ -1 := by omega
    rw [show circleIntegral (fun z : ℂ => z⁻¹ ^ (n + 1)) 0 R = 0 by
      simpa only [sub_zero, zpow_negSucc, inv_pow] using
        (circleIntegral.integral_sub_zpow_of_ne hne 0 0 R)]
    exact zero_smul _ _
  have hsum_integrals :
      (∑' n : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term n t) =
        (2 * (Real.pi : ℂ) * I) • (1 : B) := by
    rw [tsum_eq_single 0]
    · exact hterm_zero
    · intro n hn
      exact hterm_vanish n hn
  rw [hcircle, hsum_integrals, smul_smul]
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  rw [inv_mul_cancel₀ hscalar, one_smul]

private theorem continuousOn_resolvent_circle (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    ContinuousOn (fun z : ℂ => resolvent A z) (Metric.sphere (0 : ℂ) R) := by
  intro z hz
  have hzNorm : ‖z‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact (spectrum.hasDerivAt_resolvent_const_left
    (spectrum.mem_resolventSet_of_norm_lt (hzNorm ▸ hR))).continuousAt.continuousWithinAt

private theorem circleIntegrable_zpow_smul_resolvent (A : B) {R : ℝ}
    (hR : ‖A‖ < R) (n : ℕ) :
    CircleIntegrable (fun z : ℂ => z ^ n • resolvent A z) 0 R := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_pos hRpos]
  exact (continuous_pow n).continuousOn.smul (continuousOn_resolvent_circle A hR)

/-- The normalized resolvent integral sends the scalar monomial `z^n` to
the algebra power `A^n`. -/
theorem normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_smul] using
        normalized_circleIntegral_resolvent_eq_one_of_normOne A hR
  | succ n ih =>
      have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
      have hsplit : circleIntegral (fun z : ℂ => z ^ (n + 1) • resolvent A z) 0 R =
          circleIntegral (fun z : ℂ => z ^ n • (1 : B) +
            A * (z ^ n • resolvent A z)) 0 R := by
        apply circleIntegral.integral_congr hRpos.le
        intro z hz
        have hzNorm : ‖z‖ = R := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hz
        have hzRes : z ∈ resolventSet ℂ A :=
          spectrum.mem_resolventSet_of_norm_lt (hzNorm ▸ hR)
        calc
          z ^ (n + 1) • resolvent A z = z ^ n • (z • resolvent A z) := by
            rw [pow_succ, smul_smul]
          _ = z ^ n • (1 + A * resolvent A z) :=
            congrArg _ (smul_resolvent_eq_one_add_mul A hzRes)
          _ = z ^ n • (1 : B) + A * (z ^ n • resolvent A z) := by
            rw [smul_add, mul_smul_comm]
      have hAint : CircleIntegrable (fun z : ℂ => A * (z ^ n • resolvent A z)) 0 R := by
        apply ContinuousOn.circleIntegrable'
        rw [abs_of_pos hRpos]
        exact continuousOn_const.mul
          ((continuous_pow n).continuousOn.smul (continuousOn_resolvent_circle A hR))
      rw [hsplit, circleIntegral.integral_add (circleIntegrable_zpow_smul_one n) hAint,
        circleIntegral_zpow_smul_one_eq_zero, zero_add]
      rw [show circleIntegral (fun z : ℂ => A * (z ^ n • resolvent A z)) 0 R =
          A * circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R by
        simpa only [contourIntegral_circleMap] using
          contourIntegral_const_mul A
            (show ContourIntegrable (fun z : ℂ => z ^ n • resolvent A z) (circleMap 0 R) by
              exact (contourIntegrable_circleMap_iff R).mpr
                (circleIntegrable_zpow_smul_resolvent A hR n))]
      rw [← mul_smul_comm, ih, pow_succ']

private theorem circleIntegrable_eval_smul_resolvent (A : B) {R : ℝ}
    (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    CircleIntegrable (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_pos hRpos]
  exact p.continuous.continuousOn.smul (continuousOn_resolvent_circle A hR)

/-- The operator-valued Cauchy formula for polynomials on a centered circle:
integrating `p(z) R_A(z)` recovers `p(A)`. -/
theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
        Polynomial.aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun : (fun z : ℂ => Polynomial.eval z (p + q) • resolvent A z) =
          fun z => Polynomial.eval z p • resolvent A z +
            Polynomial.eval z q • resolvent A z := by
        funext z
        rw [Polynomial.eval_add, add_smul]
      rw [hfun, circleIntegral.integral_add
        (circleIntegrable_eval_smul_resolvent A hR p)
        (circleIntegrable_eval_smul_resolvent A hR q), smul_add, hp, hq,
        Polynomial.aeval_add]
  | monomial n a =>
      have hfun : (fun z : ℂ => Polynomial.eval z (Polynomial.monomial n a) • resolvent A z) =
          fun z => a • (z ^ n • resolvent A z) := by
        funext z
        rw [Polynomial.eval_monomial, smul_smul]
      rw [hfun, circleIntegral.integral_smul, smul_smul]
      rw [show (2 * (Real.pi : ℂ) * I)⁻¹ * a =
          a * (2 * (Real.pi : ℂ) * I)⁻¹ by ring]
      rw [← smul_smul, normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne A hR n]
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private theorem normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 R = 0 := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hderiv : Continuous (deriv (circleMap 0 R)) :=
    (contDiff_circleMap 0 R).continuous_deriv (n := 2) (by norm_num)
  have hcircle_ne : ∀ t, circleMap 0 R t ≠ 0 := fun _ =>
    circleMap_ne_center hRpos.ne'
  have hinv : Continuous (fun t => (circleMap 0 R t)⁻¹) :=
    Continuous.inv₀ (continuous_circleMap 0 R) hcircle_ne
  let term : ℕ → C(ℝ, B) := fun k =>
    ⟨fun t => deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + k + 1) • A ^ k), by
      exact hderiv.smul ((hinv.pow (n + k + 1)).smul continuous_const)⟩
  have hratio : ‖A‖ / R < 1 := (div_lt_one hRpos).mpr hR
  have hterm_norm (k : ℕ) :
      ‖(term k).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ ≤
        R⁻¹ ^ n * (‖A‖ / R) ^ k := by
    apply (ContinuousMap.norm_le _
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hRpos.le) n)
        (pow_nonneg (div_nonneg (norm_nonneg A) hRpos.le) k))).2
    intro t
    change ‖deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + k + 1) • A ^ k)‖ ≤
          R⁻¹ ^ n * (‖A‖ / R) ^ k
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hRpos,
      norm_I, mul_one, norm_smul, norm_pow, norm_inv, norm_circleMap_zero,
      abs_of_pos hRpos]
    calc
      R * (R⁻¹ ^ (n + k + 1) * ‖A ^ k‖) ≤
          R * (R⁻¹ ^ (n + k + 1) * ‖A‖ ^ k) := by
        gcongr
        exact norm_pow_le A k
      _ = R⁻¹ ^ n * (‖A‖ / R) ^ k := by
        rw [show n + k + 1 = n + (k + 1) by omega, pow_add, pow_succ]
        calc
          R * (R⁻¹ ^ n * (R⁻¹ ^ k * R⁻¹) * ‖A‖ ^ k) =
              R⁻¹ ^ n * (R * R⁻¹) * (R⁻¹ ^ k * ‖A‖ ^ k) := by ring
          _ = R⁻¹ ^ n * (R⁻¹ ^ k * ‖A‖ ^ k) := by
            rw [mul_inv_cancel₀ hRpos.ne', mul_one]
          _ = R⁻¹ ^ n * (‖A‖ * R⁻¹) ^ k := by rw [mul_pow]; ring
          _ = R⁻¹ ^ n * (‖A‖ / R) ^ k := by rw [div_eq_mul_inv]
  have hsum : Summable fun k =>
      ‖(term k).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_norm
      ((summable_geometric_of_lt_one (div_nonneg (norm_nonneg A) hRpos.le) hratio).mul_left
        (R⁻¹ ^ n))
  have hinterchange := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  have hpoint (t : ℝ) :
      (∑' k : ℕ, term k t) = deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ n • resolvent A (circleMap 0 R t)) := by
    have hzt : ‖A‖ < ‖circleMap 0 R t‖ := by
      simpa only [norm_circleMap_zero, abs_of_pos hRpos] using hR
    rw [show (∑' k : ℕ, term k t) =
        ∑' k : ℕ, deriv (circleMap 0 R) t •
          ((circleMap 0 R t)⁻¹ ^ (n + k + 1) • A ^ k) by rfl]
    rw [tsum_const_smul'']
    congr 1
    rw [resolvent_eq_tsum_inv_pow_smul_pow A hzt]
    rw [← tsum_const_smul'']
    congr 1
    funext k
    rw [smul_smul, ← pow_add]
    congr 2
  have hcircle : circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 R =
      ∑' k : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term k t := by
    unfold circleIntegral
    rw [hinterchange]
    apply intervalIntegral.integral_congr
    intro t _
    exact (hpoint t).symm
  have hterm_as_circle (k : ℕ) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term k t) =
        circleIntegral (fun z : ℂ => z⁻¹ ^ (n + k + 1) • A ^ k) 0 R := by
    rfl
  have hterm_vanish (k : ℕ) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term k t) = 0 := by
    rw [hterm_as_circle, circleIntegral.integral_smul_const]
    have hne : (Int.negSucc (n + k)) ≠ -1 := by omega
    rw [show circleIntegral (fun z : ℂ => z⁻¹ ^ (n + k + 1)) 0 R = 0 by
      simpa only [sub_zero, zpow_negSucc, inv_pow] using
        (circleIntegral.integral_sub_zpow_of_ne hne 0 0 R)]
    exact zero_smul _ _
  rw [hcircle]
  have hzero :
      (∑' k : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term k t) = 0 := by
    have hfun : (fun k : ℕ => ∫ t in (0 : ℝ)..(2 * Real.pi), term k t) =
        fun _ => 0 := funext hterm_vanish
    rw [hfun, tsum_zero]
  rw [hzero, smul_zero]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every strictly negative Laurent mode of the normalized centered resolvent
integral vanishes. -/
theorem normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 R = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_normOne A hR n hn

/-- The normalized resolvent integral for an operator on any complex Hilbert
space, including the zero space. -/
theorem normalized_circleIntegral_resolvent_eq_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R =
      (1 : E →L[ℂ] E) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_resolvent_eq_one_of_normOne A hR

/-- Unnormalized form of the resolvent Cauchy identity, matching the mass
hypothesis used by the double-layer normalization lemmas. -/
theorem circleIntegral_resolvent_eq_two_pi_I_smul_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    circleIntegral (resolvent A) 0 R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have h := congrArg (fun T : E →L[ℂ] E => (2 * (Real.pi : ℂ) * I) • T)
    (normalized_circleIntegral_resolvent_eq_one A hR)
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  simpa only [smul_smul, mul_inv_cancel₀ hscalar, one_smul] using h

/-- The monomial operator Cauchy formula on any complex Hilbert space. -/
theorem normalized_circleIntegral_zpow_smul_resolvent_eq_pow
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne A hR n

/-- The polynomial operator Cauchy formula on any complex Hilbert space. -/
theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
        Polynomial.aeval A p := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne A hR p

/-- Unnormalized polynomial operator Cauchy formula. -/
theorem circleIntegral_eval_smul_resolvent_eq_two_pi_I_smul_aeval
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
      (2 * (Real.pi : ℂ) * I) • Polynomial.aeval A p := by
  have h := congrArg (fun T : E →L[ℂ] E => (2 * (Real.pi : ℂ) * I) • T)
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p)
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  simpa only [smul_smul, mul_inv_cancel₀ hscalar, one_smul] using h

omit [CompleteSpace E] in
/-- Translating both the operator and spectral parameter by `c` leaves the
resolvent unchanged. -/
theorem resolvent_sub_smul_one_shift (A : E →L[ℂ] E) (c z : ℂ) :
    resolvent (A - c • (1 : E →L[ℂ] E)) z = resolvent A (z + c) := by
  unfold resolvent
  congr 1
  simp only [Algebra.algebraMap_eq_smul_one]
  module

/-- The unnormalized resolvent Cauchy identity on a circle centered at `c`.
The hypothesis is the translated Neumann-series condition
`‖A - c • 1‖ < R`. -/
theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : ‖A - c • (1 : E →L[ℂ] E)‖ < R) :
    circleIntegral (resolvent A) c R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  let B := A - c • (1 : E →L[ℂ] E)
  have hcenter : circleIntegral (resolvent A) c R = circleIntegral (resolvent B) 0 R := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have hmap : circleMap c R t = circleMap 0 R t + c := by
      rw [← circleMap_sub_center c R t]
      ring
    have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
      rw [deriv_circleMap, deriv_circleMap]
    change deriv (circleMap c R) t • resolvent A (circleMap c R t) =
      deriv (circleMap 0 R) t • resolvent B (circleMap 0 R t)
    rw [hderiv]
    congr 1
    rw [show resolvent A (circleMap c R t) = resolvent B (circleMap 0 R t) by
      rw [hmap]
      exact (resolvent_sub_smul_one_shift A c (circleMap 0 R t)).symm]
  rw [hcenter]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one B hR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
