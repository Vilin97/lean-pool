/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# The Crouzeix--Palencia bound for disk numerical ranges

The explicit nested exhaustion by concentric circles discharges every
geometric and analytic premise of the nested scalar-companion assembly when
the closed numerical range is a disk.  On a disk the canonical closed scalar
companion is the constant `star (p(c))`, so constant polynomials give exact
approximation at every stage.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanExhaustion
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionPlemeljCircle

open Complex Filter MeasureTheory Metric Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- If the closed numerical range is a disk, it is a
`(1 + sqrt 2)`-polynomial spectral set. -/
theorem crouzeix_palencia_of_closure_numericalRange_eq_closedBall
    (A : E →L[ℂ] E) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hW : closure (numericalRange A) = Metric.closedBall c R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let Omega : ℕ → SmoothJordanDomain := fun n =>
    SmoothJordanDomain.ball c (smoothApproxRadius n + R) (by
      unfold smoothApproxRadius
      positivity)
  let K : ℕ → Set ℂ := fun n =>
    compactThickeningApprox (Metric.closedBall c R) n
  have hbaseNonempty : (Metric.closedBall c R).Nonempty := by
    refine ⟨c, ?_⟩
    rw [Metric.mem_closedBall, dist_self]
    exact hR
  obtain ⟨hanti, hcompact, hnonempty, hinter⟩ :=
    compactThickeningApprox_spec (Metric.closedBall c R)
      (isCompact_closedBall c R) hbaseNonempty
  apply
    crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_approximation
      A Omega K hanti hcompact hnonempty
  · rw [hinter, hW]
  · intro n
    dsimp only [K, Omega, compactThickeningApprox]
    have hr : 0 < smoothApproxRadius n := by
      unfold smoothApproxRadius
      positivity
    rw [cthickening_closedBall hr.le hR c]
    change Metric.closedBall c (smoothApproxRadius n + R) =
      closure (Metric.ball c (smoothApproxRadius n + R))
    rw [closure_ball c (add_pos_of_pos_of_nonneg hr hR).ne']
  · intro n z hz
    change z ∈ Metric.ball c (smoothApproxRadius n + R)
    apply Metric.closedBall_subset_ball
      (show R < smoothApproxRadius n + R by
        have hr : 0 < smoothApproxRadius n := by
          unfold smoothApproxRadius
          positivity
        linarith)
    rw [← hW]
    exact hz
  · intro n t _ht w hw
    let S : ℝ := smoothApproxRadius n + R
    have hr : 0 < smoothApproxRadius n := by
      unfold smoothApproxRadius
      positivity
    have hS : 0 < S := add_pos_of_pos_of_nonneg hr hR
    have hwc : dist w c ≤ R := by
      apply Metric.mem_closedBall.mp
      rw [← hW]
      exact subset_closure hw
    have hwS : dist w c ≤ S := by
      dsimp only [S]
      linarith
    change ((starRingEnd ℂ) (-I * deriv (circleMap c S) t) *
      (w - circleMap c S t)).re ≤ 0
    have hzeta : ‖circleMap 0 S t‖ = S := by
      rw [norm_circleMap_zero, abs_of_pos hS]
    have hnormal : -I * deriv (circleMap c S) t = circleMap 0 S t := by
      rw [deriv_circleMap]
      linear_combination (-circleMap 0 S t) * I_sq
    have hsub : w - circleMap c S t =
        (w - c) - circleMap 0 S t := by
      rw [← circleMap_sub_center c S t]
      ring
    have hfirst :
        ((starRingEnd ℂ) (circleMap 0 S t) * (w - c)).re ≤
          S * dist w c := by
      calc
        ((starRingEnd ℂ) (circleMap 0 S t) * (w - c)).re ≤
            ‖(starRingEnd ℂ) (circleMap 0 S t) * (w - c)‖ :=
          Complex.re_le_norm _
        _ = S * dist w c := by
          rw [norm_mul, Complex.norm_conj, hzeta, dist_eq_norm]
    have hsecond :
        ((starRingEnd ℂ) (circleMap 0 S t) * circleMap 0 S t).re =
          S ^ 2 := by
      rw [Complex.conj_mul', hzeta, ← Complex.ofReal_pow,
        Complex.ofReal_re]
    have hthird : S * dist w c ≤ S * S :=
      mul_le_mul_of_nonneg_left hwS hS.le
    rw [hnormal, hsub, mul_sub, Complex.sub_re]
    linarith [hfirst, hsecond, hthird]
  · intro n
    have hrNext : 0 < smoothApproxRadius (n + 1) := by
      unfold smoothApproxRadius
      positivity
    have hrThis : 0 < smoothApproxRadius n := by
      unfold smoothApproxRadius
      positivity
    have hrlt : smoothApproxRadius (n + 1) < smoothApproxRadius n := by
      unfold smoothApproxRadius
      exact Nat.one_div_lt_one_div (Nat.lt_succ_self n)
    change closure (Metric.ball c (smoothApproxRadius (n + 1) + R)) ⊆
      Metric.ball c (smoothApproxRadius n + R)
    rw [closure_ball c (add_pos_of_pos_of_nonneg hrNext hR).ne']
    exact Metric.closedBall_subset_ball (by linarith)
  · intro p n
    refine ⟨fun _j => Polynomial.C (star (Polynomial.eval c p)), ?_⟩
    intro j z hz
    have hr : 0 < smoothApproxRadius n := by
      unfold smoothApproxRadius
      positivity
    have hzstage : z ∈ Metric.closedBall c (smoothApproxRadius n + R) := by
      change z ∈ Metric.cthickening (smoothApproxRadius n)
        (Metric.closedBall c R) at hz
      rwa [cthickening_closedBall hr.le hR c] at hz
    change ‖Polynomial.eval z (Polynomial.C (star (Polynomial.eval c p))) -
      crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c (smoothApproxRadius n + R)
          (add_pos_of_pos_of_nonneg hr hR)) p z‖ ≤
        1 / ((j : ℝ) + 1)
    rw [Polynomial.eval_C,
      crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
        c (add_pos_of_pos_of_nonneg hr hR) p hzstage,
      sub_self, norm_zero]
    positivity

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
