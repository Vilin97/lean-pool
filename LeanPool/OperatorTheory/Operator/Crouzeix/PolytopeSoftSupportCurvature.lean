/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Curvature of finite soft support functions

For the log-sum-exp regularization `h` of a finite directional support
function, the support-curve curvature radius is `h + h''`.  This file computes
the two derivatives through the finite exponential partition and proves that
this radius is nonnegative.  The proof separates into two elementary finite
inequalities: each exponent is bounded by the log partition, and weighted
Cauchy--Schwarz makes the velocity variance nonnegative.
-/

open Complex Set
open scoped ContDiff

/-- Angular velocity of one vertex's directional value. -/
noncomputable def polytopeDirectionalVelocity (z : ℂ) (theta : ℝ) : ℝ :=
  -z.re * Real.sin theta + z.im * Real.cos theta

/-- The first derivative of the exponential partition sum. -/
noncomputable def polytopeSoftPartitionFirst
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalVelocity z theta / delta)

/-- The second derivative of the exponential partition sum. -/
noncomputable def polytopeSoftPartitionSecond
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
      polytopeDirectionalValue z theta / delta)

/-- Weighted directional-position moment of the partition. -/
noncomputable def polytopeSoftPartitionPositionMoment
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalValue z theta / delta)

/-- Weighted square angular-velocity moment of the partition. -/
noncomputable def polytopeSoftPartitionVelocitySqMoment
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalVelocity z theta / delta) ^ 2

/-- First derivative of the log-sum-exp support, in partition coordinates. -/
noncomputable def polytopeSoftSupportFirst
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta * (polytopeSoftPartitionFirst u delta theta /
    polytopeSoftPartition u delta theta)

/-- Second derivative of the log-sum-exp support, in partition coordinates. -/
noncomputable def polytopeSoftSupportSecond
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta *
    ((polytopeSoftPartitionSecond u delta theta *
          polytopeSoftPartition u delta theta -
        polytopeSoftPartitionFirst u delta theta ^ 2) /
      polytopeSoftPartition u delta theta ^ 2)

/-- A strictly rounded support function, obtained by adding a positive
constant to the soft support. -/
noncomputable def polytopeRoundedSupport
    (u : Finset ℂ) (delta rho theta : ℝ) : ℝ :=
  polytopeSoftSupport u delta theta + rho

/-- First angular derivative of a vertex directional value. -/
theorem hasDerivAt_polytopeDirectionalValue (z : ℂ) (theta : ℝ) :
    HasDerivAt (polytopeDirectionalValue z)
      (polytopeDirectionalVelocity z theta) theta := by
  unfold polytopeDirectionalValue polytopeDirectionalVelocity
  have h := ((Real.hasDerivAt_cos theta).const_mul z.re).add
    ((Real.hasDerivAt_sin theta).const_mul z.im)
  have h' : HasDerivAt
      ((fun y => z.re * Real.cos y) + fun y => z.im * Real.sin y)
      (-z.re * Real.sin theta + z.im * Real.cos theta) theta := by
    simpa only [neg_mul, mul_neg] using h
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.add_apply]

/-- The angular velocity differentiates to minus the directional value. -/
theorem hasDerivAt_polytopeDirectionalVelocity (z : ℂ) (theta : ℝ) :
    HasDerivAt (polytopeDirectionalVelocity z)
      (-polytopeDirectionalValue z theta) theta := by
  unfold polytopeDirectionalVelocity polytopeDirectionalValue
  have h := ((Real.hasDerivAt_sin theta).const_mul (-z.re)).add
    ((Real.hasDerivAt_cos theta).const_mul z.im)
  have hcoef : (-z.re) * Real.cos theta + z.im * (-Real.sin theta) =
      -(z.re * Real.cos theta + z.im * Real.sin theta) := by
    ring
  rw [hcoef] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.add_apply]

private theorem hasDerivAt_polytopeSoftWeight
    (z : ℂ) (delta theta : ℝ) :
    HasDerivAt
      (fun x => Real.exp (polytopeDirectionalValue z x / delta))
      (Real.exp (polytopeDirectionalValue z theta / delta) *
        (polytopeDirectionalVelocity z theta / delta)) theta := by
  exact (Real.hasDerivAt_exp _).comp theta
    ((hasDerivAt_polytopeDirectionalValue z theta).div_const delta)

/-- Exact first derivative of the finite exponential partition. -/
theorem hasDerivAt_polytopeSoftPartition
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartition u delta)
      (polytopeSoftPartitionFirst u delta theta) theta := by
  unfold polytopeSoftPartition polytopeSoftPartitionFirst
  have h := HasDerivAt.sum (u := u) fun z hz =>
    hasDerivAt_polytopeSoftWeight z delta theta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rw [Finset.sum_apply]

private theorem hasDerivAt_polytopeSoftWeight_mul_velocity
    (z : ℂ) (delta theta : ℝ) :
    HasDerivAt
      (fun x => Real.exp (polytopeDirectionalValue z x / delta) *
        (polytopeDirectionalVelocity z x / delta))
      (Real.exp (polytopeDirectionalValue z theta / delta) *
        ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
          polytopeDirectionalValue z theta / delta)) theta := by
  have h := (hasDerivAt_polytopeSoftWeight z delta theta).mul
    ((hasDerivAt_polytopeDirectionalVelocity z theta).div_const delta)
  have hcoef :
      Real.exp (polytopeDirectionalValue z theta / delta) *
          (polytopeDirectionalVelocity z theta / delta) *
          (polytopeDirectionalVelocity z theta / delta) +
        Real.exp (polytopeDirectionalValue z theta / delta) *
          (-polytopeDirectionalValue z theta / delta) =
      Real.exp (polytopeDirectionalValue z theta / delta) *
        ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
          polytopeDirectionalValue z theta / delta) := by
    ring
  rw [hcoef] at h
  apply h.congr_of_eventuallyEq
    (f₁ := fun x => Real.exp (polytopeDirectionalValue z x / delta) *
      (polytopeDirectionalVelocity z x / delta))
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply]

/-- Exact second derivative of the finite exponential partition. -/
theorem hasDerivAt_polytopeSoftPartitionFirst
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartitionFirst u delta)
      (polytopeSoftPartitionSecond u delta theta) theta := by
  unfold polytopeSoftPartitionFirst polytopeSoftPartitionSecond
  have h := HasDerivAt.sum (u := u) fun z hz =>
    hasDerivAt_polytopeSoftWeight_mul_velocity z delta theta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rw [Finset.sum_apply]

/-- Exact first derivative of the log-sum-exp support. -/
theorem hasDerivAt_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupport u delta)
      (polytopeSoftSupportFirst u delta theta) theta := by
  have hlog := (hasDerivAt_polytopeSoftPartition u delta theta).log
    (polytopeSoftPartition_pos hu delta theta).ne'
  have h := hlog.const_mul delta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rfl

/-- Exact derivative of the first-support-derivative formula. -/
theorem hasDerivAt_polytopeSoftSupportFirst
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupportFirst u delta)
      (polytopeSoftSupportSecond u delta theta) theta := by
  have hquot := (hasDerivAt_polytopeSoftPartitionFirst u delta theta).div
    (hasDerivAt_polytopeSoftPartition u delta theta)
    (polytopeSoftPartition_pos hu delta theta).ne'
  have h := hquot.const_mul delta
  have hcoef : delta *
      ((polytopeSoftPartitionSecond u delta theta *
            polytopeSoftPartition u delta theta -
          polytopeSoftPartitionFirst u delta theta *
            polytopeSoftPartitionFirst u delta theta) /
        polytopeSoftPartition u delta theta ^ 2) =
      polytopeSoftSupportSecond u delta theta := by
    unfold polytopeSoftSupportSecond
    ring
  rw [hcoef] at h
  apply h.congr_of_eventuallyEq
    (f₁ := polytopeSoftSupportFirst u delta)
  exact Filter.Eventually.of_forall fun x => by
    rfl

/-- First derivative as an equality involving `deriv`. -/
theorem deriv_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (polytopeSoftSupport u delta) theta =
      polytopeSoftSupportFirst u delta theta :=
  (hasDerivAt_polytopeSoftSupport hu delta theta).deriv

/-- Second derivative as an equality involving the iterated `deriv`. -/
theorem deriv_deriv_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (deriv (polytopeSoftSupport u delta)) theta =
      polytopeSoftSupportSecond u delta theta := by
  have hfirst : deriv (polytopeSoftSupport u delta) =
      polytopeSoftSupportFirst u delta := by
    funext x
    exact deriv_polytopeSoftSupport hu delta x
  rw [hfirst]
  exact (hasDerivAt_polytopeSoftSupportFirst hu delta theta).deriv

/-- The second partition derivative is the square-velocity moment minus the
position moment. -/
theorem polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionSecond u delta theta =
      polytopeSoftPartitionVelocitySqMoment u delta theta -
        polytopeSoftPartitionPositionMoment u delta theta := by
  unfold polytopeSoftPartitionSecond
    polytopeSoftPartitionVelocitySqMoment
    polytopeSoftPartitionPositionMoment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The weighted position moment is at most the log partition times the
partition mass. -/
theorem polytopeSoftPartitionPositionMoment_le_log_mul_partition
    {u : Finset ℂ} (_hu : u.Nonempty) {delta : ℝ} (_hdelta : 0 < delta)
    (theta : ℝ) :
    polytopeSoftPartitionPositionMoment u delta theta ≤
      polytopeSoftPartition u delta theta *
        Real.log (polytopeSoftPartition u delta theta) := by
  have hterm (z : ℂ) (hz : z ∈ u) :
      polytopeDirectionalValue z theta / delta ≤
        Real.log (polytopeSoftPartition u delta theta) := by
    have hsingle : Real.exp
          (polytopeDirectionalValue z theta / delta) ≤
        polytopeSoftPartition u delta theta := by
      unfold polytopeSoftPartition
      exact Finset.single_le_sum
        (f := fun w => Real.exp
          (polytopeDirectionalValue w theta / delta))
        (fun w hw => (Real.exp_pos _).le) hz
    have hlog := Real.log_le_log (Real.exp_pos _) hsingle
    simpa only [Real.log_exp] using hlog
  unfold polytopeSoftPartitionPositionMoment
  calc
    (∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
        (polytopeDirectionalValue z theta / delta)) ≤
        ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
          Real.log (polytopeSoftPartition u delta theta) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (hterm z hz) (Real.exp_pos _).le
    _ = polytopeSoftPartition u delta theta *
        Real.log (polytopeSoftPartition u delta theta) := by
      unfold polytopeSoftPartition
      rw [Finset.sum_mul]

/-- Weighted finite Cauchy--Schwarz for the first partition derivative. -/
theorem polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionFirst u delta theta ^ 2 ≤
      polytopeSoftPartition u delta theta *
        polytopeSoftPartitionVelocitySqMoment u delta theta := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) u
    (r := fun z => Real.exp (polytopeDirectionalValue z theta / delta) *
      (polytopeDirectionalVelocity z theta / delta))
    (f := fun z => Real.exp (polytopeDirectionalValue z theta / delta))
    (g := fun z => Real.exp (polytopeDirectionalValue z theta / delta) *
      (polytopeDirectionalVelocity z theta / delta) ^ 2)
    (fun z hz => (Real.exp_pos _).le)
    (fun z hz => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (fun z hz => by
      ring_nf
      exact le_rfl)
  exact hcs

/-- The log-sum-exp support has nonnegative support-curve curvature radius
`h + h''`. -/
theorem polytopeSoftSupport_add_second_nonneg
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      polytopeSoftSupportSecond u delta theta := by
  let S := polytopeSoftPartition u delta theta
  let F := polytopeSoftPartitionFirst u delta theta
  let V := polytopeSoftPartitionVelocitySqMoment u delta theta
  let Q := polytopeSoftPartitionPositionMoment u delta theta
  have hS : 0 < S := polytopeSoftPartition_pos hu delta theta
  have hentropy : Q ≤ S * Real.log S := by
    exact polytopeSoftPartitionPositionMoment_le_log_mul_partition
      hu hdelta theta
  have hvariance : F ^ 2 ≤ S * V := by
    exact polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
      u delta theta
  have hentropyScaled : S * Q ≤ S * (S * Real.log S) :=
    mul_le_mul_of_nonneg_left hentropy hS.le
  have hnum :
      0 ≤ Real.log S * S ^ 2 + (V - Q) * S - F ^ 2 := by
    nlinarith only [hentropyScaled, hvariance]
  have hfrac :
      0 ≤ (Real.log S * S ^ 2 + (V - Q) * S - F ^ 2) / S ^ 2 :=
    div_nonneg hnum (sq_nonneg S)
  have hscaled := mul_nonneg hdelta.le hfrac
  unfold polytopeSoftSupport polytopeSoftSupportSecond
  rw [polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment]
  change 0 ≤ delta * Real.log S +
    delta * (((V - Q) * S - F ^ 2) / S ^ 2)
  have heq : delta * Real.log S +
        delta * (((V - Q) * S - F ^ 2) / S ^ 2) =
      delta *
        ((Real.log S * S ^ 2 + (V - Q) * S - F ^ 2) / S ^ 2) := by
    field_simp [hS.ne']
    ring
  rw [heq]
  exact hscaled

/-- Adding any positive constant to the soft support makes its support-curve
curvature radius strictly positive. -/
theorem polytopeSoftSupport_add_const_add_second_pos
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < (polytopeSoftSupport u delta theta + rho) +
      polytopeSoftSupportSecond u delta theta := by
  have hbase := polytopeSoftSupport_add_second_nonneg hu hdelta theta
  linarith

/-- The actual iterated derivative form of nonnegative soft-support
curvature. -/
theorem polytopeSoftSupport_add_deriv_deriv_nonneg
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      deriv (deriv (polytopeSoftSupport u delta)) theta := by
  rw [deriv_deriv_polytopeSoftSupport hu delta theta]
  exact polytopeSoftSupport_add_second_nonneg hu hdelta theta

/-- The rounded support remains `2*pi`-periodic. -/
theorem periodic_polytopeRoundedSupport
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupport u delta rho)
      (2 * Real.pi) := by
  intro theta
  unfold polytopeRoundedSupport
  rw [periodic_polytopeSoftSupport u delta theta]

/-- The rounded support remains infinitely differentiable. -/
theorem contDiff_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupport u delta rho) := by
  unfold polytopeRoundedSupport
  exact (contDiff_polytopeSoftSupport hu delta).add contDiff_const

/-- Adding the rounding constant does not change the second derivative. -/
theorem deriv_deriv_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho theta : ℝ) :
    deriv (deriv (polytopeRoundedSupport u delta rho)) theta =
      polytopeSoftSupportSecond u delta theta := by
  have hfirst : deriv (polytopeRoundedSupport u delta rho) =
      polytopeSoftSupportFirst u delta := by
    funext x
    unfold polytopeRoundedSupport
    exact ((hasDerivAt_polytopeSoftSupport hu delta x).add_const rho).deriv
  rw [hfirst]
  exact (hasDerivAt_polytopeSoftSupportFirst hu delta theta).deriv

/-- A positive rounding constant gives strictly positive support-curve
curvature radius everywhere. -/
theorem polytopeRoundedSupport_add_deriv_deriv_pos
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < polytopeRoundedSupport u delta rho theta +
      deriv (deriv (polytopeRoundedSupport u delta rho)) theta := by
  rw [deriv_deriv_polytopeRoundedSupport hu delta rho theta]
  exact polytopeSoftSupport_add_const_add_second_pos
    hu hdelta hrho theta

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
