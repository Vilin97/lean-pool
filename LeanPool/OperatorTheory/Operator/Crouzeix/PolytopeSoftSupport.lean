/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth support functions for finite planar polytopes

The directional support function of a finite convex hull is a maximum of
finitely many sinusoidal functions and is generally not smooth.  Its
log-sum-exp regularization is infinitely differentiable and periodic.  This
file records the exact one-sided bounds: it dominates every vertex support
value and exceeds any common upper bound by at most `delta * log(card)`.

These estimates are the quantitative input for constructing a smooth convex
support curve around a polygon.
-/

open Complex Set
open scoped ContDiff

/-- The real support of `z` in the unit direction of angle `theta`. -/
noncomputable def polytopeDirectionalValue (z : ℂ) (theta : ℝ) : ℝ :=
  z.re * Real.cos theta + z.im * Real.sin theta

/-- The exponential partition sum used to smooth the support function of a
finite point set. -/
noncomputable def polytopeSoftPartition
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta)

/-- The unnormalized log-sum-exp smoothing of the finite directional support
function. -/
noncomputable def polytopeSoftSupport
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta * Real.log (polytopeSoftPartition u delta theta)

/-- Each vertex directional value is `2*pi`-periodic. -/
theorem periodic_polytopeDirectionalValue (z : ℂ) :
    Function.Periodic (polytopeDirectionalValue z) (2 * Real.pi) := by
  intro theta
  unfold polytopeDirectionalValue
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The soft partition sum is `2*pi`-periodic. -/
theorem periodic_polytopeSoftPartition (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftPartition u delta) (2 * Real.pi) := by
  intro theta
  unfold polytopeSoftPartition
  apply Finset.sum_congr rfl
  intro z hz
  rw [periodic_polytopeDirectionalValue z theta]

/-- The soft support function is `2*pi`-periodic. -/
theorem periodic_polytopeSoftSupport (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftSupport u delta) (2 * Real.pi) := by
  intro theta
  unfold polytopeSoftSupport
  rw [periodic_polytopeSoftPartition u delta theta]

/-- A nonempty finite point set has a strictly positive soft partition sum. -/
theorem polytopeSoftPartition_pos {u : Finset ℂ} (hu : u.Nonempty)
    (delta theta : ℝ) :
    0 < polytopeSoftPartition u delta theta := by
  unfold polytopeSoftPartition
  exact Finset.sum_pos (fun z hz => Real.exp_pos _) hu

/-- A directional value is infinitely differentiable in its angle. -/
theorem contDiff_polytopeDirectionalValue (z : ℂ) :
    ContDiff ℝ ∞ (polytopeDirectionalValue z) := by
  unfold polytopeDirectionalValue
  exact (contDiff_const.mul Real.contDiff_cos).add
    (contDiff_const.mul Real.contDiff_sin)

/-- The soft partition sum is infinitely differentiable in its angle. -/
theorem contDiff_polytopeSoftPartition (u : Finset ℂ) (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftPartition u delta) := by
  unfold polytopeSoftPartition
  apply ContDiff.sum
  intro z hz
  exact ((contDiff_polytopeDirectionalValue z).div_const delta).exp

/-- For a nonempty finite point set, the soft support function is infinitely
differentiable in its angle. -/
theorem contDiff_polytopeSoftSupport {u : Finset ℂ} (hu : u.Nonempty)
    (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftSupport u delta) := by
  unfold polytopeSoftSupport
  exact contDiff_const.mul ((contDiff_polytopeSoftPartition u delta).log
    (fun theta => (polytopeSoftPartition_pos hu delta theta).ne'))

/-- Log-sum-exp dominates each individual vertex support value. -/
theorem polytopeDirectionalValue_le_softSupport
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ u) {delta : ℝ}
    (hdelta : 0 < delta) (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeSoftSupport u delta theta := by
  have hterm : Real.exp (polytopeDirectionalValue z theta / delta) ≤
      polytopeSoftPartition u delta theta := by
    unfold polytopeSoftPartition
    exact Finset.single_le_sum
      (f := fun w => Real.exp (polytopeDirectionalValue w theta / delta))
      (fun w hw => (Real.exp_pos _).le) hz
  have hlog : polytopeDirectionalValue z theta / delta ≤
      Real.log (polytopeSoftPartition u delta theta) := by
    have := Real.log_le_log (Real.exp_pos _) hterm
    simpa only [Real.log_exp] using this
  unfold polytopeSoftSupport
  calc
    polytopeDirectionalValue z theta =
        delta * (polytopeDirectionalValue z theta / delta) := by
      field_simp [hdelta.ne']
    _ ≤ delta * Real.log (polytopeSoftPartition u delta theta) :=
      mul_le_mul_of_nonneg_left hlog hdelta.le

/-- The soft support bound extends from the vertices to their real convex
hull. -/
theorem polytopeDirectionalValue_le_softSupport_of_mem_convexHull
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta : ℝ} (hdelta : 0 < delta) (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeSoftSupport u delta theta := by
  let f : ℂ →ₗ[ℝ] ℝ :=
    Real.cos theta • Complex.reCLM.toLinearMap +
      Real.sin theta • Complex.imCLM.toLinearMap
  have hf (w : ℂ) : f w = polytopeDirectionalValue w theta := by
    dsimp only [f, polytopeDirectionalValue]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change Real.cos theta * Complex.reCLM w +
      Real.sin theta * Complex.imCLM w =
        w.re * Real.cos theta + w.im * Real.sin theta
    rw [Complex.reCLM_apply, Complex.imCLM_apply]
    ring
  have hvertices : (u : Set ℂ) ⊆
      {w | f w ≤ polytopeSoftSupport u delta theta} := by
    intro w hw
    change f w ≤ polytopeSoftSupport u delta theta
    rw [hf]
    exact polytopeDirectionalValue_le_softSupport hw hdelta theta
  have hhalf : Convex ℝ {w | f w ≤ polytopeSoftSupport u delta theta} :=
    convex_halfSpace_le f.isLinear _
  rw [← hf z]
  exact convexHull_min hvertices hhalf hz

/-- If `M` bounds every vertex in one direction, log-sum-exp exceeds `M` by
at most `delta * log(card u)`. -/
theorem polytopeSoftSupport_le_of_forall_directionalValue_le
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta M : ℝ)
    (hM : ∀ z ∈ u, polytopeDirectionalValue z theta ≤ M) :
    polytopeSoftSupport u delta theta ≤
      M + delta * Real.log (u.card : ℝ) := by
  have hsum : polytopeSoftPartition u delta theta ≤
      (u.card : ℝ) * Real.exp (M / delta) := by
    unfold polytopeSoftPartition
    calc
      (∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta)) ≤
          ∑ _z ∈ u, Real.exp (M / delta) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [Real.exp_le_exp]
        exact (div_le_div_iff_of_pos_right hdelta).2 (hM z hz)
      _ = (u.card : ℝ) * Real.exp (M / delta) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hlog : Real.log (polytopeSoftPartition u delta theta) ≤
      Real.log (u.card : ℝ) + M / delta := by
    have hraw := Real.log_le_log
      (polytopeSoftPartition_pos hu delta theta) hsum
    rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hraw
    exact hraw
  unfold polytopeSoftSupport
  calc
    delta * Real.log (polytopeSoftPartition u delta theta) ≤
        delta * (Real.log (u.card : ℝ) + M / delta) :=
      mul_le_mul_of_nonneg_left hlog hdelta.le
    _ = M + delta * Real.log (u.card : ℝ) := by
      field_simp [hdelta.ne']
      ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
