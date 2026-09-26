/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportEnvelope
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Real dual directions in the complex plane

Every real continuous linear functional on `ℂ` is a dot product with a
unique planar coefficient vector.  A nonzero functional is therefore a
positive multiple of the unit directional functional indexed by the
argument of that coefficient vector.  This elementary identification lets
abstract separating hyperplanes be converted to the angle-indexed support
halfspaces used by the smooth support-curve construction.
-/

@[expose] public section

open Complex

/-- A real continuous linear functional on `ℂ` is determined by its values
on the real basis vectors `1` and `I`. -/
theorem realContinuousLinearMap_apply_eq_re_im
    (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add]
  rw [show (z.re : ℂ) = z.re • (1 : ℂ) by
      rw [Complex.real_smul, mul_one],
    show z.im * I = z.im • I by
      rw [Complex.real_smul],
    map_smul, map_smul]
  simp only [smul_eq_mul]

/-- The coefficient vector associated with a planar real continuous linear
functional. -/
noncomputable def realContinuousLinearMapCoefficient
    (f : ℂ →L[ℝ] ℝ) : ℂ :=
  ⟨f 1, f I⟩

@[simp] theorem realContinuousLinearMapCoefficient_re
    (f : ℂ →L[ℝ] ℝ) :
    (realContinuousLinearMapCoefficient f).re = f 1 := rfl

@[simp] theorem realContinuousLinearMapCoefficient_im
    (f : ℂ →L[ℝ] ℝ) :
    (realContinuousLinearMapCoefficient f).im = f I := rfl

/-- A nonzero planar functional has a nonzero coefficient vector. -/
theorem realContinuousLinearMapCoefficient_ne_zero
    {f : ℂ →L[ℝ] ℝ} (hf : f ≠ 0) :
    realContinuousLinearMapCoefficient f ≠ 0 := by
  intro hzero
  have hre : f 1 = 0 := by
    have := congrArg Complex.re hzero
    simpa only [realContinuousLinearMapCoefficient_re, zero_re] using this
  have him : f I = 0 := by
    have := congrArg Complex.im hzero
    simpa only [realContinuousLinearMapCoefficient_im, zero_im] using this
  apply hf
  ext z
  simp only [realContinuousLinearMap_apply_eq_re_im, zero_apply,
    hre, him, mul_zero, zero_add]

/-- Every nonzero real continuous linear functional on the complex plane is
a positive multiple of one of the unit angle-indexed directional
functionals. -/
theorem exists_pos_mul_polytopeDirectionalValue_eq_realContinuousLinearMap
    {f : ℂ →L[ℝ] ℝ} (hf : f ≠ 0) :
    ∃ c theta : ℝ, 0 < c ∧
      ∀ z : ℂ, c * polytopeDirectionalValue z theta = f z := by
  let q : ℂ := realContinuousLinearMapCoefficient f
  let c : ℝ := ‖q‖
  let theta : ℝ := q.arg
  have hq : q ≠ 0 := realContinuousLinearMapCoefficient_ne_zero hf
  have hc : 0 < c := by
    dsimp only [c]
    exact norm_pos_iff.mpr hq
  refine ⟨c, theta, hc, ?_⟩
  intro z
  unfold polytopeDirectionalValue
  calc
    c * (z.re * Real.cos theta + z.im * Real.sin theta) =
        z.re * (‖q‖ * Real.cos q.arg) +
          z.im * (‖q‖ * Real.sin q.arg) := by
      dsimp only [c, theta]
      ring
    _ = z.re * q.re + z.im * q.im := by
      rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    _ = z.re * f 1 + z.im * f I := by
      rw [show q.re = f 1 by rfl, show q.im = f I by rfl]
    _ = f z := (realContinuousLinearMap_apply_eq_re_im f z).symm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
