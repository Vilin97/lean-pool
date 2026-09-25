/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5ARepair.Parameters
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLower.KernelElementary
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteA

/-!
First and second derivatives of the power kernel restricted to affine lines.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage5AboveTwoLower.S5ARepair

open O3.Stage2RouteA

/-- The concrete smoothing kernel restricted to an affine line. -/
noncomputable def kernelLine (r theta : ℝ) (x h : Point d) (t : ℝ) : ℝ :=
  lowerKernelPhi r theta (x + t • h)

/-- The exact first directional derivative away from the unique whole-vector
origin. Coordinate zeroes are allowed. -/
noncomputable def kernelLineGradient (r theta : ℝ)
    (x h : Point d) (t : ℝ) : ℝ :=
  4 * theta * (linePower r x h t) ^ (2 * theta / r - 1) *
    linePowerPair r x h t

/-- The exact second directional derivative away from the whole-vector
origin. The coordinatewise derivative is nevertheless valid at zero
coordinates because `r > 2`. -/
noncomputable def kernelLineHessian (r theta : ℝ)
    (x h : Point d) (t : ℝ) : ℝ :=
  4 * theta *
    ((2 * theta - r) * (linePower r x h t) ^ (2 * theta / r - 2) *
        (linePowerPair r x h t) ^ (2 : ℕ) +
      (r - 1) * (linePower r x h t) ^ (2 * theta / r - 1) *
        weightedSquareSum r x h t)

lemma kernelLine_eq_linePower (r theta : ℝ) (x h : Point d) (t : ℝ) :
    kernelLine r theta x h t =
      2 * (linePower r x h t) ^ (2 * theta / r) := by
  rfl

lemma hasDerivAt_kernelLine_of_ne_zero {r theta : ℝ}
    (hr : 1 < r) (x h : Point d) (t : ℝ)
    (hz : x + t • h ≠ 0) :
    HasDerivAt (kernelLine r theta x h)
      (kernelLineGradient r theta x h t) t := by
  have hr0 : r ≠ 0 := by linarith
  have hS : linePower r x h t ≠ 0 :=
    (O3.lpPower_pos_of_ne_zero hz).ne'
  have hp := (hasDerivAt_linePower hr x h t).rpow_const
    (Or.inl hS) (p := 2 * theta / r)
  have hscaled := hp.const_mul 2
  have halg :
      2 * (linePowerDerivative r x h t * (2 * theta / r) *
        linePower r x h t ^ (2 * theta / r - 1)) =
        kernelLineGradient r theta x h t := by
    rw [kernelLineGradient, linePowerDerivative, linePowerPair]
    field_simp
    ring
  rw [← halg]
  change HasDerivAt
    (fun s : ℝ ↦ 2 * (linePower r x h s) ^ (2 * theta / r)) _ t
  exact hscaled

lemma hasDerivAt_kernelLineGradient_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) (x h : Point d) (t : ℝ)
    (hz : x + t • h ≠ 0) :
    HasDerivAt (kernelLineGradient r theta x h)
      (kernelLineHessian r theta x h t) t := by
  have hr0 : r ≠ 0 := by linarith
  have hS : linePower r x h t ≠ 0 :=
    (O3.lpPower_pos_of_ne_zero hz).ne'
  have hpow := (hasDerivAt_linePower (by linarith : 1 < r) x h t).rpow_const
    (Or.inl hS) (p := 2 * theta / r - 1)
  have hpair := hasDerivAt_linePowerPair_above_two hr x h t
  have hprod := hpow.mul hpair
  have halg :
      4 * theta *
        (linePowerDerivative r x h t * (2 * theta / r - 1) *
            linePower r x h t ^ (2 * theta / r - 1 - 1) *
              linePowerPair r x h t +
          linePower r x h t ^ (2 * theta / r - 1) *
            ((r - 1) * weightedSquareSum r x h t)) =
        kernelLineHessian r theta x h t := by
    rw [kernelLineHessian, linePowerDerivative, linePowerPair]
    field_simp
    ring
  have hfun : kernelLineGradient r theta x h =
      fun s : ℝ ↦ (4 * theta) *
        (linePower r x h s ^ (2 * theta / r - 1) * linePowerPair r x h s) := by
    funext s
    rw [kernelLineGradient]
    ring
  rw [hfun]
  rw [← halg]
  exact hprod.const_mul (4 * theta)

lemma kernelLine_twice_differentiable_of_ne_zero {r theta : ℝ}
    (hr : 2 < r) (x h : Point d) (t : ℝ)
    (hz : x + t • h ≠ 0) :
    HasDerivAt (kernelLine r theta x h)
        (kernelLineGradient r theta x h t) t ∧
      HasDerivAt (kernelLineGradient r theta x h)
        (kernelLineHessian r theta x h t) t := by
  exact ⟨hasDerivAt_kernelLine_of_ne_zero (by linarith) x h t hz,
    hasDerivAt_kernelLineGradient_of_ne_zero hr x h t hz⟩

/-- Along a line passing through the whole-vector origin, the kernel is an
exact scalar homogeneous power. This is the form used to treat the origin
without differentiating a negative power of the power sum there. -/
lemma kernelLine_eq_radial_of_eq_zero {r theta : ℝ}
    (hr : 1 ≤ r) (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    kernelLine r theta x h = fun s : ℝ ↦
      2 * (lpNorm r h) ^ (2 * theta) * |s - t| ^ (2 * theta) := by
  funext s
  have hvec : x + s • h = (s - t) • h := by
    funext i
    have hzi := congrFun hz i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hzi ⊢
    linarith
  rw [kernelLine, hvec,
    Stage5AboveTwoLower.lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0)]
  change 2 * (O3.lpNorm r ((s - t) • h)) ^ (2 * theta) = _
  have hnorm := O3.Stage2RouteC.lpNorm_smul (p := r) hr (s - t) h
  rw [hnorm]
  rw [Real.mul_rpow (abs_nonneg (s - t)) (O3.lpNorm_nonneg r h)]
  ring

/-- The first derivative at the whole-vector origin is zero by homogeneous
growth of degree `2 * theta > 2`. -/
lemma hasDerivAt_kernelLine_at_zero {r theta : ℝ}
    (hr : 1 ≤ r) (htheta : 1 < theta)
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    HasDerivAt (kernelLine r theta x h) 0 t := by
  rw [kernelLine_eq_radial_of_eq_zero hr x h t hz]
  have habs := O3.Stage2RouteA.hasDerivAt_abs_affine_rpow
    (p := 2 * theta) (a := -t) (b := 1) (t := t)
    (by nlinarith : 1 < 2 * theta)
  simp only [mul_one, neg_add_cancel, abs_zero, mul_zero] at habs
  have hfun : (fun s : ℝ ↦ |-t + s| ^ (2 * theta)) =
      fun s : ℝ ↦ |s - t| ^ (2 * theta) := by
    funext s
    congr 2
    ring
  rw [hfun] at habs
  simpa only [mul_assoc, mul_zero] using
    habs.const_mul (2 * (lpNorm r h) ^ (2 * theta))

/-- The derivative of the scalar radial model has derivative zero at the
origin when the homogeneous degree is strictly above two. This is the second
origin calculation needed for the continuous Hessian extension. -/
lemma hasDerivAt_kernelLine_radialGradient_at_zero {r theta : ℝ}
    (htheta : 1 < theta) (h : Point d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ 4 * theta * (lpNorm r h) ^ (2 * theta) *
        O3.Experimental.scalarJ (2 * theta) (s - t)) 0 t := by
  have hsub : HasDerivAt ((· - t) : ℝ → ℝ) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hjOuter := O3.Stage2RouteA.hasDerivAt_scalarJ_above_two
    (by nlinarith : 2 < 2 * theta) (u := (0 : ℝ))
  have hj := hjOuter.comp_of_eq t hsub (by simp)
  simp only [abs_zero] at hj
  have hpow : (0 : ℝ) ^ (2 * theta - 2) = 0 := by
    rw [Real.zero_rpow (by nlinarith : 2 * theta - 2 ≠ 0)]
  rw [hpow] at hj
  norm_num at hj
  simpa only [Function.comp_apply, mul_assoc, mul_zero] using hj.const_mul
    (4 * theta * (lpNorm r h) ^ (2 * theta))

end V7.Stage5AboveTwoLower.S5ARepair
