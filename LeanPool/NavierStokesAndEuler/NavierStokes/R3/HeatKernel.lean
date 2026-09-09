/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup

@[expose] public section

/-!
# The three dimensional heat kernel

The definitions in this file are the ordinary Gaussian heat kernel and its
coordinate Hessian.  The latter is proved to agree with the spatial derivatives
used in the comparison argument.
-/


noncomputable section

open scoped ContDiff

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The Euclidean heat kernel in three spatial dimensions. -/
def heatKernel (s : ℝ) (z : Space) : ℝ :=
  (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2) / (4 * s))

/-- The explicit coordinate Hessian of the Euclidean heat kernel. -/
def heatKernelSecond (s : ℝ) (i j : Fin 3) (z : Space) : ℝ :=
  (z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)) *
    heatKernel s z

theorem heatKernel_pos {s : ℝ} (hs : 0 < s) (z : Space) : 0 < heatKernel s z := by
  unfold heatKernel
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem heatKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (z : Space) :
    0 ≤ heatKernel s z := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

theorem hasFDerivAt_heatKernel {s : ℝ} (hs : 0 < s) (z : Space) :
    HasFDerivAt (heatKernel s)
      ((-(heatKernel s z / (2 * s))) • innerSL ℝ z) z := by
  have he : HasFDerivAt (fun x : Space => -(‖x‖ ^ 2) / (4 * s))
      ((4 * s)⁻¹ • (-((2 : ℝ) • innerSL ℝ z))) z := by
    simpa only [Pi.neg_apply, div_eq_mul_inv, mul_comm, two_smul] using
      (hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.const_mul ((4 * s)⁻¹)
  convert! he.exp.const_mul ((4 * Real.pi * s) ^ (-(3 / 2 : ℝ))) using 1
  ext y
  simp only [_root_.smul_apply, _root_.neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  unfold heatKernel
  field_simp
  ; ring

theorem partial_heatKernel {s : ℝ} (hs : 0 < s) (i : Fin 3) (z : Space) :
    partialD i (heatKernel s) z = -(z i / (2 * s)) * heatKernel s z := by
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  rw [(hasFDerivAt_heatKernel hs z).fderiv]
  simp [NavierStokes.ProblemStatement.coordinateVector,
    EuclideanSpace.inner_single_right]
  ring

theorem differentiable_heatKernel {s : ℝ} (hs : 0 < s) :
    Differentiable ℝ (heatKernel s) := fun z =>
  (hasFDerivAt_heatKernel hs z).differentiableAt

theorem contDiff_heatKernel (s : ℝ) : ContDiff ℝ ∞ (heatKernel s) := by
  unfold heatKernel
  exact contDiff_const.mul (((contDiff_id.norm_sq ℝ).neg.div_const (4 * s)).exp)

/-- The explicit Gaussian Hessian is the actual iterated coordinate derivative. -/
theorem heatKernelSecond_eq_partial {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    heatKernelSecond s i j z = partialD i (partialD j (heatKernel s)) z := by
  have hfirst : partialD j (heatKernel s) =
      (fun x : Space => -(x j / (2 * s)) * heatKernel s x) :=
    funext (partial_heatKernel hs j)
  have hc : HasFDerivAt (fun x : Space => x j)
      (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)).hasFDerivAt
      (x := z) using 1
    ext x
    simp [NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_left]
  have hg : HasFDerivAt (fun x : Space => -(x j / (2 * s)))
      ((-((2 * s)⁻¹)) • innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)) z := by
    convert! hc.const_mul (-((2 * s)⁻¹)) using 1
    ext x
    ring
  rw [hfirst]
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  change heatKernelSecond s i j z = fderiv ℝ ((fun x : Space => -(x j / (2 * s))) * heatKernel s) z
    (NavierStokes.ProblemStatement.coordinateVector i)
  rw [(hg.mul (hasFDerivAt_heatKernel hs z)).fderiv]
  by_cases hij : i = j
  · subst i
    simp [heatKernelSecond, NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_right]
    ; field_simp
    ; ring
  · simp [heatKernelSecond, hij,
      NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_right]
    ; field_simp
    ; ring

/-- A radial envelope for every component of the Gaussian Hessian. -/
theorem norm_heatKernelSecond_le {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    ‖heatKernelSecond s i j z‖ ≤
      (‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * heatKernel s z := by
  have hden₁ : 0 < 4 * s ^ 2 := by positivity
  have hden₂ : 0 < 2 * s := by positivity
  have hcoord : ‖z i * z j‖ ≤ ‖z‖ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le z i) (PiLp.norm_apply_le z j)
      (norm_nonneg _) (norm_nonneg _)
  have hdiag : ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hcoeff :
      ‖z i * z j / (4 * s ^ 2) - (if i = j then 1 else 0) / (2 * s)‖ ≤
        ‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
    calc
      _ ≤ ‖z i * z j / (4 * s ^ 2)‖ +
          ‖(if i = j then (1 : ℝ) else 0) / (2 * s)‖ := norm_sub_le _ _
      _ = ‖z i * z j‖ / (4 * s ^ 2) +
          ‖(if i = j then (1 : ℝ) else 0)‖ / (2 * s) := by
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos hden₁, abs_of_pos hden₂]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_right hcoord hden₁.le)
        (div_le_div_of_nonneg_right hdiag hden₂.le)
  rw [heatKernelSecond, norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hs.le z)]
  exact mul_le_mul_of_nonneg_right hcoeff (heatKernel_nonneg hs.le z)

end NavierStokesR3.Comparison
