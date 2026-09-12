/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.LpDominatedConvergence
import LeanPool.NavierStokesAndEuler.Euler.MeanL2Scaling
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The physical dilation f(x) ↦ ell*f(x/ell), including actual spatial
derivatives and their genuine Banach-valued L² norms. -/

@[expose] public section


noncomputable section


open scoped ContDiff

namespace EulerPhysicalL2Scaling

open MeasureTheory EulerSmoothLimit EulerMeanHarmonic

variable {V : Type*} [NormedAddCommGroup V]

theorem lpNorm_sq_integral (f : Space → V) (hf : MemLp f 2 volume) :
    (lpNorm f 2 volume)^2 = ∫ x, ‖f x‖^2 := by
  have hn : ‖hf.toLp f‖ = lpNorm f 2 volume := by
    rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable]
  rw [← hn, EulerLpConvergence.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem lpNorm_inv_dilation_sq (f : Space → V) (hf : MemLp f 2 volume)
    (ell : ℝ) (hell : 0 < ell) :
    lpNorm (fun x => f (ell⁻¹ • x)) 2 volume ^ 2 = ell^3 * lpNorm f 2 volume ^ 2 := by
  rw [lpNorm_sq_integral _ (memLp_dilation f hf ell⁻¹ (inv_ne_zero hell.ne')),
    lpNorm_sq_integral f hf]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖f x‖^2) hell.le]
  simp [Space, smul_eq_mul]

theorem lpNorm_inv_dilation (f : Space → V) (hf : MemLp f 2 volume)
    (ell : ℝ) (hell : 0 < ell) :
    lpNorm (fun x => f (ell⁻¹ • x)) 2 volume = Real.sqrt (ell^3)*lpNorm f 2 volume := by
  have he := lpNorm_inv_dilation_sq f hf ell hell
  have hs : (Real.sqrt (ell^3))^2 = ell^3 := Real.sq_sqrt (pow_nonneg hell.le 3)
  have hleft := lpNorm_nonneg (f := fun x => f (ell⁻¹ • x)) (p := 2) (μ := volume)
  have hright : 0 ≤ Real.sqrt (ell^3)*lpNorm f 2 volume :=
    mul_nonneg (Real.sqrt_nonneg _) lpNorm_nonneg
  nlinarith [sq_nonneg (lpNorm f 2 volume)]

variable [NormedSpace ℝ V]

/-- Scale, defined pointwise by `ell • f (ell⁻¹ • x)`. -/
def scale (ell : ℝ) (f : Space → V) : Space → V := fun x => ell • f (ell⁻¹ • x)

theorem scale_contDiff (ell : ℝ) (f : Space → V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scale ell f) :=
  (hf.comp (contDiff_id.const_smul ell⁻¹)).const_smul ell

theorem iteratedFDeriv_scale (ell : ℝ) (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (scale ell f) x =
      (ell*(ell⁻¹)^n) • iteratedFDeriv ℝ n f (ell⁻¹ • x) := by
  have hc : ContDiff ℝ n (fun y : Space => f (ell⁻¹ • y)) :=
    (hf.comp (contDiff_id.const_smul ell⁻¹)).of_le (by simp)
  change iteratedFDeriv ℝ n (fun y => ell • f (ell⁻¹ • y)) x = _
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    iteratedFDeriv_comp_const_smul ell⁻¹ (hf.of_le (by simp)), smul_smul]

theorem scale_jet_memLp (ell : ℝ) (hell : 0 < ell) (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (hn : MemLp (iteratedFDeriv ℝ n f) 2 volume) :
    MemLp (iteratedFDeriv ℝ n (scale ell f)) 2 volume := by
  have he : iteratedFDeriv ℝ n (scale ell f) =
      fun x => (ell*(ell⁻¹)^n) • iteratedFDeriv ℝ n f (ell⁻¹ • x) :=
    funext (iteratedFDeriv_scale ell f hf n)
  rw [he]
  exact (memLp_dilation _ hn ell⁻¹ (inv_ne_zero hell.ne')).const_smul (ell*(ell⁻¹)^n)

theorem lpNorm_scale_jet (ell : ℝ) (hell : 0 < ell) (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (hn : MemLp (iteratedFDeriv ℝ n f) 2 volume) :
    lpNorm (iteratedFDeriv ℝ n (scale ell f)) 2 volume =
      (ell*Real.sqrt (ell^3)*(ell⁻¹)^n)*lpNorm (iteratedFDeriv ℝ n f) 2 volume := by
  have he : iteratedFDeriv ℝ n (scale ell f) =
      (ell*(ell⁻¹)^n) • (fun x => iteratedFDeriv ℝ n f (ell⁻¹ • x)) :=
    funext (iteratedFDeriv_scale ell f hf n)
  rw [he, lpNorm_const_smul]
  change ‖ell*(ell⁻¹)^n‖*lpNorm (fun x => iteratedFDeriv ℝ n f (ell⁻¹ • x)) 2 volume = _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hell.le (pow_nonneg (inv_nonneg.mpr hell.le) n))]
  rw [lpNorm_inv_dilation _ hn ell hell]
  ring

theorem lpNorm_scale_jet_le (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (hn : MemLp (iteratedFDeriv ℝ n f) 2 volume) :
    lpNorm (iteratedFDeriv ℝ n (scale ell f)) 2 volume ≤
      (ell⁻¹)^n*lpNorm (iteratedFDeriv ℝ n f) 2 volume := by
  rw [lpNorm_scale_jet ell hell f hf n hn]
  have hp : ell^3 ≤ (1 : ℝ) := pow_le_one₀ hell.le hell1
  have hs : Real.sqrt (ell^3) ≤ 1 := (Real.sqrt_le_one).mpr hp
  have hfac : ell*Real.sqrt (ell^3) ≤ 1 := by
    exact (mul_le_mul hell1 hs (Real.sqrt_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_mul_of_nonneg_right
    (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac (pow_nonneg (inv_nonneg.mpr
            hell.le) n))
    lpNorm_nonneg

end EulerPhysicalL2Scaling
