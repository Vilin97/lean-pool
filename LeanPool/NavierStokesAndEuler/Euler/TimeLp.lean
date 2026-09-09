/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Actual Bochner L² time spaces and continuous-path embeddings used by maximal regularity. -/

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology ENNReal

/-- Lebesgue time measure restricted to the prescribed compact evolution interval. -/
def timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Icc 0 T)

/-- The actual compact time measure is finite. -/
instance timeMeasureFinite (T : ℝ) : IsFiniteMeasure (timeMeasure T) := by
  unfold timeMeasure
  infer_instance

/-- The actual Bochner L² space of time-dependent values in a normed space. -/
abbrev TimeLp (T : ℝ) (E : Type*) [NormedAddCommGroup E] := Lp E 2 (timeMeasure T)

variable {E : Type*} [NormedAddCommGroup E]

/-- A continuous compact-time path is genuinely square integrable after clamping. -/
theorem path_memLp (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    MemLp (extendPath T hT f) 2 (timeMeasure T) :=
  MemLp.of_bound (extendPath_continuous T hT f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (extendPath_norm_le T hT f))

/-- A continuous time path represented in the actual Bochner L² space. -/
def pathLp (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) : TimeLp T E :=
  (path_memLp T hT f).toLp (extendPath T hT f)

/-- The Bochner path representative is the genuine clamped continuous path almost everywhere. -/
theorem pathLp_ae (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    (pathLp T hT f : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT f :=
  (path_memLp T hT f).coeFn_toLp

/-- The continuous-path inclusion obeys the actual finite-time L² norm bound. -/
theorem pathLp_bound (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    ‖pathLp T hT f‖ ≤ (measureUnivNNReal (timeMeasure T) : ℝ) ^ (1/2 : ℝ) * ‖f‖ := by
  have hh : ‖pathLp T hT f‖ ≤ (measureUnivNNReal (timeMeasure T) : ℝ) ^ (ENNReal.toReal 2)⁻¹ * ‖f‖
    := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg f)
    filter_upwards [pathLp_ae T hT f] with t ht
    rw [ht]
    exact extendPath_norm_le T hT f t
  simpa using hh

/-- The actual path embedding preserves subtraction. -/
theorem pathLp_sub (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, E)) :
    pathLp T hT (f-g) = pathLp T hT f - pathLp T hT g := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (f-g), pathLp_ae T hT f, pathLp_ae T hT g,
    Lp.coeFn_sub (pathLp T hT f) (pathLp T hT g)] with t h1 h2 h3 h4
  simp only [Pi.sub_apply] at h4
  rw [h1, h4, h2, h3]
  rfl

/-- Uniform convergence of actual continuous paths implies convergence in actual L² time. -/
theorem pathLp_tendsto (T : ℝ) (hT : 0 ≤ T) (f : ℕ → C(Icc (0 : ℝ) T, E))
    (g : C(Icc (0 : ℝ) T, E)) (h : Filter.Tendsto f Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => pathLp T hT (f n)) Filter.atTop (𝓝 (pathLp T hT g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn := (h.sub_const g).norm
  simp only [sub_self, norm_zero] at hn
  have hb : ∀ n, ‖pathLp T hT (f n) - pathLp T hT g‖ ≤
      (measureUnivNNReal (timeMeasure T) : ℝ) ^ (1/2 : ℝ) * ‖f n-g‖ := by
    intro n
    rw [← pathLp_sub]
    exact pathLp_bound T hT _
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [mul_zero] using hn.const_mul ((measureUnivNNReal (timeMeasure T) : ℝ) ^ (1/2 : ℝ))

/-- The actual Bochner L² norm squared is the integral of the squared pointwise norm, also for Banach targets. -/
theorem norm_sq_eq_integral (T : ℝ) (f : TimeLp T E) :
    ‖f‖^2 = ∫ t, ‖f t‖^2 ∂timeMeasure T := by
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp f)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _)]
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

/-- The actual L² time norm of a continuous path is its classical time energy integral. -/
theorem pathLp_norm_sq (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    ‖pathLp T hT f‖^2 = ∫ t in (0 : ℝ)..T, ‖extendPath T hT f t‖^2 := by
  rw [norm_sq_eq_integral]
  have he : (∫ t, ‖pathLp T hT f t‖^2 ∂timeMeasure T) =
      ∫ t in Icc 0 T, ‖extendPath T hT f t‖^2 := by
    apply integral_congr_ae
    filter_upwards [pathLp_ae T hT f] with t ht
    rw [ht]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]

end EulerTimeLp
