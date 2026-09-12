/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Smooth parameter dependence of an actual integral over a compact interval. -/

@[expose] public section


noncomputable section

universe u

namespace EulerCompactParameterIntegral

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology Interval

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Parameter derivative, given by `(fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X ℝ)`. -/
def parameterDerivative (F : X × ℝ → E) (p : X × ℝ) : X →L[ℝ] E :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X ℝ)

omit [ProperSpace X] [CompleteSpace E] in
theorem parameterDerivative_contDiff (F : X × ℝ → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterDerivative F) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const

omit [CompleteSpace E] in
theorem integral_hasFDerivAt (a b : ℝ) (hab : a ≤ b) (F : X × ℝ → E)
    (hF : ContDiff ℝ ∞ F) (x : X) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, parameterDerivative F (x,t)) x := by
  have hd : Continuous (parameterDerivative F) := (parameterDerivative_contDiff F hF).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod isCompact_Icc).exists_bound_of_continuousOn
    hd.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := ball x 1) (F' := fun y t => parameterDerivative F (y,t))
    (bound := fun _ => C) (ball_mem_nhds x (by norm_num))
  · exact Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_uIoc : MeasurableSet (Ι a b))] with t ht
    intro y hy
    rw [uIoc_of_le hab] at ht
    exact hC (y,t) ⟨ball_subset_closedBall hy, ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t y _ => by
      have hin : HasFDerivAt (fun v : X => (v,t)) (ContinuousLinearMap.inl ℝ X ℝ) y :=
        (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const (𝕜 := ℝ) t y)
      exact ((hF.differentiable (by simp)) (y,t)).hasFDerivAt.comp y hin

theorem integral_contDiff_finite (n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (F : X × ℝ → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing E with
  | zero =>
      change ContDiff ℝ 0 _
      rw [contDiff_zero]
      have hi := continuous_parametric_integral_of_continuous
        (μ := volume) (f := fun y t => F (y,t)) hF.continuous
        (isCompact_Icc : IsCompact (Icc a b))
      simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using hi
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun y => ∫ t in a..b, parameterDerivative F (y,t), ?_, ?_⟩
      · exact ih (parameterDerivative F) (parameterDerivative_contDiff F hF)
      · exact integral_hasFDerivAt a b hab F hF

theorem integral_contDiff (a b : ℝ) (hab : a ≤ b) (F : X × ℝ → E)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun y => ∫ t in a..b, F (y,t)) :=
  contDiff_infty.mpr fun n => integral_contDiff_finite n a b hab F hF

end EulerCompactParameterIntegral
