/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction
import LeanPool.NavierStokesAndEuler.Euler.Foundations.BreakdownCriterion

/-! H³ stability on varying initial horizons. The comparison constant
uses only the original reference Euler solution and its full horizon. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerSmoothSobolev EulerVolterraConvolution
open scoped ContDiff Topology

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)
  (durations : ℕ → ℝ) (hD : ∀ n, 0 ≤ durations n) (hDT : ∀ n, durations n ≤ T)
  (V : ∀ n, Evolution (durations n) (hD n))

local notation "R" => fun n => U.restrictTime (durations n) (hD n) (hDT n)

include hDT in
theorem restricted_exponential_le (n : ℕ) :
    Real.exp (3*stabilityConstant U.referenceSize*durations n) ≤
      Real.exp (3*stabilityConstant U.referenceSize*T) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (hDT n)
    (mul_nonneg (by norm_num) (stabilityConstant_pos U.referenceSize_nonneg).le)

theorem eventually_h3_bound_varying
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 ((R n).difference (V n) ⟨0, le_rfl, hD n⟩) ≤ ε n) :
    ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) (durations n),
      tensorNorm 3 ((R n).difference (V n) t) ≤
        640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) := by
  have hb : Tendsto (fun n => 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
      (Real.exp (3*stabilityConstant U.referenceSize*T))
  have hs : ∀ᶠ n in atTop,
      640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) ≤ 1/2 :=
    hb.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs] with n hn t
  have hexp : 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*durations n) ≤
      640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) :=
    mul_le_mul_of_nonneg_left (U.restricted_exponential_le durations hDT n)
      (mul_nonneg (by norm_num) (hε n).le)
  exact ((R n).h3_stability (V n) U.referenceSize (ε n)
    (U.restrictTime_referenceWordBound (durations n) (hD n) (hDT n))
    (hε n) (hinit n) (hexp.trans hn) t).trans hexp

theorem sampled_h3_tendsto_zero_varying
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 ((R n).difference (V n) ⟨0, le_rfl, hD n⟩) ≤ ε n)
    (times : ∀ n, Icc (0 : ℝ) (durations n)) :
    Tendsto (fun n => tensorNorm 3 ((R n).difference (V n) (times n))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => tensorNorm_nonneg 3 _))
    ((U.eventually_h3_bound_varying durations hD hDT V ε hε hlim hinit).mono
      (fun n hn => hn (times n)))
  simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
    (Real.exp (3*stabilityConstant U.referenceSize*T))

theorem no_gradient_escape_varying
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 ((R n).difference (V n) ⟨0, le_rfl, hD n⟩) ≤ ε n)
    (times : ∀ n, Icc (0 : ℝ) (durations n)) :
    ¬ Tendsto (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) atTop atTop := by
  let err : ℕ → ℝ := fun n => (9*smoothEmbeddingConstant) *
    tensorNorm 3 ((R n).difference (V n) (times n))
  have he : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (U.sampled_h3_tendsto_zero_varying durations hD hDT V ε hε hlim hinit times).const_mul
        (9*smoothEmbeddingConstant)
  have hc : Continuous (fun r => fderiv ℝ (U.velocity (projIcc 0 T hT r)).field 0) :=
    (U.gradient_continuous 0).comp continuous_projIcc
  apply EulerBreakdownCriterion.no_escape_near_compact_trajectory
    (fun r => fderiv ℝ (U.velocity (projIcc 0 T hT r)).field 0)
    (fun n => fderiv ℝ ((V n).velocity (times n)).field 0)
    (fun n => (times n : ℝ)) err T hc.continuousOn
    (fun n => ⟨(times n).property.1,(times n).property.2.trans (hDT n)⟩) he
  apply Eventually.of_forall
  intro n
  have hb := real_smooth_fderiv_le_H3 3 ((R n).difference (V n) (times n)).field
    ((R n).difference (V n) (times n)).smooth
    (fun j _ => ((R n).difference (V n) (times n)).integrable j) 0
  have hf : ((R n).difference (V n) (times n)).field =
      ((V n).velocity (times n)).field-((R n).velocity (times n)).field :=
    funext (fieldSub_field _ _)
  rw [hf,fderiv_sub (((V n).velocity (times n)).smooth.differentiable (by simp) 0)
    (((R n).velocity (times n)).smooth.differentiable (by simp) 0)] at hb
  rw [projIcc_of_mem hT ⟨(times n).property.1,(times n).property.2.trans (hDT n)⟩]
  change ‖fderiv ℝ ((V n).velocity (times n)).field 0 -
      fderiv ℝ ((R n).velocity (times n)).field 0‖ ≤
    (9*smoothEmbeddingConstant)*tensorNorm 3 ((R n).difference (V n) (times n))
  rw [tensorNorm_eq,hf]
  exact hb

theorem no_gradient_escape_of_initial_tendsto_varying
    (hinit : Tendsto (fun n => tensorNorm 3 ((R n).difference (V n) ⟨0, le_rfl, hD n⟩))
      atTop (𝓝 0)) (times : ∀ n, Icc (0 : ℝ) (durations n)) :
    ¬ Tendsto (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) atTop atTop := by
  let ε : ℕ → ℝ := fun n => tensorNorm 3 ((R n).difference (V n) ⟨0,le_rfl,hD n⟩)+1/((n : ℝ)+1)
  have hp (n : ℕ) : 0 < ε n :=
    add_pos_of_nonneg_of_pos (tensorNorm_nonneg 3 _) (by positivity)
  have he : Tendsto ε atTop (𝓝 0) := by
    simpa only [add_zero] using hinit.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact U.no_gradient_escape_varying durations hD hDT V ε hp he
    (fun n => le_add_of_nonneg_right (by positivity)) times

end EulerOrdinarySobolev.Evolution
