/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerStability

/-! Convergence of ordinary Euler velocities in the initial H³ norm gives
pointwise convergence of their curls at every time in their common interval. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerSmoothSobolev EulerMeanBoundary EulerMeanCutoffCurl
open scoped ContDiff Topology

variable {T : ℝ} {hT : 0 ≤ T}

theorem sampled_h3_tendsto_of_initial_h3 (U : Evolution T hT)
    (V : ℕ → Evolution T hT)
    (hinit : Tendsto
      (fun n => tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩)) atTop (𝓝 0))
    (times : ℕ → Icc (0 : ℝ) T) :
    Tendsto (fun n => tensorNorm 3 (U.difference (V n) (times n))) atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun n =>
    tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩) + 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by
    intro n
    exact add_pos_of_nonneg_of_pos (tensorNorm_nonneg 3 _) (by positivity)
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [add_zero] using
      hinit.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply U.sampled_h3_tendsto_zero V ε hε hlim _ times
  intro n
  exact le_add_of_nonneg_right (by positivity)

theorem curl_tendsto_of_initial_h3 (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (hinit : Tendsto
      (fun n => tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩)) atTop (𝓝 0))
    (t : Icc (0 : ℝ) T) (x : Space) :
    Tendsto (fun n => vectorCurl ((V n).velocity t).field x) atTop
      (𝓝 (vectorCurl (U.velocity t).field x)) := by
  have h3 := U.sampled_h3_tendsto_of_initial_h3 V hinit (fun _ => t)
  have hgrad : Tendsto (fun n => fderiv ℝ ((V n).velocity t).field x) atTop
      (𝓝 (fderiv ℝ (U.velocity t).field x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => (9 * smoothEmbeddingConstant) *
        tensorNorm 3 (U.difference (V n) t)) atTop (𝓝 0) from by
          simpa only [mul_zero] using h3.const_mul (9 * smoothEmbeddingConstant))
    have hb := real_smooth_fderiv_le_H3 3 (U.difference (V n) t).field
      (U.difference (V n) t).smooth (fun j _ => (U.difference (V n) t).integrable j) x
    have hf : (U.difference (V n) t).field =
        ((V n).velocity t).field - (U.velocity t).field :=
      funext (fieldSub_field _ _)
    rw [hf, fderiv_sub (((V n).velocity t).smooth.differentiable (by simp) x)
      ((U.velocity t).smooth.differentiable (by simp) x)] at hb
    rw [tensorNorm_eq, hf]
    exact hb
  let C : (Space →L[ℝ] Space) →ₗ[ℝ] Space :=
    { toFun := curlMatrix
      map_add' := curlMatrix_add
      map_smul' := curlMatrix_smul }
  have hcurl := (C.toContinuousLinearMap.continuous.tendsto
    (fderiv ℝ (U.velocity t).field x)).comp hgrad
  change Tendsto (fun n => curlMatrix (fderiv ℝ ((V n).velocity t).field x)) atTop
    (𝓝 (curlMatrix (fderiv ℝ (U.velocity t).field x))) at hcurl
  rw [vectorCurl_eq_matrix _ x ((U.velocity t).smooth.differentiable (by simp) x)]
  exact hcurl.congr (fun n =>
    (vectorCurl_eq_matrix _ x (((V n).velocity t).smooth.differentiable (by simp) x)).symm)

end EulerOrdinarySobolev.Evolution
