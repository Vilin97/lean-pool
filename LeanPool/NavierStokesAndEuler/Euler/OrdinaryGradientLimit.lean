/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientStability
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerCauchy

@[expose] public section

/-! Common-interval smooth Euler limits under a uniform bound on the
actual time integral of the velocity gradient. The H³ bound, all higher
bounds, and path Cauchy convergence are derived from the true equations. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
open scoped Topology

def gradientTensorBound (R G : ℝ) : ℝ :=
  wordCount 3*Real.sqrt (wordCount 3*R^2*Real.exp (gradientEnergyConstant*G))

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem h3_tensorNorm_gradient_uniform (U : Evolution T hT) (R G : ℝ)
    (hR : tensorNorm 3 (U.velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.velocity t) ≤ gradientTensorBound R G := by
  apply (U.h3_tensorNorm_of_gradientIntegral G hG t).trans
  apply mul_le_mul_of_nonneg_left _ (wordCount_nonneg 3)
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (wordEnergy_le_tensorNorm _ 3).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (tensorNorm_nonneg 3 _) hR 2) (wordCount_nonneg 3))

theorem cauchyPath_of_initial_gradient (V : ℕ → Evolution T hT) (G : ℝ)
    (hG : ∀ k t, (V k).gradientIntegral t ≤ G)
    (hinit : CauchySeq (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp)) :
    CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hinit (ε/Real.exp G) (div_pos hε (Real.exp_pos _))
  refine ⟨N,fun j hj k hk => ?_⟩
  have hb := (V k).velocityPath_norm_sub_le_gradientIntegral (V j) G (hG k)
  have hi := mul_lt_mul_of_pos_right (hN j hj k hk) (Real.exp_pos G)
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos G))] at hi
  rw [dist_eq_norm,fieldPath_eq_velocityPath,fieldPath_eq_velocityPath]
  apply hb.trans_lt
  simpa only [dist_eq_norm,velocityPath_apply] using hi

end Evolution

variable {T : ℝ} {hT : 0 ≤ T}

def limitEvolutionOfGradientIntegral (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (R G : ℝ) (hR : ∀ k, tensorNorm 3 ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ k t, (V k).gradientIntegral t ≤ G)
    (hinit : ∀ q, ∃ C : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ C)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp)) : Evolution T hT :=
  limitEvolution V hpos
    (Evolution.all_order_bounds_of_h3 V (gradientTensorBound R G)
      (fun k => (V k).h3_tensorNorm_gradient_uniform R G (hR k) (hG k)) hinit)
    (Evolution.cauchyPath_of_initial_gradient V G hG hcauchy)

theorem limitEvolutionOfGradientIntegral_convergence (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (R G : ℝ) (hR : ∀ k, tensorNorm 3 ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ k t, (V k).gradientIntegral t ≤ G)
    (hinit : ∀ q, ∃ C : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ C)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp)) (q : ℕ) :
    Tendsto (fun k => jetPath (V k).velocity (V k).velocity_continuous q) atTop
      (𝓝 (jetPath (limitEvolutionOfGradientIntegral V hpos R G hR hG hinit hcauchy).velocity
        (limitEvolutionOfGradientIntegral V hpos R G hR hG hinit hcauchy).velocity_continuous q)) :=
  limitEvolution_jet_convergence V hpos
    (Evolution.all_order_bounds_of_h3 V (gradientTensorBound R G)
      (fun k => (V k).h3_tensorNorm_gradient_uniform R G (hR k) (hG k)) hinit)
    (Evolution.cauchyPath_of_initial_gradient V G hG hcauchy) q

theorem limitEvolutionOfGradientIntegral_initial (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (R G : ℝ) (hR : ∀ k, tensorNorm 3 ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ k t, (V k).gradientIntegral t ≤ G)
    (hinit : ∀ q, ∃ C : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ C)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp)) (u0 : L2)
    (hu0 : Tendsto (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp) atTop (𝓝 u0)) :
    ((limitEvolutionOfGradientIntegral V hpos R G hR hG hinit hcauchy).velocity
      ⟨0,le_rfl,hT⟩).toLp=u0 :=
  limitEvolution_initial V hpos
    (Evolution.all_order_bounds_of_h3 V (gradientTensorBound R G)
      (fun k => (V k).h3_tensorNorm_gradient_uniform R G (hR k) (hG k)) hinit)
    (Evolution.cauchyPath_of_initial_gradient V G hG hcauchy) u0 hu0

end EulerOrdinarySobolev
