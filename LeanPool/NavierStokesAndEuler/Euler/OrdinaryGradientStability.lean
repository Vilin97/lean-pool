/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerGradientControl

@[expose] public section

/-! L² stability with the actual time integral of the reference
gradient.  The spatial cancellation is exact; no energy differential
inequality is assumed. -/

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped Topology

variable {T : ℝ} {hT : 0 ≤ T}

theorem l2EnergyDerivative_gradient (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    U.l2EnergyDerivative V t ≤ 2*U.gradientNormPath t*U.l2EnergyPath V t := by
  rw [l2EnergyDerivative,differenceDerivative_eq]
  apply differenceRhs_l2_bound _ _ _ _ (U.pointwise_gradient_le t)
  · have he : (addField (U.velocity t) (U.difference V t)).field=(V.velocity t).field := by
      funext x
      simp only [addField_field,difference,fieldSub_field]
      abel
    rw [he]
    exact solenoidal_representative_divergence _ (V.solenoidal t) _ (V.velocity t).smooth
      (V.velocity t).toLp_ae
  · rw [difference,toLp_fieldSub]
    exact solenoidalSpace.sub_mem (V.solenoidal t) (U.solenoidal t)
  · rw [pressureDifference,toLp_fieldSub]
    exact gradientSpace.sub_mem (V.gradient t) (U.gradient t)

theorem l2_energy_gradientIntegral (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖^2 ≤
      ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖^2*Real.exp (2*U.gradientIntegral t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.l2EnergyPath V))
        (U.l2EnergyDerivative V (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.l2Energy_hasDerivWithinAt V ⟨r,hr.1,hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      U.l2EnergyDerivative V (projIcc 0 T hT r) ≤
        2*extendPath T hT U.gradientNormPath r*extendPath T hT (U.l2EnergyPath V) r :=
    U.l2EnergyDerivative_gradient V (projIcc 0 T hT r)
  have h := variable_linear_stability T hT
    (extendPath T hT (U.l2EnergyPath V))
    (fun r => U.l2EnergyDerivative V (projIcc 0 T hT r)) 2 U.gradientNormPath
    ((U.l2EnergyPath V).continuous.comp continuous_projIcc).continuousOn hd hb t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    l2EnergyPath,ContinuousMap.coe_mk,gradientIntegral] using h

theorem l2_stability_gradientIntegral (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖ ≤
      ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖*Real.exp (U.gradientIntegral t) := by
  have h := U.l2_energy_gradientIntegral V t
  rw [two_mul,Real.exp_add] at h
  have hp : 0 ≤ ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖*Real.exp (U.gradientIntegral t) := by
    positivity
  nlinarith [norm_nonneg (U.difference V t).toLp]

theorem velocityPath_norm_sub_le_gradientIntegral (U V : Evolution T hT) (G : ℝ)
    (hG : ∀ t, U.gradientIntegral t ≤ G) :
    ‖V.velocityPath-U.velocityPath‖ ≤
      ‖V.velocityPath ⟨0,le_rfl,hT⟩-U.velocityPath ⟨0,le_rfl,hT⟩‖*Real.exp G := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have h := U.l2_stability_gradientIntegral V t
  simp only [difference,toLp_fieldSub] at h
  simpa only [ContinuousMap.sub_apply,velocityPath_apply] using h.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hG t)) (norm_nonneg _))

end EulerOrdinarySobolev.Evolution
