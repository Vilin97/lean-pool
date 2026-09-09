/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTransportCancellation
import Mathlib.Algebra.Order.Star.Real

/-! Exact conservation of kinetic energy for the ordinary smooth Euler
class, using the genuine noncompact transport and pressure cancellations. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerContinuousTimeIntegral

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)

theorem velocity_derivative_inner_zero (t : Icc (0 : ℝ) T) :
    ⟪(U.velocity t).toLp,(U.derivative t).toLp⟫_ℝ=0 := by
  have hd := solenoidal_representative_divergence _ (U.solenoidal t)
    (U.velocity t).field (U.velocity t).smooth (U.velocity t).toLp_ae
  have ha := advection_inner_zero (U.velocity t) (U.velocity t) hd
  have hp := pressure_pairing_zero (U.gradient t) (U.solenoidal t)
  rw [real_inner_comm,U.derivative_eq_eulerRhs,eulerRhs,toLp_fieldNeg,toLp_addField,
    inner_neg_left,inner_add_left,ha,hp,add_zero,neg_zero]

theorem kineticEnergy_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => ‖(U.velocity (projIcc 0 T hT r)).toLp‖^2)
      0 (Icc (0 : ℝ) T) t := by
  have h := (U.velocityPath_hasDerivWithinAt t).norm_sq
  rw [U.velocityPath_extend] at h
  simpa only [projIcc_of_mem hT t.property,U.velocity_derivative_inner_zero,mul_zero] using h

theorem kineticEnergy_conserved (t : Icc (0 : ℝ) T) :
    ‖(U.velocity t).toLp‖^2=‖(U.velocity ⟨0,le_rfl,hT⟩).toLp‖^2 := by
  have h := eq_initial_add_integral T hT (0 : C(Icc (0 : ℝ) T,ℝ))
    (fun r => ‖(U.velocity (projIcc 0 T hT r)).toLp‖^2)
    (fun s => U.kineticEnergy_hasDerivWithinAt s) t
  simpa only [map_zero,ContinuousMap.zero_apply,add_zero,
    projIcc_of_mem hT t.property,projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using
        h

theorem velocity_norm_conserved (t : Icc (0 : ℝ) T) :
    ‖(U.velocity t).toLp‖=‖(U.velocity ⟨0,le_rfl,hT⟩).toLp‖ := by
  have h := U.kineticEnergy_conserved t
  nlinarith only [h,norm_nonneg (U.velocity t).toLp,norm_nonneg (U.velocity ⟨0,le_rfl,hT⟩).toLp]

end EulerOrdinarySobolev.Evolution
