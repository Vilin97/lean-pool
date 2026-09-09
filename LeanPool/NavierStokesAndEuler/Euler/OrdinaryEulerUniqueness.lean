/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientStability

/-! Uniqueness of actual smooth ordinary Euler evolutions, including
their pressure force. No assumed energy inequality is needed. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal

theorem smoothField_eq_of_toLp_eq (A B : SmoothL2Field Space) (h : A.toLp = B.toLp) : A=B := by
  apply field_ext
  have he : A.field=ᵐ[volume] B.field := A.toLp_ae.symm.trans (h ▸ B.toLp_ae)
  exact Measure.eq_of_ae_eq he A.smooth.continuous B.smooth.continuous

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem velocity_eq_of_initial (U V : Evolution T hT)
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp)
    (t : Icc (0 : ℝ) T) : V.velocity t=U.velocity t := by
  have h := U.l2_stability_gradientIntegral V t
  simp only [difference,toLp_fieldSub,hinit,sub_self,norm_zero,zero_mul] at h
  apply smoothField_eq_of_toLp_eq
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem pressure_eq_projected (U : Evolution T hT) (hpos : 0 < T) (t : Icc (0 : ℝ) T) :
    U.pressureForce t=pressureField (U.velocity t) := by
  apply smoothField_eq_of_toLp_eq
  have he := U.derivative_toLp_projected hpos t
  rw [derivative_eq_eulerRhs,eulerRhs,toLp_fieldNeg,toLp_addField,projectedRhs_toLp] at he
  rw [pressureField_toLp]
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using neg_injective he)

theorem pressure_eq_of_initial (U V : Evolution T hT) (hpos : 0 < T)
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp)
    (t : Icc (0 : ℝ) T) : V.pressureForce t=U.pressureForce t := by
  rw [V.pressure_eq_projected hpos t,U.pressure_eq_projected hpos t,
    U.velocity_eq_of_initial V hinit t]

end Evolution
end EulerOrdinarySobolev
