/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryCorrector
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity

@[expose] public section

/-! The actual terminal-data primary supplies the grade-one profile and all
regularity/locality data required by the recursive packet construction. -/

noncomputable section

namespace EulerTransversePacketPrimary

open EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketProvider

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)

/-- This primary is constructed from the terminal history and its genuine
forward continuation, including its actual pressure and slow curl. -/
def profileRegularity : ProfileRegularity P D.T D.T_pos.le D.support
    (primaryProfile O (vector τ hτ hτT B Y) (scalar τ hτ hτT B Y)) where
  high := vectorField τ hτ hτT B Y
  mean := Field.zero P D.T
  corrector := (correctorField τ hτ hτT B Y).congr (fun _ _ _ => by
    change O.curlCorrector (vector τ hτ hτT B Y) _ = D.curlCorrector P (vector τ hτ hτT B Y) _
    rw [hcorrector])
  pressure := scalarGradientField τ hτ hτT B Y
  high_t := vectorDerivative τ hτ hτT B Y
  mean_t := 0
  corrector_t := correctorDerivative τ hτ hτT B Y
  highDerivative := vectorDerivativeField τ hτ hτT B Y
  meanDerivative := Field.zero P D.T
  correctorDerivative := correctorDerivativeField τ hτ hτT B Y
  high_time := vectorField_time τ hτ hτT B Y
  mean_time := Field.zero_time D.T_pos.le
  corrector_time := correctorField_time τ hτ hτT B Y
  high_zero t x hx θ := vector_zero_outside τ hτ hτT B Y t x hx θ
  corrector_zero t x hx θ := by
    change O.curlCorrector (vector τ hτ hτT B Y) (t,(x,θ)) = 0
    rw [hcorrector,curlCorrector_eq τ hτ hτT B Y t x θ]
    exact corrector_zero_outside τ hτ hτT B Y t x hx θ
  pressure_zero t x hx θ := scalarGradient_zero_outside τ hτ hτT B Y t x hx θ
  mean_angle _ _ _ := rfl

end EulerTransversePacketPrimary
