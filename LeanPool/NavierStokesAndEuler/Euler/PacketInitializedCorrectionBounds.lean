/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSourceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionConstants
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionScalar

/-! Fixed source constants in the smaller-radius estimates for the actual
initialized all-order correction. They do not depend on the cutoff or frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionConstants

open EulerPacketCorrectionCoefficients EulerGevreyMetricEstimate EulerGevreyCorrectionSourceBounds
  EulerPacketCorrectionScalar

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (Kc : CorrectionCoefficientBudget D P)

/-- Correction base, given by `metricAmplification D.inverseBound⁻¹/2`. -/
def correctionBase : ℝ := metricAmplification D.inverseBound⁻¹/2

/-- Correction source cost, constructed using `sourceBound`. -/
def correctionSourceCost (R H C : ℝ) : ℝ :=
  sourceBound P (2*velocity R H C) (12*velocity R H C*(4*R)) Kc.A0 Kc.A2 1
    (correctionBase D) ((8/initialRadius R Kc.M Kc.Rc)*correctionBase D)

/-- Correction pressure cost, given by `2*Kc.M*correctionSourceCost D P Kc R H C`. -/
def correctionPressureCost (R H C : ℝ) : ℝ := 2*Kc.M*correctionSourceCost D P Kc R H C

/-- Correction time cost, given by `(1+2*Kc.M*(448*Kc.B+1))*correctionSourceCost D P Kc R H C`. -/
def correctionTimeCost (R H C : ℝ) : ℝ :=
  (1+2*Kc.M*(448*Kc.B+1))*correctionSourceCost D P Kc R H C

end EulerPacketCorrectionConstants
