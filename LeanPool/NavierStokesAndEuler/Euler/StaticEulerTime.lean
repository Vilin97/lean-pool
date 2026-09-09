/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerCorrection
public import LeanPool.NavierStokesAndEuler.Euler.ConstantEulerGraph
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeAmplitudeScaling

@[expose] public section

/-! The constructed static-datum solution and its actual time derivative
have smooth bounded spatial jets continuous in time. This includes the
one-sided derivatives at both endpoints. -/

noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerPacketCylinderField EulerAllOrderDriftCorrection
  EulerAllOrderCorrectionData EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)

def unitVelocityCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)

def unitDerivativeCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  ((correctionBudget P u C R hC hR hu hdiv).packetDerivativeCoefficient P
    ((Field.zero P 1).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)

def unitForceCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  (exactPacket P u C R hC hR hu hdiv).pressure.toSmoothTimeField.precompLinear
    (ContinuousLinearMap.inl ℝ Space ℝ)

theorem unitCoefficient_time :
    SmoothTimeField.TimeDerivative 1 zero_le_one
      (unitVelocityCoefficient P u C R hC hR hu hdiv)
      (unitDerivativeCoefficient P u C R hC hR hu hdiv) :=
  ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient_timeDerivative P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))
    ((Field.zero P 1).smul (amplitude P C R hC hR))
    ((EulerStaticCylinder.field_time P 1 u zero_le_one).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)

theorem unitVelocityCoefficient_apply (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field t x =
      EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  have h := (correctionBudget P u C R hC hR hu hdiv).packetCoefficient_eq_corrected P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)) rfl t (x,0)
  change ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient P
      ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))).field t (x,0) =
    ((correctionBudget P u C R hC hR hu hdiv).correctedFieldTower P).pointField
      (projIcc 0 1 zero_le_one t) (coveringMap P (x,0))
  rw [projIcc_of_mem zero_le_one t.property]
  exact h

theorem unitForceCoefficient_apply (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitForceCoefficient P u C R hC hR hu hdiv).field t x =
      EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  simp only [unitForceCoefficient,SmoothTimeField.precompLinear_apply,inl_apply,
    FieldTower.toSmoothTimeField_apply,EulerConstantEuler.force,ExactLiftedPacket.rawPressure,
    FieldTower.rawField,projIcc_of_mem zero_le_one t.property]

def velocityCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.coefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitVelocityCoefficient P u C R hC hR hu hdiv)

def derivativeCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.derivativeCoefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitDerivativeCoefficient P u C R hC hR hu hdiv)

def forceCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.derivativeCoefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitForceCoefficient P u C R hC hR hu hdiv)

theorem coefficient_time :
    SmoothTimeField.TimeDerivative (amplitude P C R hC hR) (amplitude_pos P C R hC hR).le
      (velocityCoefficient P u C R hC hR hu hdiv) (derivativeCoefficient P u C R hC hR hu hdiv) :=
  EulerTimeRescaling.coefficient_time (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    _ _ (unitCoefficient_time P u C R hC hR hu hdiv)

end EulerStaticEuler
