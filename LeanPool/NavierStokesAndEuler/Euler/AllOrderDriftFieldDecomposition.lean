/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftGraph
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedExactLifted

@[expose] public section

/-! Pointwise decomposition of the actual corrected velocity and pressure.
The identities concern the constructed exact packet, not an arbitrary
pair satisfying an energy bound. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)

theorem Budget.correctedFieldTower_eq :
    B.correctedFieldTower P = A.approximation.add (B.fieldTower P) := rfl

theorem Budget.correctedPressureTower_eq (R : ApproximationResidual P hT A) :
    B.correctedPressureTower P R = R.pressure.add (B.pressureTower P) := rfl

theorem Budget.correctedFieldTower_pointField (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (B.correctedFieldTower P).pointField t x =
      A.approximation.pointField t x + B.pointField P t x := by
  rw [B.correctedFieldTower_eq P, FieldTower.add_pointField,
    B.correctionTower_pointField P t]

theorem Budget.correctedPressureTower_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (B.correctedPressureTower P R).pointField t x =
      R.pressure.pointField t x + B.pointPressure P t x := by
  rw [B.correctedPressureTower_eq P R, FieldTower.add_pointField,
    B.pressureTower_pointField P t]

theorem exactPacketOfResidual_velocity_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (exactPacketOfResidual P B R).velocity.pointField t x =
      A.approximation.pointField t x + B.pointField P t x :=
  B.correctedFieldTower_pointField P t x

theorem exactPacketOfResidual_pressure_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (exactPacketOfResidual P B R).pressure.pointField t x =
      R.pressure.pointField t x + B.pointPressure P t x :=
  B.correctedPressureTower_pointField P R t x

end EulerAllOrderDriftCorrection
