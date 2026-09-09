/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
public import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CylinderMeasureDescent
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! Actual smooth four-dimensional coefficients of the corrected packet.
The lifted field equals the constructed exact velocity, has the genuine
time derivative, is periodic, and has zero divergence. -/

@[expose] public section


noncomputable section


namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}

/-- Packet coefficient, given by `G.toSmoothTimeField.add (B.correctionCoefficient P)`. -/
def Budget.packetCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  G.toSmoothTimeField.add (B.correctionCoefficient P)

/-- Packet derivative coefficient, given by `H.toSmoothTimeField.add
(B.correctionDerivativeCoefficient P)`. -/
def Budget.packetDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)

/-- Lifted packet coefficient, given by `lift (B.packetCoefficient P G) A.κ A.direction`. -/
def Budget.liftedPacketCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetCoefficient P G) A.κ A.direction

/-- Lifted packet derivative coefficient, given by `lift (B.packetDerivativeCoefficient P H) A.κ
A.direction`. -/
def Budget.liftedPacketDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetDerivativeCoefficient P H) A.κ A.direction

theorem Budget.packetCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.packetCoefficient P G).field t x = (B.correctedFieldTower P).pointField t (coveringMap P x)
        := by
  rw [B.correctedFieldTower_eq P, FieldTower.add_pointField, hG]
  change G.toSmoothTimeField.field t x + (B.fieldTower P).pointField t (coveringMap P x) = _
  rw [G.toSmoothTimeField_apply]
  change raw (t,x) + (B.fieldTower P).pointField t (coveringMap P x) =
    G.toFieldTower.pointField t (x.1,(x.2 : AddCircle P)) +
      (B.fieldTower P).pointField t (coveringMap P x)
  rw [G.toFieldTower_pointField_raw]

theorem Budget.liftedPacketCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t x =
      transportDirection A.κ A.direction ((B.correctedFieldTower P).pointField t (coveringMap P x))
          := by
  change transportDirection A.κ A.direction ((B.packetCoefficient P G).field t x) = _
  rw [B.packetCoefficient_eq_corrected P G hG]

theorem Budget.packetCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.packetCoefficient P G)
      (B.packetDerivativeCoefficient P H) :=
  (G.toSmoothTimeField_timeDerivative H hT.le h).add (B.correctionCoefficient_timeDerivative P)

theorem Budget.liftedPacketCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.liftedPacketCoefficient P G)
      (B.liftedPacketDerivativeCoefficient P H) :=
  (B.packetCoefficient_timeDerivative P G H h).map (transportLinear A.κ A.direction)

theorem Budget.liftedPacketCoefficient_periodic (G : Field P T raw)
    (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t (x.1,(c : ℝ)+x.2) =
      (B.liftedPacketCoefficient P G).field t x := by
  have hc : coveringMap P (x.1,(c : ℝ)+x.2) = coveringMap P x :=
    EulerCylinderMeasureDescent.coveringMap_deck P c x
  change transportDirection A.κ A.direction
    (EulerCylinderSmoothOrbit.pointField P G.path G.orbit t (coveringMap P (x.1,(c : ℝ)+x.2)) +
      (B.fieldTower P).pointField t (coveringMap P (x.1,(c : ℝ)+x.2))) = _
  rw [hc]
  rfl

theorem Budget.liftedPacketCoefficient_trace (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    LinearMap.trace ℝ LiftTangent
      (fderiv ℝ ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent)
          x).toLinearMap = 0 := by
  have he : ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) =
      coverVelocity P A.κ A.direction ((B.correctedFieldTower P).pointField t) :=
    funext (B.liftedPacketCoefficient_eq_corrected P G hG t)
  rw [he]
  exact coverVelocity_trace_zero P A.κ A.direction ((B.correctedFieldTower P).pointField t)
    ((B.correctedFieldTower P).field t) (B.correctedFieldTower_divergence P t)
    ((B.correctedFieldTower P).pointField_ae t) ((B.correctedFieldTower P).pointField_smooth t) x

end EulerAllOrderDriftCorrection
