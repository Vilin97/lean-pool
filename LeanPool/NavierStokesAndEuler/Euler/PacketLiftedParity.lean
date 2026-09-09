/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient

/-! The actual corrected lifted velocity is odd when its prescribed
correction data have the checked parity. Passing from L² symmetry to
the canonical point field supplies symmetry of the real flow coefficient. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set EulerLiftedGradientSpace EulerCylinderReflection EulerCorrectionAssembly

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

theorem pointField_odd
    (ho : ∀ t, -reflection P (A.field t) = A.field t) (t : Icc (0 : ℝ) T) :
    Function.Odd (A.pointField t) :=
  continuous_representative_odd P (A.field t) (A.pointField t) (ho t)
    (Continuous.uncurry_left t A.pointField_joint_continuous) (A.pointField_ae t)

end EulerAllOrderCorrectionData.FieldTower

namespace EulerAllOrderDriftCorrection

open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerCylinderReflection
  EulerCorrectionAssembly EulerPacketCylinderField EulerPacketProfileRecursion
  EulerMetricTransport EulerLiftedSmoothTimeField

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)

theorem Budget.correctedFieldTower_odd (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    -reflection P ((B.correctedFieldTower P).field t)=(B.correctedFieldTower P).field t := by
  change -reflection P (A.approximation.field t+B.commonPath P t) =
    A.approximation.field t+B.commonPath P t
  rw [map_add,neg_add,E.approximation,B.commonPath_odd P E]

theorem Budget.liftedPacketCoefficient_odd {raw : VectorField}
    (G : Field P T raw) (hG : A.approximation = G.toFieldTower)
    (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    Function.Odd ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) := by
  intro z
  rw [B.liftedPacketCoefficient_eq_corrected P G hG,
    B.liftedPacketCoefficient_eq_corrected P G hG]
  have hc : coveringMap P (-z) = -coveringMap P z := by
    simp only [coveringMap,Prod.fst_neg,Prod.snd_neg,AddCircle.coe_neg,Prod.neg_mk]
  rw [hc,(B.correctedFieldTower P).pointField_odd (B.correctedFieldTower_odd P E) t]
  exact (EulerLiftedTransportTrace.transportLinear A.κ A.direction).map_neg _

end EulerAllOrderDriftCorrection
