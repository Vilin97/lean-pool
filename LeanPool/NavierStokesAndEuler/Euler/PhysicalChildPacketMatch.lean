/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildVelocity
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform

/-! The child particle velocity matches the physical reconstruction of
the actual common correction, including the source spatial scaling. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.Parent

open Set InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerGraphPressurePotential
  EulerMetricTransport EulerPacketPhysicalTransform

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
  (B : EulerAllOrderDriftCorrection.Budget P A.T_pos C)

/-- Corrected packet velocity, constructed using `u`. -/
def correctedPacketVelocity (k : ℝ) (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + A.ell • (C.κ • A.frame.field t (A.ell⁻¹ • Y t x)
    ((B.correctedFieldTower P).pointField t (cylinderGraph P k C.direction (A.ell⁻¹ • Y t x))))

/-- Packet inverse, given by `A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)`. -/
def packetInverse (Y : Icc (0 : ℝ) A.T → Space → Space) (q : ℝ × Space) : Space :=
  A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)

theorem correctedPacketVelocity_eq_physical (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.correctedPacketVelocity B k Y u t x =
      u t x + A.ell • physicalVelocity C.κ k C.direction
        (fun q => A.frame.realField A.T A.T_pos.le q.1 q.2)
        ((B.correctedFieldTower P).rawField A.T_pos.le) (A.packetInverse Y) (t,A.ell⁻¹ • x) := by
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  simp only [correctedPacketVelocity,EulerPacketPhysicalTransform.physicalVelocity,
    EulerPacketPhysicalTransform.inverseCoordinates,EulerPacketPhysicalTransform.graphVelocity,
    EulerPacketPhysicalTransform.spaceTimeGraph_apply, packetInverse, FieldTower.rawField,
        SmoothTimeField.realField_apply,
    projIcc_of_mem A.T_pos.le t.property,hx,cylinderGraph,coveringMap]

variable {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw)
  (hV : C.approximation = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (hG : G.A = B.liftedPacketCoefficient P V)

include hV hG in
theorem lifted_graph_constraint (k : ℝ) (hk : k * C.κ = 1)
    (t : Icc (0 : ℝ) A.T) (q : LiftTangent) :
    graphConstraint k C.direction (G.A.field t q)=0 := by
  rw [hG,B.liftedPacketCoefficient_eq_corrected P V hV]
  simp only [graphConstraint_apply,transportDirection,real_inner_smul_right]
  rw [← mul_assoc,hk,one_mul,sub_self]

include hV hG in
theorem graphPushforwardVelocity_corrected (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k C.direction Y u t x = A.correctedPacketVelocity B k Y u t x := by
  have h := A.graphPushforwardVelocity_packet G k C.direction Y u C.κ
    (fun s q => (B.correctedFieldTower P).pointField s (coveringMap P q))
    (by
      intro s q
      rw [hG]
      exact B.liftedPacketCoefficient_eq_corrected P V hV s q) t x
  simpa only [correctedPacketVelocity,graphLinear_apply,cylinderGraph,coveringMap] using h

include hV hG in
theorem child_velocity_corrected (k : ℝ)
    (hgraph : ∀ t q, graphConstraint k C.direction (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k C.direction hgraph nextEll hnext hnext1).velocity.field t x =
      A.correctedPacketVelocity B k Y u t
        ((A.child G k C.direction hgraph nextEll hnext hnext1).position t x) :=
  (A.child_velocity_pushforward G k C.direction hgraph nextEll hnext hnext1 Y u hYX hvelocity t
      x).trans
    (A.graphPushforwardVelocity_corrected B V hV G hG k Y u t _)

end EulerParentPacketFrames.Parent
