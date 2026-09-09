/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildParent
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients

/-! The constructed child particle velocity is the Eulerian pushforward
of the actual graph velocity. The normalized packet formula follows
from the literal lifted coefficient, with the physical scale explicit. -/

@[expose] public section


noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
    EulerSmoothFlowGevrey

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
  (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)

include hgraph hell in
theorem physicalDisplacementCoefficient_position (t : Icc (0 : ℝ) T) (x : Vector3) :
    x+(G.physicalDisplacementCoefficient k m ell).field t x =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x := by
  rw [G.physicalDisplacementCoefficient_eq k m ell hell,
    G.displacementField_eq k m hgraph ell hell,displacement_eq]
  abel

include hgraph hell in
theorem physicalVelocityCoefficient_material (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalVelocityCoefficient k m ell).field t x =
      (physicalCoefficient k m T G.A ell).field t
        ((flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x) := by
  rw [G.physicalVelocityCoefficient_eq k m ell hell,G.velocityField_eq k m hgraph ell hell]
  rfl

end EulerPhysicalGraphFlowBounds.Data

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
  EulerMetricTransport

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Graph pushforward velocity, constructed using `u`. -/
def graphPushforwardVelocity (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t
      x))
    ((physicalCoefficient k m A.T G.A A.ell).field t (Y t x))

theorem child_position (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).position t x =
      A.position t ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
          x) :=
  A.child_particleMap G k m hgraph nextEll hnext hnext1 t x

theorem child_velocity_formula (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      let y := (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x
      A.velocity.field t y +
        (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) y)
          ((physicalCoefficient k m A.T G.A A.ell).field t y) := by
  change (EulerChildParticleTime.velocity A.displacement A.velocity
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)).field
        t x=_
  rw [EulerChildParticleTime.velocity_apply,
    G.physicalDisplacementCoefficient_position k m A.ell A.ell_pos hgraph,
    G.physicalVelocityCoefficient_material k m A.ell A.ell_pos hgraph]
  simp only [_root_.add_apply,ContinuousLinearMap.id_apply]
  abel

theorem child_velocity_pushforward (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      A.graphPushforwardVelocity G k m Y u t
        ((A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  rw [A.child_velocity_formula G k m hgraph nextEll hnext hnext1,graphPushforwardVelocity,
    A.child_position G k m hgraph nextEll hnext hnext1,hYX]
  dsimp only
  rw [hvelocity]

theorem graphPushforwardVelocity_packet
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (κ : ℝ)
    (z : Icc (0 : ℝ) A.T → LiftTangent → Space)
    (hlift : ∀ t q, G.A.field t q = transportDirection κ m (z t q))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k m Y u t x =
      u t x + A.ell • (κ • A.frame.field t (A.ell⁻¹ • Y t x)
        (z t (graphLinear k m (A.ell⁻¹ • Y t x)))) := by
  rw [graphPushforwardVelocity,physicalCoefficient_apply,hlift]
  change u t x +
    (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t x))
      (A.ell • (κ • z t (graphLinear k m (A.ell⁻¹ • Y t x))))=_
  rw [map_smul,map_smul,A.frame_apply]
  have hx : A.ell • (A.ell⁻¹ • Y t x)=Y t x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rw [hx]

end EulerParentPacketFrames.Parent
