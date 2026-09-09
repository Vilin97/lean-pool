/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentChildEulerMatch

@[expose] public section

/-! The same exact packet that constructs the next particle map supplies
its physical Euler evolution. All new flow and Euler laws are proved
from the old evolution and the actual correction solver. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow

variable {A : Parent} (E : Evolution A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z=V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A=B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k*κ=1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

def child : Evolution (A.child G k m hgraph nextEll hnext hnext1) where
  inverse := E.inverse.child G k m hgraph nextEll hnext hnext1
  velocity := A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field E.velocity
  pressure := A.exactPacketPressure m hm J support hSupport B residual k E.inverse.field E.pressure
  force := A.exactPacketForce m hm J support hSupport B residual k E.inverse.field E.force
  force_continuous := A.exactPacketForce_continuous m hm J support hSupport B residual k
    E.inverse.field E.force E.inverse.continuous E.force_continuous
  velocity_match := A.child_velocity_exact m hm J support hSupport B residual V hV G hG k
    hgraph nextEll hnext hnext1 E.inverse.field E.inverse.left_inverse E.velocity E.velocity_match
  velocity_differentiable := A.exactPacketVelocity_differentiableAt m hm J support hSupport B
    residual k E.inverse.field E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous
    E.velocity E.velocity_differentiable
  pressure_differentiable t x := by
    have hd := A.normalizedExactPressure_differentiableAt m hm J support hSupport B residual
      k hk E.inverse.field E.inverse.right_inverse E.inverse.continuous E.pressure
      E.pressure_differentiable t (A.ell⁻¹ • x)
    exact (hd.comp x ((A.ell⁻¹ • ContinuousLinearMap.id ℝ Space).differentiableAt)).const_mul
      (A.ell^2)
  pressure_gradient := A.exactPacketPressure_gradient m hm J support hSupport B residual
    k hk E.inverse.field E.inverse.right_inverse E.inverse.continuous E.pressure E.force
    E.pressure_differentiable E.pressure_gradient
  momentum_zero := A.exactPacket_momentum m hm J support hSupport B residual k hk E.inverse.field
    E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous E.velocity E.pressure
    E.velocity_match E.velocity_differentiable E.pressure_differentiable E.momentum_zero
  divergence_zero t ht x :=
    (A.exactPacket_euler m hm J support hSupport B residual k hk E.inverse.field
      E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous E.velocity E.pressure
      E.velocity_match E.velocity_differentiable E.pressure_differentiable E.momentum_zero
      E.divergence_zero t ht x).2

@[simp] theorem child_velocity :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext
      hnext1).velocity =
      A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field E.velocity := rfl

@[simp] theorem child_pressure :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext
      hnext1).pressure =
      A.exactPacketPressure m hm J support hSupport B residual k E.inverse.field E.pressure := rfl

@[simp] theorem child_force :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1).force =
      A.exactPacketForce m hm J support hSupport B residual k E.inverse.field E.force := rfl

end EulerParentPacketFrames.Evolution
