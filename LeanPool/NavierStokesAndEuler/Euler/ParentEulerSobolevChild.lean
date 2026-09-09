/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSobolevFields

@[expose] public section

/-! The constructed child Euler evolution remains in the actual
all-order spatial Sobolev class. Its fields are the parent fields plus
the very same exact packet used in the particle-map construction. -/

noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerLpTranslation EulerLpTranslation.SmoothL2Field

variable {A : Parent} {E : Evolution A} (F : SobolevData E) (L : LabelData A)
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

def child : SobolevData
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1) where
  velocity t := addField (F.velocity t)
    (L.packetVelocityField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k t)
  force t := addField (F.force t)
    (L.packetForceField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k t)
  velocity_match t x := by
    erw [Evolution.child_velocity,A.exactPacketVelocity_eq_corrected]
    erw [addField_field,L.packetVelocityField_apply]
    change E.velocity (t,x)+_=(F.velocity t).field x+_
    erw [F.velocity_match]
    rfl
  force_match t x := by
    erw [Evolution.child_force]
    erw [Parent.exactPacketForce,addField_field,F.force_match,L.packetForceField_apply]
    simp only [ExactLiftedPacket.graphPressure,map_smul]
    rfl
  velocity_continuous := continuous_jetLp_addField _ _ F.velocity_continuous
    (L.packetVelocityField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k)
  force_continuous := continuous_jetLp_addField _ _ F.force_continuous
    (L.packetForceField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k)

end EulerParentPacketFrames.SobolevData
