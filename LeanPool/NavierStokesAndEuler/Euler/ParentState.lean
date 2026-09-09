/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolevChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerEndpoints
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketCorrectionParity

@[expose] public section

/-! The recursive physical state consists of the actual Euler solution,
its all-order Sobolev fields, its particle-label bounds, and its symmetry.
Restriction and the exact packet construction preserve these data. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerCorrectionAssembly

structure SmoothState (A : Parent) where
  evolution : Evolution A
  regularity : SobolevData evolution
  labels : LabelData A
  odd : OddData A

namespace SmoothState

variable {A : Parent} (S : SmoothState A)

def restrictTime (T : ℝ) (hT : 0 < T) (hTA : T ≤ A.T) :
    SmoothState (A.restrictTime T hT hTA) where
  evolution := S.evolution.restrictTime T hT hTA
  regularity := S.regularity.restrictTime T hT hTA
  labels := S.labels.restrictTime T hT hTA
  odd := S.odd.restrictTime T hT hTA

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z=V.toFieldTower)
  (symmetry : ParityData P (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A=B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k*κ=1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

def packetChild (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1)) :
    SmoothState (A.child G k m hgraph nextEll hnext hnext1) where
  evolution := S.evolution.child m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  regularity := S.regularity.child S.labels m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  labels := labels
  odd := S.odd.childOfPacket B symmetry V hV G hG k hgraph nextEll hnext hnext1

end SmoothState
end EulerParentPacketFrames
