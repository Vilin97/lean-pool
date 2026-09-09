/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch

@[expose] public section

/-! The physical increment between the actual packet states has exactly
the normalized packet's gradient. At the fixed center this is the same
quantity used by the source error bound and geometric renewal. -/

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerCorrectionAssembly
open scoped ContDiff

variable {A : Parent} (S : SmoothState A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z=V.toFieldTower)
  (symmetry : ParityData P (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A=B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k*κ=1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1))

theorem packetChild_increment_fderiv (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement
      (S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
        nextEll hnext hnext1 labels) t) x =
      fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k S.evolution.inverse
        t)
        (A.ell⁻¹ • x) := by
  let F := S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
    nextEll hnext hnext1 labels
  have hnew : DifferentiableAt ℝ (fun y => F.evolution.velocity (t,y)) x :=
    (F.evolution.velocity_smooth t).differentiable (by simp) x
  have hold : DifferentiableAt ℝ (fun y => S.evolution.velocity (t,y)) x :=
    (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => F.evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold]
  have he : fderiv ℝ (fun y => F.evolution.velocity (t,y)) x=
      fderiv ℝ (fun y => S.evolution.velocity (t,y)) x+
        fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k
          S.evolution.inverse t)
          (A.ell⁻¹ • x) :=
    A.exactPacketVelocity_fderiv m hm J support hSupport B residual k S.evolution.inverse
      S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

theorem packetChild_center_error (C : Icc (0 : ℝ) A.T → Space →L[ℝ] Space) (error : ℝ)
    (herr : ∀ t, ‖fderiv ℝ
      (A.normalizedPacketVelocity m hm J support hSupport B residual k S.evolution.inverse t) 0-C
        t‖ ≤ error)
    (t : Icc (0 : ℝ) A.T) :
    ‖fderiv ℝ (S.velocityIncrement
      (S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
        nextEll hnext hnext1 labels) t) 0-C t‖ ≤ error := by
  rw [S.packetChild_increment_fderiv m hm J support hSupport B residual V hV symmetry G hG k hk
    hgraph
    nextEll hnext hnext1 labels t 0,smul_zero]
  exact herr t

end EulerParentPacketFrames.SmoothState
