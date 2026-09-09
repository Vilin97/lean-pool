/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketFrames
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildStructure
public import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldTime

@[expose] public section

/-! The actual composed child coefficients form the next parent data.
The next spatial scale can be chosen independently of the current scale. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerGraphInvariantFlow EulerPacketVolumeDivergence MeasureTheory

variable (A : EulerParentPacketFrames.Parent)

theorem displacement_det_one (t : Icc (0 : ℝ) A.T) (x : Space) :
    (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) x).det=1 :=
      by
  have h := A.determinant t (A.ell⁻¹ • x)
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  simpa only [hx,operatorMatrix_det] using h

variable {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

def child : EulerParentPacketFrames.Parent where
  T := A.T
  T_pos := A.T_pos
  ell := nextEll
  ell_pos := hnext
  ell_le_one := hnext1
  displacement := EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)
  velocity := EulerChildParticleTime.velocity A.displacement A.velocity
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)
  acceleration := EulerChildParticleTime.acceleration A.displacement A.velocity A.acceleration
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)
    (G.physicalAccelerationCoefficient k m A.ell)
  displacement_time := EulerChildParticleTime.displacement_time A.displacement_time
    (G.physicalDisplacementCoefficient_time k m A.ell)
  velocity_time := EulerChildParticleTime.velocity_time A.displacement_time A.velocity_time
    (G.physicalDisplacementCoefficient_time k m A.ell)
    (G.physicalVelocityCoefficient_time k m A.ell)
  initial := G.childDisplacementCoefficient_zero k m A.ell A.displacement A.initial
  determinant t x := by
    rw [operatorMatrix_det]
    exact G.childDisplacementCoefficient_det_one k m A.ell hgraph A.ell_pos
      A.displacement A.displacement_det_one t (nextEll • x)

theorem child_particleMap (t : Icc (0 : ℝ) A.T) (x : Space) :
    x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x =
      let y := (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x
      y+A.displacement.field t y := by
  change x+(EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)).field t x=_
  rw [EulerChildParticleTime.map_composition]
  have hi : x+(G.physicalDisplacementCoefficient k m A.ell).field t x =
      (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x := by
    rw [G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos,
      G.displacementField_eq k m hgraph A.ell A.ell_pos,EulerSmoothBanachFlow.displacement_eq]
    abel
  rw [hi]

theorem child_fields_match
    (E : Icc (0 : ℝ) A.T → EulerChildParticleFieldBounds.Data)
    (hD : ∀ t x, (E t).parentDisplacement.field x=A.displacement.field t x)
    (hV : ∀ t x, (E t).parentVelocity.field x=A.velocity.field t x)
    (hW : ∀ t x, (E t).parentAcceleration.field x=A.acceleration.field t x)
    (hd : ∀ t, (E t).displacement=G.displacementField k m A.ell A.ell_pos t)
    (hv : ∀ t, (E t).velocity=G.velocityField k m A.ell A.ell_pos t)
    (hw : ∀ t, (E t).acceleration=G.accelerationFieldL2 k m A.ell A.ell_pos t)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (E t).childDisplacement.field x=(A.child G k m hgraph nextEll hnext hnext1).displacement.field
      t x ∧
    (E t).childVelocity.field x=(A.child G k m hgraph nextEll hnext hnext1).velocity.field t x ∧
    (E t).childAcceleration.field x=(A.child G k m hgraph nextEll hnext hnext1).acceleration.field
      t x := by
  let H : EulerChildParticleTime.Representation E A.displacement A.velocity A.acceleration
      (G.physicalDisplacementCoefficient k m A.ell)
      (G.physicalVelocityCoefficient k m A.ell)
      (G.physicalAccelerationCoefficient k m A.ell) :=
    { parentDisplacement := hD
      parentVelocity := hV
      parentAcceleration := hW
      displacement := by
        intro u y
        rw [hd]
        exact (G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos u y).symm
      velocity := by
        intro u y
        rw [hv]
        exact (G.physicalVelocityCoefficient_eq k m A.ell A.ell_pos u y).symm
      acceleration := by
        intro u y
        rw [hw]
        exact (G.physicalAccelerationCoefficient_eq k m A.ell A.ell_pos u y).symm }
  exact ⟨H.childDisplacement t x,H.childVelocity t x,H.childAcceleration t x⟩

def childInverse (Y : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t x)

theorem childInverse_left (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (x+A.displacement.field t x)=x)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.childInverse G k m Y t
      (x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x)=x := by
  rw [A.child_particleMap G k m hgraph nextEll hnext hnext1]
  change (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t
    (Y t (_+A.displacement.field t _))=x
  rw [hYX]
  exact (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward_forward t x

theorem childInverse_right (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, Y t x+A.displacement.field t (Y t x)=x)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.childInverse G k m Y t x+
      (A.child G k m hgraph nextEll hnext hnext1).displacement.field t
        (A.childInverse G k m Y t x)=x := by
  rw [A.child_particleMap G k m hgraph nextEll hnext hnext1]
  change
    (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
        ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t x)) +
      A.displacement.field t
        ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
          ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).backward t (Y t
            x)))=x
  rw [(flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward_backward]
  exact hXY t x

theorem childInverse_joint_continuous (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) :
    Continuous (Function.uncurry (A.childInverse G k m Y)) :=
  (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A
    A.ell)).backward_joint_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hY)

theorem child_particleMap_measurePreserving
    (hparent : ∀ t, MeasurePreserving (fun x => x+A.displacement.field t x) volume volume)
    (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving
      (fun x => x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x) volume volume
        := by
  have he : (fun x => x+(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x) =
      (fun y => y+A.displacement.field t y) ∘
        (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t :=
    funext (A.child_particleMap G k m hgraph nextEll hnext hnext1 t)
  rw [he]
  exact (hparent t).comp
    (physical_forward_measurePreserving k m A.T G.time_nonneg G.A hgraph G.divergence
      A.ell A.ell_pos.ne' t)

end EulerParentPacketFrames.Parent
