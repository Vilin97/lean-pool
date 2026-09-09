/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalizedGeometry
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
public import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport

@[expose] public section

/-! The inverse carried by the physical particle map. Preservation of
volume follows from the actual determinant, and both time restriction
and the packet child propagate the two inverse laws. -/

noncomputable section

namespace EulerParentPacketFrames

open Set MeasureTheory EulerSmoothLimit EulerTimeIntervalRestriction
  EulerGraphInvariantFlow EulerPacketVolumeDivergence
open scoped ContDiff

structure ParticleInverse (A : Parent) where
  field : Icc (0 : ℝ) A.T → Space → Space
  left_inverse : ∀ t x, field t (A.position t x)=x
  right_inverse : ∀ t x, A.position t (field t x)=x
  continuous : Continuous (Function.uncurry field)

namespace Parent

variable (A : Parent)

theorem position_contDiff (t : Icc (0 : ℝ) A.T) : ContDiff ℝ ∞ (A.position t) :=
  contDiff_id.add (A.displacement.smooth t)

theorem packetPosition_contDiff (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => A.packetPosition (t,x)) := by
  have he : (fun x => A.packetPosition (t,x)) =
      (fun x => A.ell⁻¹ • A.position t (A.ell • x)) :=
    funext (A.packetPosition_apply t)
  rw [he]
  exact ((A.position_contDiff t).comp (contDiff_id.const_smul A.ell)).const_smul A.ell⁻¹

end Parent

namespace ParticleInverse

variable {A : Parent} (I : ParticleInverse A)

include I in
theorem position_bijective (t : Icc (0 : ℝ) A.T) : Function.Bijective (A.position t) :=
  ⟨Function.LeftInverse.injective (I.left_inverse t),
    Function.RightInverse.surjective (I.right_inverse t)⟩

theorem field_initial (x : Space) : I.field A.zeroTime x=x := by
  have h := I.left_inverse A.zeroTime x
  simpa only [Parent.position, Parent.zeroTime, A.initial, add_zero] using h

include I in
theorem position_measurePreserving (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving (A.position t) volume volume :=
  EulerDeformationVolume.measurePreserving_of_det_one volume (A.position t)
    (fun x => ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)
    (A.position_hasFDerivAt t) (I.position_bijective t) (A.displacement_det_one t)

theorem field_measurePreserving (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving (I.field t) volume volume :=
  EulerFlowL2Transport.inverse_measurePreserving (A.position t) (I.field t)
    (fun x => ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)
    (A.position_hasFDerivAt t) (I.left_inverse t) (I.right_inverse t)
    (Continuous.uncurry_left t I.continuous) (A.displacement_det_one t)

def normalized (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  A.packetInverse I.field (t,x)

theorem normalized_left (t : Icc (0 : ℝ) A.T) (x : Space) :
    I.normalized t (A.packetPosition (t,x))=x :=
  A.packetInverse_left I.field I.left_inverse (t,x)

theorem normalized_right (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetPosition (t,I.normalized t x)=x :=
  A.packetInverse_right I.field I.right_inverse (t,x)

theorem normalized_continuous : Continuous (Function.uncurry I.normalized) :=
  (A.packetInverse_joint_continuous I.field I.continuous).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def restrictTime (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) :
    ParticleInverse (A.restrictTime S hS hST) where
  field t := I.field (initialInclusion A.T S hST t)
  left_inverse t x := I.left_inverse (initialInclusion A.T S hST t) x
  right_inverse t x := I.right_inverse (initialInclusion A.T S hST t) x
  continuous := I.continuous.comp
    (((initialInclusion A.T S hST).continuous.comp continuous_fst).prodMk continuous_snd)

def child {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
    (k : ℝ) (m : Space) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    ParticleInverse (A.child G k m hgraph nextEll hnext hnext1) where
  field := A.childInverse G k m I.field
  left_inverse := A.childInverse_left G k m hgraph nextEll hnext hnext1 I.field I.left_inverse
  right_inverse := A.childInverse_right G k m hgraph nextEll hnext hnext1 I.field I.right_inverse
  continuous := A.childInverse_joint_continuous G k m I.field I.continuous

end ParticleInverse
end EulerParentPacketFrames
