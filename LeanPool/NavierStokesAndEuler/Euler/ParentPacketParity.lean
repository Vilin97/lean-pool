/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowParity
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Oddness of the actual displacement propagates to its true velocity
and acceleration, fixes the origin, and gives every even source
coefficient used by the packet. The genuine child flow preserves it. -/

section

/-! Spatial derivatives and genuine within-time derivatives preserve
the expected parity, including the closed interval's endpoints. -/

@[expose] public section

noncomputable section

namespace SmoothTimeField

open Set ContinuousLinearMap EulerVolterraConvolution
open scoped ContDiff

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_even_of_odd (f : E → V) (hf : ContDiff ℝ ∞ f) (ho : Function.Odd f) :
    Function.Even (fderiv ℝ f) := by
  intro x
  have he : (fun y => f (-y)) = fun y => -f y := funext ho
  have h1 := ((hf.differentiable (by simp) (-x)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).neg)
  have h2 := ((hf.differentiable (by simp) x).hasFDerivAt).neg
  have hfd : fderiv ℝ (fun y => -f y) x = -fderiv ℝ f x := h2.fderiv
  have hd : -fderiv ℝ f x = -fderiv ℝ f (-x) := by
    simpa only [Function.comp_def,he,hfd,comp_neg,comp_id] using h1.fderiv
  exact neg_injective hd.symm

theorem TimeDerivative.odd {T : ℝ} {hT : 0 ≤ T}
    {A A1 : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hd : TimeDerivative T hT A A1) (hTpos : 0 < T)
    (ho : ∀ t, Function.Odd (A.field t : E → V)) (t : Icc (0 : ℝ) T) :
    Function.Odd (A1.field t : E → V) := by
  intro x
  have h1 := hd t (-x)
  have h2 := (hd t x).neg
  have he : (fun r => A.realField T hT r (-x)) = fun r => -A.realField T hT r x :=
    funext fun r => ho (projIcc 0 T hT r) x
  rw [he] at h1
  have hs := uniqueDiffOn_Icc hTpos (t : ℝ) t.property
  exact (h1.derivWithin hs).symm.trans (h2.derivWithin hs)

end SmoothTimeField

end
end

end

@[expose] public section

noncomputable section

namespace EulerGraphInvariantFlow

open Set EulerLiftedGradientSpace

theorem physicalCoefficient_odd (k : ℝ) (m : Vector3) (T : ℝ)
    (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent) (ell : ℝ)
    (ho : ∀ t, Function.Odd (A.field t : LiftTangent → LiftTangent)) (t : Icc (0 : ℝ) T) :
    Function.Odd ((physicalCoefficient k m T A ell).field t : Vector3 → Vector3) := by
  intro x
  simp only [physicalCoefficient_apply,smul_neg,map_neg]
  rw [ho t (graphLinear k m (ell⁻¹ • x))]
  simp only [Prod.fst_neg,smul_neg]

end EulerGraphInvariantFlow

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerSmoothLimit EulerGraphInvariantFlow EulerSmoothBanachFlow
  EulerTimeIntervalRestriction

/-- Odd data, collecting `displacement`. -/
structure OddData (A : Parent) : Prop where
  displacement : ∀ t, Function.Odd (A.displacement.field t : Space → Space)

namespace OddData

variable {A : Parent} (O : OddData A)

include O

theorem velocity (t : Icc (0 : ℝ) A.T) : Function.Odd (A.velocity.field t : Space → Space) :=
  A.displacement_time.odd A.T_pos O.displacement t

theorem acceleration (t : Icc (0 : ℝ) A.T) : Function.Odd (A.acceleration.field t : Space → Space)
    :=
  A.velocity_time.odd A.T_pos O.velocity t

theorem position_odd (t : Icc (0 : ℝ) A.T) : Function.Odd (A.position t) := by
  intro x
  change -x+A.displacement.field t (-x) = -(x+A.displacement.field t x)
  rw [O.displacement t x,neg_add]

theorem position_zero (t : Icc (0 : ℝ) A.T) : A.position t 0=0 := by
  ext i
  have hi : Function.Odd (fun x : Space => (A.position t x) i) :=
    fun x => congrArg (fun v : Space => v i) (O.position_odd t x)
  exact hi.map_zero

theorem frame_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.frame.field t : Space → Space →L[ℝ]
    Space) := by
  intro x
  rw [A.frame_apply,A.frame_apply,smul_neg,
    SmoothTimeField.fderiv_even_of_odd _ (A.displacement.smooth t) (O.displacement t) (A.ell • x)]

theorem first_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.first.field t : Space → Space →L[ℝ]
    Space) := by
  intro x
  rw [A.first_apply,A.first_apply,smul_neg,
    SmoothTimeField.fderiv_even_of_odd _ (A.velocity.smooth t) (O.velocity t) (A.ell • x)]

theorem second_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.second.field t : Space → Space →L[ℝ]
    Space) := by
  intro x
  rw [A.second_apply,A.second_apply,smul_neg,
    SmoothTimeField.fderiv_even_of_odd _ (A.acceleration.smooth t) (O.acceleration t) (A.ell • x)]

theorem inverse_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.inverse.field t : Space → Space →L[ℝ]
    Space) := by
  intro x
  rw [A.inverse_apply,A.inverse_apply,O.frame_even t x]

theorem strain_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.strain.field t : Space → Space →L[ℝ]
    Space) := by
  intro x
  rw [A.strain_apply,A.strain_apply,O.first_even t x,O.inverse_even t x]

theorem curvature_even (t : Icc (0 : ℝ) A.T) : Function.Even (A.curvature.field t : Space → Space
    →L[ℝ] Space) := by
  intro x
  rw [A.curvature_apply,A.curvature_apply,O.second_even t x,O.inverse_even t x]

theorem initialStrain_even : Function.Even (A.initialStrain.field : Space → Space →L[ℝ] Space) := by
  intro x
  rw [A.initialStrain_apply,A.initialStrain_apply,O.first_even A.zeroTime x]

theorem meanEvenData (H : LowBounds A) : EulerMeanPacketProvider.EvenData (A.meanData H) where
  frame := O.frame_even
  frameDerivative := O.first_even
  curvature := O.curvature_even
  initialStrain := O.initialStrain_even
  strain := O.strain_even

theorem restrictTime (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) : OddData (A.restrictTime S hS hST) where
  displacement t := O.displacement (initialInclusion A.T S hST t)

theorem child {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
    (ho : ∀ t, Function.Odd (G.A.field t : EulerLiftedGradientSpace.LiftTangent →
        EulerLiftedGradientSpace.LiftTangent))
    (k : ℝ) (m : Space) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    OddData (A.child G k m hgraph nextEll hnext hnext1) := by
  have hcover (t : Icc (0 : ℝ) A.T) :
      Function.Odd (G.coverDisplacementCoefficient.field t :
        EulerLiftedGradientSpace.LiftTangent → EulerLiftedGradientSpace.LiftTangent) := by
    intro z
    rw [G.coverDisplacementCoefficient_apply,G.coverDisplacementCoefficient_apply,
      EulerSmoothBanachFlow.forward_odd A.T G.time_nonneg G.A ho t]
    abel
  have hd (t : Icc (0 : ℝ) A.T) :
      Function.Odd ((G.physicalDisplacementCoefficient k m A.ell).field t : Space → Space) :=
    physicalCoefficient_odd k m A.T G.coverDisplacementCoefficient A.ell hcover t
  constructor
  intro t x
  change A.displacement.field t (-x+(G.physicalDisplacementCoefficient k m A.ell).field t (-x)) +
    (G.physicalDisplacementCoefficient k m A.ell).field t (-x) =
      -(A.displacement.field t (x+(G.physicalDisplacementCoefficient k m A.ell).field t x) +
        (G.physicalDisplacementCoefficient k m A.ell).field t x)
  rw [hd t x,← neg_add,O.displacement t (x+(G.physicalDisplacementCoefficient k m A.ell).field t
      x),neg_add]

end OddData

namespace ParticleInverse

variable {A : Parent} (I : ParticleInverse A) (O : OddData A)

include O

theorem odd (t : Icc (0 : ℝ) A.T) : Function.Odd (I.field t) := by
  intro x
  have h := I.left_inverse t (-I.field t x)
  rw [O.position_odd t (I.field t x),I.right_inverse] at h
  exact h

theorem zero (t : Icc (0 : ℝ) A.T) : I.field t 0=0 := by
  ext i
  have hi : Function.Odd (fun x : Space => I.field t x i) :=
    fun x => congrArg (fun v : Space => v i) (I.odd O t x)
  exact hi.map_zero

end ParticleInverse
end EulerParentPacketFrames
