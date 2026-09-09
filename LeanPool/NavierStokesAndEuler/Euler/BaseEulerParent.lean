/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowDeformation
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction

@[expose] public section

/-! The genuine ordinary flow of a smooth divergence-free velocity gives
the first parent particle data. Its horizon can be shortened by an explicit
positive amount before applying the uniform flow-jet estimate. -/

noncomputable section

namespace EulerBaseEulerParent

open Set MeasureTheory EulerSmoothLimit EulerSmoothBanachFlow
  EulerParentPacketFrames EulerVolterraConvolution EulerTimeIntervalRestriction
open scoped ContDiff BoundedContinuousFunction

private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) := inferInstance

structure Input where
  T : ℝ
  T_pos : 0 < T
  field : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  derivative : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  time_derivative : SmoothTimeField.TimeDerivative T T_pos.le field derivative
  divergence : ∀ t x, EulerSmoothLimit.divergence (field.field t) x=0
  B : ℝ
  R : ℝ
  B_nonneg : 0 ≤ B
  R_pos : 0 < R
  small : B*R*T ≤ 1/8
  bound : ∀ n, ‖field.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2

namespace Input

variable (I : Input)

def displacement : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  displacementCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos I.small I.bound

def velocity : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  I.field.compDisplacement I.displacement

def acceleration : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  accelerationCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos I.small I.bound
    I.derivative

@[simp] theorem displacement_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.displacement.field t x=(flowData I.T I.T_pos.le I.field).forward t x-x := rfl

@[simp] theorem velocity_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.velocity.field t x=velocityFamily I.T I.T_pos.le I.field x t := by
  change I.field.field t (x+I.displacement.field t x)=_
  rw [I.displacement_apply]
  have he : x+((flowData I.T I.T_pos.le I.field).forward t x-x)=
      (flowData I.T I.T_pos.le I.field).forward t x := by abel
  rw [he]
  rfl

@[simp] theorem acceleration_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.acceleration.field t x=accelerationFamily I.T I.T_pos.le I.field I.derivative x t :=
  accelerationCoefficient_apply I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
    I.small I.bound I.derivative t x

theorem displacement_time : SmoothTimeField.TimeDerivative I.T I.T_pos.le
    I.displacement I.velocity := by
  intro t x
  have he : (fun s => I.displacement.realField I.T I.T_pos.le s x)=
      extendPath I.T I.T_pos.le (displacementFamily I.T I.T_pos.le I.field x) := rfl
  rw [he,I.velocity_apply]
  exact displacementFamily_time_derivative I.T I.T_pos.le I.field x t

theorem velocity_time : SmoothTimeField.TimeDerivative I.T I.T_pos.le
    I.velocity I.acceleration := by
  intro t x
  have he : (fun s => I.velocity.realField I.T I.T_pos.le s x)=
      extendPath I.T I.T_pos.le (velocityFamily I.T I.T_pos.le I.field x) := by
    funext s
    exact I.velocity_apply (projIcc 0 I.T I.T_pos.le s) x
  rw [he,I.acceleration_apply]
  exact velocityFamily_time_derivative I.T I.T_pos.le I.field I.derivative I.time_derivative x t

theorem displacement_initial (x : Space) : I.displacement.field ⟨0,le_rfl,I.T_pos.le⟩ x=0 := by
  rw [I.displacement_apply,(flowData I.T I.T_pos.le I.field).forward_zero,sub_self]

theorem displacement_det (t : Icc (0 : ℝ) I.T) (x : Space) :
    (ContinuousLinearMap.id ℝ Space+fderiv ℝ (I.displacement.field t : Space → Space) x).det=1 := by
  rw [← I.displacement.derivativeField_eq t x]
  change ((deformationCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
    I.small I.bound).field t x).det=1
  rw [deformationCoefficient_apply]
  exact forward_det_one I.T I.T_pos.le I.field I.divergence t x

def parent (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) : Parent where
  T := I.T
  T_pos := I.T_pos
  ell := ell
  ell_pos := hell
  ell_le_one := hell1
  displacement := I.displacement
  velocity := I.velocity
  acceleration := I.acceleration
  displacement_time := I.displacement_time
  velocity_time := I.velocity_time
  initial := I.displacement_initial
  determinant t x := by
    rw [EulerPacketVolumeDivergence.operatorMatrix_det]
    exact I.displacement_det t (ell • x)

theorem parent_position (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) I.T) (x : Space) :
    (I.parent ell hell hell1).position t x=(flowData I.T I.T_pos.le I.field).forward t x := by
  change x+I.displacement.field t x=_
  rw [I.displacement_apply]
  abel

def particleInverse (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    ParticleInverse (I.parent ell hell hell1) where
  field t x := (flowData I.T I.T_pos.le I.field).backward t x
  left_inverse t x := by
    erw [I.parent_position ell hell hell1]
    exact (flowData I.T I.T_pos.le I.field).backward_forward t x
  right_inverse t x := by
    erw [I.parent_position ell hell hell1]
    exact (flowData I.T I.T_pos.le I.field).forward_backward t x
  continuous := by
    have hc : Continuous (fun q : Icc (0 : ℝ) I.T × Space => ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (flowData I.T I.T_pos.le I.field).backward_joint_continuous.comp hc

theorem parent_velocity (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) I.T) (x : Space) :
    (I.parent ell hell hell1).velocity.field t x=
      I.field.field t ((I.parent ell hell hell1).position t x) := by
  rw [I.parent_position]
  exact I.velocity_apply t x

end Input

def horizon (T B R : ℝ) : ℝ := min T (1/(8*(1+B*R)))

theorem horizon_pos (T B R : ℝ) (hT : 0 < T) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 < horizon T B R := by
  unfold horizon
  apply lt_min hT
  positivity

theorem horizon_le (T B R : ℝ) : horizon T B R ≤ T := min_le_left _ _

theorem horizon_small (T B R : ℝ) (hT : 0 < T) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    B*R*horizon T B R ≤ 1/8 := by
  have hp := horizon_pos T B R hT hB hR
  have hd : 0 < 8*(1+B*R) := by positivity
  have he := (le_div_iff₀ hd).1 (min_le_right T (1/(8*(1+B*R))))
  change horizon T B R*(8*(1+B*R)) ≤ 1 at he
  nlinarith

def ofInterval (T : ℝ) (hT : 0 < T)
    (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (htime : SmoothTimeField.TimeDerivative T hT.le A A₁)
    (hdiv : ∀ t x, EulerSmoothLimit.divergence (A.field t) x=0)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 < R)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2) : Input where
  T := horizon T B R
  T_pos := horizon_pos T B R hT hB hR.le
  field := A.compTime (initialInclusion T (horizon T B R) (horizon_le T B R))
  derivative := A₁.compTime (initialInclusion T (horizon T B R) (horizon_le T B R))
  time_derivative := htime.restrictInitial (horizon_pos T B R hT hB hR.le).le (horizon_le T B R)
  divergence t x := hdiv (initialInclusion T (horizon T B R) (horizon_le T B R) t) x
  B := B
  R := R
  B_nonneg := hB
  R_pos := hR
  small := horizon_small T B R hT hB hR.le
  bound n := (A.compTime_jet_norm _ n).trans (hb n)

end EulerBaseEulerParent
