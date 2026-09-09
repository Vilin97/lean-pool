/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryJoinedChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry

/-! The center error in a geometric packet choice is the gradient of
the actual increment between its two Euler states. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerAllOrderDriftCorrection EulerPacketPhysicalLowBounds
open scoped ContDiff

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace GeometryJoinedChoice

variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

/-- Residual type used in parent geometry choice center. -/
abbrev residual := initializedApproximationResidual I.meanData I.data rfl
  I.historyTime I.history_pos I.history_lt I.history I.geometry.δ I.delta_pos
  I.terminal I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four

local notation "T" => state I S k hk nextEll hnext hnext1 F hSym
local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem increment_fderiv (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement T t) x =
      fderiv ℝ (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
        I.support I.support_compact F.Q res k S.evolution.inverse t) (I.parent.ell⁻¹ • x) := by
  have hnew := ((T).evolution.velocity_smooth t).differentiable (by simp) x
  have hold := (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => (T).evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold]
  have he : fderiv ℝ (fun y => (T).evolution.velocity (t,y)) x =
      fderiv ℝ (fun y => S.evolution.velocity (t,y)) x +
        fderiv ℝ (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse t) (I.parent.ell⁻¹ • x) :=
    I.parent.exactPacketVelocity_fderiv I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

theorem center_error (t : Icc (0 : ℝ) I.parent.T) :
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      shearTerm (I.geometry.primaryAmplitude I.halfBall)
        (deriv (EulerPeriodicProfile.profile I.geometry.δ)
          (k*⟪I.normal,S.evolution.inverse.normalized t 0⟫_ℝ))
        (I.data.normal.field t (S.evolution.inverse.normalized t 0))
        (EulerPacketPrimaryFactorization.canonicalVelocity I.historyTime I.history_pos I.history_lt
          I.history I.geometry.terminal I.cutoff_support t (S.evolution.inverse.normalized t 0))‖ ≤
      k^(-(1/4 : ℝ)) := by
  rw [increment_fderiv I S k hk nextEll hnext hnext1 F hSym t 0,smul_zero]
  exact (F.errors t 0).1

end GeometryJoinedChoice

namespace GeometryForwardChoice

variable (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

/-- Residual type used in parent geometry choice center. -/
abbrev residual := forwardInitializedApproximationResidual I.meanData I.data rfl
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha
  I.agreement (truncation k) F.hn k hk.four

local notation "T" => state I S k hk nextEll hnext hnext1 F hSym
local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem increment_fderiv (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement T t) x =
      fderiv ℝ (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
        I.support I.support_compact F.Q res k S.evolution.inverse t) (I.parent.ell⁻¹ • x) := by
  have hnew := ((T).evolution.velocity_smooth t).differentiable (by simp) x
  have hold := (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => (T).evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold]
  have he : fderiv ℝ (fun y => (T).evolution.velocity (t,y)) x =
      fderiv ℝ (fun y => S.evolution.velocity (t,y)) x +
        fderiv ℝ (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse t) (I.parent.ell⁻¹ • x) :=
    I.parent.exactPacketVelocity_fderiv I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

theorem center_error (t : Icc (0 : ℝ) I.parent.T) :
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      shearTerm (I.geometry.primaryAmplitude I.halfBall)
        (deriv (EulerPeriodicProfile.profile I.geometry.δ)
          (k*⟪I.normal,S.evolution.inverse.normalized t 0⟫_ℝ))
        (I.data.normal.field t (S.evolution.inverse.normalized t 0))
        (EulerPacketForwardFactorization.canonicalVelocity I.data
          I.geometry.initialCoordinate t (S.evolution.inverse.normalized t 0))‖ ≤
      k^(-(1/4 : ℝ)) := by
  rw [increment_fderiv I S k hk nextEll hnext hnext1 F hSym t 0,smul_zero]
  exact (F.errors t 0).1

end GeometryForwardChoice
end EulerParentPacketFrames
