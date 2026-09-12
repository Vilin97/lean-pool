/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInputs
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceLow
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceRenewal
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageEstimates
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageLowPropagation
public import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication

/-! The time-zero normal step: the same selected correction supplies
the next actual state, low source bounds and renewed geometric frame. -/

public section


noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerPacketGeometryLowBounds EulerParentNeighborThreshold
  EulerMeanHarmonic

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "I" => P.forwardInput hq hB
local notation "G" => P.forwardGuards hq hB
local notation "k" => frequency S.J S.X 0
local notation "hk" => S.normal_frequency 0
local notation "ell" => supportScale S.J S.X 1

/-- Forward choice: an abbreviation for `GeometryForwardChoice I P.restrictedState k hk ell
(S.support_pos 1) (S.support_one 1)`. -/
abbrev ForwardChoice :=
  GeometryForwardChoice I P.restrictedState k hk ell (S.support_pos 1) (S.support_one 1)

/-- Choose forward, choosing the witness provided by `Forward`. -/
def chooseForward : P.ForwardChoice hq hB := by
  have hsec := S.secondary_frequency 0 P.restrictedState.labels.K P.label_eq.le
  exact Classical.choice (exists_geometryForwardChoice I P.restrictedState k hk ell
    (S.support_pos 1) (S.support_one 1) (P.forwardInput_frequency hq hB) hsec.1
    (by rw [P.forwardInput_scale]; exact hsec.2))

local notation "F" => P.chooseForward hq hB

/-- Forward parent, given by `(F).parent`. -/
@[expose] def forwardParent : Parent := (F).parent

/-- Forward state, given by `GeometryForwardChoice.state I P.restrictedState k hk ell
(S.support_pos 1) (S.support_one 1) F symmetric`. -/
@[expose] def forwardState : SmoothState (P.forwardParent hq hB) :=
  GeometryForwardChoice.state I P.restrictedState k hk ell (S.support_pos 1) (S.support_one 1) F
      symmetric

theorem forward_smallness :
    (P.restrictedLow.K+2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild *
        ((G).δ*goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)))*(P.nextHorizon^2/2) +
      (P.restrictedLow.Be+((G).hchild*(G).earlyRatio+k^(-(1/4 : ℝ))))*P.nextHorizon +
      boundaryLocalizationC2*(P.restrictedLow.Bc+((G).hchild*(G).earlyRatio+k^(-(1/4 : ℝ)))) *
        P.restrictedLow.r^3*P.nextHorizon ≤ 1/2 :=
  P.successor_smallness (G).hchild (G).δ (G).earlyRatio
    (G).child_nonneg (G).delta_nonneg (G).earlyRatio_nonneg
    (P.forward_initial_cost hq hB) (P.forward_pressure_cost hq hB)

/-- Forward low as an element of `LowBounds (P.forwardParent hq hB)`. -/
@[expose] def forwardLow : LowBounds (P.forwardParent hq hB) :=
  (F).lowBounds (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    P.restricted_gradient_bound P.restricted_hessian_bound (P.forward_smallness hq hB)

/-- Forward renewal as an element of `ParentFrame (frameData (P.forwardParent hq hB))
(P.forwardGeometry hq hB).targetTime`. -/
@[expose] def forwardRenewal : ParentFrame (frameData (P.forwardParent hq hB)) (P.forwardGeometry hq
    hB).targetTime :=
  (F).renewal symmetric (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    (frameConstant*(1+previousShear S.J S.X 0))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one 0)))
    (next_frame_bounds (S := S) (n := 0)).1 (next_frame_bounds (S := S) (n := 0)).2.1
    (next_frame_bounds (S := S) (n := 0)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact

theorem forwardRenewal_matches :
    RenewalAtTarget (P.forwardGeometry hq hB) (P.forwardRenewal hq hB) :=
  (F).renewal_matches symmetric (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    (frameConstant*(1+previousShear S.J S.X 0))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one 0)))
    (next_frame_bounds (S := S) (n := 0)).1 (next_frame_bounds (S := S) (n := 0)).2.1
    (next_frame_bounds (S := S) (n := 0)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact

/-- Forward next frame, given by `(P.forwardRenewal hq hB).changeActivation
(P.forwardGeometry_targetTime hq hB)`. -/
@[expose] def forwardNextFrame : ParentFrame (frameData (P.forwardParent hq hB)) P.nextTime :=
  (P.forwardRenewal hq hB).changeActivation (P.forwardGeometry_targetTime hq hB)

/-- Whole-horizon physical bounds for the forward child, kept as one named
proof to avoid elaborating the packet estimate twice inside `Step`. -/
theorem forwardPhysicalBounds (t : Icc (0 : ℝ) (F).parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (P.forwardState hq hB).evolution.velocity (t,y)) x‖ ≤
        gradientConstant*previousShear S.J S.X 0+(G).hchild*(goodRatio+(G).earlyRatio)+
          k^(-(1/4 : ℝ)) ∧
      ‖fderiv ℝ ((P.forwardState hq hB).evolution.force t) x‖ ≤
        hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0+
          2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*(goodRatio+(G).earlyRatio)+
            k^(-(1/4 : ℝ)) :=
  (F).physical_bounds symmetric _ _ P.restricted_gradient_bound P.restricted_hessian_bound t x

/-- The forward choice's parent, state, low bounds, physical bounds and renewed
frame, with the guards' shear, spike and `earlyRatio`. -/
@[expose] def forwardStep : P.Step where
  parent := P.forwardParent hq hB
  state := P.forwardState hq hB
  targetShear := (G).hchild
  spikeAmplitude := (G).δ
  errorRatio := (G).earlyRatio
  errorRatio_nonneg := (G).earlyRatio_nonneg
  targetShear_eq := P.forwardGuards_shear hq hB
  parent_horizon := rfl
  parent_scale := rfl
  label_eq := (F).label_constant
  low := P.forwardLow hq hB
  low_exterior := rfl
  low_core := rfl
  low_pressure := rfl
  low_boundary := rfl
  low_radius := rfl
  physical_bounds := P.forwardPhysicalBounds hq hB
  bad_cost := P.forward_bad_cost hq hB
  pressure_cost := P.forward_pressure_cost hq hB
  geometry := P.forwardGeometry hq hB
  geometry_targetTime := P.forwardGeometry_targetTime hq hB
  geometry_coupling := P.forwardFrame_a
  geometry_y := rfl
  geometry_delta_pos := (I).delta_pos
  geometry_shear := rfl
  renewal_errors := P.forward_renewal_errors hq hB
  renewal := P.forwardRenewal hq hB
  renewal_matches := P.forwardRenewal_matches hq hB
  renewal_G := rfl
  renewal_error := rfl

/-- Assemble the forward packet using the shared successor invariant. -/
@[expose] def forwardNext : Stage S 1 := P.next (P.forwardStep hq hB)

theorem forwardNext_time : (P.forwardNext hq hB).time=P.nextTime := rfl

end EulerPacketInduction.Stage
