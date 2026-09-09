/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInputs
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageEstimates
public import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceLow
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceRenewal

@[expose] public section

/-! The time-zero normal step: the same selected correction supplies
the next actual state, low source bounds and renewed geometric frame. -/

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

abbrev ForwardChoice := GeometryForwardChoice I P.restrictedState k hk ell (S.support_pos 1)
  (S.support_one 1)

def chooseForward : P.ForwardChoice hq hB := by
  have hsec := S.secondary_frequency 0 P.restrictedState.labels.K P.label_eq.le
  exact Classical.choice (exists_geometryForwardChoice I P.restrictedState k hk ell
    (S.support_pos 1) (S.support_one 1) (P.forwardInput_frequency hq hB) hsec.1
    (by rw [P.forwardInput_scale]; exact hsec.2))

local notation "F" => P.chooseForward hq hB

def forwardParent : Parent := (F).parent

def forwardState : SmoothState (P.forwardParent hq hB) :=
  GeometryForwardChoice.state I P.restrictedState k hk ell (S.support_pos 1) (S.support_one 1) F
    symmetric

theorem forward_smallness :
    (P.restrictedLow.K+2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*
        ((G).δ*goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)))*(P.nextHorizon^2/2)+
      (P.restrictedLow.Be+((G).hchild*(G).earlyRatio+k^(-(1/4 : ℝ))))*P.nextHorizon+
      boundaryLocalizationC2*(P.restrictedLow.Bc+((G).hchild*(G).earlyRatio+k^(-(1/4 : ℝ))))*
        P.restrictedLow.r^3*P.nextHorizon ≤ 1/2 := by
  have he : 0 ≤ k^(-(1/4 : ℝ)) := rpow_nonneg (hk).pos.le _
  have h := P.next_localized P.nextHorizon
    ((G).hchild*(G).earlyRatio+k^(-(1/4 : ℝ)))
    (2*(gradientConstant*previousShear S.J S.X
      0)*(G).hchild*((G).δ*goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)))
    P.nextHorizon_pos.le P.nextHorizon_le_base
    (by positivity [(G).child_nonneg,(G).earlyRatio_nonneg])
    (by positivity [gradient_nonneg,S.previousShear_one 0,(G).child_nonneg,(G).delta_nonneg,
      goodRatio_pos,(G).earlyRatio_nonneg])
    (P.forward_initial_cost hq hB) (P.forward_pressure_cost hq hB)
  rw [P.restrictedLow_pressure,P.restrictedLow_exterior,P.restrictedLow_core,P.restrictedLow_radius]
  convert h using 1; ring

def forwardLow : LowBounds (P.forwardParent hq hB) :=
  (F).lowBounds (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    P.restricted_gradient_bound P.restricted_hessian_bound (P.forward_smallness hq hB)

def forwardRenewal : ParentFrame (frameData (P.forwardParent hq hB)) (P.forwardGeometry hq
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

def forwardNextFrame : ParentFrame (frameData (P.forwardParent hq hB)) P.nextTime :=
  (P.forwardRenewal hq hB).changeActivation (P.forwardGeometry_targetTime hq hB)

def forwardNext : Stage S 1 := by
  have hbad : 2*gradientConstant*previousShear S.J S.X 0*shear S.J S.X 0*(G).earlyRatio ≤
      EulerPacketPressureScale.badCost S.J 4 gradientConstant gradientConstant hessianConstant 80
        (scaleSequence S.J S.X) 0 := by
    have h := P.forward_bad_cost hq hB
    change 2*(gradientConstant*previousShear S.J S.X 0)*shear S.J S.X 0*(G).earlyRatio ≤ _ at h
    nlinarith only [h]
  have habsorb := ratio_absorption (S := S) (n := 0) (G).earlyRatio (G).earlyRatio_nonneg hbad
  have hparams := literal_step (P.forwardRenewal_matches hq hB) S.J S.X 0 S.renewal_series
    (by norm_num) (P.forward_renewal_errors hq hB) rfl
  have hcoupling : |(P.forwardRenewal hq hB).a/P.frame.a-1| ≤
      renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 := by
    have h := hparams.1
    change |(P.forwardRenewal hq hB).a/P.forwardFrame.a-1| ≤ _ at h
    rwa [P.forwardFrame_a] at h
  refine {
    parent := P.forwardParent hq hB
    state := P.forwardState hq hB
    low := P.forwardLow hq hB
    time := P.nextTime
    time_nonneg := P.nextTime_pos.le
    time_zero := fun h => by omega
    time_lower := fun _ => P.nextTime_lower
    horizon_eq := rfl
    horizon_le := P.nextHorizon_le_base
    scale_eq := rfl
    label_eq := (F).label_constant
    gradient_bound := ?_
    hessian_bound := ?_
    exterior_bound := ?_
    core_bound := ?_
    pressure_bound := ?_
    boundary_eq := rfl
    radius_eq := P.radius_eq
    frame := P.forwardNextFrame hq hB
    frame_shear := ?_
    frame_bound := ?_
    frame_error := ?_
    coupling_error := ?_
    tilt_lower := ?_
    tilt_upper := ?_
    compression := ?_ }
  · intro t x
    exact ((F).physical_bounds symmetric _ _ P.restricted_gradient_bound P.restricted_hessian_bound
      t x).1.trans
      habsorb.1
  · intro t x
    have h := ((F).physical_bounds symmetric _ _ P.restricted_gradient_bound
      P.restricted_hessian_bound t x).2
    apply h.trans
    change hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0+
      2*(gradientConstant*previousShear S.J S.X 0)*shear S.J S.X 0*(goodRatio+(G).earlyRatio)+
        k^(-(1/4 : ℝ)) ≤ hessianConstant*shear S.J S.X 0*previousShear S.J S.X 0
    nlinarith only [habsorb.2]
  · exact (P.initial_step_bound _ (P.forward_initial_cost hq hB)).1
  · exact (P.initial_step_bound _ (P.forward_initial_cost hq hB)).2
  · have h := P.pressure_step_bound _ (P.forward_pressure_cost hq hB)
    change P.low.K+2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*
      ((G).δ*goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)) ≤ _
    convert h using 1; ring
  · rw [forwardNextFrame,ParentFrame.changeActivation_shear]
    exact (P.forwardRenewal_matches hq hB).shear_eq (I).delta_pos
  · change ((P.forwardRenewal hq hB).changeActivation _).G ≤ _
    rw [ParentFrame.changeActivation_G]
    exact le_rfl
  · change ((P.forwardRenewal hq hB).changeActivation _).error ≤ _
    rw [ParentFrame.changeActivation_error]
    exact le_rfl
  · rw [forwardNextFrame,ParentFrame.changeActivation_a]
    exact P.coupling_step _ hcoupling
  · rw [forwardNextFrame,ParentFrame.changeActivation_sigma]
    exact hparams.2.1
  · rw [forwardNextFrame,ParentFrame.changeActivation_sigma]
    exact hparams.2.2
  · intro _
    have hc := (P.forwardRenewal_matches hq hB).background_compression_of_error_le_one
      (priorError S.J S.D S.X 1) (S.priorError_one 1)
    change ⟪((P.forwardRenewal hq hB).changeActivation _).B P.nextTime
        (unit (((P.forwardRenewal hq hB).changeActivation _).m P.nextTime)),
      unit (((P.forwardRenewal hq hB).changeActivation _).m P.nextTime)⟫_ℝ+
        priorError S.J S.D S.X 1 < 0
    rw [ParentFrame.changeActivation_B,ParentFrame.changeActivation_m]
    simpa only [← P.forwardGeometry_targetTime hq hB] using hc

theorem forwardNext_time : (P.forwardNext hq hB).time=P.nextTime := rfl

end EulerPacketInduction.Stage
