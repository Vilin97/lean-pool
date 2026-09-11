/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.BaseInductionStage
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGrowth
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInputs
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceLow
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceRenewal
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageEstimates
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageLowPropagation
public import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceInitial
public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication

/-! The actual infinite packet family, from the concrete first stage
and the two genuine successor constructions. -/

section

/-! The positive-history normal step. One actual correction constructs
the next Euler state, localized low bounds, renewed frame and exact
initial increment, without any premise about a future stage. -/

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerPacketGeometryLowBounds EulerParentNeighborThreshold
  EulerMeanHarmonic

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "I" => P.joinedInput hn hq hB
local notation "G" => P.joinedGuards hn hq hB
local notation "k" => frequency S.J S.X n
local notation "hk" => S.normal_frequency n
local notation "ell" => supportScale S.J S.X (n+1)

/-- Joined choice: an abbreviation for `GeometryJoinedChoice I P.restrictedState k hk ell
(S.support_pos (n+1)) (S.support_one (n+1))`. -/
abbrev JoinedChoice :=
  GeometryJoinedChoice I P.restrictedState k hk ell (S.support_pos (n+1)) (S.support_one (n+1))

/-- Choose joined, choosing the witness provided by `Joined`. -/
def chooseJoined : P.JoinedChoice hn hq hB := by
  have hsec := S.secondary_frequency n P.restrictedState.labels.K P.label_eq.le
  exact Classical.choice (exists_geometryJoinedChoice I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) rfl (P.joinedInput_frequency hn hq hB) hsec.1
    (by rw [P.joinedInput_scale hn hq hB]; exact hsec.2))

local notation "F" => P.chooseJoined hn hq hB

/-- Joined parent, given by `(F).parent`. -/
def joinedParent : Parent := (F).parent

/-- Joined state, given by `GeometryJoinedChoice.state I P.restrictedState k hk ell
(S.support_pos (n+1)) (S.support_one (n+1)) F symmetric`. -/
def joinedState : SmoothState (P.joinedParent hn hq hB) :=
  GeometryJoinedChoice.state I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

theorem joined_smallness :
    (P.restrictedLow.K+2*(gradientConstant*previousShear S.J S.X n)*(G).hchild *
        ((G).δ*goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)))*(P.nextHorizon^2/2) +
      (P.restrictedLow.Be+((G).hchild*(G).badRatio+k^(-(1/4 : ℝ))))*P.nextHorizon +
      boundaryLocalizationC2*(P.restrictedLow.Bc+((G).hchild*(G).badRatio+k^(-(1/4 : ℝ)))) *
        P.restrictedLow.r^3*P.nextHorizon ≤ 1/2 := by
  have he : 0 ≤ k^(-(1/4 : ℝ)) := rpow_nonneg (hk).pos.le _
  have h := P.next_localized P.nextHorizon
    ((G).hchild*(G).badRatio+k^(-(1/4 : ℝ)))
    (2*(gradientConstant*previousShear S.J S.X n)*(G).hchild *
      ((G).δ*goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)))
    P.nextHorizon_pos.le P.nextHorizon_le_base
    (by positivity [(G).child_nonneg,(G).badRatio_nonneg])
    (by positivity [gradient_nonneg,S.previousShear_one n,(G).child_nonneg,(G).delta_nonneg,
      goodRatio_pos,(G).badRatio_nonneg])
    (P.joined_initial_cost hn hq hB) (P.joined_pressure_cost hn hq hB)
  rw [restrictedLow_pressure,restrictedLow_exterior,restrictedLow_core,restrictedLow_radius]
  convert h using 1; ring

/-- Joined low as an element of `LowBounds (P.joinedParent hn hq hB)`. -/
def joinedLow : LowBounds (P.joinedParent hn hq hB) :=
  (F).lowBounds (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    P.restricted_gradient_bound P.restricted_hessian_bound (P.joined_smallness hn hq hB)

/-- Joined renewal as an element of `ParentFrame (frameData (P.joinedParent hn hq hB))
(P.joinedGeometry hn hq hB).targetTime`. -/
def joinedRenewal : ParentFrame (frameData (P.joinedParent hn hq hB))
    (P.joinedGeometry hn hq hB).targetTime :=
  (F).renewal symmetric (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    (frameConstant*(1+previousShear S.J S.X n))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one n)))
    (next_frame_bounds (S := S) (n := n)).1 (next_frame_bounds (S := S) (n := n)).2.1
        (next_frame_bounds (S := S) (n := n)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact

theorem joinedRenewal_matches :
    RenewalAtTarget (P.joinedGeometry hn hq hB) (P.joinedRenewal hn hq hB) :=
  (F).renewal_matches symmetric (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    (frameConstant*(1+previousShear S.J S.X n))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one n)))
    (next_frame_bounds (S := S) (n := n)).1 (next_frame_bounds (S := S) (n := n)).2.1
        (next_frame_bounds (S := S) (n := n)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact

/-- Joined next frame, given by `(P.joinedRenewal hn hq hB).changeActivation
(P.joinedGeometry_targetTime hn hq hB)`. -/
def joinedNextFrame : ParentFrame (frameData (P.joinedParent hn hq hB)) P.nextTime :=
  (P.joinedRenewal hn hq hB).changeActivation (P.joinedGeometry_targetTime hn hq hB)

/-- Joined next as an element of `Stage S (n+1)`. -/
def joinedNext : Stage S (n+1) := by
  have hbad : 2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*(G).badRatio ≤
      EulerPacketPressureScale.badCost S.J 4 gradientConstant gradientConstant hessianConstant 80
        (scaleSequence S.J S.X) n := by
    have h := P.joined_bad_cost hn hq hB
    change 2*(gradientConstant*previousShear S.J S.X n)*shear S.J S.X n*(G).badRatio ≤ _ at h
    linarith only [h]
  have habsorb := ratio_absorption (S := S) (n := n) (G).badRatio (G).badRatio_nonneg hbad
  have hparams := literal_step (P.joinedRenewal_matches hn hq hB) S.J S.X n S.renewal_series
    (by norm_num) (P.joined_renewal_errors hn hq hB) rfl
  have hcoupling : |(P.joinedRenewal hn hq hB).a/P.frame.a-1| ≤
      renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n := by
    have h := hparams.1
    change |(P.joinedRenewal hn hq hB).a/(P.joinedFrame hn).a-1| ≤ _ at h
    rwa [P.joinedFrame_a hn] at h
  refine {
    parent := P.joinedParent hn hq hB
    state := P.joinedState hn hq hB
    low := P.joinedLow hn hq hB
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
    frame := P.joinedNextFrame hn hq hB
    frame_shear := ?_
    frame_bound := ?_
    frame_error := ?_
    coupling_error := ?_
    tilt_lower := ?_
    tilt_upper := ?_
    compression := ?_ }
  · intro t x
    exact ((F).physical_bounds symmetric _ _ P.restricted_gradient_bound
      P.restricted_hessian_bound t x).1.trans habsorb.1
  · intro t x
    have h := ((F).physical_bounds symmetric _ _ P.restricted_gradient_bound
      P.restricted_hessian_bound t x).2
    apply h.trans
    change hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n +
      2*(gradientConstant*previousShear S.J S.X n)*shear S.J S.X n *
        (goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)) ≤
      hessianConstant*shear S.J S.X n*previousShear S.J S.X n
    linarith only [habsorb.2]
  · exact (P.initial_step_bound _ (P.joined_initial_cost hn hq hB)).1
  · exact (P.initial_step_bound _ (P.joined_initial_cost hn hq hB)).2
  · change P.low.K+2*(gradientConstant*previousShear S.J S.X n)*(G).hchild *
      ((G).δ*goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)) ≤ _
    have h := P.pressure_step_bound _ (P.joined_pressure_cost hn hq hB)
    convert h using 1; ring
  · rw [joinedNextFrame,ParentFrame.changeActivation_shear]
    exact (P.joinedRenewal_matches hn hq hB).shear_eq (I).delta_pos
  · change ((P.joinedRenewal hn hq hB).changeActivation _).G ≤ _
    rw [ParentFrame.changeActivation_G]
    exact le_rfl
  · change ((P.joinedRenewal hn hq hB).changeActivation _).error ≤ _
    rw [ParentFrame.changeActivation_error]
    exact le_rfl
  · rw [joinedNextFrame,ParentFrame.changeActivation_a]
    exact P.coupling_step _ hcoupling
  · rw [joinedNextFrame,ParentFrame.changeActivation_sigma]
    exact hparams.2.1
  · rw [joinedNextFrame,ParentFrame.changeActivation_sigma]
    exact hparams.2.2
  · intro _
    have hc := (P.joinedRenewal_matches hn hq hB).background_compression_of_error_le_one
      (priorError S.J S.D S.X (n+1)) (S.priorError_one (n+1))
    change ⟪((P.joinedRenewal hn hq hB).changeActivation _).B P.nextTime
        (unit (((P.joinedRenewal hn hq hB).changeActivation _).m P.nextTime)),
      unit (((P.joinedRenewal hn hq hB).changeActivation _).m P.nextTime)⟫_ℝ +
        priorError S.J S.D S.X (n+1) < 0
    rw [ParentFrame.changeActivation_B,ParentFrame.changeActivation_m]
    simpa only [← P.joinedGeometry_targetTime hn hq hB] using hc

theorem joinedNext_time : (P.joinedNext hn hq hB).time=P.nextTime := rfl

theorem joinedNext_initial_increment :
    (fun x => (P.joinedNext hn hq hB).state.evolution.velocity (0,x) -
      P.state.evolution.velocity (0,x)) = (I).high k+(I).mean k :=
  GeometryJoinedChoice.initial_increment_eq I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

theorem joinedNext_initial_velocity :
    (fun x => (P.joinedNext hn hq hB).state.evolution.velocity (0,x)) =
      (fun x => P.state.evolution.velocity (0,x))+((I).high k+(I).mean k) :=
  GeometryJoinedChoice.state_velocity_initial I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

end EulerPacketInduction.Stage

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleSequence
open scoped Topology

namespace Stage

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

/-- Successor as an element of `Stage S (n+1)`. -/
def successor {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
    (hB : commonThreshold gradientConstant hessianConstant ≤ B) : Stage S (n+1) := by
  cases n with
  | zero => exact P.forwardNext hq hB
  | succ n => exact P.joinedNext (Nat.succ_ne_zero n) hq hB

theorem successor_time {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
    (hB : commonThreshold gradientConstant hessianConstant ≤ B) :
    (P.successor hq hB).time=P.nextTime := by
  cases n with
  | zero => exact P.forwardNext_time hq hB
  | succ n => exact P.joinedNext_time (Nat.succ_ne_zero n) hq hB

end Stage

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

/-- Stages as an element of `(n : ℕ) → Stage S n | 0 => S.firstStage | n+1 => (stages
n).successor hq hB`. -/
def stages : (n : ℕ) → Stage S n
  | 0 => S.firstStage
  | n+1 => (stages n).successor hq hB

theorem stages_zero : stages S hq hB 0=S.firstStage := rfl

theorem stages_succ (n : ℕ) :
    stages S hq hB (n+1)=(stages S hq hB n).successor hq hB := rfl

theorem stages_time (n : ℕ) :
    (stages S hq hB (n+1)).time=(stages S hq hB n).nextTime :=
  (stages S hq hB n).successor_time hq hB

theorem stages_initial_step (n : ℕ) (hn : n ≠ 0) :
    (fun x => (stages S hq hB (n+1)).state.evolution.velocity (0,x)) =
      (fun x => (stages S hq hB n).state.evolution.velocity (0,x)) +
      (((stages S hq hB n).joinedInput hn hq hB).high (frequency S.J S.X n) +
        ((stages S hq hB n).joinedInput hn hq hB).mean (frequency S.J S.X n)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact (stages S hq hB (n+1)).joinedNext_initial_velocity (Nat.succ_ne_zero n) hq hB

theorem stages_gradient_atTop :
    Tendsto (fun n => (stages S hq hB n).activationGradient) atTop atTop :=
  Stage.gradient_atTop (stages S hq hB)

/-- Construction scales: an abbreviation for `Scales (requiredExponent : ℝ) (commonThreshold
gradientConstant hessianConstant)`. -/
abbrev ConstructionScales :=
  Scales (requiredExponent : ℝ) (commonThreshold gradientConstant hessianConstant)

/-- Construction scales, given by `Classical.choice (exists_scales (requiredExponent : ℝ)
(commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))`. -/
def constructionScales : ConstructionScales :=
  Classical.choice (exists_scales (requiredExponent : ℝ)
    (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))

/-- Packets, given by `stages constructionScales le_rfl le_rfl n`. -/
def packets (n : ℕ) : Stage constructionScales n := stages constructionScales le_rfl le_rfl n

theorem packets_gradient_atTop :
    Tendsto (fun n => (packets n).activationGradient) atTop atTop := Stage.gradient_atTop packets

end EulerPacketInduction
