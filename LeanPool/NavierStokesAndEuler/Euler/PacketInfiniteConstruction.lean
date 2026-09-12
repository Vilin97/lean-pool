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
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceLow
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceRenewal
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageEstimates
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageLowPropagation
public import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceInitial
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication

/-! The actual infinite packet family, from the concrete first stage
and the two genuine successor constructions. -/

section

/-! The positive-history normal step. One actual correction constructs
the next Euler state, localized low bounds, renewed frame and exact
initial increment, without any premise about a future stage. -/

public section

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
@[expose] def joinedParent : Parent := (F).parent

/-- Joined state, given by `GeometryJoinedChoice.state I P.restrictedState k hk ell
(S.support_pos (n+1)) (S.support_one (n+1)) F symmetric`. -/
@[expose] def joinedState : SmoothState (P.joinedParent hn hq hB) :=
  GeometryJoinedChoice.state I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

theorem joined_smallness :
    (P.restrictedLow.K+2*(gradientConstant*previousShear S.J S.X n)*(G).hchild *
        ((G).δ*goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)))*(P.nextHorizon^2/2) +
      (P.restrictedLow.Be+((G).hchild*(G).badRatio+k^(-(1/4 : ℝ))))*P.nextHorizon +
      boundaryLocalizationC2*(P.restrictedLow.Bc+((G).hchild*(G).badRatio+k^(-(1/4 : ℝ)))) *
        P.restrictedLow.r^3*P.nextHorizon ≤ 1/2 :=
  P.successor_smallness (G).hchild (G).δ (G).badRatio
    (G).child_nonneg (G).delta_nonneg (G).badRatio_nonneg
    (P.joined_initial_cost hn hq hB) (P.joined_pressure_cost hn hq hB)

/-- Joined low as an element of `LowBounds (P.joinedParent hn hq hB)`. -/
@[expose] def joinedLow : LowBounds (P.joinedParent hn hq hB) :=
  (F).lowBounds (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    P.restricted_gradient_bound P.restricted_hessian_bound (P.joined_smallness hn hq hB)

/-- Joined renewal as an element of `ParentFrame (frameData (P.joinedParent hn hq hB))
(P.joinedGeometry hn hq hB).targetTime`. -/
@[expose] def joinedRenewal : ParentFrame (frameData (P.joinedParent hn hq hB))
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
@[expose] def joinedNextFrame : ParentFrame (frameData (P.joinedParent hn hq hB)) P.nextTime :=
  (P.joinedRenewal hn hq hB).changeActivation (P.joinedGeometry_targetTime hn hq hB)

/-- Whole-horizon physical bounds for the joined child, kept as one named proof
to avoid elaborating the packet estimate twice inside `Step`. -/
theorem joinedPhysicalBounds (t : Icc (0 : ℝ) (F).parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (P.joinedState hn hq hB).evolution.velocity (t,y)) x‖ ≤
        gradientConstant*previousShear S.J S.X n+(G).hchild*(goodRatio+(G).badRatio)+
          k^(-(1/4 : ℝ)) ∧
      ‖fderiv ℝ ((P.joinedState hn hq hB).evolution.force t) x‖ ≤
        hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n+
          2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*(goodRatio+(G).badRatio)+
            k^(-(1/4 : ℝ)) :=
  (F).physical_bounds symmetric _ _ P.restricted_gradient_bound P.restricted_hessian_bound t x

/-- The joined choice's parent, state, low bounds, physical bounds and renewed
frame, with the guards' shear, spike and `badRatio`. -/
@[expose] def joinedStep : P.Step where
  parent := P.joinedParent hn hq hB
  state := P.joinedState hn hq hB
  targetShear := (G).hchild
  spikeAmplitude := (G).δ
  errorRatio := (G).badRatio
  errorRatio_nonneg := (G).badRatio_nonneg
  targetShear_eq := P.joinedGuards_shear hn hq hB
  parent_horizon := rfl
  parent_scale := rfl
  label_eq := (F).label_constant
  low := P.joinedLow hn hq hB
  low_exterior := rfl
  low_core := rfl
  low_pressure := rfl
  low_boundary := rfl
  low_radius := rfl
  physical_bounds := P.joinedPhysicalBounds hn hq hB
  bad_cost := P.joined_bad_cost hn hq hB
  pressure_cost := P.joined_pressure_cost hn hq hB
  geometry := P.joinedGeometry hn hq hB
  geometry_targetTime := P.joinedGeometry_targetTime hn hq hB
  geometry_coupling := P.joinedFrame_a hn
  geometry_y := rfl
  geometry_delta_pos := (I).delta_pos
  geometry_shear := rfl
  renewal_errors := P.joined_renewal_errors hn hq hB
  renewal := P.joinedRenewal hn hq hB
  renewal_matches := P.joinedRenewal_matches hn hq hB
  renewal_G := rfl
  renewal_error := rfl

/-- Assemble the joined packet using the shared successor invariant. -/
@[expose] def joinedNext : Stage S (n+1) := P.next (P.joinedStep hn hq hB)

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

public section

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleSequence
open scoped Topology

namespace Stage

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

/-- Successor as an element of `Stage S (n+1)`. -/
@[expose] def successor {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
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
@[expose] def stages : (n : ℕ) → Stage S n
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
@[expose] def packets (n : ℕ) : Stage constructionScales n :=
  stages constructionScales le_rfl le_rfl n

theorem packets_gradient_atTop :
    Tendsto (fun n => (packets n).activationGradient) atTop atTop := Stage.gradient_atTop packets

end EulerPacketInduction
