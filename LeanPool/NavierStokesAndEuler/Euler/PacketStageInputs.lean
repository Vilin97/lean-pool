/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialInput
import LeanPool.NavierStokesAndEuler.Euler.PacketStagePhysicalBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalPacketParameters
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial

/-! Actual packet inputs at every finite stage, together with the
source-only parameter cap and the chosen frequency guard. -/

section

/-! The zero-history normal stage has the same fixed parameter envelope
as every positive-history stage. Its actual initial coordinate has norm one. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketBaseGuardScales EulerPacketLowConstants
  EulerParentPacketParameterCaps EulerNormalPacketParameters

variable {A : Parent} (L : LabelData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hsupport : IsCompact support)
  (P : ParentFrame (A.transverseData m hm R support hsupport) 0) (G : ForwardGuards P)

omit [CompleteSpace U] in
theorem forwardNormalParameterSize_bound (J D : ℕ) (hJ : 2 ≤ J) (C X : ℝ) (hC : 1 ≤ C) (hX : 1 ≤ X)
    (n : ℕ) (Ti : ℝ)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (hK : L.K ≤ previousFrequency J D X n ^ 80)
    (hTi : Ti ≤ 12 / baseHorizon J X)
    (hBc : H.Bc ≤ gradientConstant * X ^ 1000 + 2)
    (hL : H.L = EulerMeanHarmonic.boundaryLocalizationC1 * H.Bc + 1)
    (hΘ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hδ : G.δ = spike J X n) (hh : G.hchild = shear J X n)
    (hshear : P.shear = previousShear J X n) :
    L.geometryForwardParameterSize H m hm R support hsupport P G Ti G.initialCoordinate ≤
      envelope J C X n := by
  have hprev : 1 ≤ P.shear := hshear.symm ▸ previousShear_one J (by omega) X hX n
  have hterm : ‖G.initialCoordinate‖ ≤ terminalCap*L.K^4 := by
    rw [G.initialCoordinate_norm]
    exact one_le_mul_of_one_le_of_one_le terminalCap_one (one_le_pow₀ L.K_one)
  have hboundary := boundary_parameter_bound gradientConstant H.Bc H.L X hX hBc hL
  have hEi : P.epsilon⁻¹ ≤ 2*previousShear J X n := by
    rw [← hshear]
    exact P.epsilon_inv_le_twice_shear G.coupling_lower hprev
  have hbasepos := baseHorizon_pos J (by omega) (zero_lt_one.trans_le hX)
  have hraw := EulerPacketParameterEnvelope.source_size_le J D hJ X hX
    C (boundaryConstant gradientConstant) terminalCap 80 320 hC
    (boundaryConstant_pos gradientConstant gradient_nonneg).le (zero_le_one.trans terminalCap_one)
    (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num) hbaseH hbaseK n
    L.K 0 Ti (560*P.horizon^10/P.epsilon) H.L ‖G.initialCoordinate‖ P.horizon P.epsilon⁻¹
    (zero_le_one.trans L.K_one) (by simpa only [rpow_ofNat] using hK)
    (by positivity) hTi hboundary hterm (zero_le_one.trans G.horizon_lower) hΘ
    (inv_nonneg.mpr G.epsilon_pos.le) hEi (by rw [div_eq_mul_inv])
  change EulerParentInitializedRadius.parameterSize L.K 0 Ti (560*P.horizon^10/P.epsilon)
    H.L G.δ ‖G.initialCoordinate‖+G.hchild ≤ _
  rw [hδ,hh]
  exact hraw

end EulerParentPacketFrames.LabelData

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.GeometryForwardInput

open Real EulerParentInitializedRadius EulerMeanHarmonic

theorem parameterSize_one {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U] (I : GeometryForwardInput U) : 1 ≤ I.parameterSize := by
  have hL : 0 ≤ I.low.L :=
    (mul_nonneg boundaryLocalizationC1_nonneg I.low.Bc_nonneg).trans I.low.L_lower
  have hb := parameterSize_bounds I.label.K 0 I.parent.T⁻¹
    (560*I.frame.horizon^10/I.frame.epsilon) I.low.L I.geometry.δ ‖I.geometry.initialCoordinate‖
    (zero_le_one.trans I.label.K_one) le_rfl (inv_nonneg.mpr I.parent.T_pos.le)
    I.geometry.growth_constant_pos.le hL I.delta_pos (norm_nonneg _)
  exact hb.1.trans (le_add_of_nonneg_right I.geometry.child_nonneg)

end EulerParentPacketFrames.GeometryForwardInput

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketSupport EulerPacketLowConstants
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerParentNeighborThreshold EulerNormalPacketParameters

section Joined

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

/-- Joined input, bundling `parent`, `label`, `low`, `normal` and the required compatibility
proofs. -/
def joinedInput : EulerPacketInitial.Input (referencePlane (P.joinedNormal hn)) where
  parent := P.restrictedParent
  label := P.restrictedState.labels
  low := P.restrictedLow
  normal := P.joinedNormal hn
  normal_unit := P.joinedNormal_unit hn
  coordinates := LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))
  support := support
  support_compact := compact
  historyTime := P.time
  history_pos := P.time_pos hn
  history_lt := P.time_lt_nextHorizon
  total_le_one := P.nextHorizon_one
  frame := P.joinedFrame hn
  geometry := P.joinedGuards hn hq hB
  halfBall := by rw [P.joinedGuards_radius]; norm_num
  neighborhood := Metric.ball 0 (1/2 : ℝ)
  neighborhood_measurable := Metric.isOpen_ball.measurableSet
  neighborhood_open := Metric.isOpen_ball
  support_subset := subset_halfBall
  neighborhood_bound := fun x hx => le_of_lt (by
      simpa only [Metric.mem_ball,dist_zero_right] using hx)
  terminal := (P.joinedGuards hn hq hB).terminal
  cutoff_support := subset_rfl
  delta_pos := by rw [P.joinedGuards_delta]; exact S.spike_pos n
  delta_le_one := by rw [P.joinedGuards_delta]; exact S.spike_one n
  child_pos := by rw [P.joinedGuards_shear]; exact zero_lt_one.trans_le (S.shear_one n)

@[simp] theorem joinedInput_parent : (P.joinedInput hn hq hB).parent=P.restrictedParent := rfl
@[simp] theorem joinedInput_label : (P.joinedInput hn hq hB).label=P.restrictedState.labels := rfl
@[simp] theorem joinedInput_low : (P.joinedInput hn hq hB).low=P.restrictedLow := rfl
@[simp] theorem joinedInput_frame : (P.joinedInput hn hq hB).frame=P.joinedFrame hn := rfl
@[simp] theorem joinedInput_geometry : (P.joinedInput hn hq hB).geometry=P.joinedGuards hn hq hB :=
    rfl
@[simp] theorem joinedInput_terminal :
    (P.joinedInput hn hq hB).terminal=(P.joinedGuards hn hq hB).terminal := rfl

theorem joinedInput_parameterSize : (P.joinedInput hn hq hB).parameterSize ≤ envelope S.J 4 S.X n :=
  P.restrictedState.labels.normalParameterSize_bound P.restrictedLow
    (P.joinedNormal hn) (P.joinedNormal_unit hn)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))) support compact
    P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) (P.joinedGuards hn hq hB)
    S.J S.D (by have h := S.stage_large; omega) 4 S.X (by norm_num) S.x_one n
    P.time⁻¹ P.restrictedParent.T⁻¹ S.actual.initial_shear S.actual.initial_frequency P.label_eq.le
    (P.time_reciprocal hn) P.restricted_horizon_reciprocal P.core_cap P.boundary_eq rfl rfl
    (((P.joinedFrame_horizon hn).trans P.restrictedFrame_horizon).le.trans
      P.source_stage.horizon_le_Theta)
    (P.joinedGuards_delta hn hq hB) (P.joinedGuards_shear hn hq hB)
    ((P.joinedFrame_shear hn).trans P.frame_shear)

theorem joinedInput_frequency : (P.joinedInput hn hq hB).frequencyGuard (frequency S.J S.X n) :=
  S.source_frequency n _ (P.joinedInput hn hq hB).parameterSize_one
    (P.joinedInput_parameterSize hn hq hB)

theorem joinedInput_targetTime :
    ((P.joinedInput hn hq hB).geometry.lowGeometry (P.joinedInput hn hq
        hB).halfBall).targetTime=P.nextTime :=
  P.joinedGeometry_targetTime hn hq hB

theorem joinedInput_sigma_bound :
    (P.joinedInput hn hq hB).frame.sigma*scaleSequence S.J S.X n ≤ 2 := by
  change (P.joinedFrame hn).sigma*scaleSequence S.J S.X n ≤ 2
  rw [P.joinedFrame_sigma]
  exact P.normalized_sigma

theorem joinedInput_scale : (P.joinedInput hn hq hB).parent.ell=supportScale S.J S.X n := P.scale_eq

end Joined

section Forward

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

/-- Forward input, bundling `parent`, `label`, `low`, `normal` and the required compatibility
proofs. -/
def forwardInput : GeometryForwardInput (referencePlane P.forwardNormal) where
  parent := P.restrictedParent
  label := P.restrictedState.labels
  low := P.restrictedLow
  normal := P.forwardNormal
  normal_unit := P.forwardNormal_unit
  coordinates := LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)
  support := support
  support_compact := compact
  total_le_one := P.nextHorizon_one
  frame := P.forwardFrame
  geometry := P.forwardGuards hq hB
  halfBall := by rw [P.forwardGuards_radius]; norm_num
  neighborhood := Metric.ball 0 (1/2 : ℝ)
  neighborhood_measurable := Metric.isOpen_ball.measurableSet
  neighborhood_open := Metric.isOpen_ball
  support_subset := subset_halfBall
  neighborhood_bound := fun x hx => le_of_lt (by
      simpa only [Metric.mem_ball,dist_zero_right] using hx)
  cutoff_support := subset_rfl
  delta_pos := by rw [P.forwardGuards_delta]; exact S.spike_pos 0
  delta_le_one := by rw [P.forwardGuards_delta]; exact S.spike_one 0
  child_pos := by rw [P.forwardGuards_shear]; exact zero_lt_one.trans_le (S.shear_one 0)

@[simp] theorem forwardInput_parent : (P.forwardInput hq hB).parent=P.restrictedParent := rfl
@[simp] theorem forwardInput_label : (P.forwardInput hq hB).label=P.restrictedState.labels := rfl
@[simp] theorem forwardInput_low : (P.forwardInput hq hB).low=P.restrictedLow := rfl
@[simp] theorem forwardInput_frame : (P.forwardInput hq hB).frame=P.forwardFrame := rfl
@[simp] theorem forwardInput_geometry : (P.forwardInput hq hB).geometry=P.forwardGuards hq hB := rfl

theorem forwardInput_parameterSize : (P.forwardInput hq hB).parameterSize ≤ envelope S.J 4 S.X 0 :=
  P.restrictedState.labels.forwardNormalParameterSize_bound P.restrictedLow
    P.forwardNormal P.forwardNormal_unit
    (LinearIsometryEquiv.refl ℝ (referencePlane P.forwardNormal)) support compact
    P.forwardFrame (P.forwardGuards hq hB) S.J S.D (by have h := S.stage_large; omega)
    4 S.X (by norm_num) S.x_one 0 P.restrictedParent.T⁻¹
    S.actual.initial_shear S.actual.initial_frequency P.label_eq.le P.restricted_horizon_reciprocal
    P.core_cap P.boundary_eq
    ((P.forwardFrame_horizon.trans P.restrictedFrame_horizon).le.trans
        P.source_stage.horizon_le_Theta)
    (P.forwardGuards_delta hq hB) (P.forwardGuards_shear hq hB)
    (P.forwardFrame_shear.trans P.frame_shear)

theorem forwardInput_frequency : (P.forwardInput hq hB).frequencyGuard (frequency S.J S.X 0) :=
  S.source_frequency 0 _ (P.forwardInput hq hB).parameterSize_one (P.forwardInput_parameterSize hq
      hB)

theorem forwardInput_targetTime :
    ((P.forwardInput hq hB).geometry.lowGeometry (P.forwardInput hq
        hB).halfBall).targetTime=P.nextTime :=
  P.forwardGeometry_targetTime hq hB

theorem forwardInput_sigma_bound : (P.forwardInput hq hB).frame.sigma*scaleSequence S.J S.X 0 ≤ 2
    := by
  change P.forwardFrame.sigma*scaleSequence S.J S.X 0 ≤ 2
  rw [P.forwardFrame_sigma]
  exact P.normalized_sigma

theorem forwardInput_scale : (P.forwardInput hq hB).parent.ell=supportScale S.J S.X 0 := P.scale_eq

end Forward

end EulerPacketInduction.Stage
