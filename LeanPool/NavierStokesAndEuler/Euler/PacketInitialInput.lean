/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSmoothFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryInitialAmplitude
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryInitialBounds

/-! Genuine parent/geometry inputs for an initial increment. The high and
mean fields below are the actual solved profiles, not prescribed bounds. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitial

open Set EulerSmoothLimit EulerSpatialCutoffs EulerParentPacketFrames
  EulerTransversePacketProvider EulerPacketSourceGeometry EulerPacketCylinderField
  EulerPacketTerminalDatum EulerPacketUniformSource EulerPhysicalL2Scaling
  EulerPacketSourceFrequency EulerLpTranslation EulerAllOrderDriftCorrection

/-- Input data, collecting `parent`, `label`, `low`, `normal`, `normal_unit`, `coordinates` and
their compatibility conditions. -/
structure Input (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] where
  /-- Parent of `Input`, of type `Parent`. -/
  parent : Parent
  /-- Label of `Input`, of type `LabelData parent`. -/
  label : LabelData parent
  /-- Low of `Input`, of type `LowBounds parent`. -/
  low : LowBounds parent
  /-- Normal of `Input`, of type `Space`. -/
  normal : Space
  normal_unit : ‖normal‖=1
  /-- Coordinates of `Input`, of type `U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane
  normal`. -/
  coordinates : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane normal
  /-- Support set of `Input`, of type `Set Space`. -/
  support : Set Space
  support_compact : IsCompact support
  /-- History time of `Input`, of type `ℝ`. -/
  historyTime : ℝ
  history_pos : 0 < historyTime
  history_lt : historyTime < parent.T
  total_le_one : parent.T ≤ 1
  /-- Frame supplied by `Input`. -/
  frame : ParentFrame (parent.transverseData normal normal_unit coordinates support
      support_compact) historyTime
  /-- Geometry supplied by `Input`. -/
  geometry : Guards history_pos history_lt frame
    (parent.historyOn low normal normal_unit coordinates support support_compact historyTime
        history_pos history_lt)
  halfBall : (1/2 : ℝ) ≤ geometry.radius
  /-- Neighborhood of `Input`, of type `Set Space`. -/
  neighborhood : Set Space
  neighborhood_measurable : MeasurableSet neighborhood
  neighborhood_open : IsOpen neighborhood
  support_subset : support ⊆ neighborhood
  neighborhood_bound : ∀ x ∈ neighborhood, ‖x‖ ≤ (1/2 : ℝ)
  /-- Terminal of `Input`, of type `U`. -/
  terminal : U
  cutoff_support : tsupport innerCutoff ⊆ support
  delta_pos : 0 < geometry.δ
  delta_le_one : geometry.δ ≤ 1
  child_pos : 0 < geometry.hchild

namespace Input

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)

/-- Data: an abbreviation for `A.parent.transverseData A.normal A.normal_unit A.coordinates
A.support A.support_compact`. -/
abbrev data : Data U := A.parent.transverseData A.normal A.normal_unit A.coordinates A.support
    A.support_compact
/-- Mean data: an abbreviation for `A.parent.meanData A.low`. -/
abbrev meanData : EulerMeanPacketProvider.Data := A.parent.meanData A.low
/-- History: an abbreviation for `A.parent.historyOn A.low A.normal A.normal_unit A.coordinates
A.support A.support_compact A.historyTime A.history_pos A.history_lt`. -/
abbrev history : HistoryData (A.data.initial A.historyTime A.history_pos A.history_lt.le) :=
  A.parent.historyOn A.low A.normal A.normal_unit A.coordinates A.support A.support_compact
    A.historyTime A.history_pos A.history_lt

/-- Parameter size, constructed using `A.label.geometryParameterSize`. -/
def parameterSize : ℝ := A.label.geometryParameterSize A.low A.normal A.normal_unit A.coordinates
  A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
  A.historyTime⁻¹ A.parent.T⁻¹ A.terminal

/-- Alpha, given by `A.geometry.primaryAmplitude A.halfBall`. -/
def alpha : ℝ := A.geometry.primaryAmplitude A.halfBall

theorem alpha_pos : 0 < A.alpha := A.geometry.primaryAmplitude_pos A.halfBall A.delta_pos
    A.child_pos

/-- Frequency guard, given by `frequencyConstant*A.parameterSize^frequencyPower ≤ smallPower k`. -/
def frequencyGuard (k : ℝ) : Prop := frequencyConstant*A.parameterSize^frequencyPower ≤ smallPower k

/-- High, constructed using `initializedInitialHigh`. -/
def high (k : ℝ) : Space → Space :=
  initializedInitialHigh A.meanData A.data A.historyTime A.history_pos A.history_lt A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k

/-- Mean, constructed using `initializedInitialMean`. -/
def mean (k : ℝ) : Space → Space :=
  initializedInitialMean A.meanData A.data A.historyTime A.history_pos A.history_lt A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k

/-- High field, constructed using `initializedInitialHighField`. -/
def highField (k : ℝ) : SmoothL2Field Space :=
  initializedInitialHighField A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k

/-- Mean field, constructed using `initializedInitialMeanField`. -/
def meanField (k : ℝ) : SmoothL2Field Space :=
  initializedInitialMeanField A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k

theorem highField_field (k : ℝ) : (A.highField k).field=A.high k := rfl
theorem meanField_field (k : ℝ) : (A.meanField k).field=A.mean k := rfl

theorem parameterSize_one : 1 ≤ A.parameterSize :=
  (A.label.geometry_initial_primitives A.low A.normal A.normal_unit A.coordinates
    A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
    A.halfBall A.historyTime⁻¹ A.parent.T⁻¹ (A.history_lt.le.trans A.total_le_one) le_rfl
    A.total_le_one le_rfl A.neighborhood A.neighborhood_measurable A.neighborhood_open
    A.support_subset A.neighborhood_bound A.terminal A.delta_pos).1

theorem initial_bounds (x : ℝ) (hσ : A.frame.sigma * x ≤ 2) (k : ℝ)
    (hk : 4 ≤ k) (hfrequency : A.frequencyGuard k) (s : ℕ) :
    derivativeSum s (A.high k) ≤
      (A.parent.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        EulerPacketInitialCost.sourceConstant s *
        A.parameterSize^(EulerPacketInitialAmplitude.degree+EulerPacketInitialCost.sourcePower s)) *
        Real.exp (-x/8) ∧
    derivativeSum s (A.mean k) ≤
      (A.parent.ell⁻¹)^s/k^2*(EulerPacketInitialCost.sourceConstant s *
        A.parameterSize^EulerPacketInitialCost.sourcePower s) :=
  A.label.geometry_initial_bounds A.low A.normal A.normal_unit A.coordinates
    A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
    A.halfBall A.historyTime⁻¹ A.parent.T⁻¹ (A.history_lt.le.trans A.total_le_one) le_rfl
    A.total_le_one le_rfl A.neighborhood A.neighborhood_measurable A.neighborhood_open
    A.support_subset A.neighborhood_bound A.terminal A.cutoff_support A.delta_pos A.delta_le_one
    A.child_pos x hσ k hk hfrequency s

theorem initial_support (k : ℝ) :
    tsupport (A.high k) ⊆ Metric.closedBall 0 2 ∧ tsupport (A.mean k) ⊆ Metric.closedBall 0 2 := by
  apply initializedInitial_common_support A.meanData A.data rfl A.historyTime A.history_pos
      A.history_lt
    A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha ?_ (truncation k) k
  intro x hx
  have hb := A.neighborhood_bound x (A.support_subset hx)
  simpa only [Metric.mem_closedBall,dist_zero_right] using hb

/-- Agreement: an abbreviation for `A.parent.sourceAgreement A.normal A.normal_unit
A.coordinates A.support A.support_compact A.low`. -/
abbrev agreement : SourceCoefficientAgreement A.meanData A.data :=
  A.parent.sourceAgreement A.normal A.normal_unit A.coordinates A.support A.support_compact A.low

theorem sameQ_initial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
    (Q : Budget period A.data.T_pos
      (initializedCorrectionData A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
          A.history
        A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation k) hn
            k hk)) :
    scale A.parent.ell
      (initializedExactPhysicalVelocity A.meanData A.data rfl A.historyTime A.history_pos
          A.history_lt
        A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement
        (truncation k) hn k hk Q ⟨0,le_rfl,A.data.T_pos.le⟩ id)=A.high k+A.mean k :=
  initializedExactPhysicalVelocity_initial_split A.meanData A.data rfl A.historyTime A.history_pos
      A.history_lt
    A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation
        k) hn k hk Q

end Input
end EulerPacketInitial
