/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentUniformForwardChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedState
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardUniformCosts

@[expose] public section

/-! The actual zero-history geometry constructs the forward packet and
its new smooth Euler state at the uniformly chosen frequency. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketCylinderField EulerPacketTerminalDatum
  EulerPacketSourceFrequency EulerPacketUniformSource EulerAllOrderDriftCorrection
  EulerGraphInvariantFlow EulerPacketPhysicalLowBounds

structure GeometryForwardInput (U : Type) [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [CompleteSpace U] where
  parent : Parent
  label : LabelData parent
  low : LowBounds parent
  normal : Space
  normal_unit : ‖normal‖=1
  coordinates : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane normal
  support : Set Space
  support_compact : IsCompact support
  total_le_one : parent.T ≤ 1
  frame : ParentFrame (parent.transverseData normal normal_unit coordinates support
    support_compact) 0
  geometry : ForwardGuards frame
  halfBall : (1/2 : ℝ) ≤ geometry.radius
  neighborhood : Set Space
  neighborhood_measurable : MeasurableSet neighborhood
  neighborhood_open : IsOpen neighborhood
  support_subset : support ⊆ neighborhood
  neighborhood_bound : ∀ x ∈ neighborhood, ‖x‖ ≤ (1/2 : ℝ)
  cutoff_support : tsupport innerCutoff ⊆ support
  delta_pos : 0 < geometry.δ
  delta_le_one : geometry.δ ≤ 1
  child_pos : 0 < geometry.hchild

namespace GeometryForwardInput

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : GeometryForwardInput U)

abbrev data : Data U := I.parent.transverseData I.normal I.normal_unit I.coordinates I.support
  I.support_compact
abbrev meanData : EulerMeanPacketProvider.Data := I.parent.meanData I.low
abbrev agreement : SourceCoefficientAgreement I.meanData I.data :=
  I.parent.sourceAgreement I.normal I.normal_unit I.coordinates I.support I.support_compact I.low

def parameterSize : ℝ := I.label.geometryForwardParameterSize I.low I.normal I.normal_unit
  I.coordinates
  I.support I.support_compact I.frame I.geometry I.parent.T⁻¹ I.geometry.initialCoordinate

def alpha : ℝ := I.geometry.primaryAmplitude I.halfBall

theorem alpha_pos : 0 < I.alpha := I.geometry.primaryAmplitude_pos I.halfBall I.delta_pos
  I.child_pos

def frequencyGuard (k : ℝ) : Prop := frequencyConstant*I.parameterSize^frequencyPower ≤ smallPower k

abbrev correctionBudget (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) :=
  Budget period I.data.T_pos
    (forwardInitializedCorrectionData I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) hn k hk)

end GeometryForwardInput

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section ConstructorInjectivity

attribute [local irreducible] Parent.child

structure GeometryForwardChoice where
  hn : 1 ≤ truncation k
  Q : I.correctionBudget k hk.four hn
  flow : EulerPhysicalGraphFlowBounds.Data period I.parent.T
  graph : ∀ t q, graphConstraint k I.normal (flow.A.field t q)=0
  coefficient : flow.A=Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k)
  labels : LabelData (I.parent.child flow k I.normal graph nextEll hnext hnext1)
  label_constant : labels.K=k^80
  displacement_bound : ∀ (t : Icc (0 : ℝ) I.parent.T) (x : Space),
    ‖(flow.displacementField k I.normal I.parent.ell I.parent.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))
  errors : S.evolution.ForwardSourceErrors I.normal I.normal_unit I.coordinates I.support
    I.support_compact Q
    (forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) hn k hk.four)
    k I.geometry I.halfBall (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ)))

end ConstructorInjectivity

theorem exists_geometryForwardChoice
    (hfrequency : I.frequencyGuard k) (hK : I.label.K ≤ k)
    (hell : I.parent.ell⁻¹ ≤ k^(3/4 : ℝ)) :
    Nonempty (GeometryForwardChoice I S k hk nextEll hnext hnext1) := by
  let J := I.label.geometryForwardInputs I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.frame I.geometry I.halfBall
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
      I.neighborhood_bound
    I.parent.T⁻¹ I.total_le_one le_rfl
  have hp := I.label.geometryForward_uniform_primitives I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.frame I.geometry I.halfBall
    I.parent.T⁻¹ I.total_le_one le_rfl
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
      I.neighborhood_bound
    I.geometry.initialCoordinate I.delta_pos I.delta_le_one
  obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := I.label.forward_uniform_child
    S.evolution.inverse I.low
    I.normal I.normal_unit I.coordinates I.support I.support_compact J
    I.geometry.δ I.delta_pos I.delta_le_one I.geometry.initialCoordinate I.cutoff_support I.alpha
      I.alpha_pos
    (profileEnvelope I.parameterSize) hp.1 hp.2.1 k hk (hp.2.2.trans hfrequency)
    hK hell nextEll hnext hnext1
  refine ⟨⟨hn,Q,G,hgraph,hG,LC,hLC,hdisplacement,?_⟩⟩
  intro t x
  constructor
  · exact (herror t x).1
  · erw [forwardPressureTerm_eq_coefficient]
    exact (herror t x).2

namespace GeometryForwardChoice

variable (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

def parent : Parent := I.parent.child F.flow k I.normal F.graph nextEll hnext hnext1

def state (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) : SmoothState F.parent :=
  S.forwardChild I.low I.normal I.normal_unit I.coordinates I.support I.support_compact hSym
    I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha
    (truncation k) F.hn k hk.four F.Q F.flow F.coefficient F.graph nextEll hnext hnext1 F.labels

theorem state_label_constant (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) :
    (state I S k hk nextEll hnext hnext1 F hSym).labels.K=k^80 := F.label_constant

end GeometryForwardChoice
end EulerParentPacketFrames
