/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentUniformJoinedChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedState
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialExactLimit

@[expose] public section

/-! Actual activation geometry and one uniform frequency comparison
construct the joined packet, its physical state, and both source errors. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketTerminalDatum EulerPacketSourceFrequency EulerPacketUniformSource
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketPhysicalLowBounds

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section ConstructorInjectivity

attribute [local irreducible] Parent.child

structure GeometryJoinedChoice where
  hn : 1 ≤ truncation k
  Q : I.correctionBudget k hk.four hn
  flow : EulerPhysicalGraphFlowBounds.Data period I.parent.T
  graph : ∀ t q, graphConstraint k I.normal (flow.A.field t q)=0
  coefficient : flow.A=Q.liftedPacketCoefficient period
    (initializedNormalizedField I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history
      I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) k)
  labels : LabelData (I.parent.child flow k I.normal graph nextEll hnext hnext1)
  label_constant : labels.K=k^80
  displacement_bound : ∀ (t : Icc (0 : ℝ) I.parent.T) (x : Space),
    ‖(flow.displacementField k I.normal I.parent.ell I.parent.ell_pos t).field x‖ ≤ k^(-(1/4 : ℝ))
  errors : S.evolution.SourceErrors I.normal I.normal_unit I.coordinates I.support
    I.support_compact Q
    (initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) hn k hk.four)
    k I.geometry I.halfBall I.cutoff_support (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ)))

end ConstructorInjectivity

theorem exists_geometryJoinedChoice
    (hterminal : I.terminal=I.geometry.terminal)
    (hfrequency : I.frequencyGuard k) (hK : I.label.K ≤ k)
    (hell : I.parent.ell⁻¹ ≤ k^(3/4 : ℝ)) :
    Nonempty (GeometryJoinedChoice I S k hk nextEll hnext hnext1) := by
  let J := I.label.geometryInputs I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.historyTime I.history_pos I.history_lt I.frame I.geometry
      I.halfBall
    I.historyTime⁻¹ I.parent.T⁻¹ (I.history_lt.le.trans I.total_le_one) le_rfl I.total_le_one le_rfl
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
      I.neighborhood_bound
  have hp := I.label.geometry_uniform_primitives I.low I.normal I.normal_unit I.coordinates
    I.support I.support_compact I.historyTime I.history_pos I.history_lt I.frame I.geometry
      I.halfBall
    I.historyTime⁻¹ I.parent.T⁻¹ (I.history_lt.le.trans I.total_le_one) le_rfl I.total_le_one le_rfl
    I.neighborhood I.neighborhood_measurable I.neighborhood_open I.support_subset
      I.neighborhood_bound
    I.terminal I.delta_pos I.delta_le_one
  obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := I.label.joined_uniform_child
    S.evolution.inverse I.low
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    I.historyTime I.history_pos I.history_lt J I.geometry.δ I.delta_pos I.delta_le_one
    I.terminal I.cutoff_support I.alpha I.alpha_pos (profileEnvelope I.parameterSize) hp.1 hp.2.1
    k hk (hp.2.2.trans hfrequency) hK hell nextEll hnext hnext1
  refine ⟨⟨hn,Q,G,hgraph,hG,LC,hLC,hdisplacement,?_⟩⟩
  intro t x
  constructor
  · simp only [← hterminal]
    exact (herror t x).1
  · erw [pressureTerm_eq_coefficient]
    simp only [← hterminal]
    exact (herror t x).2

namespace GeometryJoinedChoice

variable (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

def parent : Parent := I.parent.child F.flow k I.normal F.graph nextEll hnext hnext1

def state (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) : SmoothState F.parent :=
  S.joinedChild I.low I.normal I.normal_unit I.coordinates I.support I.support_compact hSym
    I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) F.hn k hk.four
    I.historyTime I.history_pos I.history_lt F.Q F.flow F.coefficient F.graph nextEll hnext hnext1
      F.labels

theorem state_label_constant (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) :
    (state I S k hk nextEll hnext hnext1 F hSym).labels.K=k^80 := F.label_constant

theorem initial_trace : I.exactInitial k hk.four F.hn F.Q=I.high k+I.mean k :=
  I.exactInitial_eq k hk.four F.hn F.Q

end GeometryJoinedChoice
end EulerParentPacketFrames
