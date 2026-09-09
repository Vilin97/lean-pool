/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryJoinedChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketChildLowGuards

@[expose] public section

/-! The same geometrically selected correction supplies the actual
child's whole-horizon physical bounds and its next localized source guard. -/

noncomputable section

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.earlyRatio)+
          k^(-(1/4 : ℝ)))*(I.parent.T^2/2)+
        (I.low.Be+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))))*I.parent.T+
        boundaryLocalizationC2*(I.low.Bc+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))))*
          I.low.r^3*I.parent.T ≤ 1/2) : LowBounds F.parent := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  let V := forwardInitializedNormalizedField I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.forwardChildLowBounds I.normal I.normal_unit I.coordinates I.support
    I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall

theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.earlyRatio)+
          k^(-(1/4 : ℝ)))*(I.parent.T^2/2)+
        (I.low.Be+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))))*I.parent.T+
        boundaryLocalizationC2*(I.low.Bc+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))))*
          I.low.r^3*I.parent.T ≤ 1/2) :
    (F.lowBounds CM CH hCM hCH
      hsmall).Be=I.low.Be+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
      hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
      hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.earlyRatio)+
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L=
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  have h := S.evolution.exactForwardPacket_whole_horizon_low_bounds I.normal I.normal_unit
    I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1

end EulerParentPacketFrames.GeometryForwardChoice

namespace EulerParentPacketFrames.GeometryJoinedChoice

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.badRatio)+
          k^(-(1/4 : ℝ)))*(I.parent.T^2/2)+
        (I.low.Be+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4 : ℝ))))*I.parent.T+
        boundaryLocalizationC2*(I.low.Bc+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4 : ℝ))))*
          I.low.r^3*I.parent.T ≤ 1/2) : LowBounds F.parent := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
    I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
      k) F.hn k hk.four
  let V := initializedNormalizedField I.meanData I.data rfl I.historyTime I.history_pos
    I.history_lt I.history
    I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.joinedChildLowBounds I.normal I.normal_unit I.coordinates I.support
    I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.cutoff_support I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall

theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.badRatio)+
          k^(-(1/4 : ℝ)))*(I.parent.T^2/2)+
        (I.low.Be+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4 : ℝ))))*I.parent.T+
        boundaryLocalizationC2*(I.low.Bc+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4 : ℝ))))*
          I.low.r^3*I.parent.T ≤ 1/2) :
    (F.lowBounds CM CH hCM hCH hsmall).Be=I.low.Be+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
      : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
      : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
      hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.badRatio)+
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L=
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤
      CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
    I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
      k) F.hn k hk.four
  have h := S.evolution.exactPacket_whole_horizon_low_bounds I.normal I.normal_unit I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
      I.cutoff_support
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1

end EulerParentPacketFrames.GeometryJoinedChoice
