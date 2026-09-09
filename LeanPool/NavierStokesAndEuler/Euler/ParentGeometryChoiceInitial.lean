/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceCenter
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardInitialSupport

@[expose] public section

/-! The initial traces of the actual chosen Euler states are the same
compact high and mean increments used in the initial-data convergence
proof. Restriction to a shorter horizon preserves these equalities. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerAllOrderDriftCorrection EulerPacketPhysicalLowBounds EulerPhysicalL2Scaling

namespace SmoothState

theorem velocityIncrement_restrictTime {A B : Parent} (S : SmoothState A) (T : SmoothState B)
    (s : ℝ) (hs : 0 < s) (hA : s ≤ A.T) (hB : s ≤ B.T) :
    (S.restrictTime s hs hA).velocityIncrement (T.restrictTime s hs hB) =
      S.velocityIncrement T := rfl

end SmoothState

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace GeometryJoinedChoice

variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support
      I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos
    I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]

variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem initial_increment : S.velocityIncrement T 0 = I.exactInitial k hk.four F.hn F.Q := by
  funext x
  have he : (T).evolution.velocity (0,x) =
      addVelocity I.parent.ell (fun y => S.evolution.velocity (0,y))
        (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse I.parent.zeroTime) x :=
    I.parent.exactPacketVelocity_eq_addVelocity I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity
        I.parent.zeroTime x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=_
  rw [he]
  simp only [addVelocity,add_sub_cancel_left,
    normalized_initial I S k hk nextEll hnext hnext1 F,EulerPacketInitial.Input.exactInitial,scale]
  rfl

theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k :=
  (initial_increment I S k hk nextEll hnext hnext1 F hSym).trans
    (I.exactInitial_eq k hk.four F.hn F.Q)

theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) := by
  funext x
  have he := congrFun (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym) x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=(I.high k+I.mean k) x at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem restricted_initial_increment (s : ℝ) (hs : 0 < s) (hT : s ≤ I.parent.T) :
    (S.restrictTime s hs hT).velocityIncrement ((T).restrictTime s hs hT) 0 =
      I.high k+I.mean k := initial_increment_eq I S k hk nextEll hnext hnext1 F hSym

end GeometryJoinedChoice

namespace GeometryForwardInput

variable (I : GeometryForwardInput U)

def high (k : ℝ) : Space → Space := forwardInitializedInitialHigh I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k

def mean (k : ℝ) : Space → Space := forwardInitializedInitialMean I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k

def exactInitial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk hn) :
    Space → Space := scale I.parent.ell
  (forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
    (truncation k) hn k hk Q I.parent.zeroTime id)

theorem exactInitial_eq (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk
  hn) :
    I.exactInitial k hk hn Q=I.high k+I.mean k :=
  forwardInitializedExactPhysicalVelocity_initial_split I.meanData I.data rfl I.geometry.δ
    I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) hn k hk Q

end GeometryForwardInput

namespace GeometryForwardChoice

variable (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support
      I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]

variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem initial_increment : S.velocityIncrement T 0 = I.exactInitial k hk.four F.hn F.Q := by
  funext x
  have he : (T).evolution.velocity (0,x) =
      addVelocity I.parent.ell (fun y => S.evolution.velocity (0,y))
        (I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates
          I.support I.support_compact F.Q res k S.evolution.inverse I.parent.zeroTime) x :=
    I.parent.exactPacketVelocity_eq_addVelocity I.normal I.normal_unit I.coordinates
      I.support I.support_compact F.Q res k S.evolution.inverse S.evolution.velocity
        I.parent.zeroTime x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=_
  rw [he]
  simp only [addVelocity,add_sub_cancel_left,
    normalized_initial I S k hk nextEll hnext hnext1 F,GeometryForwardInput.exactInitial,scale]

theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k :=
  (initial_increment I S k hk nextEll hnext hnext1 F hSym).trans
    (I.exactInitial_eq k hk.four F.hn F.Q)

theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) := by
  funext x
  have he := congrFun (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym) x
  change (T).evolution.velocity (0,x)-S.evolution.velocity (0,x)=(I.high k+I.mean k) x at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem restricted_initial_increment (s : ℝ) (hs : 0 < s) (hT : s ≤ I.parent.T) :
    (S.restrictTime s hs hT).velocityIncrement ((T).restrictTime s hs hT) 0 =
      I.high k+I.mean k := initial_increment_eq I S k hk nextEll hnext hnext1 F hSym

end GeometryForwardChoice
end EulerParentPacketFrames
