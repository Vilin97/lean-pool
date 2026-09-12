/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceInitial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSupport

/-! The actual chosen packet states preserve common compact initial
support. The forward mean contribution is localized even when its
boundary coefficient is nonzero. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPhysicalL2Scaling

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

include hTime in
theorem forwardInitializedInitialMean_support (N : ℕ) (k : ℝ) :
    tsupport (forwardInitializedInitialMean M D δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 := by
  apply EulerPacketInitial.mean_scaled_support k⁻¹ k D.m₀ M.ℓ M.ℓ_pos
  intro i _ θ
  exact source_mean_initial_support period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) i θ

include hTime in
theorem forwardInitializedInitial_common_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (forwardInitializedInitialHigh M D δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 ∧
      tsupport (forwardInitializedInitialMean M D δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 := by
  refine ⟨(forwardInitializedInitialHigh_support M D hTime δ hδ ξ hs α hS N k).trans ?_,
    forwardInitializedInitialMean_support M D hTime δ hδ ξ hs α N k⟩
  exact Metric.closedBall_subset_closedBall (by have h := M.ℓ_le_one; linarith only [h])

end EulerPacketTerminalDatum

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency

theorem support_of_difference (f g : Space → Space) (R : ℝ)
    (hf : tsupport f ⊆ Metric.closedBall 0 R)
    (hd : tsupport (g - f) ⊆ Metric.closedBall 0 R) :
    tsupport g ⊆ Metric.closedBall 0 R := by
  have he : g=f+(g-f) := by ext x; simp only [Pi.add_apply,Pi.sub_apply]; abel_nf
  conv_lhs => rw [he]
  exact (tsupport_add f (g - f)).trans (union_subset hf hd)

namespace GeometryForwardInput

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : GeometryForwardInput U)

theorem initial_support (k : ℝ) :
    tsupport (I.high k) ⊆ Metric.closedBall 0 2 ∧ tsupport (I.mean k) ⊆ Metric.closedBall 0 2 := by
  apply forwardInitializedInitial_common_support I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha ?_ (truncation k) k
  intro x hx
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    I.neighborhood_bound x (I.support_subset hx)

end GeometryForwardInput

namespace GeometryForwardChoice

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

theorem initial_support (hS : tsupport (fun x => S.evolution.velocity (0, x)) ⊆ Metric.closedBall 0
    2) :
    tsupport (fun x => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (0, x)) ⊆
      Metric.closedBall 0 2 := by
  rw [state_velocity_initial I S k hk nextEll hnext hnext1 F hSym]
  have h := I.initial_support k
  exact (tsupport_add _ _).trans
    (union_subset hS ((tsupport_add _ _).trans (union_subset h.1 h.2)))

theorem initial_compact (hS : tsupport (fun x => S.evolution.velocity (0, x)) ⊆ Metric.closedBall 0
    2) :
    HasCompactSupport (fun x => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity
        (0, x)) :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
    (initial_support I S k hk nextEll hnext hnext1 F hSym hS)

end GeometryForwardChoice

namespace GeometryJoinedChoice

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

theorem initial_support (hS : tsupport (fun x => S.evolution.velocity (0, x)) ⊆ Metric.closedBall 0
    2) :
    tsupport (fun x => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (0, x)) ⊆
      Metric.closedBall 0 2 := by
  rw [state_velocity_initial I S k hk nextEll hnext hnext1 F hSym]
  have h := I.initial_support k
  exact (tsupport_add _ _).trans
    (union_subset hS ((tsupport_add _ _).trans (union_subset h.1 h.2)))

end GeometryJoinedChoice
end EulerParentPacketFrames
