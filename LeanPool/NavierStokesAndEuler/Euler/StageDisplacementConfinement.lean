/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInfiniteConstruction

@[expose] public section

/-!
# Uniform confinement of the constructed particle maps

Each selected successor retains the proved quarter-power displacement bound
for its change of particle labels. Composition adds displacements without a
factor involving the parent derivative. The scale construction already bounds
the sum of these quarter-power costs. Thus all stages carry every fixed ball
of initial labels into one fixed ball of physical positions.

This is a statement about the actual selected packet family, not an assumed
bound on its velocity or velocity gradients. Vorticity confinement additionally
requires its transport identity along these particle maps.
-/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

theorem child_displacement_norm_le {M δ : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) A.T) (x : Space), ‖A.displacement.field t x‖ ≤ M)
    (hsmall : ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
      ‖(G.displacementField k m A.ell A.ell_pos t).field x‖ ≤ δ)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    ‖(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x‖ ≤ M + δ := by
  change ‖(EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)).field t x‖ ≤ M + δ
  simp only [EulerChildParticleTime.displacement_apply,
    G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos]
  exact (norm_add_le _ _).trans (add_le_add (hparent t _) (hsmall t x))

end EulerParentPacketFrames.Parent

namespace EulerPacketInduction.Stage

open Set Finset EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketSourceScaleSequence EulerPacketLowConstants EulerParentNeighborThreshold
  EulerTimeIntervalRestriction

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

theorem forwardNext_displacement_norm_le (P : Stage S 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.forwardNext hq hB).parent.T) (x : Space) :
    ‖(P.forwardNext hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X 0)^(-(1/4 : ℝ)) := by
  let F := P.chooseForward hq hB
  exact P.restrictedParent.child_displacement_norm_le F.flow (frequency S.J S.X 0)
    (P.forwardInput hq hB).normal F.graph (supportScale S.J S.X 1)
    (S.support_pos 1) (S.support_one 1)
    (fun s y => hparent (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le s) y)
    F.displacement_bound t x

theorem joinedNext_displacement_norm_le {n : ℕ} (P : Stage S n) (hn : n ≠ 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.joinedNext hn hq hB).parent.T) (x : Space) :
    ‖(P.joinedNext hn hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X n)^(-(1/4 : ℝ)) := by
  let F := P.chooseJoined hn hq hB
  exact P.restrictedParent.child_displacement_norm_le F.flow (frequency S.J S.X n)
    (P.joinedInput hn hq hB).normal F.graph (supportScale S.J S.X (n+1))
    (S.support_pos (n+1)) (S.support_one (n+1))
    (fun s y => hparent (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le s) y)
    F.displacement_bound t x

theorem successor_displacement_norm_le {n : ℕ} (P : Stage S n)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.successor hq hB).parent.T) (x : Space) :
    ‖(P.successor hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X n)^(-(1/4 : ℝ)) := by
  cases n with
  | zero => exact P.forwardNext_displacement_norm_le hq hB hparent t x
  | succ n => exact P.joinedNext_displacement_norm_le (Nat.succ_ne_zero n) hq hB hparent t x

end EulerPacketInduction.Stage

namespace EulerPacketInduction

open Set Finset EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketSourceScaleSequence EulerPacketLowConstants EulerParentNeighborThreshold

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem stages_displacement_norm_le_partial_sum (n : ℕ) :
    ∀ (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) (x : Space),
      ‖(stages S hq hB n).parent.displacement.field t x‖ ≤
        ‖(stages S hq hB 0).parent.displacement.field‖ +
          ∑ i ∈ range n, (frequency S.J S.X i)^(-(1/4 : ℝ)) := by
  induction n with
  | zero =>
    intro t x
    simpa only [range_zero,sum_empty,add_zero] using
      (BoundedContinuousFunction.norm_coe_le_norm
        ((stages S hq hB 0).parent.displacement.field t) x).trans
          (ContinuousMap.norm_coe_le_norm (stages S hq hB 0).parent.displacement.field t)
  | succ n ih =>
    intro t x
    rw [sum_range_succ, ← add_assoc]
    exact (stages S hq hB n).successor_displacement_norm_le hq hB ih t x

def particleDisplacementCap : ℝ := ‖(stages S hq hB 0).parent.displacement.field‖ + S.δ

theorem stages_displacement_norm_le (n : ℕ)
    (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) (x : Space) :
    ‖(stages S hq hB n).parent.displacement.field t x‖ ≤ particleDisplacementCap S hq hB := by
  exact (stages_displacement_norm_le_partial_sum S hq hB n t x).trans
    (add_le_add le_rfl (EulerPacketPressureScale.finite_sum_le S.correction_series n))

theorem stages_position_mapsTo_closedBall (R : ℝ) (n : ℕ)
    (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) :
    MapsTo ((stages S hq hB n).parent.position t) (Metric.closedBall 0 R)
      (Metric.closedBall 0 (R + particleDisplacementCap S hq hB)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (norm_add_le _ _).trans
    (add_le_add hx (stages_displacement_norm_le S hq hB n t x))

theorem packets_position_mapsTo_closedBall (R : ℝ) (n : ℕ)
    (t : Icc (0 : ℝ) (packets n).parent.T) :
    MapsTo ((packets n).parent.position t) (Metric.closedBall 0 R)
      (Metric.closedBall 0 (R + particleDisplacementCap constructionScales le_rfl le_rfl)) :=
  stages_position_mapsTo_closedBall constructionScales le_rfl le_rfl R n t

end EulerPacketInduction
