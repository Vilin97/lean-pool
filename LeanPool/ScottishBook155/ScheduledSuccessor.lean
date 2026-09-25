/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.BentSeedStage
public import LeanPool.ScottishBook155.SuccessorCardinal


/-!
# The active-or-idle scheduled successor

At a scheduled transition the named target point is either already hit, in
which case the transition is idle, or it is added by the protected one-point
extension.
-/

@[expose] public section

namespace ScottishBook155

private theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num
private theorem one_pos : (0 : ℝ) < 1 := by norm_num

/-- The canonical successor transition which ensures that `y` is hit. -/
noncomputable def scheduledSuccessor
    (S : ProtectedStage.{0} ((1 : ℝ) / 2)) (y : S.target) :
    ProtectedTransition S 1 := by
  classical
  exact if hy : y ∈ Set.range S.map then idleTransition S
    else (protectedSuccessor (by exact half_pos) (by exact one_pos) S y hy).toTransition

theorem scheduledSuccessor_hits
    (S : ProtectedStage.{0} ((1 : ℝ) / 2)) (y : S.target) :
    ∃ x : (scheduledSuccessor S y).next.source,
      (scheduledSuccessor S y).next.map x =
        (scheduledSuccessor S y).targetEmbedding y := by
  by_cases hy : y ∈ Set.range S.map
  · rw [scheduledSuccessor, dite_eq_left hy]
    change ∃ x, S.map x = y
    exact hy
  · rw [scheduledSuccessor, dite_eq_right hy]
    let P := protectedSuccessor (by exact half_pos) (by exact one_pos) S y hy
    change ∃ x : P.next.source,
      P.next.map x = P.targetEmbedding y
    refine ⟨P.sourceEquiv (WithLp.toLp 1 ((0 : S.source), P.height)), ?_⟩
    exact P.hits

theorem scheduledSuccessor_source_mk_le
    (S : ProtectedStage.{0} ((1 : ℝ) / 2)) (y : S.target)
    (hM : Cardinal.mk S.source ≤ stageCardinal) :
    Cardinal.mk (scheduledSuccessor S y).next.source ≤ stageCardinal := by
  by_cases hy : y ∈ Set.range S.map
  · rw [scheduledSuccessor, dite_eq_left hy]
    simpa [idleTransition] using hM
  · rw [scheduledSuccessor, dite_eq_right hy]
    change Cardinal.mk
      ((protectedSuccessor (by exact half_pos) (by exact one_pos)
        S y hy).next.source) ≤ stageCardinal
    exact protectedSuccessor_source_mk_le half_pos one_pos S y hy hM

theorem scheduledSuccessor_target_mk_le
    (S : ProtectedStage.{0} ((1 : ℝ) / 2)) (y : S.target)
    (hM : Cardinal.mk S.source ≤ stageCardinal)
    (hN : Cardinal.mk S.target ≤ stageCardinal) :
    Cardinal.mk (scheduledSuccessor S y).next.target ≤ stageCardinal := by
  by_cases hy : y ∈ Set.range S.map
  · rw [scheduledSuccessor, dite_eq_left hy]
    simpa [idleTransition] using hN
  · rw [scheduledSuccessor, dite_eq_right hy]
    change Cardinal.mk
      ((protectedSuccessor (by exact half_pos) (by exact one_pos)
        S y hy).next.target) ≤ stageCardinal
    exact protectedSuccessor_target_mk_le half_pos one_pos S y hy hM hN

theorem bentSeedStage_source_mk_le :
    Cardinal.mk bentSeedStage.source ≤ stageCardinal := by
  change Cardinal.mk ℝ ≤ stageCardinal
  exact real_mk_le_stageCardinal

theorem bentSeedStage_target_mk_le :
    Cardinal.mk bentSeedStage.target ≤ stageCardinal := by
  change Cardinal.mk (OneSum ℝ) ≤ stageCardinal
  exact oneSum_mk_le_stageCardinal real_mk_le_stageCardinal

end ScottishBook155
