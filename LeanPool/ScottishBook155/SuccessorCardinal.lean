/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.RecursionCardinal
import LeanPool.ScottishBook155.StageSystem

/-!
# Cardinal bounds for protected successors
-/

namespace ScottishBook155

theorem oneSum_mk_le_stageCardinal
    {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (hM : Cardinal.mk M ≤ stageCardinal) :
    Cardinal.mk (OneSum M) ≤ stageCardinal := by
  calc
    Cardinal.mk (OneSum M) = Cardinal.mk (M × ℝ) :=
      Cardinal.mk_congr (WithLp.linearEquiv 1 ℝ (M × ℝ)).toEquiv
    _ = Cardinal.mk M * Cardinal.mk ℝ := by
      rw [Cardinal.mk_prod]
      simp
    _ ≤ max (max (Cardinal.mk M) (Cardinal.mk ℝ)) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ stageCardinal := max_le
      (max_le hM real_mk_le_stageCardinal) aleph0_le_stageCardinal

theorem protectedSuccessor_source_mk_le
    {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (S : ProtectedStage.{0} r) (y : S.target) (hy : y ∉ Set.range S.map)
    (hM : Cardinal.mk S.source ≤ stageCardinal) :
    Cardinal.mk ((protectedSuccessor hr hL S y hy).next.source) ≤
      stageCardinal := by
  change Cardinal.mk (OneSum S.source) ≤ stageCardinal
  exact oneSum_mk_le_stageCardinal hM

theorem protectedSuccessor_target_mk_le
    {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (S : ProtectedStage.{0} r) (y : S.target) (hy : y ∉ Set.range S.map)
    (hM : Cardinal.mk S.source ≤ stageCardinal)
    (hN : Cardinal.mk S.target ≤ stageCardinal) :
    Cardinal.mk ((protectedSuccessor hr hL S y hy).next.target) ≤
      stageCardinal := by
  dsimp only [protectedSuccessor]
  apply CardinalControl.protectedEnvelope_mk_le
  · exact aleph0_le_stageCardinal
  · exact hN
  · apply CardinalControl.adjunctionSpace_mk_le
    · exact aleph0_le_stageCardinal
    · exact hM
    · exact hN
    · simpa using real_mk_le_stageCardinal
  · simpa using real_mk_le_stageCardinal
  · exact stageCardinal_power_aleph0

end ScottishBook155
