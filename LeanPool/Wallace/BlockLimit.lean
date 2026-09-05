/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.BlockFilters
import LeanPool.Wallace.FusionSchedule
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Limits along block-density ultrafilters

A free ultrafilter cannot remain in finitely many finite blocks.  Consequently the block label
of an ultrafilter-generic position tends to infinity.  This turns the vanishing geometric error
on a retained member of the ultrafilter into convergence to zero in the circle.
-/

open Filter Set Topology

namespace Wallace

noncomputable section

open TriangularPreprocess

/-- Along a free ultrafilter, the label of the finite block containing `n` tends to infinity. -/
theorem tendsto_blockOf_atTop
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) {p : Ultrafilter ℕ}
    (hp : (p : Filter ℕ) ≤ cofinite) :
    Tendsto (blockOf N hN) p atTop := by
  rw [Filter.tendsto_atTop]
  intro L
  have hfinite : {n : ℕ | blockOf N hN n < L}.Finite := by
    have heq : {n : ℕ | blockOf N hN n < L} =
        ⋃ l ∈ Set.Iio L, {n : ℕ | blockOf N hN n = l} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro hn
        exact ⟨blockOf N hN n, hn, rfl⟩
      · rintro ⟨l, hl, hnl⟩
        simpa [hnl] using hl
    rw [heq]
    exact (Set.finite_Iio L).biUnion fun l _hl ↦ blockFiber_finite N hN l
  have hcompl : {n : ℕ | ¬ blockOf N hN n < L} ∈ (cofinite : Filter ℕ) := by
    simpa only [Set.compl_ofPred] using hfinite.compl_mem_cofinite
  have hlarge : {n : ℕ | L ≤ blockOf N hN n} ∈ (cofinite : Filter ℕ) := by
    simpa only [not_lt] using hcompl
  exact hp hlarge

/-- The scheduled error evaluated at the block label tends to zero along every free
ultrafilter. -/
theorem tendsto_stageError_blockOf
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) {p : Ultrafilter ℕ}
    (hp : (p : Filter ℕ) ≤ cofinite) :
    Tendsto (fun n ↦ FusionSchedule.stageError (blockOf N hN n)) p (nhds 0) :=
  FusionSchedule.tendsto_stageError.comp (tendsto_blockOf_atTop N hN hp)

/-- If a circle-valued sequence is bounded by twice the scheduled error on a member of a free
ultrafilter, then it converges to zero along that ultrafilter. -/
theorem tendsto_zero_of_norm_le_stageError_on_mem
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) {p : Ultrafilter ℕ}
    (hp : (p : Filter ℕ) ≤ cofinite)
    {f : ℕ → UnitAddCircle} {U : Set ℕ} (hU : U ∈ p)
    (hbound : ∀ n ∈ U,
      ‖f n‖ ≤ 2 * FusionSchedule.stageError (blockOf N hN n)) :
    Tendsto f p (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto
      (fun n ↦ 2 * FusionSchedule.stageError (blockOf N hN n)) p (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) p (nhds 2)).mul
        (tendsto_stageError_blockOf N hN hp))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) p (nhds 0)) hupper
  · exact Eventually.of_forall fun n ↦ norm_nonneg (f n)
  · filter_upwards [hU] with n hn
    exact hbound n hn

end

end Wallace
