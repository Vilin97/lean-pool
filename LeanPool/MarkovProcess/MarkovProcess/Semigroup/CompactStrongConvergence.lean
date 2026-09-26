/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic


/-!
# Equibounded strong convergence is uniform on compact sets

A family of continuous linear operators whose operator norms share one common bound and which
converges to zero at every point converges to zero uniformly on every compact set.  The common
bound makes the family equi-Lipschitz, so a finite `δ`-net of the compact set reduces the uniform
assertion to finitely many pointwise ones.

Main results: `eventually_forall_mem_norm_apply_le_of_isCompact`.

Neither completeness of the spaces nor countable generation of the index filter is used, and
nothing is asserted about convergence in the operator norm, which is strictly stronger.
-/

@[expose] public section

open Filter Topology

namespace MarkovProcess.Semigroup

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Equibounded strong convergence to zero is uniform on compact sets.**  If the operators
`T i` share the bound `‖T i‖ ≤ C` and `T i x → 0` for every vector `x`, then for every compact
set `K` and every `ε > 0` the estimate `‖T i x‖ ≤ ε` holds for all `x ∈ K` simultaneously,
eventually along the index filter. -/
theorem eventually_forall_mem_norm_apply_le_of_isCompact {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] F) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ K, ‖T i x‖ ≤ ε := by
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  set δ : ℝ := ε / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨s, -, hsfin, hcover⟩ :=
    hK.elim_finite_subcover_image (c := fun y : E ↦ Metric.ball y δ)
      (fun _ _ ↦ Metric.isOpen_ball)
      (fun y hy ↦ Set.mem_iUnion₂.2 ⟨y, hy, Metric.mem_ball_self hδ⟩)
  have hfin : ∀ᶠ i in l, ∀ y ∈ s, ‖T i y‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finite hsfin]
    intro y _
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp (hT y) (ε / 2) (by positivity)]
      with i hi
    exact hi.le
  filter_upwards [hfin] with i hi x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hdist : ‖x - y‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.1 hxy).le
  have hsplit : T i x = T i y + T i (x - y) := by
    rw [← map_add]
    congr 1
    abel
  have hbound : ‖T i (x - y)‖ ≤ ε / 2 := by
    calc
      ‖T i (x - y)‖ ≤ ‖T i‖ * ‖x - y‖ := (T i).le_opNorm _
      _ ≤ (|C| + 1) * δ := by
        refine mul_le_mul ?_ hdist (norm_nonneg _) hCpos.le
        exact (hC i).trans (by linarith [le_abs_self C])
      _ = ε / 2 := by
        rw [hδdef]
        field_simp
  calc
    ‖T i x‖ = ‖T i y + T i (x - y)‖ := by rw [hsplit]
    _ ≤ ‖T i y‖ + ‖T i (x - y)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hi y hy) hbound
    _ = ε := add_halves ε

end MarkovProcess.Semigroup
