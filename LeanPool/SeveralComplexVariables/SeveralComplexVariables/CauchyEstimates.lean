/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.MetricSpace.Thickening
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Derivatives

/-!
# Cauchy estimates and local derivative bounds

These estimates reuse the one-variable Cauchy estimate on coordinate slices. The source has the
supremum norm, so a coordinate disc fits in the ball of the same radius. Derivatives are also
uniformly bounded on small closed thickenings of compact subsets of a one-variable holomorphic
domain.

## Main results

`norm_partialDeriv_le` is the Cauchy estimate for a coordinate derivative on a polydisc.
`norm_partialDeriv_le_of_slice` is the one-variable slice form.
`AnalyticOnNhd.exists_cthickening_deriv_bound` bounds derivatives uniformly on a closed
thickening of a compact subset of a one-variable domain.
-/

public section

open Complex Function Metric Set

/-- The derivative of a holomorphic function is uniformly bounded on a sufficiently small closed
thickening of any compact subset of its open domain. -/
theorem AnalyticOnNhd.exists_cthickening_deriv_bound
    {Ω K : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hΩopen : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.cthickening δ K, ‖deriv f w‖ ≤ C := by
  obtain ⟨δ₁, hδ₁, hδ₁compact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hδ₂Ω⟩ := hK.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hcompact : IsCompact (Metric.cthickening δ K) :=
    hδ₁compact.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono (min_le_left _ _) K)
  have hsub : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hδ₂Ω
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hf.deriv.continuousOn.mono hsub).norm
  exact ⟨δ, lt_min hδ₁ hδ₂, hsub, max C 0, le_max_right _ _,
    fun w hw => (hC (Set.mem_image_of_mem _ hw)).trans (le_max_left _ _)⟩

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Updating one coordinate within its closed disc stays in the corresponding sup-norm ball. -/
theorem update_mem_closedBall {z : ι → ℂ} {i : ι} {w : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hw : w ∈ closedBall (z i) r) : update z i w ∈ closedBall z r := by
  rw [mem_closedBall, dist_pi_le_iff hr]
  intro j
  by_cases hji : j = i
  · simpa [hji] using hw
  · simpa [Function.update_of_ne hji] using hr

omit [Fintype ι] in
/-- Cauchy's first derivative bound only needs holomorphy along the chosen coordinate disc. -/
theorem norm_partialDeriv_le_of_slice {f : (ι → ℂ) → F} {z : ι → ℂ}
    (i : ι) {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ (fun w => f (update z i w)) (closedBall (z i) r))
    (hM : ∀ w ∈ sphere (z i) r, ‖f (update z i w)‖ ≤ M) :
    ‖partialDeriv i f z‖ ≤ M / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hf.diffContOnCl_ball Subset.rfl) hM

/-- A bound on a closed sup-norm ball controls every coordinate derivative at its center. -/
theorem norm_partialDeriv_le {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {z : ι → ℂ} (i : ι) {r M : ℝ} (hr : 0 < r)
    (hball : closedBall z r ⊆ U) (hM : ∀ w ∈ closedBall z r, ‖f w‖ ≤ M) :
    ‖partialDeriv i f z‖ ≤ M / r := by
  apply norm_partialDeriv_le_of_slice i hr
  · intro w hw
    exact ((hf _ (hball (update_mem_closedBall hr.le hw))).differentiableAt.comp w
      (hasDerivAt_update z i w).differentiableAt).differentiableWithinAt
  · intro w hw
    exact hM _ (update_mem_closedBall hr.le (sphere_subset_closedBall hw))

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
