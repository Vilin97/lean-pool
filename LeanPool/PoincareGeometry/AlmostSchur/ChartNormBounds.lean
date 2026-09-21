/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.SobolevReconstruction
public import LeanPool.PoincareGeometry.AlmostSchur.GlobalEnergy

/-! # Uniform chart constants

Compact subsets of a trivialization domain have a uniform inverse-frame norm bound.
The metric need only be continuous. The cutoff bound is independent of the function
that will subsequently be localized. No localization L² estimate is assumed here.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace AlmostSchur

section Bundle

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

omit [FiniteDimensional ℝ F] in
/-- Continuity of the metric norm of the inverse trivialization, on its domain. -/
theorem continuousOn_norm_symmL (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [e.IsLinear ℝ] :
    ContinuousOn (fun p : B × F => ‖e.symmL ℝ p.1 p.2‖) (e.baseSet ×ˢ univ) := by
  have hs : ContinuousOn
      (fun p : B × F => (TotalSpace.mk p.1 (e.symmL ℝ p.1 p.2) : TotalSpace F V))
      (e.baseSet ×ˢ univ) := by
    apply e.continuousOn_symm.congr
    intro p hp
    dsimp only
    rw [e.symmL_apply hp.1]
  have hi := hs.inner_bundle hs
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using hi.sqrt

/-- A genuine uniform operator-norm bound on any compact subset of the domain. -/
theorem exists_bound_symmL_on_isCompact
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B)) [e.IsLinear ℝ]
    {K : Set B} (hK : IsCompact K) (hKe : K ⊆ e.baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖e.symmL ℝ x‖ ≤ C := by
  have hc := hK.prod (isCompact_closedBall (0 : F) 1)
  have hn := (continuousOn_norm_symmL e).mono
    (show K ×ˢ Metric.closedBall (0 : F) 1 ⊆ e.baseSet ×ˢ univ from
      fun p hp => ⟨hKe hp.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_max_right _ _)
  intro u hu
  have h := hC (x, u) ⟨hx, by simp [Metric.mem_closedBall, dist_zero_right, hu]⟩
  have h' : ‖e.symmL ℝ x u‖ ≤ C := by simpa only [norm_norm] using h
  exact h'.trans (le_max_left _ _)

end Bundle

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- The inverse tangent chart is uniformly bounded on a compact subset of its source. -/
theorem exists_bound_tangentChart_symmL (c : M) {K : Set M}
    (hK : IsCompact K) (hKc : K ⊆ (chartAt H c).source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K,
      ‖(trivializationAt E (TangentSpace I) c).symmL ℝ x‖ ≤ B := by
  apply exists_bound_symmL_on_isCompact _ hK
  simpa only [TangentBundle.trivializationAt_baseSet] using hKc

end Tangent

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M]

open RellichKondrachov.Geometry.Manifold.Sobolev

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The fixed localized cutoff has globally bounded Euclidean derivative. -/
theorem exists_bound_fderiv_localize_one (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E,
      ‖fderiv ℝ (FiniteChartData.localize (d := d) (fun _ => (1 : ℝ)) i) y‖ ≤ D := by
  have hf := FiniteChartData.localize_mem_C1c (d := d)
    (f := fun _ => (1 : ℝ)) contMDiff_const i
  obtain ⟨D, hD⟩ := (hf.2.fderiv ℝ).exists_bound_of_continuous
    (hf.1.continuous_fderiv (by norm_num))
  exact ⟨max D 0, le_max_right _ _, fun y => (hD y).trans (le_max_left _ _)⟩

end Cutoff

end AlmostSchur
