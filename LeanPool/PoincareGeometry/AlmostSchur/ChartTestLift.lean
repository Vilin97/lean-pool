/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyMean

/-! # Compactly supported coordinate tests lifted to the manifold

The lift is extension by zero through a fixed chart. Its regularity and support
are proved from the support of the coordinate test, without a global cutoff.
-/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

/-- Extension by zero of a scalar coordinate test through a fixed chart. -/
def chartTestLift (c : M) (φ : E → ℝ) : M → ℝ :=
  (extChartAt I c).source.indicator (φ ∘ extChartAt I c)

/-- On the chart source the lift is the coordinate test. -/
theorem chartTestLift_of_mem (c : M) (φ : E → ℝ) {x : M}
    (hx : x ∈ (extChartAt I c).source) :
    chartTestLift (I := I) c φ x = φ (extChartAt I c x) :=
  indicator_of_mem hx _

/-- On the chart target the pullback of the lift equals the original test. -/
theorem chartTestLift_comp_symm (c : M) (φ : E → ℝ) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    chartTestLift (I := I) c φ ((extChartAt I c).symm z) = φ z := by
  rw [chartTestLift_of_mem c φ ((extChartAt I c).map_target hz),
    (extChartAt I c).right_inv hz]

/-- The lifted support is contained in the compact inverse image of the test support. -/
theorem tsupport_chartTestLift_subset (c : M) (φ : E → ℝ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (extChartAt I c).target) :
    tsupport (chartTestLift (I := I) c φ) ⊆ (extChartAt I c).symm '' tsupport φ := by
  have hk : IsCompact ((extChartAt I c).symm '' tsupport φ) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm c).mono hs)
  apply closure_minimal _ hk.isClosed
  intro x hx
  have hxs : x ∈ (extChartAt I c).source := by
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  refine ⟨extChartAt I c x, subset_tsupport _ ?_, (extChartAt I c).left_inv hxs⟩
  change chartTestLift (I := I) c φ x ≠ 0 at hx
  change φ (extChartAt I c x) ≠ 0
  rwa [chartTestLift_of_mem c φ hxs] at hx

/-- In particular, the lifted support stays inside the chart source. -/
theorem tsupport_chartTestLift_subset_source (c : M) (φ : E → ℝ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (extChartAt I c).target) :
    tsupport (chartTestLift (I := I) c φ) ⊆ (extChartAt I c).source := by
  rintro x hx
  obtain ⟨z, hz, rfl⟩ := tsupport_chartTestLift_subset c φ hc hs hx
  exact (extChartAt I c).map_target (hs hz)

/-- Compactly supported C¹ coordinate tests give genuine global C¹ functions. -/
theorem contMDiff_chartTestLift (c : M) (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (chartTestLift (I := I) c φ) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := tsupport_chartTestLift_subset_source c φ hc hs hx
  have hd : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (φ ∘ extChartAt I c) x :=
    hφ.contMDiff.contMDiffAt.comp x
      (contMDiffAt_extChartAt' (I := I) (x := c) (by simpa using hxs))
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source c).mem_nhds hxs] with y hy
  exact chartTestLift_of_mem c φ hy

/-- Coordinate differentiation of the lifted test is exactly differentiation of the test. -/
theorem fderiv_chartTestLift_comp_symm (c : M) (φ : E → ℝ) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    fderiv ℝ (chartTestLift (I := I) c φ ∘ (extChartAt I c).symm) z = fderiv ℝ φ z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_extChartAt_target c).mem_nhds hz] with y hy
  exact chartTestLift_comp_symm c φ hy

end AlmostSchur
