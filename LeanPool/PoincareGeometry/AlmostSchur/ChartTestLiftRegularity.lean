/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartTestLift

/-!
# Arbitrary-order regularity of lifted chart tests

The original energy argument only needed C¹ lifts.  Distributional elliptic
uniqueness and the classical Poisson identification need the same construction
at arbitrary finite or infinite order.  The support argument is unchanged.
-/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

/-- A compactly supported Cⁿ coordinate test whose support stays in the chart
target extends by zero to a genuine global Cⁿ manifold function. -/
theorem contMDiff_chartTestLift_of_order (n : ℕ∞) (c : M) (φ : E → ℝ)
    (hφ : ContDiff ℝ n φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) :
    ContMDiff I 𝓘(ℝ, ℝ) n (chartTestLift (I := I) c φ) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := tsupport_chartTestLift_subset_source c φ hc hs hx
  have hd : ContMDiffAt I 𝓘(ℝ, ℝ) n (φ ∘ extChartAt I c) x :=
    hφ.contMDiff.contMDiffAt.comp x
      (contMDiffAt_extChartAt' (I := I) (x := c) (by simpa using hxs))
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source c).mem_nhds hxs] with y hy
  exact chartTestLift_of_mem c φ hy

/-- The lifted coordinate test retains compact support. -/
theorem hasCompactSupport_chartTestLift (c : M) (φ : E → ℝ)
    (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) :
    HasCompactSupport (chartTestLift (I := I) c φ) := by
  have himage : IsCompact ((extChartAt I c).symm '' tsupport φ) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt_symm c).mono hs)
  exact himage.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartTestLift_subset c φ hc hs)

end AlmostSchur
