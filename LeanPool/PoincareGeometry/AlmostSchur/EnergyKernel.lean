/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GlobalEnergy
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Rigidity of functions with zero differential -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
/-- Vanishing intrinsic differential implies local constancy, by the
mean-value theorem on a ball inside each coordinate chart. -/
theorem isLocallyConstant_of_differential_eq_zero (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (hdf : ∀ x, mvfderiv I f x = 0) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  let φ := extChartAt I x
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hz : φ x ∈ φ.target := φ.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := I) x) (φ x) hz
  have hcoord : ContDiffOn ℝ 1 (f ∘ φ.symm) φ.target := by
    apply ContMDiffOn.contDiffOn
    exact hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)
  have hd : DifferentiableOn ℝ (f ∘ φ.symm) (Metric.ball (φ x) r) :=
    (hcoord.differentiableOn (by norm_num)).mono hball
  have hd0 : EqOn (fderiv ℝ (f ∘ φ.symm)) 0 (Metric.ball (φ x) r) := by
    intro z hzb
    have hzt := hball hzb
    have hy : φ.symm z ∈ (chartAt H x).source := by
      simpa [φ] using φ.map_target hzt
    ext u
    have he := fderiv_chart_comp f x (φ.symm z) hy
      ((hf _).mdifferentiableAt (by norm_num)) u
    change fderiv ℝ (f ∘ φ.symm) (φ (φ.symm z)) u = _ at he
    simpa only [φ.right_inv hzt, hdf, Pi.zero_apply, zero_apply] using he
  have hnear : ∀ᶠ y in 𝓝 x, φ y ∈ Metric.ball (φ x) r :=
    (continuousAt_extChartAt (I := I) x) (Metric.ball_mem_nhds _ hr)
  filter_upwards [hnear, (isOpen_extChartAt_source (I := I) x).mem_nhds hx] with y hy hys
  have he := Metric.isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball (φ x) r).isPreconnected hd hd0 hy (Metric.mem_ball_self hr)
  simpa only [Function.comp_apply, φ.left_inv hys, φ.left_inv hx] using he

/-- On a connected manifold, a C1 function with zero differential is constant. -/
theorem eq_of_differential_eq_zero [PreconnectedSpace M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (hdf : ∀ x, mvfderiv I f x = 0)
    (x y : M) : f x = f y :=
  (isLocallyConstant_of_differential_eq_zero f hf hdf).apply_eq_of_preconnectedSpace x y

end AlmostSchur
