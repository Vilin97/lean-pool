/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GradientRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates

/-! # A regular metric-dual frame from coordinate gradients

The gradient of each scalar coordinate is dual to the corresponding tangent
coordinate frame. This supplies a regular reconstruction from metric pairings,
without assuming the vector field being reconstructed is already regular.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- An actual scalar coordinate, with the chart's totalization outside its source. -/
def chartScalarCoordinate {ι : Type*} (b : Module.Basis ι ℝ E) (c : M) (i : ι) : M → ℝ :=
  fun y ↦ b.coord i (extChartAt I c y)

/-- Every scalar coordinate is C² at points of its chart. -/
theorem contMDiffAt_chartScalarCoordinate {ι : Type*} (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 2 (chartScalarCoordinate (I := I) b c i) x :=
  (b.coord i).toContinuousLinearMap.contMDiff.contMDiffAt.comp x
    (contMDiffAt_extChartAt' hx)

/-- The metric-dual frame consists of gradients of actual scalar coordinates. -/
def metricDualFrame {ι : Type*} (b : Module.Basis ι ℝ E) (c : M) (i : ι) : Π y, TM y :=
  gradient (I := I) (chartScalarCoordinate (I := I) b c i)

/-- The constructed dual frame is genuinely C¹ locally, by gradient regularity. -/
theorem contMDiffAt_metricDualFrame {ι : Type*} (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% (metricDualFrame (I := I) b c i)) x := by
  letI : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  exact contMDiffAt_gradient (I := I) 1
    (contMDiffAt_chartScalarCoordinate (I := I) b c x hx i)

/-- The pairing with the tangent coordinate frame is exactly Kronecker delta. -/
theorem metricDualFrame_inner_localFrame {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source) (i j : ι) :
    inner ℝ (metricDualFrame (I := I) b c i x)
      ((trivializationAt E TM c).localFrame b j x) = if j = i then 1 else 0 := by
  let e := trivializationAt E TM c
  have hs := contMDiffAt_chartScalarCoordinate (I := I) b c x hx i
  rw [metricDualFrame, inner_gradient, localFrame_eq_symmL,
    ← fderiv_chart_comp (chartScalarCoordinate (I := I) b c i) c x hx
      (hs.mdifferentiableAt (by norm_num)) (b j)]
  have he : (chartScalarCoordinate (I := I) b c i ∘ (extChartAt I c).symm) =ᶠ[
      𝓝 (extChartAt I c x)] (b.coord i).toContinuousLinearMap := by
    filter_upwards [(isOpen_extChartAt_target (I := I) c).mem_nhds
      ((extChartAt I c).map_source (by simpa using hx))] with z hz
    simp only [Function.comp_apply, chartScalarCoordinate, (extChartAt I c).right_inv hz]
    rfl
  rw [he.fderiv_eq, (b.coord i).toContinuousLinearMap.fderiv]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

/-- Reconstruction from metric pairings against a coordinate frame, using its
actual metric-dual frame. This holds for every vector, with no regularity input. -/
theorem eq_sum_inner_localFrame_smul_metricDualFrame {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source) (v : TM x) :
    v = ∑ i, inner ℝ v ((trivializationAt E TM c).localFrame b i x) •
      metricDualFrame (I := I) b c i x := by
  classical
  let e := trivializationAt E TM c
  let B := e.basisAt b hx
  have hb (j : ι) : inner ℝ v (B j) = inner ℝ
      (∑ i, inner ℝ v (e.localFrame b i x) • metricDualFrame (I := I) b c i x) (B j) := by
    rw [← e.localFrame_apply_of_mem_baseSet b hx]
    dsimp [e]
    simp only [sum_inner, real_inner_smul_left, metricDualFrame_inner_localFrame b c x hx]
    simp
  have he : (innerSL ℝ v).toLinearMap =
      (innerSL ℝ (∑ i, inner ℝ v (e.localFrame b i x) • metricDualFrame (I := I) b c i x)).toLinearMap :=
    B.ext hb
  apply ext_inner_right ℝ
  intro w
  exact congrArg (fun L ↦ L w) he

/-- Smoothness of all metric pairings with a local frame implies smoothness
of the field, via the proved dual-frame reconstruction. -/
theorem contMDiffAt_section_of_inner_localFrame {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source)
    (W : Π y, TM y)
    (hW : ∀ i, ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% W) x := by
  have hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (T% (fun y ↦ ∑ i, inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y) •
        metricDualFrame (I := I) b c i y)) x :=
    ContMDiffAt.sum_section (fun i _ ↦ (hW i).smul_section (contMDiffAt_metricDualFrame b c x hx i))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' E y) (eq_sum_inner_localFrame_smul_metricDualFrame b c y hy (W y))

end AlmostSchur
