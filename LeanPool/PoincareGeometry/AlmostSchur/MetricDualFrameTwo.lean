/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricDualFrame

/-! # C² regularity and reconstruction for the actual metric-dual frame -/

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
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Scalar coordinates have the C³ regularity needed to differentiate the dual frame twice. -/
theorem contMDiffAt_chartScalarCoordinate_three {ι : Type*} (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 3 (chartScalarCoordinate (I := I) b c i) x :=
  (b.coord i).toContinuousLinearMap.contMDiff.contMDiffAt.comp x
    (contMDiffAt_extChartAt' hx)

/-- A C² metric gives a C² actual metric-dual coordinate frame. -/
theorem contMDiffAt_metricDualFrame_two {ι : Type*} (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (metricDualFrame (I := I) b c i)) x := by
  letI : IsContMDiffRiemannianBundle I (↑(2 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  exact contMDiffAt_gradient (I := I) 2
    (contMDiffAt_chartScalarCoordinate_three (I := I) b c x hx i)

/-- C² metric pairings imply C² regularity of a tangent field; no prior
regularity assumption on that field is used. -/
theorem contMDiffAt_section_of_inner_localFrame_two {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source)
    (W : Π y, TM y)
    (hW : ∀ i, ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y ↦ inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% W) x := by
  have hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
      (T% (fun y ↦ ∑ i, inner ℝ (W y) ((trivializationAt E TM c).localFrame b i y) •
        metricDualFrame (I := I) b c i y)) x :=
    ContMDiffAt.sum_section (fun i _ ↦ (hW i).smul_section (contMDiffAt_metricDualFrame_two b c x hx i))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' E y) (eq_sum_inner_localFrame_smul_metricDualFrame b c y hy (W y))

end AlmostSchur
