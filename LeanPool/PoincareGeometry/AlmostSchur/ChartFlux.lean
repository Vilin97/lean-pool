/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.OpenDomainIntegration

/-!
# Compactly supported vector fields in a chart

Coordinate fields are extended by zero outside the chart target. A compact
intrinsic support contained in the chart gives compact support strictly inside
that target, so the extension is C1 and introduces no boundary term.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The true coordinate field, extended by zero off the chart target. -/
def chartFlux (c : M) (X : Π x : M, TM x) : E → E :=
  (extChartAt I c).target.indicator (coordinateVectorField (I := I) c X)

/-- On the open chart target the zero extension agrees on a neighborhood
with the actual coordinate field. -/
theorem chartFlux_eventually_eq (c : M) (X : Π x : M, TM x) (z : E)
    (hz : z ∈ (extChartAt I c).target) :
    chartFlux (I := I) c X =ᶠ[𝓝 z] coordinateVectorField (I := I) c X := by
  filter_upwards [(isOpen_extChartAt_target c).mem_nhds hz] with y hy
  exact Set.indicator_of_mem hy _

/-- Zero extension leaves the connection divergence unchanged at interior
points of the chart. -/
theorem localConnectionDivergence_chartFlux
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c : M) (X : Π x : M, TM x) (z : E)
    (hz : z ∈ (extChartAt I c).target) :
    localConnectionDivergence (coordinateConnection cov b c) (chartFlux (I := I) c X) z =
      localConnectionDivergence (coordinateConnection cov b c)
        (coordinateVectorField (I := I) c X) z := by
  have he := chartFlux_eventually_eq c X z hz
  simp only [localConnectionDivergence, he.fderiv_eq, he.eq_of_nhds]

/-- The zero-extended flux still represents the actual connection trace
at every chart point. -/
theorem divergence_eq_chartFlux
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (c : M) (X : Π x : M, TM x) (z : E)
    (hz : z ∈ (extChartAt I c).target)
    (hX : MDiffAt (T% X) ((extChartAt I c).symm z)) :
    divergence cov X ((extChartAt I c).symm z) =
      localConnectionDivergence (coordinateConnection cov b c) (chartFlux (I := I) c X) z := by
  have hx : (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  rw [localConnectionDivergence_chartFlux cov b c X z hz]
  simpa only [(extChartAt I c).right_inv hz] using
    divergence_eq_localConnectionDivergence cov b X c ((extChartAt I c).symm z) hx hX

/-- Intrinsic compact support controls the support of the zero extension. -/
theorem tsupport_chartFlux_subset_image (c : M) (X : Π x : M, TM x)
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    tsupport (chartFlux (I := I) c X) ⊆
      extChartAt I c '' tsupport (fun x => ‖X x‖) := by
  have hK : IsCompact (extChartAt I c '' tsupport (fun x => ‖X x‖)) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt c).mono hs)
  apply closure_minimal _ hK.isClosed
  intro z hz
  have hzU : z ∈ (extChartAt I c).target := by
    by_contra hn
    exact hz (Set.indicator_of_notMem hn _)
  have hn : ‖X ((extChartAt I c).symm z)‖ ≠ 0 := by
    intro hn
    have hX := norm_eq_zero.mp hn
    apply hz
    simp only [chartFlux, Set.indicator_of_mem hzU, coordinateVectorField, hX, map_zero]
  exact ⟨(extChartAt I c).symm z, subset_closure hn, (extChartAt I c).right_inv hzU⟩

/-- A field compactly supported in a chart gives a compact coordinate flux. -/
theorem hasCompactSupport_chartFlux (c : M) (X : Π x : M, TM x)
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    HasCompactSupport (chartFlux (I := I) c X) :=
  (hc.image_of_continuousOn ((continuousOn_extChartAt c).mono hs)).of_isClosed_subset
    isClosed_closure (tsupport_chartFlux_subset_image c X hc hs)

/-- Its coordinate support remains inside the open chart domain. -/
theorem tsupport_chartFlux_subset_target (c : M) (X : Π x : M, TM x)
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    tsupport (chartFlux (I := I) c X) ⊆ (extChartAt I c).target := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := tsupport_chartFlux_subset_image c X hc hs hz
  exact (extChartAt I c).map_source (hs hx)

/-- Extension by zero of a C1 compact chart-supported field is globally C1. -/
theorem contDiff_chartFlux (c : M) (X : Π x : M, TM x)
    (hX : CMDiff[(chartAt H c).source] 1 (T% X))
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    ContDiff ℝ 1 (chartFlux (I := I) c X) := by
  apply contDiff_of_tsupport_subset (isOpen_extChartAt_target c) _
    (tsupport_chartFlux_subset_target c X hc hs)
  apply (contDiffOn_coordinateVectorField c X hX).congr
  intro z hz
  simp only [chartFlux, Set.indicator_of_mem hz]

end AlmostSchur
