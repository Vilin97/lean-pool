/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace.BoundaryNull
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace.MembershipStability

/-!
# Continuity of the area functional on `NRR.ConvexSubbody`

The real-valued area functional `ConvexSubbody.area` is continuous for the Hausdorff-metric
topology on the fixed-parent hyperspace `ConvexSubbody K`. The argument proceeds through
almost-everywhere convergence of the `0/1` carrier indicators and the dominated-convergence
theorem, with the constant parent indicator as an integrable dominating function.

* `ConvexSubbody.tendsto_indicator_ae` — off the (null) frontier of the limit body, the carrier
  indicators converge pointwise; this holds almost everywhere.
* `ConvexSubbody.tendsto_area` — filter-level convergence of the areas along any convergent family
  of subbodies.
* `ConvexSubbody.continuous_area` — the area functional is continuous.
-/

@[expose] public section

open MeasureTheory
open Filter Topology

open NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- The carrier of a subbody is measurable (it is compact, hence closed). -/
theorem measurableSet_body (C : ConvexSubbody K) :
    MeasurableSet (C.body : Set Plane) :=
  C.isCompact.isClosed.measurableSet

/-- **Area as an indicator integral.** The area of a subbody equals the Lebesgue integral of the
`0/1` indicator of its carrier. -/
theorem area_eq_integral_indicator (C : ConvexSubbody K) :
    C.area = ∫ x, (C.body : Set Plane).indicator (fun _ => (1 : ℝ)) x ∂volume := by
  rw [integral_indicator_const (1 : ℝ) C.measurableSet_body]
  simp [ConvexSubbody.area, measureReal_def]

/-
**Almost-everywhere indicator convergence.** For a Hausdorff-convergent family of subbodies,
the `0/1` carrier indicators converge pointwise almost everywhere to the indicator of the limit
body.
-/
theorem tendsto_indicator_ae
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀)) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun a =>
          ((C a).body : Set Plane).indicator (fun _ => (1 : ℝ)) x)
        l
        (𝓝
          ((C₀.body : Set Plane).indicator (fun _ => (1 : ℝ)) x)) := by
  have h_ae : ∀ᵐ x ∂volume, x ∉ frontier (C₀.body : Set Plane) :=
    MeasureTheory.compl_mem_ae_iff.mpr C₀.frontier_null
  filter_upwards [h_ae] with x hx
  have h_event : ∀ᶠ a in l, x ∈ (C a).body ↔ x ∈ C₀.body :=
    ConvexSubbody.eventually_mem_iff_of_not_mem_frontier hC hx
  apply tendsto_const_nhds.congr'
  filter_upwards [h_event] with a ha
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  exact if_congr ha.symm rfl rfl

/-- The constant parent indicator dominates every subbody indicator pointwise. -/
theorem norm_indicator_le_parent (C : ConvexSubbody K) (x : Plane) :
    ‖(C.body : Set Plane).indicator (fun _ => (1 : ℝ)) x‖
      ≤ (K : Set Plane).indicator (fun _ => (1 : ℝ)) x := by
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
  exact Set.indicator_le_indicator_of_subset C.subset_parent (fun _ => zero_le_one) x

/-- The parent indicator is integrable (the parent has finite volume). -/
theorem integrable_parent_indicator (K : Geometry.ConvexBody Plane) :
    Integrable (fun x => (K : Set Plane).indicator (fun _ => (1 : ℝ)) x) volume := by
  rw [ MeasureTheory.integrable_indicator_iff ];
  · simp? +zetaDelta at *;
    exact K.isCompact.measure_lt_top;
  · exact K.isCompact.measurableSet

/-- **Continuity at a point** of the area functional, via dominated convergence with the parent
indicator as dominating function. -/
theorem continuousAt_area (C₀ : ConvexSubbody K) :
    ContinuousAt (fun C : ConvexSubbody K => C.area) C₀ := by
  have h_dominated : Filter.Tendsto (fun C => ∫ x, (C.body : Set Plane).indicator (fun _ => (1 :
    ℝ)) x ∂volume) (nhds C₀) (nhds (∫ x, (C₀.body : Set Plane).indicator (fun _ => (1 : ℝ)) x
    ∂volume)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence ?_ ?_ ?_ ?_ ?_;
    · exact fun x => (K : Set Plane).indicator (fun _ => 1) x
    · exact Filter.Eventually.of_forall fun n => Measurable.aestronglyMeasurable ( by
        exact Measurable.indicator measurable_const ( by
          exact n.measurableSet_body ) );
    · exact Filter.Eventually.of_forall fun C => Filter.Eventually.of_forall fun x =>
        norm_indicator_le_parent C x;
    · convert integrable_parent_indicator K;
    · convert ConvexSubbody.tendsto_indicator_ae _;
      exact Filter.tendsto_id;
  convert h_dominated using 1;
  rw [ show ( fun C : ConvexSubbody K => C.area ) = fun C => ∫ x, ( C.body : Set Plane
    ).indicator ( fun _ => ( 1 : ℝ ) ) x ∂volume from funext fun _ =>
    ConvexSubbody.area_eq_integral_indicator _ ]; rw [ ContinuousAt ];

/-- **Filter-level area convergence.** Along any Hausdorff-convergent family of subbodies, the
areas converge. -/
theorem tendsto_area
    {α : Type*} {l : Filter α}
    {C : α → ConvexSubbody K} {C₀ : ConvexSubbody K}
    (hC : Tendsto C l (𝓝 C₀)) :
    Tendsto (fun a => (C a).area) l (𝓝 C₀.area) :=
  ((continuous_iff_continuousAt.mpr (fun C₀ => continuousAt_area C₀)).tendsto C₀).comp hC

/-- **Continuity of the area functional** on the fixed-parent hyperspace. -/
theorem continuous_area
    (K : Geometry.ConvexBody Plane) :
    Continuous fun C : ConvexSubbody K => C.area :=
  continuous_iff_continuousAt.mpr (fun C₀ => continuousAt_area C₀)

end ConvexSubbody

end NRR
