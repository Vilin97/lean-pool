/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.IndicatorStability

/-!
# `NRR.EMP.VariableBody.CellAreaContinuity` — joint continuity of cell area

The restricted power-cell area `cellArea hA C s w i` depends continuously on the triple
`(C, s, w)` of parent subbody, configuration, and weight vector. The argument is a dominated
convergence: the area is the Lebesgue integral of the `0/1` cell indicator, these indicators
converge almost everywhere along any convergent filter (`tendsto_cell_indicator_ae`), and every
cell is contained in the fixed parent body `K`, so the constant parent indicator is an integrable
dominating function.

* `continuous_cellArea` — joint continuity in body, sites, and weights.
* `continuous_cellArea_compactFamily` — the composition with a continuous site family
  `sites : C(X, Config n)`, needing only continuity of `X`, not compactness.
-/

open MeasureTheory Filter Topology
open NRR NRR.Geometry NRR.Geometry.ConvexBody
open scoped RealInnerProductSpace

namespace NRR.EMP.VariableBody

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ}

/-- The configuration topology is induced by the point map from the metric space `Fin n → E2`,
hence first countable; this makes neighbourhood filters countably generated, as required by the
filter form of dominated convergence. -/
instance instFirstCountableTopologyConfig (n : ℕ) : FirstCountableTopology (Config n) :=
  (show Topology.IsInducing (Config.pts (n := n)) by
      rw [Topology.isInducing_iff]; exact Config.topology_eq_induced n).firstCountableTopology

/-- Each restricted cell is measurable (it is compact, hence closed). -/
theorem cellSet_measurableSet
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (cellSet hA C s w i) :=
  (cellSet_isCompact hA C s w i).isClosed.measurableSet

/-- **Cell area as an indicator integral.** The restricted cell area equals the Lebesgue integral
of the `0/1` indicator of the cell. -/
theorem cellArea_eq_integral_indicator
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) :
    cellArea hA C s w i =
      ∫ x, (cellSet hA C s w i).indicator (fun _ => (1 : ℝ)) x ∂volume := by
  rw [integral_indicator_const (1 : ℝ) (cellSet_measurableSet hA C s w i)]
  rw [cellArea_def, cellSet_def]
  simp [PowerDiagram.bodyCellArea, measureReal_def]

/-- The constant parent indicator dominates every cell indicator pointwise. -/
theorem norm_cell_indicator_le_parent
    (hA : 0 < A) (C : BodySpace K A)
    (s : Config n) (w : Fin n → ℝ) (i : Fin n) (x : Plane) :
    ‖(cellSet hA C s w i).indicator (fun _ => (1 : ℝ)) x‖
      ≤ (K : Set Plane).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ cellSet hA C s w i
  · have hxK : x ∈ (K : Set Plane) := cellSet_subset_parent hA C s w i hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxK]
    norm_num
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- **Joint continuity of the restricted power-cell area.** The area depends continuously on the
parent subbody, the configuration, and the weight vector. -/
theorem continuous_cellArea
    (hA : 0 < A) (i : Fin n) :
    Continuous fun z :
        BodySpace K A × Config n × (Fin n → ℝ) =>
      cellArea hA z.1 z.2.1 z.2.2 i := by
  rw [continuous_iff_continuousAt]
  rintro ⟨C₀, s₀, w₀⟩
  -- Rewrite the area functional as an integral of the cell indicator.
  have hfun :
      (fun z : BodySpace K A × Config n × (Fin n → ℝ) =>
          cellArea hA z.1 z.2.1 z.2.2 i)
        = fun z => ∫ x, (cellSet hA z.1 z.2.1 z.2.2 i).indicator (fun _ => (1 : ℝ)) x ∂volume :=
    funext fun z => cellArea_eq_integral_indicator hA z.1 z.2.1 z.2.2 i
  -- Coordinate projections of the convergent filter.
  have hC : Tendsto (fun z : BodySpace K A × Config n × (Fin n → ℝ) => z.1)
      (𝓝 (C₀, s₀, w₀)) (𝓝 C₀) := continuous_fst.tendsto _
  have hs : Tendsto (fun z : BodySpace K A × Config n × (Fin n → ℝ) => z.2.1)
      (𝓝 (C₀, s₀, w₀)) (𝓝 s₀) := (continuous_fst.comp continuous_snd).tendsto _
  have hw : Tendsto (fun z : BodySpace K A × Config n × (Fin n → ℝ) => z.2.2)
      (𝓝 (C₀, s₀, w₀)) (𝓝 w₀) := (continuous_snd.comp continuous_snd).tendsto _
  -- Dominated convergence with the parent indicator as dominating function.
  have h_dom :
      Tendsto
        (fun z : BodySpace K A × Config n × (Fin n → ℝ) =>
          ∫ x, (cellSet hA z.1 z.2.1 z.2.2 i).indicator (fun _ => (1 : ℝ)) x ∂volume)
        (𝓝 (C₀, s₀, w₀))
        (𝓝 (∫ x, (cellSet hA C₀ s₀ w₀ i).indicator (fun _ => (1 : ℝ)) x ∂volume)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => (K : Set Plane).indicator (fun _ => (1 : ℝ)) x) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun z =>
        Measurable.aestronglyMeasurable
          (Measurable.indicator measurable_const (cellSet_measurableSet hA z.1 z.2.1 z.2.2 i))
    · exact Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun x =>
        norm_cell_indicator_le_parent hA z.1 z.2.1 z.2.2 i x
    · exact ConvexSubbody.integrable_parent_indicator K
    · exact tendsto_cell_indicator_ae hA hC hs hw i
  rw [ContinuousAt, hfun]
  convert h_dom using 2
  exact cellArea_eq_integral_indicator hA C₀ s₀ w₀ i

/-- **Compact-family composition form.** For a continuous site family `sites : C(X, Config n)`,
the restricted cell area is continuous jointly in the parent subbody, the base point `x : X`, and
the weight vector. Only continuity of `X` is used; compactness is not required. -/
theorem continuous_cellArea_compactFamily
    {X : Type*} [MetricSpace X]
    (sites : C(X, Config n))
    (hA : 0 < A) (i : Fin n) :
    Continuous fun z :
        BodySpace K A × X × (Fin n → ℝ) =>
      cellArea hA z.1 (sites z.2.1) z.2.2 i := by
  have hmap : Continuous fun z : BodySpace K A × X × (Fin n → ℝ) =>
      (z.1, sites z.2.1, z.2.2) :=
    continuous_fst.prodMk
      ((sites.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
  exact (continuous_cellArea hA i).comp hmap

end NRR.EMP.VariableBody
