/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitz
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitzForward
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartDataRiemannian`

Riemannian-specialized chart/partition-of-unity data for Sobolev theory.

This file constructs finite chart data on a compact Riemannian manifold, with the additional
guarantee that each partition-of-unity function is supported in a chart neighborhood on which the
inverse extended chart is Lipschitz (with respect to the Riemannian distance).

This is the natural input needed to compare chart pushforward measures against Euclidean Hausdorff
measure on the fixed compact supports used by the manifold Rellich glue.

## Main definitions / results

- `RellichKondrachov.Geometry.Manifold.Sobolev.RiemannianFiniteChartData`
- `RellichKondrachov.Geometry.Manifold.Sobolev.exists_riemannianFiniteChartData`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Topology Filter
open _root_.Manifold _root_.Bundle
open RellichKondrachov.Geometry.Manifold.Riemannian
open scoped Manifold NNReal ENNReal

universe uE uH uM

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMChartDataRiemannian : MeasurableSpace M := borel M
local instance instBorelSpaceMChartDataRiemannian : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEChartDataRiemannian : MeasurableSpace E := borel E
local instance instBorelSpaceEChartDataRiemannian : BorelSpace E := ⟨rfl⟩

/-- A `FiniteChartData` together with explicit Lipschitz neighborhoods (in
chart coordinates) for the inverse extended chart, and a partition-of-unity
subordination guarantee to those neighborhoods. -/
structure RiemannianFiniteChartData where
  /-- Underlying finite chart data. -/
  d : FiniteChartData.{uE, uH, uM, uM} (H := H) (M := M) I
  /-- Lipschitz constant for each chart inverse on a fixed ball. -/
  C : d.ι → ℝ≥0
  /-- Lipschitz constant for each (forward) extended chart on the preimage of the chart ball. -/
  Cfwd : d.ι → ℝ≥0
  /-- Radius of the chart ball on which the inverse is Lipschitz. -/
  r : d.ι → ℝ
  /-- Positivity of the radii. -/
  r_pos : ∀ i, 0 < r i
  /-- Riemannian-distance Lipschitz control of the inverse extended chart on the chart ball. -/
  riemannianLipschitz_symm :
    ∀ i, ∀ y₁ ∈ Metric.ball (extChartAt I (d.center i) (d.center i)) (r i) ∩ range I,
      ∀ y₂ ∈ Metric.ball (extChartAt I (d.center i) (d.center i)) (r i) ∩ range I,
        riemannianEDist I
          ((extChartAt I (d.center i)).symm y₁)
          ((extChartAt I (d.center i)).symm y₂) ≤
          (C i : ENNReal) * edist y₁ y₂
  /-- Riemannian-distance Lipschitz control of the (forward) extended chart on the preimage of the
  chart ball (inside the chart source). -/
  riemannianLipschitz :
    ∀ i,
      ∀ x₁ ∈
        (extChartAt I (d.center i)) ⁻¹'
            Metric.ball (extChartAt I (d.center i) (d.center i)) (r i) ∩
          (extChartAt I (d.center i)).source,
        ∀ x₂ ∈
          (extChartAt I (d.center i)) ⁻¹'
              Metric.ball (extChartAt I (d.center i) (d.center i)) (r i) ∩
            (extChartAt I (d.center i)).source,
          edist (extChartAt I (d.center i) x₁) (extChartAt I (d.center i) x₂) ≤
            (Cfwd i : ENNReal) * riemannianEDist I x₁ x₂
  /-- The partition-of-unity is subordinate to the preimage of the chart ball
  (inside the chart source). -/
  subordinate_ball :
    ∀ i,
      closure (Function.support (d.ρ i : M → ℝ)) ⊆
        (extChartAt I (d.center i)) ⁻¹' Metric.ball (extChartAt I (d.center i) (d.center i)) (r i) ∩
          (extChartAt I (d.center i)).source

namespace RiemannianFiniteChartData

variable {I}

/-!
## Chart balls

The `RiemannianFiniteChartData` structure equips each chart index with a radius `r i`. The
corresponding *chart ball* is the intersection of the Euclidean metric ball in chart coordinates
with the chart target.

This set is used throughout the Sobolev/Rellich development to localize measure comparisons and
compactness arguments.
-/

/-- The chart ball in model-space coordinates associated to chart index `i`. -/
def chartBall (dR : RiemannianFiniteChartData (H := H) (M := M) I) (i : dR.d.ι) : Set E :=
  Metric.ball (extChartAt I (dR.d.center i) (dR.d.center i)) (dR.r i) ∩
    (extChartAt I (dR.d.center i)).target

end RiemannianFiniteChartData

section Compact

variable [T2Space M] [CompactSpace M]

omit
  [FiniteDimensional ℝ E]
  [IsManifold I n∞ M]
  [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space M]
  [CompactSpace M] in
private lemma isOpen_chartBallSource (x : M) (r : ℝ) :
    IsOpen ((extChartAt I x) ⁻¹' Metric.ball (extChartAt I x x) r ∩ (extChartAt I x).source) := by
  have hs : IsOpen ((extChartAt I x).source : Set M) :=
    isOpen_extChartAt_source (I := I) (x := x)
  have ht : IsOpen (Metric.ball (extChartAt I x x) r) := Metric.isOpen_ball
  have hcont : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
    continuousOn_extChartAt (I := I) (x := x)
  -- Use a `ContinuousOn` preimage lemma, and reorder intersections.
  simpa [inter_left_comm, inter_assoc, inter_comm] using
    (ContinuousOn.isOpen_inter_preimage (f := extChartAt I x) (s := (extChartAt I x).source)
      (t := Metric.ball (extChartAt I x x) r) hcont hs ht)

/-- On a compact Riemannian manifold, there exists finite chart data together with explicit
Lipschitz neighborhoods (in chart coordinates) for chart inverses and a partition-of-unity
subordination to those neighborhoods. -/
theorem exists_riemannianFiniteChartData :
    Nonempty (RiemannianFiniteChartData (H := H) (M := M) I) := by
  classical
  -- Build the emetric structure induced by the Riemannian metric, so `riemannianEDist` is the
  -- `edist`.
  haveI : T3Space M := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : BorelSpace M := ⟨rfl⟩
  haveI : IsRiemannianManifold I M := by infer_instance
  -- Choose a Lipschitz neighborhood for each point (for the chart inverse in chart coordinates).
  have hLipData :
      ∀ x : M, ∃ (C : ℝ≥0), 0 < C ∧ ∃ (r : ℝ), 0 < r ∧
        LipschitzOnWith C (extChartAt I x).symm (Metric.ball (extChartAt I x x) r ∩ range I) := by
    intro x
    exact
      lipschitzOnWith_symm_extChartAt_ofRiemannianMetric
        (I := I) (M := M) x
  choose Cinv Cinv_pos rE rE_pos hLipSymm using hLipData
  -- Choose a Lipschitz neighborhood for each point (for the forward chart on a small Riemannian
  -- ball).
  have hFwdData :
      ∀ x : M, ∃ (C : ℝ≥0), 0 < C ∧ ∃ (r : ℝ≥0), 0 < r ∧
        LipschitzOnWith C (extChartAt I x) {y : M | riemannianEDist I x y < (r : ℝ≥0∞)} := by
    intro x
    exact
      RellichKondrachov.Geometry.Manifold.Riemannian.lipschitzOnWith_extChartAt_ofRiemannianMetric
        (I := I) (M := M) x
  choose Cfwd Cfwd_pos rM rM_pos hLipFwdBall using hFwdData
  -- Shrink chart radii so that the chart-ball preimage lies in the forward Lipschitz neighborhood.
  let r' : M → ℝ := fun x => min (rE x) ((rM x / Cinv x : ℝ≥0) : ℝ)
  have r'_pos : ∀ x : M, 0 < r' x := by
    intro x
    have h₁ : 0 < rE x := rE_pos x
    have h₂' : 0 < (rM x / Cinv x : ℝ≥0) := by
      exact div_pos (rM_pos x) (Cinv_pos x)
    have h₂ : 0 < ((rM x / Cinv x : ℝ≥0) : ℝ) := by
      exact_mod_cast h₂'
    exact lt_min_iff.2 ⟨h₁, h₂⟩
  -- Define the corresponding open neighborhood in `M` (preimage of the chart ball, inside the
  -- chart source).
  let U : M → Set M := fun x =>
    (extChartAt I x) ⁻¹' Metric.ball (extChartAt I x x) (r' x) ∩ (extChartAt I x).source
  have hU_open : ∀ x : M, IsOpen (U x) := by
    intro x
    simpa [U] using isOpen_chartBallSource (I := I) x (r' x)
  have hcover : (univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨x, ?_⟩
    have hxball : extChartAt I x x ∈ Metric.ball (extChartAt I x x) (r' x) :=
      Metric.mem_ball_self (r'_pos x)
    exact ⟨hxball, mem_extChartAt_source (I := I) x⟩
  -- Extract a finite subcover and build a partition of unity subordinate to it.
  rcases (isCompact_univ.elim_finite_subcover U hU_open hcover) with ⟨t, ht⟩
  let ι' := {x : M // x ∈ t}
  have hU' : (univ : Set M) ⊆ ⋃ i : ι', U (i : M) := by
    intro x hx
    have : x ∈ ⋃ y ∈ (t : Finset M), U y := ht hx
    rcases mem_iUnion₂.1 this with ⟨y, hy, hxy⟩
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  haveI : SigmaCompactSpace M := by infer_instance
  have hU'_open : ∀ i : ι', IsOpen (U (i : M)) := fun i => hU_open (i : M)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (ι := ι') (I := I) (M := M)
      (s := (univ : Set M)) isClosed_univ (fun i => U (i : M)) hU'_open hU' with
    ⟨ρ, hρsub⟩
  -- Package into finite chart data, keeping the original `FiniteChartData` interface.
  let d : FiniteChartData.{uE, uH, uM, uM} (H := H) (M := M) I :=
    { ι := ι'
      instFintype := Finset.Subtype.fintype t
      center := fun i => (i : M)
      ρ := ρ
      subordinate := by
        intro i
        -- Subordination to the chosen `U` implies subordination to the chart source.
        have hsubU : closure (Function.support (ρ i : M → ℝ)) ⊆ U (i : M) := hρsub i
        have hUsub : U (i : M) ⊆ (extChartAt I (i : M)).source := by
          intro x hx
          exact hx.2
        -- `extChartAt.source = chartAt.source`.
        have hfinal : closure (Function.support (ρ i : M → ℝ)) ⊆ (chartAt H (i : M)).source := by
          rw [← extChartAt_source (I := I)]
          exact hsubU.trans hUsub
        exact hfinal }
  -- Produce the additional Lipschitz data indexed by `d.ι`.
  refine ⟨{
    d := d
    C := fun i => Cinv (i : M)
    Cfwd := fun i => Cfwd (i : M)
    r := fun i => r' (i : M)
    r_pos := fun i => r'_pos (i : M)
    riemannianLipschitz_symm := fun i y₁ hy₁ y₂ hy₂ => by
      have hLip' :
          LipschitzOnWith (Cinv (i : M)) (extChartAt I (i : M)).symm
            (Metric.ball (extChartAt I (i : M) (i : M)) (r' (i : M)) ∩ range I) :=
        (hLipSymm (i : M)).mono (by
          intro y hy
          refine ⟨?_, hy.2⟩
          exact Metric.ball_subset_ball (min_le_left _ _) hy.1)
      simpa [IsRiemannianManifold.out (I := I) (M := M)] using (hLip' (x := y₁) hy₁ (y := y₂) hy₂)
    riemannianLipschitz := fun i x₁ hx₁ x₂ hx₂ => by
      -- Restrict the forward Lipschitz statement to the chart-ball preimage.
      let x : M := (i : M)
      have hU_sub :
          U x ⊆ {y : M | riemannianEDist I x y < (rM x : ℝ≥0∞)} := by
        intro y hy
        have hy_source : y ∈ (extChartAt I x).source := hy.2
        have hy_ball : extChartAt I x y ∈ Metric.ball (extChartAt I x x) (r' x) := hy.1
        have hy_ball_big : extChartAt I x y ∈ Metric.ball (extChartAt I x x) (rE x) := by
          have hr : r' x ≤ rE x := min_le_left _ _
          exact Metric.ball_subset_ball hr hy_ball
        have hx_ball : extChartAt I x x ∈ Metric.ball (extChartAt I x x) (rE x) :=
          Metric.mem_ball_self (rE_pos x)
        have hy_range : extChartAt I x y ∈ range I := by
          exact extChartAt_target_subset_range (I := I) (x := x) ((extChartAt I x).map_source
            hy_source)
        have hx_range : extChartAt I x x ∈ range I := by
          exact extChartAt_target_subset_range (I := I) (x := x) (mem_extChartAt_target x)
        -- Use the inverse Lipschitz control to bound `riemannianEDist I x y`.
        have hLip_symm_xy :
            edist x y ≤ (Cinv x : ℝ≥0∞) * edist (extChartAt I x x) (extChartAt I x y) := by
          -- Apply Lipschitz for `(extChartAt I x).symm` on the larger ball.
          have hLip' :
              edist ((extChartAt I x).symm (extChartAt I x x)) ((extChartAt I x).symm (extChartAt I
                x y)) ≤
                (Cinv x : ℝ≥0∞) * edist (extChartAt I x x) (extChartAt I x y) :=
            (hLipSymm x) (x := extChartAt I x x) ⟨hx_ball, hx_range⟩ (y := extChartAt I x y)
              ⟨hy_ball_big, hy_range⟩
          have hx_symm : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv (I := I)
            x
          have hy_symm : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv
            hy_source
          simpa only [hx_symm, hy_symm] using hLip'
        have hy_edist_lt :
            edist (extChartAt I x x) (extChartAt I x y) < ((rM x / Cinv x : ℝ≥0) : ℝ≥0∞) := by
          have hy_dist : dist (extChartAt I x y) (extChartAt I x x) < r' x := by
            simpa [Metric.mem_ball, dist_comm] using hy_ball
          have hr' : r' x ≤ ((rM x / Cinv x : ℝ≥0) : ℝ) := min_le_right _ _
          have hy_dist' : dist (extChartAt I x y) (extChartAt I x x) < ((rM x / Cinv x : ℝ≥0) : ℝ)
            :=
            lt_of_lt_of_le hy_dist hr'
          -- Convert `dist` bound to `edist` bound.
          have hthis :
              edist (extChartAt I x y) (extChartAt I x x) <
                ENNReal.ofReal (((rM x / Cinv x : ℝ≥0) : ℝ)) :=
            (edist_lt_ofReal).2 hy_dist'
          rw [ENNReal.ofReal_coe_nnreal] at hthis
          rw [edist_comm]
          exact hthis
        have hC_ne : (Cinv x : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (Cinv_pos x))
        have hC_ne_top : (Cinv x : ℝ≥0∞) ≠ ⊤ := by simp
        have hmul_lt :
            (Cinv x : ℝ≥0∞) * edist (extChartAt I x x) (extChartAt I x y) < (rM x : ℝ≥0∞) := by
          have hC_ne' : (Cinv x : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt (Cinv_pos x))
          have hy_edist_lt' :
              edist (extChartAt I x x) (extChartAt I x y) < (rM x : ℝ≥0∞) / (Cinv x : ℝ≥0∞) := by
            simpa [ENNReal.coe_div hC_ne'] using hy_edist_lt
          have hmul :=
            ENNReal.mul_lt_mul_left hC_ne hC_ne_top (b := edist (extChartAt I x x) (extChartAt I x
              y))
              (c := (rM x : ℝ≥0∞) / (Cinv x : ℝ≥0∞)) hy_edist_lt'
          have hmul' :
              edist (extChartAt I x x) (extChartAt I x y) * (Cinv x : ℝ≥0∞) < (rM x : ℝ≥0∞) := by
            simpa [ENNReal.div_mul_cancel hC_ne hC_ne_top] using hmul
          simpa [mul_comm] using hmul'
        have : riemannianEDist I x y < (rM x : ℝ≥0∞) := by
          -- `edist x y = riemannianEDist I x y` for the induced emetric structure.
          have hle : riemannianEDist I x y ≤ (Cinv x : ℝ≥0∞) * edist (extChartAt I x x) (extChartAt
            I x y) := by
            simpa [IsRiemannianManifold.out (I := I) (M := M)] using hLip_symm_xy
          exact lt_of_le_of_lt hle hmul_lt
        exact this
      have hLipU :
          LipschitzOnWith (Cfwd x) (extChartAt I x) (U x) :=
        (hLipFwdBall x).mono hU_sub
      simpa [IsRiemannianManifold.out (I := I) (M := M)] using (hLipU (x := x₁) hx₁ (y := x₂) hx₂)
    subordinate_ball := fun i => ?_
  }⟩
  -- Extract the `U`-subordination and rewrite it in the promised form.
  have hsubU : closure (Function.support (ρ i : M → ℝ)) ⊆ U (i : M) := hρsub i
  simpa [U, d] using hsubU

end Compact

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
