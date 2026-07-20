/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannian
import LeanPool.RellichKondrachov.MeasureTheory.Measure.HausdorffVolume

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannianVolume`

Compare chart pushforward measures arising from the Riemannian Hausdorff volume measure against
Lebesgue `volume` on the chart model space.

This is a convenience layer on top of
`RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannian`, which gives domination by the
Euclidean Hausdorff measure `μH[dim]`. Since `μH[finrank]` is an additive Haar measure on
finite-dimensional real inner product spaces, it is a scalar multiple of `volume`. We record the
resulting domination by `volume` on chart balls.

## Main results

 - `RellichKondrachov.Geometry.Manifold.Sobolev.RiemannianFiniteChartData.`
   `chartMeasure_restrict_le_volume`
 - `RellichKondrachov.Geometry.Manifold.Sobolev.RiemannianFiniteChartData.`
   `volume_restrict_le_chartMeasure`
 -/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

universe uE uH uM

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMChartMeasureRiemannianVolume :
    MeasurableSpace M := borel M
local instance instBorelSpaceMChartMeasureRiemannianVolume : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEChartMeasureRiemannianVolume :
    MeasurableSpace E := borel E
local instance instBorelSpaceEChartMeasureRiemannianVolume : BorelSpace E := ⟨rfl⟩
local instance
    instOpensMeasurableSpaceEChartMeasureRiemannianVolume :
    OpensMeasurableSpace E := by
  infer_instance

namespace RiemannianFiniteChartData

variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)

/-!
## Finiteness of comparison constants

The comparison lemmas in this file produce explicit `ℝ≥0∞` constants. For downstream `Lp` change-
of-measure equivalences we also need these constants to be finite (`≠ ∞`).
-/

private lemma volume_closedBall_unit_ne_zero :
    ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ 0 := by
  have hpos :
      0 < (volume : Measure E) (Metric.closedBall (0 : E) 1) := by
    simpa using (Metric.measure_closedBall_pos (μ := (volume : Measure E)) (x := (0 : E)) (r := (1
      : ℝ))
      (by norm_num))
  exact hpos.ne'

private lemma hausdorff_closedBall_unit_ne_top :
    ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1)) ≠ ∞ := by
  -- `μH[dim]` is finite on compact sets, and closed balls are compact in finite-dimensional spaces.
  have hcompact : IsCompact (Metric.closedBall (0 : E) (1 : ℝ)) :=
    isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))
  exact hcompact.measure_ne_top (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E))

private lemma volume_closedBall_unit_ne_top :
    ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ ∞ := by
  have hcompact : IsCompact (Metric.closedBall (0 : E) (1 : ℝ)) :=
    isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))
  exact hcompact.measure_ne_top (μ := (volume : Measure E))

private lemma hausdorff_div_volume_closedBall_unit_ne_top :
    ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
        ((volume : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ := by
  -- `a / b = a * b⁻¹`, and both factors are finite once `b ≠ 0`.
  have hnum : (μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) ≠ ∞ :=
    hausdorff_closedBall_unit_ne_top (E := E)
  have hden0 : ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ 0 :=
    volume_closedBall_unit_ne_zero (E := E)
  have hdenInv : (((volume : Measure E) (Metric.closedBall (0 : E) 1))⁻¹) ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top.2 hden0)
  -- Expand `/` and use `mul_ne_top`.
  simpa [div_eq_mul_inv] using (ENNReal.mul_ne_top hnum hdenInv)

private lemma volume_div_hausdorff_closedBall_unit_ne_top :
    (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
        ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ := by
  have hnum : ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≠ ∞ :=
    volume_closedBall_unit_ne_top (E := E)
  have hden0 : ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1)) ≠ 0 := by
    -- `μH[dim]` is an additive Haar measure in finite-dimensional spaces, hence open-positive.
    have hpos :
        0 < (μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1) := by
      simpa using
        (Metric.measure_closedBall_pos
          (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E)) (x := (0 : E)) (r := (1 : ℝ))
          (by norm_num))
    exact hpos.ne'
  have hdenInv : (((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))⁻¹) ≠ ∞
    := by
    simpa using (ENNReal.inv_ne_top.2 hden0)
  simpa [div_eq_mul_inv] using (ENNReal.mul_ne_top hnum hdenInv)

omit [IsManifold I (1 : WithTop ℕ∞) M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M] in
lemma chartMeasure_volume_constant_ne_top (i : dR.d.ι) :
    ((((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
          ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1))))) ≠ ∞ := by
  have hC : ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) ≠ ∞ := by
    have hbase : (dR.C i : ℝ≥0∞) ≠ ∞ := by simp
    have hexp : 0 ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact ENNReal.rpow_ne_top_of_nonneg hexp hbase
  have hratio :
      ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
          ((volume : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ :=
    hausdorff_div_volume_closedBall_unit_ne_top (E := E)
  simpa using (ENNReal.mul_ne_top hC hratio)

omit [IsManifold I (1 : WithTop ℕ∞) M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T3Space M] in
lemma volume_chartMeasure_constant_ne_top (i : dR.d.ι) :
    ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
            ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) ≠ ∞ := by
  have hratio :
      (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
          ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) ≠ ∞ :=
    volume_div_hausdorff_closedBall_unit_ne_top (E := E)
  have hCfwd : ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) ≠ ∞ := by
    have hbase : (dR.Cfwd i : ℝ≥0∞) ≠ ∞ := by simp
    have hexp : 0 ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact ENNReal.rpow_ne_top_of_nonneg hexp hbase
  simpa [mul_assoc, mul_left_comm, mul_comm] using (ENNReal.mul_ne_top hratio hCfwd)

/-- On the chart ball, the chart pushforward measure of the Riemannian Hausdorff volume measure is
dominated by Lebesgue `volume` on the chart model space. -/
lemma chartMeasure_restrict_le_volume (i : dR.d.ι) :
    (FiniteChartData.chartMeasure (d := dR.d) (I := I)
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M))
          i).restrict
        (chartBall (dR := dR) (I := I) i) ≤
      (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
          ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1)))) •
        (volume : Measure E).restrict (chartBall (dR := dR) (I := I) i) := by
  classical
  -- First apply the domination by `μH[dim]` from `ChartMeasureRiemannian`.
  have hμH :
      (FiniteChartData.chartMeasure (d := dR.d) (I := I)
            (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M :=
              M)) i).restrict
          (chartBall (dR := dR) (I := I) i) ≤
        ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict (chartBall (dR := dR) (I := I) i) :=
    RiemannianFiniteChartData.chartMeasure_restrict_le_hausdorff (dR := dR) (I := I) i
  -- Rewrite `μH[dim]` as a scalar multiple of `volume`.
  have hHvol :
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
        ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1))) • (volume : Measure E) := by
    simpa using (RellichKondrachov.hausdorffMeasure_eq_smul_volume (E := E))
  have hHvol_restrict :
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict (chartBall (dR := dR) (I := I) i) =
        ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1))) •
          (volume : Measure E).restrict (chartBall (dR := dR) (I := I) i) := by
    -- Apply `restrict` to both sides of `hHvol`, then use `restrict_smul`.
    have :=
      congrArg (fun μ : Measure E => μ.restrict (chartBall (dR := dR) (I := I) i)) hHvol
    simpa using this
  -- Combine scalars.
  have :
      ((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict (chartBall (dR := dR) (I := I) i) =
        (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
            ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
              ((volume : Measure E) (Metric.closedBall (0 : E) 1)))) •
          (volume : Measure E).restrict (chartBall (dR := dR) (I := I) i) := by
    -- `a • (b • μ) = (a*b) • μ`, and `restrict` commutes with `smul`.
    simp [hHvol_restrict, smul_smul]
  exact hμH.trans_eq this

/-- On the chart ball, Lebesgue `volume` on the chart model space is dominated by the chart
pushforward measure of the Riemannian Hausdorff volume measure. -/
lemma volume_restrict_le_chartMeasure (i : dR.d.ι) :
    (volume : Measure E).restrict (chartBall (dR := dR) (I := I) i) ≤
      (((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
            ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) •
        (FiniteChartData.chartMeasure (d := dR.d) (I := I)
              (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M
                := M)) i).restrict
          (chartBall (dR := dR) (I := I) i)) := by
  classical
  let S : Set E := chartBall (dR := dR) (I := I) i
  -- Rewrite `volume` as a scalar multiple of `μH[dim]`.
  have hVol :
      (volume : Measure E) =
        ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E)) := by
    simpa using (RellichKondrachov.volume_eq_smul_hausdorffMeasure (E := E))
  have hVolS :
      (volume : Measure E).restrict S =
        ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E)).restrict S := by
    simpa using congrArg (fun μ : Measure E => μ.restrict S) hVol
  have hVolS' :
      (volume : Measure E).restrict S =
        (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict S := by
    simpa [Measure.restrict_smul] using hVolS
  have hHaus :
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict S ≤
        ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) •
          (FiniteChartData.chartMeasure (d := dR.d) (I := I)
                (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M
                  := M)) i).restrict
            S :=
    RiemannianFiniteChartData.hausdorff_restrict_le_chartMeasure (dR := dR) (I := I) i
  -- Multiply by the scalar relating `volume` and `μH[dim]`, and combine scalars.
  have :
      (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) •
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E).restrict S ≤
        (((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
                ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
              ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ))) •
          (FiniteChartData.chartMeasure (d := dR.d) (I := I)
                (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M
                  := M)) i).restrict
            S) := by
    -- `•` is monotone for nonnegative scalars.
    intro A
    have hA := hHaus A
    have :=
      mul_le_mul_right hA
        (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
          ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1)))
    simpa [Measure.smul_apply, smul_smul, mul_assoc, mul_left_comm, mul_comm] using this
  -- Conclude by rewriting the left-hand side as `volume.restrict S`.
  simpa [S, hVolS'] using (le_trans (le_of_eq hVolS') this)

end RiemannianFiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
