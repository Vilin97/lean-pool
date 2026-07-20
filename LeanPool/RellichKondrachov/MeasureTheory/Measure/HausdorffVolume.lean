/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# `RellichKondrachov.MeasureTheory.Measure.HausdorffVolume`

Relate Hausdorff measure `μH[finrank]` and Lebesgue measure `volume` on finite-dimensional real
normed vector spaces.

Mathlib provides the exact identification `μH[n] = volume` on `ι → ℝ`, and shows that
`μH[finrank ℝ E]` is an additive Haar measure on any finite-dimensional real normed space `E`.
Using uniqueness of Haar measures, we record the resulting proportionality
`μH[finrank] = c • volume` on general `E`, which is the form needed for transferring `L²` and
compactness statements across equivalent measures.
-/

namespace RellichKondrachov

open scoped ENNReal MeasureTheory Topology
open MeasureTheory TopologicalSpace Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceHausdorffVolume : MeasurableSpace E := borel E
local instance instBorelSpaceHausdorffVolume : BorelSpace E := ⟨rfl⟩

/-- `μH[finrank]` is a scalar multiple of `volume` on a finite-dimensional real normed space. -/
theorem hausdorffMeasure_eq_smul_volume :
    (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
      ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
          ((volume : Measure E) (Metric.closedBall (0 : E) 1))) • (volume : Measure E) := by
  classical
  haveI : SecondCountableTopology E := by infer_instance
  haveI : LocallyCompactSpace E := by infer_instance
  let K₀ : PositiveCompacts E :=
    ⟨⟨Metric.closedBall (0 : E) 1, isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))⟩,
      (Metric.nonempty_ball.2 (by norm_num : (0 : ℝ) < (1 : ℝ))).mono <|
        Metric.ball_subset_interior_closedBall (x := (0 : E)) (ε := (1 : ℝ))⟩
  have hμH :
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
        (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K₀ • Measure.addHaarMeasure K₀ := by
    simpa using
      (Measure.addHaarMeasure_unique (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E)) K₀)
  have hvol :
      (volume : Measure E) = (volume : Measure E) K₀ • Measure.addHaarMeasure K₀ := by
    simpa using (Measure.addHaarMeasure_unique (μ := (volume : Measure E)) K₀)
  have hv0 : (volume : Measure E) K₀ ≠ 0 := by
    exact (Measure.measure_pos_of_nonempty_interior (μ := (volume : Measure E)) (s := (K₀ : Set E))
      K₀.interior_nonempty).ne'
  have hvTop : (volume : Measure E) K₀ ≠ ∞ := by
    exact (K₀.isCompact.measure_lt_top (μ := (volume : Measure E))).ne
  set c : ℝ≥0∞ := (1 : ℝ≥0∞) / (volume : Measure E) K₀
  have hc : c * (volume : Measure E) K₀ = (1 : ℝ≥0∞) := by
    simpa [c] using (ENNReal.div_mul_cancel hv0 hvTop (b := (1 : ℝ≥0∞)))
  have hhaar : Measure.addHaarMeasure K₀ = c • (volume : Measure E) := by
    have :
        c • (volume : Measure E) = Measure.addHaarMeasure K₀ := by
      calc
        c • (volume : Measure E) = c • ((volume : Measure E) K₀ • Measure.addHaarMeasure K₀) := by
              -- Rewrite only the measure `volume`, not the scalar `c`.
              simpa using congrArg (fun μ : Measure E => c • μ) hvol
        _ = (c * (volume : Measure E) K₀) • Measure.addHaarMeasure K₀ := by
              simp [smul_smul]
        _ = Measure.addHaarMeasure K₀ := by simp [hc]
    simpa [c] using this.symm
  have :
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
        ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) K₀ /
            (volume : Measure E) K₀) • (volume : Measure E) := by
    calc
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
          (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K₀ • Measure.addHaarMeasure K₀ := hμH
      _ = (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K₀ •
            (c • (volume : Measure E)) := by
            simp [hhaar]
      _ = ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) K₀ /
              (volume : Measure E) K₀) • (volume : Measure E) := by
            simp [c, smul_smul, div_eq_mul_inv]
  simpa [K₀] using this

/-! ### Inverting the proportionality -/

/-- `volume` is a scalar multiple of `μH[finrank]` on a finite-dimensional
real inner product space. -/
theorem volume_eq_smul_hausdorffMeasure :
    (volume : Measure E) =
      (((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
          ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) •
        (μH[(Module.finrank ℝ E : ℝ)] : Measure E) := by
  classical
  haveI : SecondCountableTopology E := by infer_instance
  haveI : LocallyCompactSpace E := by infer_instance
  let K : Set E := Metric.closedBall (0 : E) 1
  have hv0 : (volume : Measure E) K ≠ 0 := by
    have hne : (interior K).Nonempty := by
      refine ⟨0, ?_⟩
      have : (0 : E) ∈ Metric.ball (0 : E) 1 := Metric.mem_ball_self (by norm_num)
      exact (Metric.ball_subset_interior_closedBall (x := (0 : E)) (ε := (1 : ℝ)) this)
    exact (MeasureTheory.Measure.measure_pos_of_nonempty_interior
      (μ := (volume : Measure E)) (s := K) hne).ne'
  have hvTop : (volume : Measure E) K ≠ ∞ := by
    exact (isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))).measure_lt_top.ne
  have hμH0 : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K ≠ 0 := by
    have hne : (interior K).Nonempty := by
      refine ⟨0, ?_⟩
      have : (0 : E) ∈ Metric.ball (0 : E) 1 := Metric.mem_ball_self (by norm_num)
      exact (Metric.ball_subset_interior_closedBall (x := (0 : E)) (ε := (1 : ℝ)) this)
    exact
      (MeasureTheory.Measure.measure_pos_of_nonempty_interior
        (μ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E)) (s := K) hne).ne'
  have hμHTop : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K ≠ ∞ := by
    exact (isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))).measure_lt_top.ne
  set a : ℝ≥0∞ := (μH[(Module.finrank ℝ E : ℝ)] : Measure E) K
  set b : ℝ≥0∞ := (volume : Measure E) K
  have hab : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) = (a / b) • (volume : Measure E) := by
    simpa [a, b, K] using (hausdorffMeasure_eq_smul_volume (E := E))
  have hba_mul_hab : (b / a) * (a / b) = 1 := by
    -- `b/a * a/b = 1` when both `a` and `b` are nonzero and finite.
    calc
      (b / a) * (a / b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv, mul_assoc]
      _ = b * (a⁻¹ * a) * b⁻¹ := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = b * (1 : ℝ≥0∞) * b⁻¹ := by
            simp [ENNReal.inv_mul_cancel hμH0 hμHTop]
      _ = b * b⁻¹ := by simp
      _ = (1 : ℝ≥0∞) := by
            simpa using (ENNReal.mul_inv_cancel hv0 hvTop)
  have : (b / a) • (μH[(Module.finrank ℝ E : ℝ)] : Measure E) = (volume : Measure E) := by
    calc
      (b / a) • (μH[(Module.finrank ℝ E : ℝ)] : Measure E) =
          (b / a) • ((a / b) • (volume : Measure E)) := by
            simp [hab]
      _ = ((b / a) * (a / b)) • (volume : Measure E) := by
            simp [smul_smul]
      _ = (volume : Measure E) := by simp [hba_mul_hab]
  simpa [a, b, K] using this.symm

end

end RellichKondrachov
