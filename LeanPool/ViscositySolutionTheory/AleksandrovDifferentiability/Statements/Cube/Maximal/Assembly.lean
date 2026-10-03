/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Maximal.Fubini

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Coordinate-slice maximal estimate assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem coordinateSlice_measureConstant_bound {n : ℕ} {Ccoord Cmeasure osc t : ℝ}
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure) (hosc : 0 ≤ osc) (ht : 0 < t) :
    (n : ENNReal) * ENNReal.ofReal (Ccoord * osc / t) ≤
      ENNReal.ofReal (Cmeasure * osc / t) := by
  have hscale_nonneg : 0 ≤ osc / t := div_nonneg hosc ht.le
  have hreal :
      (n : ℝ) * (Ccoord * osc / t) ≤ Cmeasure * osc / t := by
    have hscaled := mul_le_mul_of_nonneg_right hmeasure hscale_nonneg
    calc
      (n : ℝ) * (Ccoord * osc / t) =
          ((n : ℝ) * Ccoord) * (osc / t) := by ring
      _ ≤ Cmeasure * (osc / t) := hscaled
      _ = Cmeasure * osc / t := by ring
  have hleft :
      (n : ENNReal) * ENNReal.ofReal (Ccoord * osc / t) =
        ENNReal.ofReal ((n : ℝ) * (Ccoord * osc / t)) := by
    rw [← ENNReal.ofReal_natCast n]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  rw [hleft]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Version of `CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate` where the scalar
measure-constant comparison is supplied in real-valued coefficient form. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate_of_measureConstant
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n}
    {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hmass : CoordinateSliceSourceMassBound μslice (sourceCubeOscillation n u))
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate μslice (2 * Cmax) Ccoord
        (sourceCubeOscillation n u) t)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    CoordinateSliceMaximalTotalBadSetEstimate u μslice Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate hdiff hmass hmax ht hfubini
    (coordinateSlice_measureConstant_bound hmeasure
      (sourceCubeOscillation_nonneg_of_boundedOn hbounded) ht)

/-- Two-term constant absorption used in the source upper-contact estimate: if a single constant
dominates the `t` coefficient and the oscillation coefficient separately, then it dominates their
sum. -/
theorem two_mul_add_le_mul_add_of_two_mul_le {A B C t osc : ℝ}
    (hA : 2 * A ≤ C) (hB : 2 * B ≤ C) (ht : 0 ≤ t) (hosc : 0 ≤ osc) :
    2 * (A * t + B * osc) ≤ C * (t + osc) := by
  have ht_part : (2 * A) * t ≤ C * t :=
    mul_le_mul_of_nonneg_right hA ht
  have hosc_part : (2 * B) * osc ≤ C * osc :=
    mul_le_mul_of_nonneg_right hB hosc
  calc
    2 * (A * t + B * osc) = (2 * A) * t + (2 * B) * osc := by ring
    _ ≤ C * t + C * osc := add_le_add ht_part hosc_part
    _ = C * (t + osc) := by ring

/-- Constant absorption for the concrete maximal-slice threshold expression. -/
theorem maximalSlice_threshold_le_of_coefficient_bounds {n : ℕ} {C ρ K₀ t osc : ℝ}
    (hK : 2 * (K₀ * (n : ℝ)) ≤ C)
    (hoscCoeff :
      2 * (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 + 1 / (ρ / Real.sqrt (n : ℝ))) ≤ C)
    (ht : 0 ≤ t) (hosc : 0 ≤ osc) :
    2 *
        ((K₀ * t) * (n : ℝ) +
          (osc / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
            osc / (ρ / Real.sqrt (n : ℝ)))) ≤
      C * (t + osc) := by
  have hrewrite :
      (K₀ * t) * (n : ℝ) +
          (osc / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
            osc / (ρ / Real.sqrt (n : ℝ))) =
        (K₀ * (n : ℝ)) * t +
          (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
            1 / (ρ / Real.sqrt (n : ℝ))) * osc := by
    ring
  rw [hrewrite]
  exact two_mul_add_le_mul_add_of_two_mul_le hK hoscCoeff ht hosc

/-- Source-route assembly from concrete localized-maximal slice controls to the packaged
upper-contact decomposition. After this theorem, the remaining work is to construct the slice
second-derivative measures, prove their one-dimensional endpoint control, prove the concrete
total-bad-set estimate, and choose dimensional constants. -/
theorem ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls
    {n : ℕ} {C ρ K₀ : ℝ}
    (hC_nonneg : 0 ≤ C) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hslice :
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ μslice : CoordinateSliceMeasureFamily n,
                CoordinateSliceOneDimEndpointControl u μslice ρ K₀ ∧
                  CoordinateSliceMaximalTotalBadSetEstimate u μslice C t ∧
                    2 *
                        ((K₀ * t) * (n : ℝ) +
                          (sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)) ^ 2 +
                            sourceCubeOscillation n u / (ρ / Real.sqrt (n : ℝ)))) ≤
                      C * (t + sourceCubeOscillation n u)) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine ConvexUpperContactEstimateDecompositionStatement.of_sliceEndpointControl
    (n := n) (C := C) (ρ := ρ) hC_nonneg hρ hρ_le_one ?_
  intro u t ht hbounded hconvex
  rcases hslice u t ht hbounded hconvex with
    ⟨μslice, hendpoint, hmeasure, hthreshold⟩
  refine ⟨coordinateSliceMaximalBadPredicate μslice, K₀ * t, ?_, ?_, hmeasure, hthreshold⟩
  · exact mul_nonneg hK₀ ht.le
  · exact hendpoint.coordinateSliceMaximalEndpointControl hconvex

/-- Coefficient-bound version of
`ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls`. This is the most
convenient source-route entry point after proving the concrete analytic estimates: the final
pointwise threshold inequality follows from two scalar coefficient inequalities and
nonnegativity of `t` and `osc`. -/
theorem ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_of_coefficients
    {n : ℕ} {C ρ K₀ : ℝ}
    (hC_nonneg : 0 ≤ C) (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hKcoeff : 2 * (K₀ * (n : ℝ)) ≤ C)
    (hoscCoeff :
      2 * (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 + 1 / (ρ / Real.sqrt (n : ℝ))) ≤ C)
    (hslice :
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ μslice : CoordinateSliceMeasureFamily n,
                CoordinateSliceOneDimEndpointControl u μslice ρ K₀ ∧
                  CoordinateSliceMaximalTotalBadSetEstimate u μslice C t) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls
    (n := n) (C := C) (ρ := ρ) (K₀ := K₀)
    hC_nonneg hρ hρ_le_one hK₀ ?_
  intro u t ht hbounded hconvex
  rcases hslice u t ht hbounded hconvex with ⟨μslice, hendpoint, hmeasure⟩
  refine ⟨μslice, hendpoint, hmeasure, ?_⟩
  exact maximalSlice_threshold_le_of_coefficient_bounds
    hKcoeff hoscCoeff ht.le (sourceCubeOscillation_nonneg_of_boundedOn hbounded)

/-- Version of
`ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_of_coefficients`
where the concrete total-bad-set estimate is first proved with a smaller measure constant
`Cmeasure`, then enlarged to the final dimensional constant `C`. -/
theorem ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_of_measureConstant
    {n : ℕ} {C Cmeasure ρ K₀ : ℝ}
    (hC_nonneg : 0 ≤ C) (hmeasure_le : Cmeasure ≤ C)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hKcoeff : 2 * (K₀ * (n : ℝ)) ≤ C)
    (hoscCoeff :
      2 * (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 + 1 / (ρ / Real.sqrt (n : ℝ))) ≤ C)
    (hslice :
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ μslice : CoordinateSliceMeasureFamily n,
                CoordinateSliceOneDimEndpointControl u μslice ρ K₀ ∧
                  CoordinateSliceMaximalTotalBadSetEstimate u μslice Cmeasure t) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_of_coefficients
    (n := n) (C := C) (ρ := ρ) (K₀ := K₀)
    hC_nonneg hρ hρ_le_one hK₀ hKcoeff hoscCoeff ?_
  intro u t ht hbounded hconvex
  rcases hslice u t ht hbounded hconvex with ⟨μslice, hendpoint, hmeasure⟩
  exact ⟨μslice, hendpoint, hmeasure.mono_constant_of_boundedOn hmeasure_le ht hbounded⟩

/-- Fully packaged constant-choice version of the concrete maximal-slice route. The final
dimensional constant is chosen as the maximum of the measure constant and the two scalar
coefficients needed for threshold absorption. -/
theorem ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_with_chosenConstant
    {n : ℕ} {Cmeasure ρ K₀ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hslice :
      ∀ (u : SourceCubeSpace n → ℝ) (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            ConvexOn ℝ (sourceOpenCube n 3) u →
              ∃ μslice : CoordinateSliceMeasureFamily n,
                CoordinateSliceOneDimEndpointControl u μslice ρ K₀ ∧
                  CoordinateSliceMaximalTotalBadSetEstimate u μslice Cmeasure t) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  let C : ℝ :=
    max Cmeasure
      (max (2 * (K₀ * (n : ℝ)))
        (2 * (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 + 1 / (ρ / Real.sqrt (n : ℝ)))))
  have hC_nonneg : 0 ≤ C :=
    hCmeasure_nonneg.trans (le_max_left _ _)
  have hmeasure_le : Cmeasure ≤ C :=
    le_max_left _ _
  have hKcoeff : 2 * (K₀ * (n : ℝ)) ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hoscCoeff :
      2 * (1 / (ρ / Real.sqrt (n : ℝ)) ^ 2 + 1 / (ρ / Real.sqrt (n : ℝ))) ≤ C := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  exact
    ConvexUpperContactEstimateDecompositionStatement.of_maximalSliceControls_of_measureConstant
      (n := n) (C := C) (Cmeasure := Cmeasure) (ρ := ρ) (K₀ := K₀)
      hC_nonneg hmeasure_le hρ hρ_le_one hK₀ hKcoeff hoscCoeff hslice

end AleksandrovDifferentiability
