/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.Reconstruction
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.LineScalar

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Full-measure directional estimate assembly

This file turns directional scalar estimate sets and mixed-directional quadratic reconstruction
data into full-measure second-order differentiability statements.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [MeasurableSpace E]

/-- The zero-direction scalar estimate set has null complement inside every domain. -/
theorem measure_diff_directionalLineScalarEstimateSet_zero
    {μ : Measure E} (s : Set E) (u : E → ℝ) :
    μ (s \ directionalLineScalarEstimateSet (0 : E) u) = 0 := by
  simp

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_zero`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_zero
    {μ : Measure E} (s : Set E) (u : E → ℝ) :
    μ (s \ directionalLineScalarQuotientEstimateSet (0 : E) u) = 0 := by
  simp

/-- Almost-everywhere zero-direction scalar estimate membership inside every domain. -/
theorem ae_restrict_mem_directionalLineScalarEstimateSet_zero
    {μ : Measure E} (s : Set E) (u : E → ℝ) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarEstimateSet (0 : E) u := by
  filter_upwards with x
  exact mem_directionalLineScalarEstimateSet_zero u x

/-- Quotient-estimate version of
`ae_restrict_mem_directionalLineScalarEstimateSet_zero`. -/
theorem ae_restrict_mem_directionalLineScalarQuotientEstimateSet_zero
    {μ : Measure E} (s : Set E) (u : E → ℝ) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarQuotientEstimateSet (0 : E) u := by
  filter_upwards with x
  exact mem_directionalLineScalarQuotientEstimateSet_zero u x

/-- Nonzero scalar rescaling of the direction preserves the null complement of the scalar
directional-line good set. -/
theorem measure_diff_directionalLineScalarEstimateSet_smul_eq
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    μ (s \ directionalLineScalarEstimateSet (c • v) u) =
      μ (s \ directionalLineScalarEstimateSet v u) := by
  rw [directionalLineScalarEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_smul_eq`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_smul_eq
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    μ (s \ directionalLineScalarQuotientEstimateSet (c • v) u) =
      μ (s \ directionalLineScalarQuotientEstimateSet v u) := by
  rw [directionalLineScalarQuotientEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Almost-everywhere scalar directional-line membership is invariant under nonzero scalar
rescaling of the direction. -/
theorem ae_restrict_mem_directionalLineScalarEstimateSet_smul_iff
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    (∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarEstimateSet (c • v) u) ↔
      ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarEstimateSet v u := by
  rw [directionalLineScalarEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Quotient-estimate version of
`ae_restrict_mem_directionalLineScalarEstimateSet_smul_iff`. -/
theorem ae_restrict_mem_directionalLineScalarQuotientEstimateSet_smul_iff
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    (∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarQuotientEstimateSet (c • v) u) ↔
      ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarQuotientEstimateSet v u := by
  rw [directionalLineScalarQuotientEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Full measure of the fixed-direction scalar estimate good set implies full measure of the
corresponding punctured normalized quotient good set. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
    {μ : Measure E} {s : Set E} {v : E} {u : E → ℝ}
    (hnull : μ (s \ directionalLineScalarEstimateSet v u) = 0) :
    μ (s \ directionalLineScalarQuotientEstimateSet v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet hnull

/-- Full measure of the local mixed-directional quadratic estimate set implies full measure of its
punctured normalized quotient-estimate version. -/
theorem measure_diff_mixedDirectionalQuadraticQuotientSet_eq_zero_of_estimateSet
    {ι : Type*} {μ : Measure E} {s : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull : μ (s \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    μ (s \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    mixedDirectionalQuadraticEstimateSet_subset_mixedDirectionalQuadraticQuotientSet hnull

/-- Full measure of the local polarized mixed-directional quadratic estimate set implies full
measure of its punctured normalized quotient-estimate version. -/
theorem measure_diff_polarizedMixedDirectionalQuotientSet_eq_zero_of_estimateSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E}
    {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull : μ (s \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    μ (s \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    polarizedMixedDirectionalQuadraticSet_subset_polarizedMixedDirectionalQuadraticQuotientSet
    hnull

/-- Almost-everywhere membership in the fixed-direction scalar estimate good set implies
almost-everywhere membership in the corresponding quotient good set. -/
theorem ae_restrict_mem_directionalLineScalarQuotientEstimateSet_of_estimateSet
    {μ : Measure E} {s : Set E} {v : E} {u : E → ℝ}
    (h : ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarEstimateSet v u) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalLineScalarQuotientEstimateSet v u :=
  h.mono fun _x hx =>
    directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet hx

/-- Almost-everywhere membership in the mixed-directional estimate good set implies
almost-everywhere membership in the corresponding quotient good set. -/
theorem ae_restrict_mem_mixedDirectionalQuadraticQuotientSet_of_estimateSet
    {ι : Type*} {μ : Measure E} {s : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (h : ∀ᵐ x ∂μ.restrict s, x ∈ mixedDirectionalQuadraticEstimateSet D v u) :
    ∀ᵐ x ∂μ.restrict s, x ∈ mixedDirectionalQuadraticQuotientEstimateSet D v u :=
  h.mono fun _x hx =>
    mixedDirectionalQuadraticEstimateSet_subset_mixedDirectionalQuadraticQuotientSet hx

/-- Almost-everywhere membership in the polarized mixed-directional estimate good set implies
almost-everywhere membership in the corresponding quotient good set. -/
theorem ae_restrict_mem_polarizedMixedDirectionalQuotientSet_of_estimateSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E}
    {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (h : ∀ᵐ x ∂μ.restrict s, x ∈ polarizedMixedDirectionalQuadraticEstimateSet D v u) :
    ∀ᵐ x ∂μ.restrict s,
      x ∈ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u :=
  h.mono fun _x hx =>
    polarizedMixedDirectionalQuadraticSet_subset_polarizedMixedDirectionalQuadraticQuotientSet hx

/-- Finite bookkeeping for directional slices: if each selected pure direction and each selected
pairwise-sum direction has scalar estimate data on a full-measure subset of `s`, then the bundled
finite directional slice target holds a.e. on `s`. -/
theorem ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, x ∈ directionalLineScalarEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpair hi hj)
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact ⟨(fun i hi => hpurex i hi), (fun i hi j hj => hpairx i hi j hj)⟩

/-- Null-complement form of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure`. -/
theorem measure_diff_directionalSliceEstimateSet_eq_zero_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure hs D v hpure hpair)

/-- Off-diagonal version of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure`: pairwise full-measure
hypotheses are only needed when the two selected directions are different. -/
theorem ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, i ≠ j →
          x ∈ directionalLineScalarEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    by_cases hij : i ≠ j
    · filter_upwards [ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs
          (hpair hi hj hij)] with x hx
      intro _hij
      exact hx
    · exact Filter.Eventually.of_forall fun _x hij' => (hij hij').elim
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact directionalSliceEstimateAt_of_pure_offDiagonal
    (by
      intro i hi
      exact hpurex i hi)
    (by
      intro i hi j hj hij
      exact hpairx i hi j hj hij)

/-- Null-complement form of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure_offDiagonal`. -/
theorem measure_diff_directionalSliceSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)

/-- Quotient-estimate version of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure`. -/
theorem ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceQuotientEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarQuotientEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, x ∈ directionalLineScalarQuotientEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpair hi hj)
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact ⟨(fun i hi => hpurex i hi), (fun i hi j hj => hpairx i hi j hj)⟩

/-- Null-complement form of
`ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure`. -/
theorem measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure hs D v hpure hpair)

/-- Non-quotient scalar line full-measure hypotheses imply full measure of the finite quotient
slice target. -/
theorem measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLineEstimate_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure hs D v
    (fun {i} hi =>
      measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
        (hpure (i := i) hi))
    (fun {i} hi {j} hj =>
      measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
        (hpair (i := i) hi (j := j) hj))

/-- Off-diagonal quotient-estimate version of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure_offDiagonal`. -/
theorem ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceQuotientEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarQuotientEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, i ≠ j →
          x ∈ directionalLineScalarQuotientEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    by_cases hij : i ≠ j
    · filter_upwards [ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs
          (hpair hi hj hij)] with x hx
      intro _hij
      exact hx
    · exact Filter.Eventually.of_forall fun _x hij' => (hij hij').elim
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact directionalSliceQuotientEstimateAt_of_pure_offDiagonal
    (by
      intro i hi
      exact hpurex i hi)
    (by
      intro i hi j hj hij
      exact hpairx i hi j hj hij)

/-- Null-complement form of
`ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure_offDiagonal`. -/
theorem measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)

/-- Off-diagonal version of
`measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLineEstimate_fullMeasure`. -/
theorem
    measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLineEstimate_fullMeasure_offDiag
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
    hs D v
    (fun {i} hi =>
      measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
        (hpure (i := i) hi))
    (fun {i} hi {j} hj hij =>
      measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
        (hpair (i := i) hi (j := j) hj hij))

/-- Full measure of the compatible finite slice target implies full measure of the compatible
finite quotient-slice target. -/
theorem measure_diff_compatibleDirectionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceQuotientEstimateSet
    hnull

/-- Full measure of the compatible finite slice target also implies full measure of the older
existential finite quotient-slice target. -/
theorem measure_diff_directionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceEstimateSet_subset_directionalSliceQuotientEstimateSet
    hnull

/-- Full measure of the compatible finite slice target implies full measure of the symmetric
compatible finite slice target. -/
theorem measure_diff_symmetricCompatibleSliceSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleDirectionalSliceEstimateSet
    hnull

/-- Full measure of the compatible finite quotient-slice target implies full measure of the
symmetric compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceQuotientSet_subset_symmetricCompatibleDirectionalSliceQuotientSet
    hnull

/-- Full measure of the compatible finite slice target implies full measure of the symmetric
compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
    D v
    (measure_diff_compatibleDirectionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
      D v hnull)

/-- Full measure of the symmetric compatible finite slice target implies full measure of the
symmetric compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_symmetricSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    symmetricCompatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleQuotientSet
    hnull

end AleksandrovDifferentiability
