/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.FullMeasure
public import Mathlib.Analysis.Convex.Continuous

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Statement of the convex Aleksandrov theorem

This file freezes the target theorem surface without asserting the theorem as an axiom.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The target Aleksandrov second order differentiability statement for convex functions.

The statement is intentionally formulated over a finite-dimensional real inner product space,
rather than a matrix space. The almost-everywhere assertion is taken with respect to Lebesgue
measure restricted to the open convex domain.
-/
def ConvexAleksandrovAEStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ᵐ x ∂(volume.restrict Ω), SecondOrderDifferentiableAt u x

/-- Equivalent null-exceptional-set formulation of `ConvexAleksandrovAEStatement`. -/
def ConvexAleksandrovNullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume.restrict Ω (secondOrderBadSet u) = 0

/-- Null-exceptional-set formulation using the exceptional set already intersected with the
domain. -/
def ConvexAleksandrovNullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume (secondOrderBadSetOn Ω u) = 0

/-- Fubini/slicing target for the finite-dimensional proof: for every fixed direction, the set of
base points whose affine-line restriction has scalar quadratic estimate data at the base parameter
has full measure in the domain. -/
def DirectionalLineScalarEstimateFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ξ : E, volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0

/-- Punctured normalized quotient version of
`DirectionalLineScalarEstimateFubiniStatement`. -/
def DirectionalLineScalarQuotientFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ξ : E, volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0

/-- Unit-direction version of `DirectionalLineScalarEstimateFubiniStatement`. Scalar-rescaling
invariance and the zero-direction lemma turn this into the all-directions statement. -/
def DirectionalLineScalarUnitFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ξ : E, ‖ξ‖ = 1 → volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0

/-- Punctured normalized quotient version of
`DirectionalLineScalarUnitFubiniStatement`. -/
def DirectionalLineScalarQuotientUnitFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ ξ : E, ‖ξ‖ = 1 → volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0

/-- The stronger local scalar directional-line Fubini target implies its punctured normalized
quotient version. -/
theorem DirectionalLineScalarEstimateFubiniStatement.quotient
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarEstimateFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u := by
  intro hΩ hu ξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
    (h hΩ hu ξ)

/-- Unit-direction scalar Fubini implies the all-directions scalar Fubini target. -/
theorem DirectionalLineScalarUnitFubiniStatement.fubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarUnitFubiniStatement E Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u := by
  intro hΩ hu ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hc : ‖ξ‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hξ)
    rw [← measure_diff_directionalLineScalarEstimateSet_smul_eq
      (μ := volume) Ω (v := ξ) (c := ‖ξ‖⁻¹) hc u]
    exact h hΩ hu (‖ξ‖⁻¹ • ξ) (norm_inv_norm_smul_eq_one hξ)

/-- Unit-direction quotient Fubini implies the all-directions quotient Fubini target. -/
theorem DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientUnitFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u := by
  intro hΩ hu ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hc : ‖ξ‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hξ)
    rw [← measure_diff_directionalLineScalarQuotientEstimateSet_smul_eq
      (μ := volume) Ω (v := ξ) (c := ‖ξ‖⁻¹) hc u]
    exact h hΩ hu (‖ξ‖⁻¹ • ξ) (norm_inv_norm_smul_eq_one hξ)

/-- The stronger local scalar unit-direction Fubini target implies its punctured normalized
quotient version. -/
theorem DirectionalLineScalarUnitFubiniStatement.quotient
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarUnitFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u := by
  intro hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
    (h hΩ hu ξ hξ)

/-- Slicewise version of `DirectionalLineScalarEstimateFubiniStatement`: for every affine line
parallel to a fixed direction, almost every line parameter gives an ambient base point carrying
scalar estimate data in that same direction. This is the one-dimensional input that a future
finite-dimensional Fubini/disintegration argument should integrate over transverse parameters. -/
def DirectionalLineScalarEstimateSlicewiseStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ x ξ : E, ∀ᵐ t ∂volume.restrict (lineDomain Ω x ξ),
      x + t • ξ ∈ directionalLineScalarEstimateSet ξ u

/-- Punctured normalized quotient version of
`DirectionalLineScalarEstimateSlicewiseStatement`. -/
def DirectionalLineScalarQuotientSlicewiseStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    ∀ x ξ : E, ∀ᵐ t ∂volume.restrict (lineDomain Ω x ξ),
      x + t • ξ ∈ directionalLineScalarQuotientEstimateSet ξ u

/-- The stronger local scalar slicewise target implies its punctured normalized quotient
version. -/
theorem DirectionalLineScalarEstimateSlicewiseStatement.quotient
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarEstimateSlicewiseStatement E Ω u) :
    DirectionalLineScalarQuotientSlicewiseStatement E Ω u := by
  intro hΩ hu x ξ
  exact (h hΩ hu x ξ).mono fun _t ht =>
    directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet ht

/-- The remaining finite-dimensional measure-theoretic transfer for the directional-line scalar
estimate target: slicewise almost-everywhere goodness along every affine line parallel to `ξ`
implies ambient full measure of the fixed-direction good set. -/
def DirectionalLineScalarSlicewiseToFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
    DirectionalLineScalarEstimateFubiniStatement E Ω u

/-- Punctured normalized quotient version of
`DirectionalLineScalarSlicewiseToFubiniStatement`. -/
def DirectionalLineScalarQuotientSlicewiseToFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
    DirectionalLineScalarQuotientFubiniStatement E Ω u

/-- Unit-direction version of `DirectionalLineScalarSlicewiseToFubiniStatement`. Since scalar
directional-line good sets are invariant under nonzero rescaling and the zero direction is
automatic, this is enough for the all-directions transfer. -/
def DirectionalLineScalarUnitSlicewiseToFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
    DirectionalLineScalarUnitFubiniStatement E Ω u

/-- Unit-direction quotient version of `DirectionalLineScalarSlicewiseToFubiniStatement`. -/
def DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) : Prop :=
  DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u

/-- A unit-direction slicewise-to-Fubini transfer gives the all-directions transfer. -/
theorem DirectionalLineScalarUnitSlicewiseToFubiniStatement.fubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarUnitFubiniStatement.fubiniStatement E (h hslice)

/-- Quotient version of
`DirectionalLineScalarUnitSlicewiseToFubiniStatement.fubiniStatement`. -/
theorem DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement.fubiniStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E (h hslice)

/-- Finite-family version of the slicewise-to-Fubini transfer tailored to the polarization
argument. It asks only for ambient full measure in the selected pure directions `v i` and in the
off-diagonal pairwise-sum directions `v i + v j`. -/
def FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
    IsOpen Ω → ConvexOn ℝ Ω u →
      (∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
      (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
        volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0)

/-- Punctured normalized quotient version of
`FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement`. -/
def FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
    IsOpen Ω → ConvexOn ℝ Ω u →
      (∀ ⦃i : ι⦄, i ∈ D →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
      (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
        volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)

/-- Compatible finite-slice full-measure target: for a chosen finite direction family, the set of
base points carrying scalar line estimates with one shared ambient first-order slope has full
measure in the domain. This is stronger than the raw linewise Fubini target and is the natural
input for compatible finite-dimensional reconstruction. -/
def CompatibleDirectionalSliceFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume (Ω \ compatibleDirectionalSliceEstimateSet D v u) = 0

/-- Punctured normalized quotient version of
`CompatibleDirectionalSliceFullMeasureStatement`. -/
def CompatibleDirectionalSliceQuotientFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0

/-- Symmetric-compatible finite-slice full-measure target. This is the same compatible
first-order finite-slice data, with pairwise-sum quadratic coefficients already symmetrized on the
finite frame. -/
def SymmetricCompatibleDirectionalSliceFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume (Ω \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0

/-- Punctured normalized quotient version of
`SymmetricCompatibleDirectionalSliceFullMeasureStatement`. -/
def SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E) : Prop :=
  IsOpen Ω → ConvexOn ℝ Ω u →
    volume (Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0

/-- The non-quotient compatible finite-slice full-measure target implies its quotient version. -/
theorem CompatibleDirectionalSliceFullMeasureStatement.quotient
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v) :
    CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_compatibleDirectionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
    D v (h hΩ hu)

/-- Compatible full-measure slice data implies full measure of the symmetrized compatible
finite-slice locus. -/
theorem CompatibleDirectionalSliceFullMeasureStatement.symmetric
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v) :
    SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_symmetricCompatibleSliceSet_eq_zero_of_compatibleSliceSet
    D v (h hΩ hu)

/-- Compatible quotient full-measure slice data implies full measure of the symmetrized compatible
quotient finite-slice locus. -/
theorem CompatibleDirectionalSliceQuotientFullMeasureStatement.symmetric
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
    D v (h hΩ hu)

/-- Non-quotient compatible full-measure slice data implies full measure of the symmetrized
compatible quotient finite-slice locus. -/
theorem CompatibleDirectionalSliceFullMeasureStatement.symmetricQuotient
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceFullMeasureStatement D E Ω u v) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceSet
    D v (h hΩ hu)

/-- Symmetric-compatible full-measure slice data implies its punctured normalized quotient
version with the same symmetric finite-slice data. -/
theorem SymmetricCompatibleDirectionalSliceFullMeasureStatement.quotient
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_symmetricSliceSet
    D v (h hΩ hu)


end AleksandrovDifferentiability
