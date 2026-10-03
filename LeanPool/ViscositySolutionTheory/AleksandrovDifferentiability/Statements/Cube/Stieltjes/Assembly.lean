/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Controls

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Concrete Stieltjes upper-contact estimate assembly
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

namespace ConvexUpperContactEstimateDecompositionStatement

/-- Source-route assembly theorem for the concrete convex source-local Stieltjes slice family.

This packages the current state of the upper-contact estimate route: once first differentiability
a.e., the one-dimensional endpoint-control estimate, the Fubini estimate, and the scalar measure
constant comparison are supplied for the concrete Stieltjes slices, the abstract upper-contact
decomposition follows with the chosen dimensional constant from `Cube.Maximal`. -/
theorem of_convexSourceRightDerivStieltjesControls_with_chosenConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ K₀ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hendpoint :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ K₀)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hbound :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            (n : ENNReal) *
                ENNReal.ofReal (Ccoord * sourceCubeOscillation n u / t) ≤
              ENNReal.ofReal (Cmeasure * sourceCubeOscillation n u / t)) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine
    of_maximalSliceControls_with_chosenConstant
      (n := n) (Cmeasure := Cmeasure) (ρ := ρ) (K₀ := K₀)
      hCmeasure_nonneg hρ hρ_le_one hK₀ ?_
  intro u t ht hbounded hu
  let μslice := coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu
  refine ⟨μslice, ?_, ?_⟩
  · exact
      (hendpoint hu hbounded).coordinateSliceOneDimEndpointControl
  · exact
      CoordinateSliceMaximalTotalBadSetEstimate.of_convexSourceRightDerivStieltjes_boundedOn
        (n := n) (u := u) (Cmax := Cmax) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (t := t)
        (hdiff hbounded hu) hu hbounded hmax ht
        (hfubini hu t ht hbounded) (hbound (u := u) t ht hbounded)

/-- Source-route assembly theorem for the concrete convex source-local Stieltjes slice family,
with the finite-union measure constant supplied as the source-style real coefficient inequality
`(n : ℝ) * Ccoord ≤ Cmeasure`. -/
theorem of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ K₀ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hendpoint :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ K₀)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n := by
  refine
    of_maximalSliceControls_with_chosenConstant
      (n := n) (Cmeasure := Cmeasure) (ρ := ρ) (K₀ := K₀)
      hCmeasure_nonneg hρ hρ_le_one hK₀ ?_
  intro u t ht hbounded hu
  let μslice := coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu
  refine ⟨μslice, ?_, ?_⟩
  · exact
      (hendpoint hu hbounded).coordinateSliceOneDimEndpointControl
  · exact
      CoordinateSliceMaximalTotalBadSetEstimate.of_convexStieltjes_boundedOn_measureConstant
        (n := n) (u := u) (Cmax := Cmax) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (t := t)
        (hdiff hbounded hu) hu hbounded hmax ht
        (hfubini hu t ht hbounded) hmeasure

/-- Source-route assembly from symmetric-remainder estimates for the concrete convex
source-local Stieltjes slice family. The one-dimensional endpoint constant is fixed to `2`,
because the maximal non-bad estimate controls the symmetric interval mass by `t * (2*h)`. -/
theorem of_convexSourceRightDerivStieltjesSymmetricRemainderControls_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hrem :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesSymmetricRemainderBound u hu ρ)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ) (K₀ := 2)
    hCmeasure_nonneg hρ hρ_le_one (by norm_num) hmeasure hmax hdiff
    (fun {u} hu hbounded =>
      (hrem (u := u) hu hbounded).endpointControl hρ_le_one)
    hfubini

/-- Source-route assembly from endpoint comparison bounds for the concrete convex source-local
Stieltjes slice family. -/
theorem of_convexSourceRightDerivStieltjesEndpointBounds_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hbounds :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds u hu ρ)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ) (K₀ := 2)
    hCmeasure_nonneg hρ hρ_le_one (by norm_num) hmeasure hmax hdiff
    (fun {u} hu hbounded =>
      (hbounds (u := u) hu hbounded).endpointControl hρ_le_one)
    hfubini

/-- Source-route assembly from exact endpoint identities for the concrete convex source-local
Stieltjes slice family. -/
theorem of_convexSourceRightDerivStieltjesEndpointIdentities_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hident :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u),
        BoundedOn (sourceOpenCube n 3) u →
          CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities u hu ρ)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjesEndpointBounds_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax hdiff
    (fun {u} hu hbounded =>
      (hident (u := u) hu hbounded).endpointBounds)
    hfubini

/-- Source-route assembly for the concrete convex source-local Stieltjes slice family.

This is the current source-faithful cube wrapper: convexity supplies the one-dimensional
Stieltjes endpoint-control input, so the remaining analytic assumptions are first differentiability
a.e., the localized maximal estimate, the Fubini estimate for the coordinate maximal bad fibers,
and the scalar finite-union constant comparison. -/
theorem of_convexSourceRightDerivStieltjes_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjesControls_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ) (K₀ := 2)
    hCmeasure_nonneg hρ hρ_le_one (by norm_num) hmeasure hmax hdiff
    (fun {u} hu _hbounded =>
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl.of_convex
        (u := u) (hu := hu) hρ_le_one)
    hfubini

/-- Shorter alias for the concrete convex source-local Stieltjes decomposition route. -/
theorem of_convexStieltjes_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexSourceRightDerivStieltjes_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax hdiff hfubini

/-- Concrete convex source-local Stieltjes decomposition route after discharging the
first-differentiability-a.e. input by Rademacher and local Lipschitz regularity of convex
functions. The remaining analytic input is the coordinate Fubini estimate for the localized
maximal bad fibers. -/
theorem of_convexStieltjes_of_fubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax
    (fun {_u} _hbounded hu =>
      ConvexOn.volume_sourceOpenCube_diff_firstOrderDifferentiabilitySet_eq_zero hu)
    hfubini

/-- Concrete convex source-local Stieltjes decomposition route from the sharper transverse
Fubini boundary. This leaves the remaining Fubini work in the source-proof form: a product
measure estimate with transverse constant `Ctrans`, plus the scalar comparison
`Ctrans * (2 * Cmax) <= Ccoord`. -/
theorem of_convexStieltjes_of_transverseFubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (htrans :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalTransverseFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              Ctrans t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_fubini_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
    (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hmax
    (fun {u} hu t ht hbounded =>
      (htrans (u := u) hu t ht hbounded).fubiniEstimate
        hCtrans_nonneg hfubiniConst
        (div_nonneg (sourceCubeOscillation_nonneg_of_boundedOn hbounded) ht.le))

/-- Concrete convex source-local Stieltjes decomposition route from measurability of the
coordinate maximal bad sets. The canonical coordinate charts are already measure-preserving;
this wrapper leaves only the genuine analytic measurability obligation plus scalar constants. -/
theorem of_convexStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hbad :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_transverseFubini_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      CoordinateSliceMaximalTransverseFubiniEstimate.of_badSetMeasurable
        (hbad (u := u) hu t ht hbounded) hAmeasure)

/-- Concrete convex source-local Stieltjes decomposition route from measurability of the
interval-average-exceeds set. This is the current sharp source-facing measurability input for
the Fubini step. -/
theorem of_convexStieltjes_of_averageExceedsMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (havg :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t) :
    ConvexUpperContactEstimateDecompositionStatement n :=
  of_convexStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
    (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
    (Cmeasure := Cmeasure) (ρ := ρ)
    hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
    hAmeasure hfubiniConst hmax
    (fun {u} hu t ht hbounded =>
      (havg (u := u) hu t ht hbounded).badSetMeasurable)

end ConvexUpperContactEstimateDecompositionStatement

namespace ConvexUpperContactEstimateStatement

/-- Packaged upper-contact estimate from the concrete convex source-local Stieltjes route.

Convexity supplies the coordinate Stieltjes endpoint-control input. The remaining hypotheses are
the first-differentiability-a.e. input, the localized maximal estimate, the coordinate Fubini
estimate for the localized maximal bad fibers, and the scalar finite-union constant comparison. -/
theorem of_convexSourceRightDerivStieltjes_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hdiff :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄,
        BoundedOn (sourceOpenCube n 3) u →
          ConvexOn ℝ (sourceOpenCube n 3) u →
            volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (ConvexUpperContactEstimateDecompositionStatement.of_convexStieltjes_with_chosenMeasureConstant
      (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
      (ρ := ρ)
      hCmeasure_nonneg hρ hρ_le_one hmeasure hmax hdiff hfubini)

/-- Packaged upper-contact estimate from the concrete convex source-local Stieltjes route after
discharging first differentiability a.e. The remaining analytic input is the coordinate Fubini
estimate for the localized maximal bad fibers. -/
theorem of_convexSourceRightDerivStieltjes_of_fubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hfubini :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              (2 * Cmax) Ccoord (sourceCubeOscillation n u) t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (by
      open ConvexUpperContactEstimateDecompositionStatement in
      exact of_convexStieltjes_of_fubini_with_chosenMeasureConstant
        (n := n) (Cmax := Cmax) (Ccoord := Ccoord) (Cmeasure := Cmeasure)
        (ρ := ρ)
        hCmeasure_nonneg hρ hρ_le_one hmeasure hmax hfubini)

/-- Packaged upper-contact estimate from the sharper transverse Fubini boundary. -/
theorem of_convexSourceRightDerivStieltjes_of_transverseFubini_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (htrans :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceMaximalTransverseFubiniEstimate
              (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
              Ctrans t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (by
      open ConvexUpperContactEstimateDecompositionStatement in
      exact of_convexStieltjes_of_transverseFubini_with_chosenMeasureConstant
        (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (ρ := ρ)
        hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
        hfubiniConst hmax htrans)

/-- Packaged upper-contact estimate from measurability of the concrete convex source-local
Stieltjes maximal bad sets. -/
theorem of_convexSourceRightDerivStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (hbad :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (by
      open ConvexUpperContactEstimateDecompositionStatement in
      exact of_convexStieltjes_of_badSetMeasurable_with_chosenMeasureConstant
        (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (ρ := ρ)
        hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
        hAmeasure hfubiniConst hmax hbad)

/-- Packaged upper-contact estimate from measurability of the concrete convex source-local
Stieltjes interval-average-exceeds sets. -/
theorem of_convexSourceRightDerivStieltjes_of_averageExceedsMeasurable_with_chosenMeasureConstant
    {n : ℕ} {Cmax Ctrans Ccoord Cmeasure ρ : ℝ}
    (hCmeasure_nonneg : 0 ≤ Cmeasure)
    (hρ : 0 < ρ) (hρ_le_one : ρ ≤ 1)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hfubiniConst : Ctrans * (2 * Cmax) ≤ Ccoord)
    (hmax : LocalizedMaximalEstimateStatement Cmax)
    (havg :
      ∀ ⦃u : SourceCubeSpace n → ℝ⦄ (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
        (t : ℝ),
        0 < t →
          BoundedOn (sourceOpenCube n 3) u →
            CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t) :
    ConvexUpperContactEstimateStatement n :=
  ConvexUpperContactEstimateStatement.of_decomposition
    (by
      open ConvexUpperContactEstimateDecompositionStatement in
      exact of_convexStieltjes_of_averageExceedsMeasurable_with_chosenMeasureConstant
        (n := n) (Cmax := Cmax) (Ctrans := Ctrans) (Ccoord := Ccoord)
        (Cmeasure := Cmeasure) (ρ := ρ)
        hCmeasure_nonneg hρ hρ_le_one hmeasure hCtrans_nonneg
        hAmeasure hfubiniConst hmax havg)

end ConvexUpperContactEstimateStatement

end AleksandrovDifferentiability
