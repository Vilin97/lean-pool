/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ComponentFunctionFieldBoundary
import LeanPool.Stafford38.Stafford38.Geometry.ComponentProjectiveClosureNormalization
import LeanPool.Stafford38.Stafford38.Geometry.ComponentProjectiveOrder
import LeanPool.Stafford38.Stafford38.Geometry.RetainedProjectiveCompletion

/-!
# Exact normalized projective coordinates at a retained boundary place

This file is a small, theorem-only adapter for the finite-gradient geometry
route.  It keeps the residue field and the completed-DVR map supplied by the
retained place, and records the projective normalization, the distinguished
coordinate ratio, and the two zero-residue facts needed by downstream
certificates.
-/

namespace Stafford38.Geometry.CanonicalFiniteGradientProjectiveCoordinates

open IsLocalRing
open Stafford38.Characteristic
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveClosureNormalization
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

/- The common-scale equation is retained explicitly: this is the bridge used
by the homogeneous-equation transport theorem, rather than an opaque
membership assertion about a projective closure. -/
theorem exists_completed_normalized_projective_coordinates
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (P : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hBP : reducedOrderBaseIdeal k I ≤ P.asIdeal)
    (hi : Transcendental k (componentCoordinate P i)) :
    ∃ W : Data k (ComponentFractionField P) (componentCoordinate P i),
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
          (ComponentFractionField P) := W.ambientAlgebra
      ∃ (chart : Fin (n + 1))
        (q : Fin (n + 1) → W.place.valuation.toSubring)
        (scale : ComponentFractionField P),
        scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) ∧
        q (Fin.succ i) = q 0 * W.place.parameter ∧
        (let V := W.place.valuation.toSubring
         letI : IsDiscreteValuationRing V := W.place.isDiscrete
         letI : Algebra W.coefficientField V :=
           (relativeCoefficientMap W.coefficientField W.place).toAlgebra
         let qhat := fun a ↦ retainedToCompletedPowerSeries W (q a)
         let ratio := retainedToCompletedPowerSeries W W.place.parameter
         qhat chart = 1 ∧ qhat 0 ≠ 0 ∧ ratio ≠ 0 ∧
         PowerSeries.constantCoeff (qhat 0) = 0 ∧
         PowerSeries.constantCoeff ratio = 0 ∧
         qhat (Fin.succ i) = qhat 0 * ratio) := by
  have hnormalized := exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace P i hi
  obtain ⟨W, chart, q, scale, hscale, hchart, hzero, hq, hratio⟩ := hnormalized
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  have hzero_nonunit : ¬IsUnit (q 0) :=
    normalizedComponentProjectivePoint_zero_nonunit
      I i hdisjoint P hBP W q scale hq
  refine ⟨W, chart, q, scale, hscale, hchart, hzero, hq, hratio, ?_⟩
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  let : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  have h := retainedCompleted_projective_order_properties W (ι := Fin (n + 1))
    (q := q) (chart := chart) (zero := 0) (axis := Fin.succ i)
    hchart hzero hzero_nonunit hratio
  exact h


end

end Stafford38.Geometry.CanonicalFiniteGradientProjectiveCoordinates
