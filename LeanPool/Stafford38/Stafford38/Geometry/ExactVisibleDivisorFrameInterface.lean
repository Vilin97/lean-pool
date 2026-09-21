/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CanonicalFiniteGradientProjectiveCoordinates
import LeanPool.Stafford38.Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction

/-!
# Exact visible-divisor-frame interface

A bare DVR, coefficient field, and residue-field finiteness do not by
themselves produce the retained `Data`, normalized projective column, and
`VisibleDivisorFrame` required by `HasVisibleDivisorFrame`.

The repository already constructs the retained `Data` and the normalized
column, including the exact parameter identity.  The first unsupported bridge
is therefore isolated as `HasCompatibleVisibleFrame`: a visible differential
frame on that same retained column.  Its divisor parameter `D.t` is independent
of `W.place.parameter`: the former may be chosen as a genuine DVR uniformizer,
whereas the retained coordinate can have higher valuation after ramification.

The exact producer is supplied separately by
`ExactDivisorialVisibleFrameExistence`.
-/

namespace Stafford38.Geometry.ExactVisibleDivisorFrameInterface

open IsLocalRing
open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CanonicalFiniteGradientProjectiveCoordinates
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u


variable {k : Type u} [Field k] {m : ℕ}

/-- The exact missing datum after a retained place and normalized projective
column have been fixed: a visible differential frame on that same column.
Constructing it still requires a finite differential lattice containing the
unit and coordinate differentials and the explicit modulo-`D.t` inclusion
stored in `D.visible`. -/
def HasCompatibleVisibleFrame
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    [CharZero k]
    (W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩)) :
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  (Fin (m + 1) → W.place.valuation.toSubring) → Prop := by
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    exact fun q ↦
      ∃ D : VisibleDivisorFrame (V := V)
          (KaehlerDifferential.D k (ComponentFractionField P)) (Fin m),
        D.Q₀ = q 0 ∧
          D.Q₁ = q (Fin.succ ⟨0, hm⟩) ∧
          ∀ j, D.Q j = q (Fin.succ j)

/-- Once the compatible frame is supplied, the retained data, common-scale
normalization, and exact parameter identity are exactly the fields required by
`HasVisibleDivisorFrame`. -/
theorem hasVisibleDivisorFrame_of_compatible_normalized_column
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    (W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩)) :
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    ∀ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
      q 0 ≠ 0 →
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) →
      q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter →
      HasCompatibleVisibleFrame P hm W q →
      HasVisibleDivisorFrame P hm := by
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  dsimp only
  intro q scale hq0 hq hratio hframe
  obtain ⟨D, hQ₀, hQ₁, hQ⟩ := hframe
  exact ⟨W, q, scale, hq0, hq, hratio, D, hQ₀, hQ₁, hQ⟩

/-- Trust-zero prefix: the existing component theorem supplies the retained
`Data`, a normalized projective column, and the exact parameter identity.  For
the very same witnesses, a compatible visible frame is sufficient and is the
only remaining premise. -/
theorem exists_normalized_column_with_exact_frame_obligation
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    (hi : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩),
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
          (ComponentFractionField P) := W.ambientAlgebra
      let V := W.place.valuation.toSubring
      letI : IsDiscreteValuationRing V := W.place.isDiscrete
      ∃ (chart : Fin (m + 1)) (q : Fin (m + 1) → V)
          (scale : ComponentFractionField P),
        scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) ∧
        q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter ∧
        (HasCompatibleVisibleFrame P hm W q → HasVisibleDivisorFrame P hm) := by
  obtain ⟨W, chart, q, scale, hscale, hchart, hq0, hq, hratio⟩ :=
    exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace P ⟨0, hm⟩ hi
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  refine ⟨W, chart, q, scale, hscale, hchart, hq0, hq, hratio, ?_⟩
  exact hasVisibleDivisorFrame_of_compatible_normalized_column P hm W q scale
    hq0 hq hratio

/-- In the actual axis-avoidance context, the existing trust-zero prefix also
forces the normalized denominator to be a nonunit.  Together with the retained
parameter's nonzero/nonunit fields, this supplies the order-theoretic inputs;
the compatible visible frame remains the first gap. -/
theorem exists_axisAvoiding_normalized_column_with_exact_frame_obligation
    [CharZero k] [IsAlgClosed k]
    (I : RightIdeal (PresentedWeyl k m)) (hm : 0 < m)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (⟨0, hm⟩ : Fin m))} : Set (SymbolRing k m))))
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hBP : reducedOrderBaseIdeal k I ≤ P.asIdeal)
    (hi : Transcendental k (componentCoordinate P ⟨0, hm⟩)) :
    ∃ W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩),
      letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
          (ComponentFractionField P) := W.ambientAlgebra
      let V := W.place.valuation.toSubring
      letI : IsDiscreteValuationRing V := W.place.isDiscrete
      ∃ (chart : Fin (m + 1)) (q : Fin (m + 1) → V)
          (scale : ComponentFractionField P),
        scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
        (∀ a, (q a : ComponentFractionField P) =
          scale * componentProjectivePoint P a) ∧
        q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter ∧
        ¬ IsUnit (q 0) ∧
        (HasCompatibleVisibleFrame P hm W q → HasVisibleDivisorFrame P hm) := by
  obtain ⟨W, chart, q, scale, hscale, hchart, hq0, hq, hratio⟩ :=
    exists_normalizedProjectivePoint_relativeRetainedBoundaryPlace P ⟨0, hm⟩ hi
  let : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  let : IsDiscreteValuationRing V := W.place.isDiscrete
  have hq0nonunit : ¬ IsUnit (q 0) :=
    normalizedComponentProjectivePoint_zero_nonunit
      I ⟨0, hm⟩ hdisjoint P hBP W q scale hq
  refine ⟨W, chart, q, scale, hscale, hchart, hq0, hq, hratio,
    hq0nonunit, ?_⟩
  exact hasVisibleDivisorFrame_of_compatible_normalized_column P hm W q scale
    hq0 hq hratio

/-- The exact geometric witness missing after the trust-zero retained-place
prefix.  Unlike `DivisorialVisibleFrameExistence`, this retains the same
`Data`, the normalized projective column, its exact parameter identity, and a
`VisibleDivisorFrame` attached to that column. -/
def HasNormalizedCompatibleVisibleFrame
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m) : Prop :=
  ∃ W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩),
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    ∃ (chart : Fin (m + 1)) (q : Fin (m + 1) → V)
        (scale : ComponentFractionField P),
      scale ≠ 0 ∧ q chart = 1 ∧ q 0 ≠ 0 ∧
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) ∧
      q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter ∧
      HasCompatibleVisibleFrame P hm W q

/-- The exact witness above forgets to the pre-existing terminal input. -/
theorem hasVisibleDivisorFrame_of_normalizedCompatibleVisibleFrame
    [CharZero k]
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    (h : HasNormalizedCompatibleVisibleFrame P hm) :
    HasVisibleDivisorFrame P hm := by
  obtain ⟨W, chart, q, scale, hscale, hchart, hq0, hq, hratio, hframe⟩ := h
  exact hasVisibleDivisorFrame_of_compatible_normalized_column P hm W q scale
    hq0 hq hratio hframe

/-- Repaired residual with exactly the ambient hypotheses of the actual lane C
consumer.  The target-context hypotheses are retained because, in particular,
axis avoidance is needed to force the homogeneous denominator to vanish; the
component-only strengthening is false in general. -/
def ExactDivisorialVisibleFrameExistence : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)),
    0 < n →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    ∀ P : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k),
      P.asIdeal ∈
        (reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)).minimalPrimes →
      Transcendental k
        (componentCoordinate P ⟨0, Nat.zero_lt_succ n⟩) →
      HasNormalizedCompatibleVisibleFrame P (Nat.zero_lt_succ n)

/-- The repaired residual has a direct, trust-zero adapter to the actual
higher-dimensional producer. -/
theorem higherDimensionalCanonicalVisibleDivisorFrameProduction_of_exactResidual
    (h : ExactDivisorialVisibleFrameExistence.{u}) :
    HigherDimensionalCanonicalVisibleDivisorFrameProduction.{u} := by
  intro k _ _ _ n N d hn hdisjoint P hP htrans
  exact hasVisibleDivisorFrame_of_normalizedCompatibleVisibleFrame P
    (Nat.zero_lt_succ n) (h k n N d hn hdisjoint P hP htrans)


end

end Stafford38.Geometry.ExactVisibleDivisorFrameInterface
