/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.SpecializedNoncharacteristicEquality
import LeanPool.Stafford38.Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction
import LeanPool.Stafford38.Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
import LeanPool.Stafford38.Stafford38.Weyl.FilteredScalarLifting
import LeanPool.Stafford38.Stafford38.FixedSourceAssembly

/-!
# Typed assembly interfaces for the paper proof

This module packages three application interfaces used by the canonical Weyl
construction. The first two include the characteristic-support and symbol
dictionaries; the third supplies a retained boundary place with a visible
divisor frame on each nonconstant component.

`Stafford38.FoundationClosure` proves every field and imports this module on
the ordinary root dependency path. No field is installed as an axiom or
typeclass. The assembly theorems here remain conditional when considered in
isolation; their hypotheses are discharged by the unconditional development.
-/

namespace Stafford38.PaperInputs

open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.CharacteristicTransposedFilteredModuleSupport
open Stafford38.EulerSurjectivity
open Stafford38.SpecializedNoncharacteristicEquality
open Stafford38.Geometry.CanonicalResidueExtensionAssembly
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylEulerResidue
open Stafford38.WeylPBWMonicBridge
open Stafford38.Weyl.FilteredScalarLifting

universe u

/-- Exact Stafford-specific output of the noncharacteristic inverse-image
application.  This is support avoidance, not the stronger filtered predecessor
to which it is converted by a separate trust-zero algebraic theorem. -/
def CanonicalNoncharacteristicSupportAvoidance : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      Disjoint
        (transposedOrderAssociatedGradedSupport k
          (canonicalRightIdeal (presentedCoordinate k n) d N))
        (PrimeSpectrum.zeroLocus
          ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
            Set (SymbolRing k (n + 1))))

/-- Assembly interfaces whose fields are proved in `Stafford38.FoundationClosure`. -/
structure Inputs : Prop where
  noncharacteristicApplication :
    CanonicalNoncharacteristicSupportAvoidance.{u}
  residueExtensionSymbolControl :
    CanonicalResidueExtensionSymbolControl.{u}
  higherDimensionalVisibleDivisorFrameProduction :
    HigherDimensionalCanonicalVisibleDivisorFrameProduction.{u}

/-- Canonical support vanishes under the three explicit paper inputs.
This theorem is conditional and introduces no project axiom. -/
theorem canonicalSupportVanishing_of_inputs (h : Inputs.{u}) :
    Stafford38.UniversalAssembly.CanonicalSupportVanishing.{u} := by
  let hunit : CanonicalStrictUnitCoordinatePreimage.{u} := by
    intro k _ _ _ n N d hN hd
    exact strictUnitCoordinatePreimage_of_transposedSupport_disjoint_axis
      k n N d (h.noncharacteristicApplication k n N d hN hd)
  exact canonicalSupportDescent
      (algebraicallyClosedCanonicalSupportVanishing_of_residueExtension_rankSplit
        hunit h.residueExtensionSymbolControl
          (higherDimensionalCanonicalResidueExtensionConormalAxisProduction_of_nonconstantFiniteGradient
            (higherDimensionalCanonicalResidueExtensionNonconstantFiniteGradientProduction_of_visibleDivisorFrame
              h.higherDimensionalVisibleDivisorFrameProduction)))

/-- The universal identity under the explicit paper inputs. -/
theorem universalStatement_of_inputs (h : Inputs.{u}) :
    Stafford38.UniversalStatement.{u} :=
  Stafford38.UniversalAssembly.universalStatement_of_canonicalSupportVanishing
    (canonicalSupportVanishing_of_inputs h)

/-- The stronger paper statement, with the exact Bernstein exponent. -/
theorem universalFixedSourceStatement_of_inputs (h : Inputs.{u}) :
    Stafford38.FixedSource.UniversalFixedSourceStatement.{u} :=
  Stafford38.FixedSource.universalFixedSourceStatement_of_canonicalSupportVanishing
    (canonicalSupportVanishing_of_inputs h)


end Stafford38.PaperInputs
