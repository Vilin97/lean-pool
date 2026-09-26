/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.FilteredScalarLifting
public import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints


/-!
# Reduced order support after scalar extension

The terminal Gabber consumer is formulated over a Laurent-series coefficient
field.  This file identifies its geometric reduced support with the ordinary
reduced order support of the scalar-extended canonical Weyl quotient.  Thus a
universal Gabber theorem can be run directly over the extension field; no
unrecorded transport of Poisson closure is needed.
-/

@[expose] public section

namespace Stafford38.Characteristic.GeometricSupportScalarExtension

open Stafford38
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Weyl.FilteredScalarLifting
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.Weyl.PresentedScalarExtension

noncomputable section

universe u v

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-- Radical commutes with extension up to taking the target radical.  This
form needs no surjectivity of the coefficient map. -/
theorem radical_map_radical_eq
    {σ : Type*} (I : Ideal (MvPolynomial σ k)) :
    ((I.radical.map
      (scalarPolynomialMap (k := k) (K := K) σ)).radical) =
      ((I.map
        (scalarPolynomialMap (k := k) (K := K) σ)).radical) := by
  apply le_antisymm
  · calc
      (I.radical.map
          (scalarPolynomialMap (k := k) (K := K) σ)).radical ≤
          ((I.map
            (scalarPolynomialMap (k := k) (K := K) σ)).radical).radical :=
        Ideal.radical_mono
          (Ideal.map_radical_le
            (f := scalarPolynomialMap (k := k) (K := K) σ) (I := I))
      _ = (I.map
          (scalarPolynomialMap (k := k) (K := K) σ)).radical :=
        Ideal.radical_idem _
  · apply Ideal.radical_mono
    exact Ideal.map_mono Ideal.le_radical

/-- The geometric reduced extension of the ground canonical support is
literally the reduced order support of the scalar-extended canonical quotient.
This is the coefficient-field bridge required by the terminal Laurent Gabber
interface. -/
theorem geometricReducedOrderSupportIdeal_eq_scalarExtension
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    geometricReducedOrderSupportIdeal (k := k) (K := K)
        (canonicalRightIdeal (presentedCoordinate k n) d N) =
      reducedOrderSupportIdeal K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension
            (k := k) (K := K) (n + 1) d) N) := by
  change
    (((orderInitialIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)).radical.map
      (scalarPolynomialMap
        (k := k) (K := K) (PhaseVar (n + 1)))).radical) =
      (orderInitialIdeal K
        (canonicalRightIdeal (presentedCoordinate K n)
          (presentedWeylScalarExtension
            (k := k) (K := K) (n + 1) d) N)).radical
  rw [← symbolScalarExtension_toRingHom (k := k) (K := K) (n + 1)]
  have heq :
      orderInitialIdeal K
          (canonicalRightIdeal (presentedCoordinate K n)
            (presentedWeylScalarExtension
              (k := k) (K := K) (n + 1) d) N) =
        (orderInitialIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)).map
            (symbolScalarExtension
              (k := k) (K := K) (n + 1)).toRingHom := by
    apply le_antisymm
    · exact target_orderInitialIdeal_le_map_source_orderInitialIdeal
        (k := k) (K := K) n N d
    · exact presentedWeylScalarExtension_map_orderInitialIdeal_le
        (k := k) (K := K) n N d
  rw [heq]
  exact radical_map_radical_eq
    (K := K)
    (orderInitialIdeal k
      (canonicalRightIdeal (presentedCoordinate k n) d N))


end

end Stafford38.Characteristic.GeometricSupportScalarExtension
