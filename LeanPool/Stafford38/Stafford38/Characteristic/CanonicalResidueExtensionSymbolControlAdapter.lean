/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalLaurentSymbolControl
import LeanPool.Stafford38.Stafford38.Characteristic.GeometricSupportScalarExtension
import LeanPool.Stafford38.Stafford38.Characteristic.MinimalPrimePoisson
import LeanPool.Stafford38.Stafford38.Geometry.CanonicalResidueExtensionAssembly

/-!
# Residue-extension symbol control from base-relative Poisson closure

The consumer `equationConormalLocus_groundMap_subset_geometricReducedSupport`
states its scalar extension through `scalarPolynomialMap`, whose coefficient
map is `algebraMap k (LaurentSeries K)`.  The terminal interface
`CanonicalResidueExtensionSymbolControl` states its conormal locus through
`groundPolynomialMap`, whose coefficient map is the explicit composite
`(algebraMap K (LaurentSeries K)).comp (algebraMap k K)`.

Diagnosis (`#synth`, `pp.explicit`): both `Algebra k (LaurentSeries K)` and
`Algebra K (LaurentSeries K)` are the instance
`HahnSeries.powerSeriesAlgebra ℤ K`, whose structure map is
`(ofPowerSeries ℤ K).comp (algebraMap _ (PowerSeries K))`, and the power-series
structure map is `C ∘ algebraMap`.  The two coefficient maps are therefore
propositionally equal ring homomorphisms (`groundLaurentMap_eq_algebraMap`
below), even though no `IsScalarTower k K (LaurentSeries K)` instance exists:
the `Algebra`-derived scalar action on `LaurentSeries K` is multiplication by
the structure map, not `HahnSeries.instSMul`.  No scalar-tower instance is
constructed or needed here; the bridge is an equality of ring homomorphisms.

The mathematical content is unchanged from the existing adapter: symbol
control follows from base-relative Poisson closure of the geometric reduced
order support over the same Laurent field `LaurentSeries K`.

## Reduction to a field-generic Gabber fragment

`CanonicalResidueExtensionGeometricBaseRelativePoisson` asks for base-relative
Poisson closure of the *geometric* reduced support: the radical of the scalar
extension, to `LaurentSeries K`, of the ground reduced support.  The repository
identifies that ideal with the ordinary reduced order support of the
scalar-extended canonical quotient over the field `LaurentSeries K`
(`geometricReducedOrderSupportIdeal_eq_scalarExtension`) and transports PBW
monicity along the same extension.  The second section records the exact
consequence: the residue-extension input is implied by a Gabber fragment
stated over an arbitrary characteristic-zero field, with no scalar extension,
algebraic closure, or Laurent series in its statement; and that fragment is
implied by involutivity of every minimal prime of the order initial ideal.

Nothing here proves any Gabber-type statement; the new predicates are
theorem-shaped interfaces that a caller must still prove.
-/

namespace Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.CanonicalLaurentSymbolControl
open Stafford38.Characteristic.GeometricSupportScalarExtension
open Stafford38.Characteristic.MinimalPrimePoisson
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.CanonicalResidueExtensionAssembly
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Weyl.PresentedScalarExtension
open Stafford38.WeylEulerResidue
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

section CoefficientMaps

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The explicit composite coefficient map `k → K → LaurentSeries K` is the
structure map of the `Algebra k (LaurentSeries K)` instance.  Both sides are
`ofPowerSeries ℤ K ∘ C ∘ algebraMap`, differing only by an identity
`algebraMap K K`. -/
theorem groundLaurentMap_eq_algebraMap :
    groundLaurentMap (k := k) (K := K) = algebraMap k (LaurentSeries K) := by
  refine RingHom.ext fun a => ?_
  simp only [groundLaurentMap, RingHom.comp_apply, HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]

/-- Consequently the two polynomial coefficient-extension maps agree. -/
theorem groundPolynomialMap_eq_scalarPolynomialMap (σ : Type*) :
    groundPolynomialMap (k := k) (K := K) σ =
      scalarPolynomialMap (k := k) (K := LaurentSeries K) σ := by
  unfold groundPolynomialMap scalarPolynomialMap
  rw [groundLaurentMap_eq_algebraMap]

/-- The ground equation-conormal locus is the equation-conormal locus of the
`scalarPolynomialMap` extension. -/
theorem groundEquationConormalLocus_eq {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) :
    groundEquationConormalLocus (k := k) (K := K) I =
      equationConormalLocus
        (I.map (scalarPolynomialMap (k := k) (K := LaurentSeries K) (Fin n))) := by
  unfold groundEquationConormalLocus
  rw [groundPolynomialMap_eq_scalarPolynomialMap]

end CoefficientMaps

/-- The exact arbitrary-residue-field geometric input.  For every field
extension `K/k`, the geometric reduced order support of the canonical quotient
is required to be base-relatively Poisson over `LaurentSeries K`.  This is a
theorem-shaped interface, not an axiom: callers must provide a proof of it.
It is stated verbatim as in
`Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter`. -/
def CanonicalResidueExtensionGeometricBaseRelativePoisson : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      IsBaseRelativePoisson
        (geometricReducedOrderSupportIdeal
          (K := LaurentSeries K)
          (canonicalRightIdeal (presentedCoordinate k n) d N))

/-- Arbitrary residue-field symbol control follows from the corresponding
base-relative Poisson statement over the same completed residue field. -/
theorem canonicalResidueExtensionSymbolControl_of_geometric_inputs
    (hgabber : CanonicalResidueExtensionGeometricBaseRelativePoisson.{u}) :
    CanonicalResidueExtensionSymbolControl.{u} := by
  intro k _ _ _ K _ _ n N d hN hd
  have : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  have : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap
      (algebraMap K (LaurentSeries K)).injective
  let W := canonicalRightIdeal (presentedCoordinate k n) d N
  rcases exists_canonical_fibrePolynomial n N hd with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro q hq
  have hq' : q ∈ equationConormalLocus
      ((reducedOrderBaseIdeal k W).map
        (scalarPolynomialMap (k := k) (K := LaurentSeries K)
          (Fin (n + 1)))) := by
    rw [groundEquationConormalLocus_eq] at hq
    exact hq
  have hqSupport : q ∈ MvPolynomial.zeroLocus (LaurentSeries K)
      (geometricReducedOrderSupportIdeal
        (K := LaurentSeries K) W) :=
    equationConormalLocus_groundMap_subset_geometricReducedSupport
      W (hgabber k K n N d hN hd) hq'
  have hprincipal : presentedPrincipalComponent k
        (@Stafford38.WeylFiltration.orderWeight (n + 1)) N d ∈
      reducedOrderSupportIdeal k W :=
    orderInitialIdeal_le_reducedOrderSupportIdeal k W
      (canonical_orderPrincipalComponent_mem_initialIdeal k n N hd)
  have hmapped : scalarPolynomialMap
        (k := k) (K := LaurentSeries K) (PhaseVar (n + 1))
        (presentedPrincipalComponent k
          (@Stafford38.WeylFiltration.orderWeight (n + 1)) N d) ∈
      geometricReducedOrderSupportIdeal
        (K := LaurentSeries K) W :=
    Ideal.le_radical (Ideal.mem_map_of_mem
      (scalarPolynomialMap
        (k := k) (K := LaurentSeries K) (PhaseVar (n + 1))) hprincipal)
  have hzero := hqSupport _ hmapped
  rw [← hP] at hzero
  rw [groundLaurentMap_eq_algebraMap]
  simpa only [MvPolynomial.aeval_eq_eval, eval_scalarPolynomialMap] using hzero


/-! ## Reduction to a field-generic Gabber fragment -/

/-- The base-relative Gabber fragment for the canonical quotient over an
arbitrary characteristic-zero field.  No algebraic closure, scalar extension,
or Laurent series occurs in the statement. -/
def CanonicalBaseRelativePoissonOverFields : Prop :=
  ∀ (L : Type u) [Field L] [CharZero L] (n N : ℕ)
    (d : PresentedWeyl L (n + 1)),
    0 < N → IsPBWMonicAt L (.inr (0 : Fin (n + 1))) N d →
      IsBaseRelativePoisson
        (reducedOrderSupportIdeal L
          (canonicalRightIdeal (presentedCoordinate L n) d N))

/-- Gabber's theorem in its usual form for the canonical quotient over an
arbitrary characteristic-zero field: every minimal prime of the order initial
ideal is involutive. -/
def CanonicalMinimalPrimeInvolutivityOverFields : Prop :=
  ∀ (L : Type u) [Field L] [CharZero L] (n N : ℕ)
    (d : PresentedWeyl L (n + 1)),
    0 < N → IsPBWMonicAt L (.inr (0 : Fin (n + 1))) N d →
      ∀ P ∈ (orderInitialIdeal L
          (canonicalRightIdeal (presentedCoordinate L n) d N)).minimalPrimes,
        IsInvolutive P

/-- Minimal-prime involutivity gives the base-relative fragment on the
radical. -/
theorem canonicalBaseRelativePoissonOverFields_of_minimalPrimeInvolutivity
    (h : CanonicalMinimalPrimeInvolutivityOverFields.{u}) :
    CanonicalBaseRelativePoissonOverFields.{u} := by
  intro L _ _ n N d hN hd
  exact radical_isBaseRelativePoisson_of_minimalPrimes_isInvolutive
    (orderInitialIdeal L (canonicalRightIdeal (presentedCoordinate L n) d N))
    (h L n N d hN hd)

/-- The residue-extension geometric input follows from the field-generic
fragment, applied over `LaurentSeries K` to the scalar-extended operator. -/
theorem canonicalResidueExtensionGeometricBaseRelativePoisson_of_overFields
    (h : CanonicalBaseRelativePoissonOverFields.{u}) :
    CanonicalResidueExtensionGeometricBaseRelativePoisson.{u} := by
  intro k _ _ _ K _ _ n N d hN hd
  have : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  have : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap
      (algebraMap K (LaurentSeries K)).injective
  rw [geometricReducedOrderSupportIdeal_eq_scalarExtension
    (k := k) (K := LaurentSeries K) n N d]
  exact h (LaurentSeries K) n N
    (presentedWeylScalarExtension (k := k) (K := LaurentSeries K) (n + 1) d)
    hN
    (presentedWeylScalarExtension_isPBWMonicAt
      (k := k) (K := LaurentSeries K) n N hd)

/-- Residue-extension symbol control from the field-generic fragment. -/
theorem canonicalResidueExtensionSymbolControl_of_overFields
    (h : CanonicalBaseRelativePoissonOverFields.{u}) :
    CanonicalResidueExtensionSymbolControl.{u} :=
  canonicalResidueExtensionSymbolControl_of_geometric_inputs
    (canonicalResidueExtensionGeometricBaseRelativePoisson_of_overFields h)

/-- Residue-extension symbol control from minimal-prime involutivity over
arbitrary characteristic-zero fields. -/
theorem canonicalResidueExtensionSymbolControl_of_minimalPrimeInvolutivity
    (h : CanonicalMinimalPrimeInvolutivityOverFields.{u}) :
    CanonicalResidueExtensionSymbolControl.{u} :=
  canonicalResidueExtensionSymbolControl_of_overFields
    (canonicalBaseRelativePoissonOverFields_of_minimalPrimeInvolutivity h)


end

end Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter
