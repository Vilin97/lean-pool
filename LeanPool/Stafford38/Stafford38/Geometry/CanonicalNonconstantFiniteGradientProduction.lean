/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.AffineComponentCoordinateSplit
public import LeanPool.Stafford38.Stafford38.Geometry.CanonicalConstantCoordinateBranch
public import LeanPool.Stafford38.Stafford38.Geometry.CanonicalResidueExtensionAssembly
public import LeanPool.Stafford38.Stafford38.Geometry.FiniteGradientResidueExtension


/-!
# Canonical finite-gradient production

The terminal residue-extension consumer needs only one finite gradient
conormal row.  This file records the corresponding weaker nonconstant
component interface and adapts it to the existing component-split assembly.
The actual construction of the finite-gradient certificate remains a separate
geometric problem.
-/

@[expose] public section

namespace Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.CanonicalConstantCoordinateBranch
open Stafford38.Geometry.CanonicalResidueExtensionAssembly
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

/-- The nonconstant component interface with the weakest certificate needed by
the terminal conormal-axis consumer. -/
def HigherDimensionalCanonicalResidueExtensionNonconstantFiniteGradientProduction :
    Prop :=
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
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
        Nonempty
          (FiniteGradientBoundaryCertificateOver
            (k := k) (K := K) (n + 1) (Nat.zero_lt_succ n)
            (reducedOrderBaseIdeal k
              (canonicalRightIdeal (presentedCoordinate k n) d N)))

/-- A finite-gradient certificate on the transcendental component supplies the
exact conormal axis consumed by the residue-extension assembly.  The
constant-coordinate component is handled by the existing ground-field branch.
-/
theorem conormalAxisProduction_of_nonconstantFiniteGradient
    (hnonconstant :
      HigherDimensionalCanonicalResidueExtensionNonconstantFiniteGradientProduction.{u}) :
    HigherDimensionalCanonicalResidueExtensionConormalAxisProduction.{u} := by
  intro k _ _ _ n N d hn hN hd hdisjoint hsupp
  let I := reducedOrderBaseIdeal k
    (canonicalRightIdeal (presentedCoordinate k n) d N)
  have hproper : I ≠ ⊤ :=
    reducedOrderBaseIdeal_ne_top_of_support_nonempty
      (canonicalRightIdeal (presentedCoordinate k n) d N) hsupp
  obtain ⟨P, hP, hIP, hconstant | htranscendental⟩ :=
    exists_minimalPrime_coordinate_constant_or_transcendental
      I hproper ⟨0, Nat.zero_lt_succ n⟩
  · obtain ⟨c, hc⟩ := hconstant
    exact
      exists_residueExtensionConormalAxis_of_minimalPrime_coordinate_constant
        (Nat.zero_lt_succ n) I P.asIdeal
        (reducedOrderBaseIdeal_isRadical k
          (canonicalRightIdeal (presentedCoordinate k n) d N))
        hP c hc
  · obtain ⟨K, fieldK, algebraK, W⟩ :=
      hnonconstant k n N d hn hdisjoint P hP htranscendental
    let : Field K := fieldK
    let : Algebra k K := algebraK
    let : CharZero K :=
      charZero_of_injective_algebraMap (algebraMap k K).injective
    obtain ⟨y, xi, hgeneric, hresidue⟩ :=
      exists_groundConormalAxis_of_finiteGradientBoundaryCertificateOver
        (k := k) (K := K) (Nat.zero_lt_succ n) I W.some
    exact ⟨K, fieldK, algebraK, y, xi, hgeneric, hresidue⟩


end

end Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction
