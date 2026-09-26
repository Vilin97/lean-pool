/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalPageEulerInequality
public import LeanPool.Stafford38.Stafford38.Characteristic.BaseLocalizedKoszulPositivity
public import LeanPool.Stafford38.Stafford38.Characteristic.NoncharacteristicMinimalPrime
public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalSupportAvoidanceFromCokernel
public import LeanPool.Stafford38.Stafford38.Characteristic.MinimalSupportExistence


/-!
The contradiction between the canonical page length inequality and Koszul positivity.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalKoszulContradiction

open scoped Pointwise
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialRingEquivalence
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.Characteristic.CanonicalPageEulerInequality
open Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
open Stafford38.Characteristic.BaseLocalizedKoszulPositivity
open Stafford38.Characteristic.NoncharacteristicMinimalPrime
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

open CanonicalSupportAvoidanceFromCokernel

noncomputable section
variable (k : Type*) [Field k] [CharZero k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

attribute [local instance] sourceModule targetModule

/-- The tangential coefficient-ring action on the canonical associated graded module. -/
local instance gradedModule : Module (T k n) (Graded k n N d) :=
  oldCoeffModule n (Graded k n N d)

/-- The embedding of tangential coefficients into the full symbol ring, as an algebra structure. -/
local instance coefficientAlgebra : Algebra (T k n) (SymbolRing k (n + 1)) :=
  (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
    (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom).toAlgebra

local instance coefficientTower :
    IsScalarTower (T k n) (SymbolRing k (n + 1)) (Graded k n N d) :=
  IsScalarTower.of_compHom (T k n) (SymbolRing k (n + 1)) (Graded k n N d)

include hd in
/-- At a minimal tangential support prime, the actual page Euler inequality
contradicts the strict coordinate Koszul inequality. -/
theorem no_minimal_coordinate_cokernel_support
    (q : PrimeSpectrum (T k n))
    (hqmem : q ∈ Module.support (T k n)
      (Graded k n N d ⧸ (oldCoordinateMap (k := k) n (Graded k n N d)).range))
    (hqmin : ∀ p ∈ Module.support (T k n)
        (Graded k n N d ⧸ (oldCoordinateMap (k := k) n (Graded k n N d)).range),
      p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) : False := by
  let E := Graded k n N d
  let R := T k n
  let C := SymbolRing k (n + 1)
  let x : C := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let fC : Module.End C E := LinearMap.lsmul C E x
  have hf : fC.restrictScalars R = oldCoordinateMap (k := k) n E := rfl
  have hfinite := canonical_finite_old_coordinate_kernel_cokernel hd
  have : Module.Finite R (fC.restrictScalars R).ker := hfinite.1
  have : Module.Finite R (E ⧸ (fC.restrictScalars R).range) := hfinite.2
  have hlength := localized_kernel_and_cokernel_isFiniteLength fC q hqmem hqmin
  let S := q.asIdeal.primeCompl
  let ek := localizedEquiv S (firstSourceGradedKernelEquiv k n N d)
  let ec := localizedEquiv S (firstTargetGradedCokernelEquiv k n N d)
  have hA : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).SourceTotal 1)) :=
    ek.symm.isFiniteLength hlength.2
  have hB : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).TargetTotal 1)) :=
    ec.symm.isFiniteLength hlength.1
  have hle := canonicalPage_length_target_le_source k n N d hd S hA hB
  rw [ec.length_eq, ek.length_eq] at hle
  have hlt := localized_length_cokernel_gt_kernel (R := R) (C := C) (E := E)
    x q hqmem hqmin (fun p hp =>
      canonical_minimalPrime_mem_of_normalCoordinate_false d hd hp)
  exact (not_lt_of_ge hle) hlt


include hd in
theorem coordinate_cokernel_subsingleton :
    Subsingleton (Graded k n N d ⧸
      (oldCoordinateMap (k := k) n (Graded k n N d)).range) := by
  let U := Graded k n N d ⧸
    (oldCoordinateMap (k := k) n (Graded k n N d)).range
  have : Module.Finite (T k n) U :=
    (canonical_finite_old_coordinate_kernel_cokernel hd).2
  by_contra h
  have : Nontrivial U := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨q, hqmem, hqmin⟩ :=
    MinimalSupportExistence.exists_minimal_support_prime (R := T k n) (U := U)
  exact no_minimal_coordinate_cokernel_support k n N d hd q hqmem hqmin

include hd in
theorem coordinate_quotSMulTop_subsingleton :
    Subsingleton (QuotSMulTop
      (MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1))
      (Graded k n N d)) := by
  let C := SymbolRing k (n + 1)
  let E := Graded k n N d
  let x : C := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let f : Module.End C E := LinearMap.lsmul C E x
  have hf : oldCoordinateMap (k := k) n E = f.restrictScalars (T k n) := rfl
  have hz := coordinate_cokernel_subsingleton k n N d hd
  rw [hf, LinearMap.range_restrictScalars] at hz
  have : Subsingleton (E ⧸ f.range) :=
    (Submodule.Quotient.restrictScalarsEquiv (T k n) f.range).toEquiv.subsingleton_congr.mp hz
  have hrange : f.range = x • (⊤ : Submodule C E) := by
    ext z
    rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and]
    rfl
  change Subsingleton (E ⧸ x • (⊤ : Submodule C E))
  rw [← hrange]
  infer_instance

include hd in
theorem canonical_support_avoidance :
    Disjoint
      (CharacteristicTransposedFilteredModuleSupport.transposedOrderAssociatedGradedSupport k
        (Stafford38.WeylEulerResidue.canonicalRightIdeal
          (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} : Set (SymbolRing k (n + 1)))) :=
  canonical_support_avoidance_of_coordinate_cokernel_subsingleton
    k n N d (coordinate_quotSMulTop_subsingleton k n N d hd)


end
end Stafford38.Characteristic.CanonicalKoszulContradiction
