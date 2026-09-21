/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalPageEulerInequality
import LeanPool.Stafford38.Stafford38.Characteristic.BaseLocalizedKoszulPositivity
import LeanPool.Stafford38.Stafford38.Characteristic.NoncharacteristicMinimalPrime
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalSupportAvoidanceFromCokernel
import LeanPool.Stafford38.Stafford38.Characteristic.MinimalSupportExistence

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

noncomputable section
variable (k : Type*) [Field k] [CharZero k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hN : 0 < N) (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

attribute [local instance] sourceModule targetModule

local instance gradedModule : Module (T k n) (Graded k n N d) :=
  oldCoeffModule n (Graded k n N d)

local instance coefficientAlgebra : Algebra (T k n) (SymbolRing k (n + 1)) :=
  (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
    (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom).toAlgebra

local instance coefficientTower :
    IsScalarTower (T k n) (SymbolRing k (n + 1)) (Graded k n N d) :=
  IsScalarTower.of_compHom (T k n) (SymbolRing k (n + 1)) (Graded k n N d)

include hN hd in
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
  let ek := localizedEquiv S (firstSourceGradedKernelEquiv k n N d hd)
  let ec := localizedEquiv S (firstTargetGradedCokernelEquiv k n N d hd)
  have hA : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d hd).SourceTotal 1)) :=
    ek.symm.isFiniteLength hlength.2
  have hB : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d hd).TargetTotal 1)) :=
    ec.symm.isFiniteLength hlength.1
  have hle := canonicalPage_length_target_le_source k n N d hd S hA hB
  rw [ec.length_eq, ek.length_eq] at hle
  have hlt := localized_length_cokernel_gt_kernel (R := R) (C := C) (E := E)
    x q hqmem hqmin (fun p hp =>
      canonical_minimalPrime_mem_of_normalCoordinate_false d hN hd hp)
  exact (not_lt_of_ge hle) hlt


include hN hd in
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
  exact no_minimal_coordinate_cokernel_support k n N d hN hd q hqmem hqmin

include hN hd in
theorem coordinate_quotSMulTop_subsingleton :
    Subsingleton (QuotSMulTop
      (MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1))
      (Graded k n N d)) := by
  let C := SymbolRing k (n + 1)
  let E := Graded k n N d
  let x : C := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let f : Module.End C E := LinearMap.lsmul C E x
  have hf : oldCoordinateMap (k := k) n E = f.restrictScalars (T k n) := rfl
  have hz := coordinate_cokernel_subsingleton k n N d hN hd
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

include hN hd in
theorem canonical_support_avoidance :
    Disjoint
      (Stafford38.CharacteristicTransposedFilteredModuleSupport.transposedOrderAssociatedGradedSupport k
        (Stafford38.WeylEulerResidue.canonicalRightIdeal
          (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} : Set (SymbolRing k (n + 1)))) :=
  CanonicalSupportAvoidanceFromCokernel.canonical_support_avoidance_of_coordinate_cokernel_subsingleton
    k n N d hd (coordinate_quotSMulTop_subsingleton k n N d hN hd)


end
end Stafford38.Characteristic.CanonicalKoszulContradiction
