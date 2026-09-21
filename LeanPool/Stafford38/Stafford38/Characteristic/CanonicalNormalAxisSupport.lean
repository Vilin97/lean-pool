/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Polynomial.DistinguishedVariable
import LeanPool.Stafford38.Stafford38.Characteristic.TransposedFilteredModuleSupport
import LeanPool.Stafford38.Stafford38.Geometry.ConormalAxisContradiction

/-!
# Scheme-theoretic exclusion of the punctured normal fibre axis

The canonical order symbol is homogeneous, fibre-only, and has unit pure
normal coefficient.  Hence a characteristic-support prime containing every
tangential momentum variable must also contain the normal momentum variable.
This is the exact prime-ideal form of normal-axis exclusion.  It proves no
filtered strictness or noncharacteristic inverse-image theorem.
-/

namespace Stafford38.Characteristic.CanonicalNormalAxisSupport

open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicTransposedFilteredModuleSupport
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylEulerResidue
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylTranspositionFiltration

noncomputable section

variable {k : Type*} [Field k] {n N : ℕ}

/-- The phase variables other than the distinguished normal momentum that may
occur in the canonical principal symbol. -/
def tangentialMomentumVariables (n : ℕ) : Set (PhaseVar (n + 1)) :=
  {v | ∃ i : Fin (n + 1), i ≠ 0 ∧ v = .inr i}

/-- A fibre-only polynomial uses only momentum variables. -/
theorem vars_subset_momentum_of_isFibreOnly
    {P : SymbolRing k (n + 1)} (hP : IsFibreOnly k P) :
    (P.vars : Set (PhaseVar (n + 1))) ⊆ Set.range Sum.inr := by
  classical
  intro v hv
  rcases v with i | i
  · obtain ⟨m, hm, hmi⟩ := (MvPolynomial.mem_vars_iff_mem_support _).mp hv
    have hzero := hP m (MvPolynomial.mem_support_iff.mp hm) i
    exact False.elim ((Finsupp.mem_support_iff.mp hmi) hzero)
  · exact ⟨i, rfl⟩

/-- The variables of a fibre-only polynomial split into the distinguished
normal momentum and the tangential momenta. -/
theorem vars_subset_normal_insert_tangential
    {P : SymbolRing k (n + 1)} (hP : IsFibreOnly k P) :
    (P.vars : Set (PhaseVar (n + 1))) ⊆
      insert (.inr (0 : Fin (n + 1))) (tangentialMomentumVariables n) := by
  intro v hv
  obtain ⟨i, rfl⟩ := vars_subset_momentum_of_isFibreOnly hP hv
  by_cases hi : i = 0
  · left
    rw [hi]
  · right
    exact ⟨i, hi, rfl⟩

/-- Every canonical characteristic-support prime containing all tangential
momentum variables contains the distinguished normal momentum variable. -/
theorem normalMomentum_mem_of_mem_canonicalSupport
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p : PrimeSpectrum (SymbolRing k (n + 1))}
    (hp : p ∈ orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N))
    (htan : ∀ i : Fin (n + 1), i ≠ 0 →
      MvPolynomial.X (.inr i) ∈ p.asIdeal) :
    MvPolynomial.X (.inr (0 : Fin (n + 1))) ∈ p.asIdeal := by
  let P := presentedPrincipalComponent k orderWeight N d
  have hPmem : P ∈ p.asIdeal := by
    rw [orderCharacteristicSupport_eq_zeroLocus,
      PrimeSpectrum.mem_zeroLocus] at hp
    exact hp (canonical_orderPrincipalComponent_mem_initialIdeal k n N hd)
  apply AlgebraicAnalysis.MvPolynomial.X_mem_of_homogeneous_mem_prime
    (canonical_orderPrincipalComponent_isHomogeneous n N hd)
    (vars_subset_normal_insert_tangential
      (canonical_orderPrincipalComponent_isFibreOnly k n N hd))
    (canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd)
    isUnit_one p.isPrime hPmem
  intro v hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact htan i hi

/-- Equivalently, no canonical support prime lies on the punctured normal
momentum axis. -/
theorem no_canonicalSupport_prime_on_punctured_normal_axis
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ¬ ∃ p ∈ orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N),
      (∀ i : Fin (n + 1), i ≠ 0 →
        MvPolynomial.X (.inr i) ∈ p.asIdeal) ∧
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ∉ p.asIdeal := by
  rintro ⟨p, hp, htan, hnormal⟩
  exact hnormal (normalMomentum_mem_of_mem_canonicalSupport d hd hp htan)

/-- The same punctured-axis exclusion for the transposed associated-graded
support used by the left-module noncharacteristic theorem. -/
theorem normalMomentum_mem_of_mem_transposedCanonicalSupport
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p : PrimeSpectrum (SymbolRing k (n + 1))}
    (hp : p ∈ transposedOrderAssociatedGradedSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N))
    (htan : ∀ i : Fin (n + 1), i ≠ 0 →
      MvPolynomial.X (.inr i) ∈ p.asIdeal) :
    MvPolynomial.X (.inr (0 : Fin (n + 1))) ∈ p.asIdeal := by
  let τ : SymbolRing k (n + 1) →+* SymbolRing k (n + 1) :=
    (symbolTranspositionEquiv k).toRingEquiv.toRingHom
  let q : PrimeSpectrum (SymbolRing k (n + 1)) :=
    PrimeSpectrum.comap τ p
  have hqModule : q ∈ Module.support (SymbolRing k (n + 1))
      (OrderAssociatedGradedModule k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) := by
    rw [transposedOrderAssociatedGradedSupport_eq_preimage] at hp
    exact hp
  have hq : q ∈ orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N) := by
    rw [orderCharacteristicSupport_eq_zeroLocus]
    rw [Module.support_eq_zeroLocus,
      annihilator_orderAssociatedGradedModule] at hqModule
    exact hqModule
  have hqtan : ∀ i : Fin (n + 1), i ≠ 0 →
      MvPolynomial.X (.inr i) ∈ q.asIdeal := by
    intro i hi
    change symbolTransposition k (MvPolynomial.X (.inr i)) ∈ p.asIdeal
    rw [symbolTransposition_momentum]
    exact p.asIdeal.neg_mem (htan i hi)
  have hqnormal := normalMomentum_mem_of_mem_canonicalSupport d hd hq hqtan
  change symbolTransposition k
      (MvPolynomial.X (.inr (0 : Fin (n + 1)))) ∈ p.asIdeal at hqnormal
  rw [symbolTransposition_momentum] at hqnormal
  simpa using p.asIdeal.neg_mem hqnormal

/-- No prime of the transposed canonical support lies on the punctured normal
momentum axis. -/
theorem no_transposedCanonicalSupport_prime_on_punctured_normal_axis
    (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ¬ ∃ p ∈ transposedOrderAssociatedGradedSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N),
      (∀ i : Fin (n + 1), i ≠ 0 →
        MvPolynomial.X (.inr i) ∈ p.asIdeal) ∧
      MvPolynomial.X (.inr (0 : Fin (n + 1))) ∉ p.asIdeal := by
  rintro ⟨p, hp, htan, hnormal⟩
  exact hnormal
    (normalMomentum_mem_of_mem_transposedCanonicalSupport d hd hp htan)


end

end Stafford38.Characteristic.CanonicalNormalAxisSupport
