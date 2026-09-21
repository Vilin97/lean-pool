/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.RelativeFractionFieldTransport
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Trace.Quotient

/-!
# A retained source-DVR place

This file retains the local map from the source DVR in the divisorial
construction and proves finiteness of the induced residue extension. It does
not construct a relative coefficient-field map, residue separability, an
inverse limit, or a power-series chart.
-/

namespace Stafford38.Geometry.RetainedDVR

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.RelativeDivisorialTower
open Stafford38.Geometry.RelativeFractionFieldTransport

noncomputable section


universe u v w

def ResidueExtensionFinite
    {A V : Type*} [CommRing A] [IsLocalRing A]
    [CommRing V] [IsLocalRing V] (factor : A →+* V)
    (hlocal : IsLocalHom factor) : Prop := by
  letI : Algebra A V := factor.toAlgebra
  letI : IsLocalHom (algebraMap A V) := hlocal
  exact Module.Finite (ResidueField A) (ResidueField V)

/-- A divisorial place retaining its local source-DVR map. -/
structure RetainedDVRPlace
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    {L : Type w} [Field L] [Algebra A L] (a : A) where
  valuation : ValuationSubring L
  isDiscrete : IsDiscreteValuationRing valuation.toSubring
  parameter : valuation.toSubring
  parameter_eq : (parameter : L) = algebraMap A L a
  parameter_ne : parameter ≠ 0
  parameter_nonunit : ¬IsUnit parameter
  factor : A →+* valuation.toSubring
  factor_commutes :
    valuation.toSubring.subtype.comp factor = algebraMap A L
  factor_isLocal : IsLocalHom factor
  residue_finite : ResidueExtensionFinite factor factor_isLocal

/-- Localization at the lying-over prime retains a local map from the source
DVR, and its residue field is finite over the source residue field. -/
theorem exists_retainedDVRPlace
    {A : Type u} {F : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field L] [Algebra A L] [Algebra F L] [IsScalarTower A F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (a : A) (ha_ne : a ≠ 0) (ha_nonunit : ¬IsUnit a) :
    Nonempty (RetainedDVRPlace A (L := L) a) := by
  let C : Type w := integralClosure A L
  letI : IsDedekindDomain C := integralClosure.isDedekindDomain A F L
  letI : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L C
  have hinjAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective A F)
  have hinjAC : Function.Injective (algebraMap A C) := by
    intro x y hxy
    apply hinjAL
    calc
      algebraMap A L x = algebraMap C L (algebraMap A C x) :=
        (IsScalarTower.algebraMap_apply A C L x).symm
      _ = algebraMap C L (algebraMap A C y) := congrArg (algebraMap C L) hxy
      _ = algebraMap A L y := IsScalarTower.algebraMap_apply A C L y
  let m := maximalIdeal A
  have hm_ne : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  letI : m.IsPrime := (maximalIdeal.isMaximal A).isPrime
  have hker : RingHom.ker (algebraMap A C) ≤ m := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjAC]
    exact bot_le
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := A) (S := C) m hker
  letI : Q.IsPrime := hQprime
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ
    apply hm_ne
    calc
      m = Q.comap (algebraMap A C) := hQcomap.symm
      _ = (⊥ : Ideal C).comap (algebraMap A C) := by rw [hQ]
      _ = RingHom.ker (algebraMap A C) :=
        (RingHom.ker_eq_comap_bot (algebraMap A C)).symm
      _ = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hinjAC
  have hQmax : Q.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (R := A) (S := C) Q
    rw [hQcomap]
    exact maximalIdeal.isMaximal A
  letI : Q.IsMaximal := hQmax
  let RQ : Type w := Localization.subalgebra.ofField L Q.primeCompl
    Q.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing RQ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      C hQ_ne RQ
  let Rsub : Subring L :=
    (Localization.subalgebra.ofField L Q.primeCompl
      Q.primeCompl_le_nonZeroDivisors).toSubring
  have hmem : ∀ y : L, y ∈ Rsub ∨ y⁻¹ ∈ Rsub := by
    intro y
    obtain ⟨r, hr | hr⟩ :=
      (ValuationRing.isFractionRing_iff.mp
        (inferInstance : IsFractionRing RQ L)).1 y
    · left; rw [hr]; exact r.property
    · right; rw [hr]; exact r.property
  let V : ValuationSubring L := ValuationSubring.ofSubring Rsub hmem
  have hVdvr : IsDiscreteValuationRing V.toSubring := by
    change IsDiscreteValuationRing RQ
    infer_instance
  letI : IsScalarTower A C RQ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower A RQ L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let factor : A →+* RQ := algebraMap A RQ
  have hfactor : V.toSubring.subtype.comp factor = algebraMap A L := by
    ext r
    exact IsScalarTower.algebraMap_apply A RQ L r
  have hfactorLocal : IsLocalHom factor := by
    refine ⟨fun r hr ↦ ?_⟩
    by_contra hru
    have hrm : r ∈ m := by
      rw [mem_maximalIdeal]
      exact hru
    have hfactor_mem : factor r ∈ maximalIdeal RQ := by
      change algebraMap C RQ (algebraMap A C r) ∈ maximalIdeal RQ
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff RQ Q]
      change r ∈ Q.comap (algebraMap A C)
      rw [hQcomap]
      exact hrm
    exact (mem_nonunits_iff.mp hfactor_mem) hr
  let aC : C := algebraMap A C a
  have haC_mem : aC ∈ Q := by
    have ha : a ∈ Q.comap (algebraMap A C) := by
      rw [hQcomap, mem_maximalIdeal]
      exact ha_nonunit
    simpa only [Ideal.mem_comap, aC] using ha
  let aRQ : RQ := algebraMap C RQ aC
  have haRQ_mem : aRQ ∈ maximalIdeal RQ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff RQ Q aC).2 haC_mem
  have haRQ_nonunit : ¬IsUnit aRQ := mem_nonunits_iff.mp haRQ_mem
  have haRQ_eq : (aRQ : L) = algebraMap A L a := by
    change algebraMap C L (algebraMap A C a) = algebraMap A L a
    exact IsScalarTower.algebraMap_apply A C L a
  have haRQ_ne : aRQ ≠ 0 := by
    intro ha0
    apply ha_ne
    apply hinjAL
    calc
      algebraMap A L a = (aRQ : L) := haRQ_eq.symm
      _ = ((0 : RQ) : L) := congrArg ((↑) : RQ → L) ha0
      _ = algebraMap A L 0 := by simp
  letI : Algebra A RQ := factor.toAlgebra
  letI : IsLocalHom (algebraMap A RQ) := hfactorLocal
  letI : IsNoetherian A C := IsIntegralClosure.isNoetherian A F L C
  letI : Module.Finite A C := inferInstance
  letI : Q.LiesOver m := ⟨hQcomap.symm⟩
  letI : Module.Finite (A ⧸ m) (C ⧸ Q) := inferInstance
  let sourceResidue : (A ⧸ m) ≃+* ResidueField A :=
    (Ideal.quotEquivOfEq (@IsLocalRing.ker_residue A _ _).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := residue A) residue_surjective)
  let targetResidue : (C ⧸ Q) ≃+* ResidueField RQ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q RQ).trans
      ((Ideal.quotEquivOfEq (@IsLocalRing.ker_residue RQ _ _).symm).trans
        (RingHom.quotientKerEquivOfSurjective
          (f := residue RQ) residue_surjective))
  have hcompat :
      RingHom.comp (algebraMap (ResidueField A) (ResidueField RQ))
          sourceResidue.toRingHom =
        RingHom.comp targetResidue.toRingHom
          (algebraMap (A ⧸ m) (C ⧸ Q)) := by
    ext r
    change residue RQ (factor r) = residue RQ (factor r)
    rfl
  have hfinite : Module.Finite (ResidueField A) (ResidueField RQ) :=
    Module.Finite.of_equiv_equiv sourceResidue targetResidue hcompat
  exact ⟨{
    valuation := V
    isDiscrete := hVdvr
    parameter := aRQ
    parameter_eq := haRQ_eq
    parameter_ne := haRQ_ne
    parameter_nonunit := haRQ_nonunit
    factor := factor
    factor_commutes := hfactor
    factor_isLocal := hfactorLocal
    residue_finite := hfinite
  }⟩

end

end Stafford38.Geometry.RetainedDVR
