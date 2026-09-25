/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.GaloisAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
/-!
# The chosen complete valuation and primitive Lubin--Tate point

This module constructs the actual complete discrete valuation on an explicit
finite equal-characteristic Lubin--Tate level.  It proves that the chosen
primitive point generates the integral closure and is a uniformizer.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  exists_integralClosure_standard_fundamental_identity →
    exists_integralClosure_standard_fundamental_identity

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  hasUniqueValuationExtension_of_finite_separable →
    hasUniqueValuationExtension_of_finite_separable


noncomputable
section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

private theorem isEisensteinAt_map_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {f : Polynomial R} {I : Ideal R}
    (hf : f.IsEisensteinAt I) :
    (f.map e).IsEisensteinAt (I.map e) := by
  have hmem_iff (J : Ideal R) (x : R) :
      e.toRingHom x ∈ J.map e.toRingHom ↔ x ∈ J := by
    constructor
    · intro hx
      rcases
          (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hx with
        ⟨y, hy, hey⟩
      exact e.injective hey ▸ hy
    · exact Ideal.mem_map_of_mem e.toRingHom
  constructor
  · rw [Polynomial.leadingCoeff_map_of_injective e.injective]
    change e.toRingHom f.leadingCoeff ∉ I.map e.toRingHom
    rw [hmem_iff I]
    exact hf.leading
  · intro i hi
    rw [Polynomial.natDegree_map_eq_of_injective e.injective] at hi
    rw [Polynomial.coeff_map]
    change e.toRingHom (f.coeff i) ∈ I.map e.toRingHom
    rw [hmem_iff I]
    exact hf.mem hi
  · rw [Polynomial.coeff_map, ← Ideal.map_pow]
    change e.toRingHom (f.coeff 0) ∉ (I ^ 2).map e.toRingHom
    rw [hmem_iff (I ^ 2)]
    exact hf.notMem

private theorem
    isIntegral_mem_adjoin_of_powerBasis_minpoly_isEisensteinAt
    {R K L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsFractionRing R K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : PowerBasis K L) (pi : R) (hpi : Irreducible pi)
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R)))
    {z : L} (hzint : IsIntegral R z) :
    z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
  have hdiscInt :
      IsIntegral R (Algebra.discr K B.basis) :=
    Algebra.discr_isIntegral K (fun i => by
      simpa using hBint.pow (i : ℕ))
  obtain ⟨d, hd⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hdiscInt
  have hd0 : d ≠ 0 := by
    intro hd0
    have hdisc0 : Algebra.discr K B.basis ≠ 0 :=
      Algebra.discr_not_zero_of_basis K B.basis
    apply hdisc0
    rw [← hd, hd0, map_zero]
  obtain ⟨m, unit, hdu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hpi
  have H :=
    Algebra.discr_mul_isIntegral_mem_adjoin K hBint hzint
  rw [← hd, hdu, map_mul, map_pow] at H
  have Hpow :
      pi ^ m • z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
    have HR :
        ((↑unit : R) * pi ^ m) • z ∈
          Algebra.adjoin R ({B.gen} : Set L) := by
      rw [← IsScalarTower.algebraMap_smul K]
      simpa [map_mul, map_pow] using H
    have Hu :=
      Subalgebra.smul_mem
        (Algebra.adjoin R ({B.gen} : Set L)) HR (↑(unit⁻¹) : R)
    simpa [smul_smul, ← mul_assoc] using Hu
  exact mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hpi)
    hBint hzint Hpow hei

private theorem
    integralClosure_adjoin_eq_top_of_powerBasis_minpoly_isEisensteinAt
    {R K L A : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Field L] [CommRing A]
    [Algebra R K] [Algebra K L] [Algebra R L]
    [Algebra R A] [Algebra A L]
    [IsScalarTower R K L] [IsScalarTower R A L]
    [IsFractionRing R K] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure A R L]
    (B : PowerBasis K L) (pi : R) (hpi : Irreducible pi)
    (a : A) (ha : algebraMap A L a = B.gen)
    (hmap_injective : Function.Injective (algebraMap A L))
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R))) :
    Algebra.adjoin R ({a} : Set A) = ⊤ := by
  apply top_unique
  intro z _hz
  let j : A →ₐ[R] L := IsScalarTower.toAlgHom R A L
  have hzint : IsIntegral R (j z) :=
    IsIntegralClosure.isIntegral_iff.mpr ⟨z, rfl⟩
  have hzfield :
      j z ∈ Algebra.adjoin R ({B.gen} : Set L) :=
    isIntegral_mem_adjoin_of_powerBasis_minpoly_isEisensteinAt
      B pi hpi hBint hei hzint
  have hmap :
      (Algebra.adjoin R ({a} : Set A)).map j =
        Algebra.adjoin R ({B.gen} : Set L) := by
    rw [AlgHom.map_adjoin_singleton]
    congr 2
  rw [← hmap] at hzfield
  rcases hzfield with ⟨y, hy, hyz⟩
  have hya : y = z := hmap_injective hyz
  exact hya ▸ hy

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]

/-- The canonical complete discrete valuation on the equal-characteristic
Laurent-series base used by the explicit Lubin--Tate level construction. -/
noncomputable def equalCharacteristicLubinTateBaseCompleteDVF
    (F : LocalField.{0, v} K₀) :
    ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
      F.residueField⸨X⸩ := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  letI : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  exact LocalFieldTheory.localCompleteDVF F.residueField⸨X⸩

/-- The valuation packaged by the chosen Laurent-series base is the canonical
valuation induced by the equal-characteristic valuative relation. -/
theorem equalCharacteristicLubinTateBaseCompleteDVF_valuation_eq
    (F : LocalField.{0, v} K₀) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation =
      letI : ValuativeRel F.residueField⸨X⸩ :=
        equalCharacteristicLaurentValuativeRel F
      ValuativeRel.valuation F.residueField⸨X⸩ := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  change
    (LocalFieldTheory.localCompleteDVF F.residueField⸨X⸩).valuation =
      ValuativeRel.valuation F.residueField⸨X⸩
  unfold LocalFieldTheory.localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- Identity on Laurent-series elements identifies the canonical valuative
integer ring with the valuation ring packaged by the chosen complete DVF. -/
private noncomputable def
    equalCharacteristicLaurentValuativeIntegerEquivLubinTateBaseValuationSubring
    (F : LocalField.{0, v} K₀) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    (ValuativeRel.valuation F.residueField⸨X⸩).integer ≃+*
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  let hval :=
    equalCharacteristicLubinTateBaseCompleteDVF_valuation_eq F
  exact
    { toFun := fun x => ⟨x, by
        change
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuation
              (x : F.residueField⸨X⸩) ≤ 1
        rw [hval]
        exact x.property⟩
      invFun := fun x => ⟨x, by
        change
          ValuativeRel.valuation F.residueField⸨X⸩
              (x : F.residueField⸨X⸩) ≤ 1
        rw [← hval]
        exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

/-- Power series are exactly the valuation ring of the chosen
equal-characteristic Laurent-series base. -/
noncomputable def
    equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring
    (F : LocalField.{0, v} K₀) :
    F.residueField⟦X⟧ ≃+*
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  exact
    (powerSeriesEquivLaurentValuativeInteger F.residueField).trans
      (equalCharacteristicLaurentValuativeIntegerEquivLubinTateBaseValuationSubring
        F)

/-- The power-series/valuation-ring equivalence is the usual inclusion after
coercion to the Laurent-series field. -/
@[simp]
theorem
    equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring_coe
    (F : LocalField.{0, v} K₀) (f : F.residueField⟦X⟧) :
    ((equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F f :
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring) :
      F.residueField⸨X⸩) =
        (f : F.residueField⸨X⸩) := by
  rfl

/-- The Laurent parameter `T`, now regarded as an element of the valuation
ring packaged by the chosen base complete DVF. -/
noncomputable def equalCharacteristicLubinTateBaseUniformizerInteger
    (F : LocalField.{0, v} K₀) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring :=
  equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F
    (PowerSeries.X : F.residueField⟦X⟧)

/-- The chosen base valuation-ring parameter has Laurent-series value `T`. -/
@[simp]
theorem equalCharacteristicLubinTateBaseUniformizerInteger_coe
    (F : LocalField.{0, v} K₀) :
    (equalCharacteristicLubinTateBaseUniformizerInteger F :
      F.residueField⸨X⸩) =
        equalCharacteristicLaurentUniformizer F := by
  rw [equalCharacteristicLubinTateBaseUniformizerInteger,
    equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring_coe]
  rfl

/-- The Laurent parameter is irreducible in the valuation ring packaged by
the chosen base complete DVF. -/
theorem equalCharacteristicLubinTateBaseUniformizerInteger_irreducible
    (F : LocalField.{0, v} K₀) :
    Irreducible (equalCharacteristicLubinTateBaseUniformizerInteger F) := by
  exact
    PowerSeries.X_irreducible.map
      (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F)

/-- The integral primitive division polynomial, with its coefficients
transported from `κ[[T]]` to the chosen base valuation ring. -/
noncomputable def
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    Polynomial
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring :=
  (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
    (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F)

/-- The primitive division polynomial remains monic after transport to the
chosen base valuation ring. -/
theorem
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_monic
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
      F n).Monic :=
  (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).map _

/-- Mapping the valuation-ring primitive polynomial into the Laurent-series
field recovers the original primitive division polynomial. -/
theorem
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_map
    (F : LocalField.{0, v} K₀) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
        F n).map
          (algebraMap
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
            F.residueField⸨X⸩) =
      equalCharacteristicLubinTatePrimitivePolynomial F n := by
  rw [equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring,
    Polynomial.map_map,
    ← equalCharacteristicLubinTateIntegralPrimitivePolynomial_map]
  congr 1

private theorem equalCharacteristicLubinTateLevelCompleteDVFData_exists
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ∃ target :
        ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
          (equalCharacteristicLubinTateLevelField F n),
      ∃ hExt :
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
            target.valuation,
        letI :
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
              target.valuation := hExt
        IsIntegralClosure target.valuationSubring
            (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
            (equalCharacteristicLubinTateLevelField F n) ∧
          ValuationTheory.DiscreteValuationField.ValuedExtension.degree
              (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
              target.toDVF =
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                target.toDVF *
              ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
                target.toDVF := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  exact
    exists_integralClosure_standard_fundamental_identity
      (K := F.residueField⸨X⸩)
      (L := equalCharacteristicLubinTateLevelField F n)
      (equalCharacteristicLubinTateBaseCompleteDVF F)

/-- A complete-DVF structure on the explicit equal-characteristic
Lubin--Tate level field, chosen from its actual integral closure over
`κ((T))`. -/
noncomputable def equalCharacteristicLubinTateLevelCompleteDVF
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0}
      (equalCharacteristicLubinTateLevelField F n) :=
  Classical.choose
    (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n)

/-- The chosen level valuation extends the canonical Laurent-series base
valuation. -/
theorem equalCharacteristicLubinTateLevelCompleteDVF_hasExtension
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation :=
  Classical.choose
    (Classical.choose_spec
      (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n))

/-- Provides the canonical extension instance for the chosen
equal-characteristic Lubin--Tate level valuation. -/
noncomputable instance
    equalCharacteristicLubinTateLevelCompleteDVF_hasExtensionInstance
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateBaseCompleteDVF F).valuation.HasExtension
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation :=
  equalCharacteristicLubinTateLevelCompleteDVF_hasExtension F n

/-- The valuation ring of the chosen level target is the actual integral
closure of the Laurent-series base valuation ring. -/
theorem equalCharacteristicLubinTateLevelCompleteDVF_isIntegralClosure
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsIntegralClosure
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
      (equalCharacteristicLubinTateLevelField F n) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n))).1

/-- The chosen integral-closure valuation realizes the fundamental identity
for the explicit finite Lubin--Tate level. -/
theorem equalCharacteristicLubinTateLevelCompleteDVF_fundamentalIdentity
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF :=
  (Classical.choose_spec
    (Classical.choose_spec
      (equalCharacteristicLubinTateLevelCompleteDVFData_exists F n))).2

/-- The power-basis generator is integral over the chosen base valuation
ring.  Its witness is the transported integral primitive polynomial, not a
field-level integrality surrogate. -/
theorem
    equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsIntegral
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
      (equalCharacteristicLubinTateLevelPowerBasis F n).gen := by
  let P :=
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring F n
  refine
    ⟨P,
      equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_monic
        F n, ?_⟩
  calc
    Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen P =
        Polynomial.aeval
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen
          (P.map
            (algebraMap
              (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
              F.residueField⸨X⸩)) := by
            symm
            exact Polynomial.aeval_map_algebraMap
              F.residueField⸨X⸩
              (equalCharacteristicLubinTateLevelPowerBasis F n).gen P
    _ = Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (equalCharacteristicLubinTatePrimitivePolynomial F n) := by
          rw [
            equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_map]
    _ = Polynomial.aeval
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
        (minpoly F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) := by
          rw [equalCharacteristicLubinTateLevelPowerBasis_minpoly]
    _ = 0 :=
      minpoly.aeval F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen

/-- The chosen primitive Lubin--Tate division point belongs to the actual
integral-closure valuation ring selected on the level field. -/
theorem
    equalCharacteristicLubinTateLevelPowerBasis_gen_mem_valuationSubring
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen ∈
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring := by
  let :
      IsIntegralClosure
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelCompleteDVF_isIntegralClosure F n
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A :=
          (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring)
        (R :=
          (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring)
        (B := equalCharacteristicLubinTateLevelField F n)).1
        (equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
          F n) with
    ⟨x, hx⟩
  change
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen ≤ 1
  rw [← hx]
  exact x.property

/-- The primitive level-`n+1` division point as an element of the chosen
target valuation ring.  Its norm computation below proves that this element
is a uniformizer. -/
noncomputable def equalCharacteristicLubinTatePrimitivePointInteger
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring :=
  ⟨(equalCharacteristicLubinTateLevelPowerBasis F n).gen,
    equalCharacteristicLubinTateLevelPowerBasis_gen_mem_valuationSubring F n⟩

/-- The valuation-ring primitive point has the original power-basis generator
as its underlying level-field element. -/
@[simp]
theorem equalCharacteristicLubinTatePrimitivePointInteger_coe
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePointInteger F n :
      equalCharacteristicLubinTateLevelField F n) =
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen :=
  rfl

/-- The transported integral primitive polynomial is Eisenstein at the
chosen Laurent uniformizer. -/
theorem
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_isEisensteinAt
    (F : LocalField.{0, v} K₀)
    (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
      F n).IsEisensteinAt
        (Ideal.span
          ({equalCharacteristicLubinTateBaseUniformizerInteger F} :
            Set
              (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring)) := by
  have h :=
    isEisensteinAt_map_ringEquiv
      (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F)
      (equalCharacteristicLubinTateIntegralPrimitivePolynomial_isEisensteinAt
        F n)
  change
    (equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
      F n).IsEisensteinAt
        (Ideal.map
          (equalCharacteristicPowerSeriesEquivLubinTateBaseValuationSubring F)
          (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧))) at h
  convert h using 1
  rw [Ideal.map_span]
  simp [equalCharacteristicLubinTateBaseUniformizerInteger]

/-- The integral minimal polynomial of the primitive point is the transported
Lubin--Tate primitive polynomial. -/
theorem equalCharacteristicLubinTatePrimitivePoint_minpoly
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    minpoly
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring
        F n := by
  apply Polynomial.map_injective
    (algebraMap
      (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
      F.residueField⸨X⸩)
    (fun x y h => Subtype.ext h)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions'
      F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
        F n),
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_map,
    equalCharacteristicLubinTateLevelPowerBasis_minpoly]

/-- The primitive Lubin--Tate point generates the entire chosen integral
closure over the Laurent-series valuation ring. -/
theorem equalCharacteristicLubinTatePrimitivePointInteger_adjoin_eq_top
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        ({equalCharacteristicLubinTatePrimitivePointInteger F n} :
          Set
            (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) =
      ⊤ := by
  let :
      FiniteDimensional F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let :
      IsGalois F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  let :
      IsScalarTower
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateLevelField F n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :
      IsIntegralClosure
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTateBaseCompleteDVF F).valuationSubring
        (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelCompleteDVF_isIntegralClosure F n
  apply
    integralClosure_adjoin_eq_top_of_powerBasis_minpoly_isEisensteinAt
      (equalCharacteristicLubinTateLevelPowerBasis F n)
      (equalCharacteristicLubinTateBaseUniformizerInteger F)
      (equalCharacteristicLubinTateBaseUniformizerInteger_irreducible F)
      (equalCharacteristicLubinTatePrimitivePointInteger F n)
      (by rfl)
      (fun x y h => Subtype.ext h)
      (equalCharacteristicLubinTateLevelPowerBasis_gen_isIntegral_over_baseValuationSubring
        F n)
  simpa only [equalCharacteristicLubinTatePrimitivePoint_minpoly F n] using
    equalCharacteristicLubinTatePrimitivePolynomialInBaseValuationSubring_isEisensteinAt
      F n

/-- Finite separability gives uniqueness of the chosen complete valuation
extension on the explicit level field. -/
theorem
    equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueValuationExtension
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension.{0, 0, 0,
      0, y}
      (base := equalCharacteristicLubinTateBaseCompleteDVF F)
      (target := equalCharacteristicLubinTateLevelCompleteDVF F n) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  exact
    (hasUniqueValuationExtension_of_finite_separable
        (equalCharacteristicLubinTateBaseCompleteDVF F)
        (equalCharacteristicLubinTateLevelCompleteDVF F n) :
      ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension.{0, 0,
        0, 0, y}
        (base := equalCharacteristicLubinTateBaseCompleteDVF F)
        (target := equalCharacteristicLubinTateLevelCompleteDVF F n))

/-- Uniqueness after forgetting completeness, in the form required by the
real lower ramification groups. -/
theorem
    equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, y}
      (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
      (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF :=
  equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueValuationExtension F n

private theorem addVal_prod_valuationSubringAut
    {K₁ L₁ : Type} [Field K₁] [Field L₁] [Algebra K₁ L₁]
    [FiniteDimensional K₁ L₁]
    (base : DVF.{0, 0} K₁) (target : DVF.{0, 0} L₁)
    [base.valuation.HasExtension target.valuation]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target)
    (a : target.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (∏ sigma : Gal(L₁/K₁),
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma a) =
      Nat.card Gal(L₁/K₁) •
        IsDiscreteValuationRing.addVal target.valuationSubring a := by
  classical
  have hprod : ∀ s : Finset Gal(L₁/K₁),
      IsDiscreteValuationRing.addVal target.valuationSubring
          (∏ sigma ∈ s,
            valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a) =
        ∑ sigma ∈ s,
          IsDiscreteValuationRing.addVal target.valuationSubring
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert sigma s hs ih =>
        rw [Finset.prod_insert hs, Finset.sum_insert hs,
          IsDiscreteValuationRing.addVal_mul, ih]
  simpa [IsDiscreteValuationRing.addVal_ringEquiv,
    Nat.card_eq_fintype_card] using
    hprod Finset.univ

section PrimitivePointUniformizer

noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forUniformizer
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forUniformizer
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n

private theorem
    equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
      (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
      (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF :=
  equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension F n

/-- The image of the Laurent parameter in a Lubin--Tate level has additive
valuation equal to the ramification index. -/
theorem equalCharacteristicLubinTateBaseUniformizerInteger_map_addVal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (integerMap
          (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
          (equalCharacteristicLubinTateBaseUniformizerInteger F)) =
      (ramificationIndex
        (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
        (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF : ℕ∞) := by
  exact
    addVal_integerMap_eq_ramificationIndex_of_irreducible
      (equalCharacteristicLubinTateBaseCompleteDVF F)
      (equalCharacteristicLubinTateLevelCompleteDVF F n)
      (equalCharacteristicLubinTateBaseUniformizerInteger_irreducible F)

/-- The norm identity for the negative primitive point, lifted to the chosen
valuation rings as the product of its full Galois orbit. -/
theorem equalCharacteristicLubinTateBaseUniformizer_orbitProduct
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    let base := equalCharacteristicLubinTateBaseCompleteDVF F
    let target := equalCharacteristicLubinTateLevelCompleteDVF F n
    integerMap base.toDVF target.toDVF
        (equalCharacteristicLubinTateBaseUniformizerInteger F) =
      ∏ sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩),
        valuationSubringAutOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF)
          (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
            F n)
          sigma (-equalCharacteristicLubinTatePrimitivePointInteger F n) := by
  classical
  dsimp only
  apply Subtype.ext
  simp only [integerMap_apply,
    equalCharacteristicLubinTateBaseUniformizerInteger_coe]
  change
    algebraMap F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n)
        (equalCharacteristicLaurentUniformizer F) =
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring.subtype
          (∏ sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩),
            valuationSubringAutOfUniqueExtension
              (base :=
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
              (target :=
                (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
              (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
                F n)
              sigma (-equalCharacteristicLubinTatePrimitivePointInteger F n))
  rw [map_prod]
  calc
    algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (equalCharacteristicLaurentUniformizer F) =
        algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)
          (Algebra.norm F.residueField⸨X⸩
            (-equalCharacteristicLubinTateLevelGenerator F n)) := by
              rw [equalCharacteristicLubinTate_norm_neg_levelGenerator]
    _ = ∏ sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩),
        sigma (-equalCharacteristicLubinTateLevelGenerator F n) :=
      Algebra.norm_eq_prod_automorphisms
        F.residueField⸨X⸩
        (-equalCharacteristicLubinTateLevelGenerator F n)
    _ = ∏ sigma : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩),
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.valuationSubring.subtype
            (valuationSubringAutOfUniqueExtension
              (base :=
                (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF)
              (target :=
                (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF)
              (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
                F n)
              sigma (-equalCharacteristicLubinTatePrimitivePointInteger F n)) := by
      apply Finset.prod_congr rfl
      intro sigma _hsigma
      change
        sigma (-equalCharacteristicLubinTateLevelGenerator F n) =
          sigma (-(equalCharacteristicLubinTateLevelPowerBasis F n).gen)
      rfl

/-- The chosen primitive Lubin--Tate division point has normalized additive
valuation one in the integral-closure valuation ring. -/
theorem equalCharacteristicLubinTatePrimitivePointInteger_addVal
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (equalCharacteristicLubinTatePrimitivePointInteger F n) = 1 := by
  let base := equalCharacteristicLubinTateBaseCompleteDVF F
  let target := equalCharacteristicLubinTateLevelCompleteDVF F n
  let e := ramificationIndex base.toDVF target.toDVF
  let d := degree base.toDVF target.toDVF
  let lambda := equalCharacteristicLubinTatePrimitivePointInteger F n
  have hbase :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF
            (equalCharacteristicLubinTateBaseUniformizerInteger F)) =
        (e : ℕ∞) := by
    exact equalCharacteristicLubinTateBaseUniformizerInteger_map_addVal F n
  have horbit :=
    equalCharacteristicLubinTateBaseUniformizer_orbitProduct F n
  have hadd := congrArg
    (IsDiscreteValuationRing.addVal target.valuationSubring) horbit
  have hnorm :
      (e : ℕ∞) =
        Nat.card Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) •
          IsDiscreteValuationRing.addVal target.valuationSubring lambda := by
    rw [hbase] at hadd
    rw [addVal_prod_valuationSubringAut
      base.toDVF target.toDVF
      (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
        F n)] at hadd
    simpa [lambda] using hadd
  have hcard :
      Nat.card Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) = d := by
    simpa [d, degree] using
      (IsGalois.card_aut_eq_finrank F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n))
  have hnorm' :
      (e : ℕ∞) =
        (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring lambda := by
    rw [hcard] at hnorm
    simpa [nsmul_eq_mul] using hnorm
  have hdpos : 0 < d := by
    rw [← hcard]
    exact Nat.card_pos
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hfund :
      d = e * residueDegree base.toDVF target.toDVF := by
    simpa [d, e] using
      equalCharacteristicLubinTateLevelCompleteDVF_fundamentalIdentity F n
  have hene : e ≠ 0 := by
    intro he
    apply hdne
    rw [hfund, he, zero_mul]
  have hfne : residueDegree base.toDVF target.toDVF ≠ 0 := by
    intro hf
    apply hdne
    rw [hfund, hf, mul_zero]
  have hele : e ≤ d := by
    rw [hfund]
    exact Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hfne)
  have hvne :
      IsDiscreteValuationRing.addVal target.valuationSubring lambda ≠ 0 := by
    intro hv
    have hecoe : (e : ℕ∞) ≠ 0 := by
      exact_mod_cast hene
    apply hecoe
    simpa [hv] using hnorm'
  have hdcoe : (d : ℕ∞) ≠ 0 := by
    exact_mod_cast hdne
  have hmul_le :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring lambda ≤
      (d : ℕ∞) * 1 := by
    rw [← hnorm']
    have hcast : (e : ℕ∞) ≤ (d : ℕ∞) := by
      exact_mod_cast hele
    simpa using hcast
  have hvle :
      IsDiscreteValuationRing.addVal target.valuationSubring lambda ≤ 1 :=
    (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1 hmul_le
  have honele :
      1 ≤ IsDiscreteValuationRing.addVal target.valuationSubring lambda :=
    Order.one_le_iff_ne_zero.mpr hvne
  exact le_antisymm hvle honele

/-- The chosen primitive point is irreducible in the integral-closure
valuation ring. -/
theorem equalCharacteristicLubinTatePrimitivePointInteger_irreducible
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    Irreducible (equalCharacteristicLubinTatePrimitivePointInteger F n) := by
  let target := equalCharacteristicLubinTateLevelCompleteDVF F n
  let lambda := equalCharacteristicLubinTatePrimitivePointInteger F n
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  have hv :
      IsDiscreteValuationRing.addVal target.valuationSubring lambda =
        IsDiscreteValuationRing.addVal target.valuationSubring varpi := by
    rw [equalCharacteristicLubinTatePrimitivePointInteger_addVal,
      IsDiscreteValuationRing.addVal_uniformizer hvarpi]
  exact
    ((IsDiscreteValuationRing.addVal_eq_iff_associated lambda varpi).1 hv).symm.irreducible
      hvarpi

/-- The chosen primitive Lubin--Tate division point is a uniformizer of the
explicit level field with its integral-closure valuation. -/
theorem equalCharacteristicLubinTatePrimitivePoint_isUniformizer
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation.IsUniformizer
      (equalCharacteristicLubinTatePrimitivePointInteger F n :
        equalCharacteristicLubinTateLevelField F n) := by
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (equalCharacteristicLubinTateLevelCompleteDVF F n).valuation)
    (equalCharacteristicLubinTatePrimitivePointInteger_irreducible F n).maximalIdeal_eq

end PrimitivePointUniformizer

/-- After passing the primitive point to the chosen valuation ring, its
Galois displacement is still the evaluation of the genuine Lubin--Tate
bracket polynomial for `a - 1`.  The normalized valuation is computed below
from the first nonzero visible coefficient. -/
theorem
    equalCharacteristicLubinTatePrimitivePointInteger_displacement_coe_eq_aeval
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ)
    (σ : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩))
    (a : equalCharacteristicLubinTateUnitParameter F n)
    (ha :
      σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) :
    ((RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension
            (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              F n)
            σ (equalCharacteristicLubinTatePrimitivePointInteger F n) -
        equalCharacteristicLubinTatePrimitivePointInteger F n :
      (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring) :
      equalCharacteristicLubinTateLevelField F n) =
        Polynomial.aeval
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen
          (equalCharacteristicLubinTateBracketPolynomial F (n + 1)
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1)) := by
  let x := (equalCharacteristicLubinTateLevelPowerBasis F n).gen
  have hone :
      equalCharacteristicLubinTateLevelBracket F n (n + 1) 1 x = x := by
    apply Subtype.ext
    change
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) 1
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n
    exact
      equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)
  change
    σ x - x =
      Polynomial.aeval x
        (equalCharacteristicLubinTateBracketPolynomial F (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a - 1))
  rw [ha,
    ← equalCharacteristicLubinTateLevelBracket_eq_aeval F n (n + 1)
      (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) x]
  calc
    equalCharacteristicLubinTateLevelBracket F n (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a) x - x =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
            (equalCharacteristicLubinTateUnitParameterSeries F n a) x -
          equalCharacteristicLubinTateLevelBracket F n (n + 1) 1 x := by
            rw [hone]
    _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n a - 1) x := by
      apply Subtype.ext
      change
        equalCharacteristicLubinTateAmbientBracket F
              (equalCharacteristicSeparableCoefficientHom F)
              (equalCharacteristicSeparableUniformizer F) (n + 1)
              (equalCharacteristicLubinTateUnitParameterSeries F n a)
              (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) -
            equalCharacteristicLubinTateAmbientBracket F
              (equalCharacteristicSeparableCoefficientHom F)
              (equalCharacteristicSeparableUniformizer F) (n + 1) 1
              (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
          equalCharacteristicLubinTateAmbientBracket F
            (equalCharacteristicSeparableCoefficientHom F)
            (equalCharacteristicSeparableUniformizer F) (n + 1)
            (equalCharacteristicLubinTateUnitParameterSeries F n a - 1)
            (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      exact
        (congrArg
          (fun f :
              AddMonoid.End
                (SeparableClosure F.residueField⸨X⸩) =>
            f (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
          (equalCharacteristicLubinTateAmbientBracket_sub F
            (equalCharacteristicSeparableCoefficientHom F)
            (equalCharacteristicSeparableUniformizer F) (n + 1)
            (equalCharacteristicLubinTateUnitParameterSeries F n a) 1)).symm

section PrimitivePointDisplacementValuation

noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n

/-- In the chosen level valuation, the Laurent parameter has additive
valuation equal to the explicit Lubin--Tate degree `(q - 1)q^n`. -/
theorem equalCharacteristicLubinTateBaseUniformizerInteger_map_addVal_eq_degree
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (equalCharacteristicLubinTateLevelCompleteDVF F n).valuationSubring
        (integerMap
          (equalCharacteristicLubinTateBaseCompleteDVF F).toDVF
          (equalCharacteristicLubinTateLevelCompleteDVF F n).toDVF
          (equalCharacteristicLubinTateBaseUniformizerInteger F)) =
      ((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) := by
  let base := equalCharacteristicLubinTateBaseCompleteDVF F
  let target := equalCharacteristicLubinTateLevelCompleteDVF F n
  have horbit :=
    equalCharacteristicLubinTateBaseUniformizer_orbitProduct F n
  have hadd := congrArg
    (IsDiscreteValuationRing.addVal target.valuationSubring) horbit
  rw [addVal_prod_valuationSubringAut
    base.toDVF target.toDVF
    (equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension_zero
      F n)] at hadd
  rw [(IsDiscreteValuationRing.addVal target.valuationSubring).map_neg,
    equalCharacteristicLubinTatePrimitivePointInteger_addVal] at hadd
  rw [nsmul_one, Nat.card_eq_fintype_card] at hadd
  calc
    _ = (Fintype.card Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) : ℕ∞)
      := hadd
    _ = ((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) := by
      congr 1
      rw [← Nat.card_eq_fintype_card]
      exact
        (IsGalois.card_aut_eq_finrank F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n)).trans
          (equalCharacteristicLubinTateLevelField_finrank F n)


end PrimitivePointDisplacementValuation

end ChosenRamificationTarget

end LubinTate

end
