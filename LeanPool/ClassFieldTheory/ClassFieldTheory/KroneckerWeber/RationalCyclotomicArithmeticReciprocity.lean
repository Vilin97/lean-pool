/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
/-!
# Arithmetic reciprocity for rational cyclotomic ray class fields

This module uses an ordinary rational uniformizer, not its inverse, and
the arithmetic global norm-residue map.  Consequently an unramified
prime `q` acts on roots of unity by the direct power `q`.  The finite
Galois/ray-class comparison is retained as a `ContinuousMulEquiv` with
the native quotient and finite Krull topologies.
-/

open scoped IsMulCommutative NumberField Cyclotomic

noncomputable section

namespace KroneckerWeber

open GlobalClassFieldTheory
open GlobalClassFieldTheory.GlobalClassFields
open GlobalClassFieldTheory.Reciprocity

open scoped Classical in
/-- The ordinary rational uniformizer at `q`, transported to the
adic-completion model used by idèles. -/
noncomputable def rationalPrimeUniformizerLocalInput
    (q : Nat.Primes) :
    ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ :=
  finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)
    (rationalPrimeFinitePlaceFieldUnit q)

open scoped Classical in
/-- In the absolute-value logarithmic coordinate, an ordinary
uniformizer has value `-1`. -/
theorem rationalPrimeUniformizerLocalInput_valuationMap
    (q : Nat.Primes) :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        (NumberField.HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (rationalPrimeUniformizerLocalInput q))) =
      -1 := by
  rw [rationalPrimeUniformizerLocalInput,
    (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm_apply_apply,
    rationalPrimeFinitePlaceFieldUnit_valuationMap]

open scoped Classical in
/-- The previously used value-one absolute-logarithmic input is the
inverse of the ordinary uniformizer. -/
theorem rationalPrimeArithmeticFrobeniusLocalInput_eq_inv_uniformizer
    (q : Nat.Primes) :
    rationalPrimeArithmeticFrobeniusLocalInput q =
      (rationalPrimeUniformizerLocalInput q)⁻¹ := by
  rw [rationalPrimeArithmeticFrobeniusLocalInput,
    rationalPrimeUniformizerLocalInput, map_inv]

section NonzeroOrder

variable (m : ℕ) [NeZero m]

open scoped Classical in
/-- A nonzero cyclotomic level remains nonzero after casting to the rational field. -/
local instance rationalCyclotomicArithmeticReciprocityRationalLevelNeZero : NeZero (m : ℚ) :=
  ⟨by exact_mod_cast (NeZero.ne m)⟩

attribute [local instance] rationalCyclotomicArithmeticReciprocityRationalLevelNeZero

open scoped Classical in
noncomputable /-- The rational cyclotomic level is a number field. -/
local instance rationalCyclotomicArithmeticReciprocityLevelNumberField :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨m, NeZero.pos m⟩

attribute [local instance] rationalCyclotomicArithmeticReciprocityLevelNumberField

open scoped Classical in
noncomputable local instance
    rationalCyclotomicArithmeticLevelIsCyclotomicExtension :
    IsCyclotomicExtension {m} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) := by
  change
    IsCyclotomicExtension
      {((⟨m, NeZero.pos m⟩ : ℕ+) : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension _

attribute [local instance] rationalCyclotomicArithmeticLevelIsCyclotomicExtension

open scoped Classical in
noncomputable local instance
    rationalCyclotomicArithmeticLevelIsAbelianGalois :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  IsCyclotomicExtension.isAbelianGalois {m} ℚ _

attribute [local instance] rationalCyclotomicArithmeticLevelIsAbelianGalois

open scoped Classical in
/-- Arithmetic reciprocity on the ordinary uniformizer agrees
literally with geometric reciprocity on its inverse.  This equality
fixes the normalization independently of the cyclotomic character. -/
theorem
    arithmeticGlobalNormResidue_uniformizer_eq_globalNormResidue_inverseUniformizer
    (q : Nat.Primes) :
    arithmeticGlobalNormResidueMonoidHom
        ℚ
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (IdeleGroup.finitePlaceIdeleClass
          (RayClass.rationalPrime q)
          (rationalPrimeUniformizerLocalInput q)) =
      globalNormResidueMonoidHom
        ℚ
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (IdeleGroup.finitePlaceIdeleClass
          (RayClass.rationalPrime q)
          (rationalPrimeArithmeticFrobeniusLocalInput q)) := by
  let n : ℕ+ := ⟨m, NeZero.pos m⟩
  let g : IdeleClassGroup ℚ →*
      Gal(KummerTheory.rationalCyclotomicLevel n / ℚ) :=
    globalNormResidueMonoidHom ℚ (KummerTheory.rationalCyclotomicLevel n)
  let i : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ →*
      IdeleClassGroup ℚ :=
    IdeleGroup.finitePlaceIdeleClass (RayClass.rationalPrime q)
  let u : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ :=
    rationalPrimeUniformizerLocalInput q
  calc
    arithmeticGlobalNormResidueMonoidHom
        ℚ (KummerTheory.rationalCyclotomicLevel n) (i u) =
        (g (i u))⁻¹ :=
      arithmeticGlobalNormResidueMonoidHom_apply
        ℚ (KummerTheory.rationalCyclotomicLevel n) (i u)
    _ = g (i (u⁻¹)) := (map_inv (g.comp i) u).symm
    _ = g (i (rationalPrimeArithmeticFrobeniusLocalInput q)) :=
      congrArg (g.comp i)
        (rationalPrimeArithmeticFrobeniusLocalInput_eq_inv_uniformizer q).symm

open scoped Classical in
/-- At `q ∤ m`, the arithmetic global norm-residue symbol of the
ordinary one-place uniformizer is arithmetic Frobenius `ζ ↦ ζ ^ q`. -/
theorem
    rationalCyclotomicLevel_arithmeticGlobalNormResidue_at_unramifiedPrime
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (arithmeticGlobalNormResidueMonoidHom
          ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (IdeleGroup.finitePlaceIdeleClass
            (RayClass.rationalPrime q)
            (rationalPrimeUniformizerLocalInput q))) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  rw [
    arithmeticGlobalNormResidue_uniformizer_eq_globalNormResidue_inverseUniformizer
      m,
    rationalCyclotomicLevel_globalNormResidue_at_unramifiedPrime
      m q hq]

open scoped Classical in
/-- Arithmetic-Frobenius-normalized topological reciprocity for the actual finite
cyclotomic level inside the fixed rational separable closure. -/
noncomputable def
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
    :
    Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩ / ℚ) ≃ₜ*
      RayClass.RayClassGroup (RayClass.rationalModulus m) := by
  exact
    (commutativeGroupInversionContinuousMulEquiv
      (Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩ / ℚ))).trans
      (rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup m)

open scoped Classical in
/-- Arithmetic reciprocity sends the arithmetic norm-residue symbol
of an idèle class to its genuine rational ray class. -/
theorem
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup_arithmeticGlobalNormResidue
    (c : IdeleClassGroup ℚ) :
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
        m
        (arithmeticGlobalNormResidueMonoidHom
          ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m)) c := by
  change
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup m
        ((arithmeticGlobalNormResidueMonoidHom
          ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩) c)⁻¹) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m)) c
  rw [
    arithmeticGlobalNormResidueMonoidHom_apply,
    inv_inv,
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_globalNormResidue]

open scoped Classical in
/-- Inverse arithmetic ray reciprocity sends the ray class of an
idèle class back to its arithmetic global norm-residue symbol. -/
theorem
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup_symm_mk
    (c : IdeleClassGroup ℚ) :
    (rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
        m).symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) c) =
      arithmeticGlobalNormResidueMonoidHom
        ℚ
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩) c := by
  apply
    (rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
      m).injective
  rw [
    (rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
      m).apply_symm_apply,
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup_arithmeticGlobalNormResidue]

open scoped Classical in
/-- The inverse arithmetic ray reciprocity image of the ordinary
uniformizer class at `q ∤ m` has direct cyclotomic exponent `q`. -/
theorem
    rationalCyclotomicLevel_arithmeticRayReciprocity_at_unramifiedPrime
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        ((rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup
            m).symm
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.rationalModulus m))
            (IdeleGroup.finitePlaceIdeleClass
              (RayClass.rationalPrime q)
              (rationalPrimeUniformizerLocalInput q)))) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  rw [
    rationalCyclotomicLevelArithmeticGaloisContinuousMulEquivRayClassGroup_symm_mk,
    rationalCyclotomicLevel_arithmeticGlobalNormResidue_at_unramifiedPrime
      m q hq]

end NonzeroOrder

end KroneckerWeber
