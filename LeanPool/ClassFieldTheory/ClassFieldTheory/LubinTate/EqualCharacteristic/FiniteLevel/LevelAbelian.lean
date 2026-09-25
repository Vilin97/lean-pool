/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import Mathlib.FieldTheory.Galois.Abelian
/-!
# The uniformizer norm identity: abelian equal-characteristic Lubin--Tate level fields

The finite unit parameters constructed previously exhaust the automorphisms
of a level field.  To prove commutativity genuinely, we express each truncated
bracket as evaluation of a polynomial over the Laurent-series base.  Algebra
maps therefore commute with brackets.  Multiplicativity of the genuine
truncated brackets on division points and commutativity of power-series
multiplication then show that any two parameter automorphisms commute on the
power-basis generator, hence everywhere.
-/

@[expose] public section

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Since the finite parameter injection and the Galois group have the same
cardinality, every level-field automorphism comes from a parameter. -/
theorem equalCharacteristicLubinTateUnitParameterToGal_surjective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Surjective
      (equalCharacteristicLubinTateUnitParameterToGal F n) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : Finite
      (Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :=
    equalCharacteristicLubinTateLevelField_galFinite F n
  have hcard :
      Nat.card (Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) ≤
        Nat.card (equalCharacteristicLubinTateUnitParameter F n) := by
    rw [equalCharacteristicLubinTateLevelField_natCard_gal,
      equalCharacteristicLubinTateLevelField_finrank,
      equalCharacteristicLubinTateUnitParameter_natCard]
  have hbijective : Function.Bijective
      (equalCharacteristicLubinTateUnitParameterToGal F n) :=
    Function.Injective.bijective_of_nat_card_le
      (equalCharacteristicLubinTateUnitParameterToGal_injective F n) hcard
  exact hbijective.2

/-- Explicit exhaustion statement for the automorphisms of a level field. -/
theorem equalCharacteristicLubinTateLevelField_exists_unitParameter
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ)
    (σ : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :
    ∃ a : equalCharacteristicLubinTateUnitParameter F n,
      σ = equalCharacteristicLubinTateUnitParameterAlgEquiv F n a := by
  obtain ⟨a, ha⟩ :=
    equalCharacteristicLubinTateUnitParameterToGal_surjective F n σ
  exact ⟨a, ha.symm⟩

/-- The polynomial over the Laurent-series base whose evaluation is a
truncated Lubin--Tate bracket. -/
noncomputable def equalCharacteristicLubinTateBracketPolynomial
    (F : LocalField.{u, v} K)
    (m : ℕ) (a : F.residueField⟦X⟧) :
    Polynomial F.residueField⸨X⸩ :=
  ∑ i ∈ Finset.range m,
    Polynomial.C
        (algebraMap F.residueField F.residueField⸨X⸩
          (PowerSeries.coeff i a)) *
      equalCharacteristicLubinTatePiPolynomialIterate F i

/-- Evaluating the bracket polynomial in any ambient field gives the genuine
truncated bracket. -/
theorem equalCharacteristicLubinTateBracketPolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A)
    (m : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicLubinTateBracketPolynomial F m a) =
      equalCharacteristicLubinTateAmbientBracket F
        (φ.comp (algebraMap F.residueField F.residueField⸨X⸩))
        (φ (equalCharacteristicLaurentUniformizer F)) m a x := by
  rw [equalCharacteristicLubinTateBracketPolynomial,
    Polynomial.eval₂_finsetSum,
    equalCharacteristicLubinTateAmbientBracket_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    equalCharacteristicLubinTatePiPolynomialIterate_eval₂]
  rfl

/-- A truncated bracket, regarded as an endomorphism of the simple level
field.  Its membership proof is the previously established closure of the
level field under brackets. -/
noncomputable def equalCharacteristicLubinTateLevelBracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelField F n :=
  ⟨equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) m a x.1,
    equalCharacteristicLubinTateAmbientBracket_mem_levelField_of_mem
      F n m a x.2⟩

/-- States the theorem `equalCharacteristicLubinTateLevelBracket_coe`. -/
@[simp]
theorem equalCharacteristicLubinTateLevelBracket_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateLevelField F n) :
    (equalCharacteristicLubinTateLevelBracket F n m a x :
      SeparableClosure F.residueField⸨X⸩) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) m a x.1 :=
  rfl

/-- Inside the level field, a truncated bracket is evaluation of its bracket
polynomial. -/
theorem equalCharacteristicLubinTateLevelBracket_eq_aeval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelBracket F n m a x =
      Polynomial.aeval x
        (equalCharacteristicLubinTateBracketPolynomial F m a) := by
  let ι : equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      SeparableClosure F.residueField⸨X⸩ :=
    IsScalarTower.toAlgHom F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n)
      (SeparableClosure F.residueField⸨X⸩)
  apply ι.injective
  change ι (equalCharacteristicLubinTateLevelBracket F n m a x) =
    ι (Polynomial.aeval x
      (equalCharacteristicLubinTateBracketPolynomial F m a))
  rw [← Polynomial.aeval_algHom_apply (f := ι)]
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) m a x.1 =
      Polynomial.eval₂ (equalCharacteristicSeparableBaseHom F) x.1
        (equalCharacteristicLubinTateBracketPolynomial F m a)
  rw [equalCharacteristicLubinTateBracketPolynomial_eval₂]
  rfl

/-- Algebra endomorphisms of the level field commute with its bracket
polynomials. -/
theorem equalCharacteristicLubinTateLevelBracket_map
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (σ : equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    σ (equalCharacteristicLubinTateLevelBracket F n m a x) =
      equalCharacteristicLubinTateLevelBracket F n m a (σ x) := by
  calc
    σ (equalCharacteristicLubinTateLevelBracket F n m a x) =
        σ (Polynomial.aeval x
          (equalCharacteristicLubinTateBracketPolynomial F m a)) :=
      congrArg σ
        (equalCharacteristicLubinTateLevelBracket_eq_aeval F n m a x)
    _ = Polynomial.aeval (σ x)
        (equalCharacteristicLubinTateBracketPolynomial F m a) :=
      (Polynomial.aeval_algHom_apply σ x
        (equalCharacteristicLubinTateBracketPolynomial F m a)).symm
    _ = equalCharacteristicLubinTateLevelBracket F n m a (σ x) :=
      (equalCharacteristicLubinTateLevelBracket_eq_aeval F n m a (σ x)).symm

/-- The power-basis generator is the chosen primitive point in the ambient
separable closure. -/
@[simp]
theorem equalCharacteristicLubinTateLevelPowerBasis_gen_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ((equalCharacteristicLubinTateLevelPowerBasis F n).gen :
      SeparableClosure F.residueField⸨X⸩) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n :=
  rfl

/-- Bracketing the power-basis generator with a parameter series gives the
corresponding parameter root. -/
theorem equalCharacteristicLubinTateLevelBracket_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n a)
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
  apply Subtype.ext
  rfl

/-- A parameter automorphism sends any parameter root by applying that
parameter's bracket to the automorphism's generator image. -/
theorem equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_levelRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n b) =
      equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n a) := by
  calc
    equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n b) =
        equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
          (equalCharacteristicLubinTateLevelBracket F n (n + 1)
            (equalCharacteristicLubinTateUnitParameterSeries F n b)
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen) :=
      congrArg (equalCharacteristicLubinTateUnitParameterAlgEquiv F n a)
        (equalCharacteristicLubinTateLevelBracket_gen F n b).symm
    _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) :=
      equalCharacteristicLubinTateLevelBracket_map F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterAlgEquiv F n a).toAlgHom
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen
    _ = equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n a) := by
      rw [equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen]

/-- Commutativity of power-series multiplication makes the two possible
iterated parameter brackets agree on the primitive point. -/
theorem equalCharacteristicLubinTateUnitParameterLevelBracket_comm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n a) =
      equalCharacteristicLubinTateLevelBracket F n (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n a)
        (equalCharacteristicLubinTateUnitParameterLevelRoot F n b) := by
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n a)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n a)
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          (equalCharacteristicLubinTateUnitParameterSeries F n b)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
  rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (equalCharacteristicLubinTateUnitParameterSeries F n a)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n),
    ← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLubinTateUnitParameterSeries F n a)
        (equalCharacteristicLubinTateUnitParameterSeries F n b)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n),
    mul_comm]

/-- Any two automorphisms arising from finite unit parameters commute. -/
theorem equalCharacteristicLubinTateUnitParameterAlgEquiv_comm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterAlgEquiv F n a *
        equalCharacteristicLubinTateUnitParameterAlgEquiv F n b =
      equalCharacteristicLubinTateUnitParameterAlgEquiv F n b *
        equalCharacteristicLubinTateUnitParameterAlgEquiv F n a := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  change
    equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
        (equalCharacteristicLubinTateUnitParameterAlgEquiv F n b
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) =
      equalCharacteristicLubinTateUnitParameterAlgEquiv F n b
        (equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
  rw [equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen,
    equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen,
    equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_levelRoot,
    equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_levelRoot]
  exact equalCharacteristicLubinTateUnitParameterLevelBracket_comm F n a b

/-- The full finite-level Galois group is commutative. -/
theorem equalCharacteristicLubinTateLevelField_gal_comm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ)
    (σ τ : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :
    σ * τ = τ * σ := by
  obtain ⟨a, rfl⟩ := equalCharacteristicLubinTateLevelField_exists_unitParameter F n σ
  obtain ⟨b, rfl⟩ := equalCharacteristicLubinTateLevelField_exists_unitParameter F n τ
  exact equalCharacteristicLubinTateUnitParameterAlgEquiv_comm F n a b

/-- The Galois group of the explicit level field is a commutative group. -/
instance equalCharacteristicLubinTateLevelField_isMulCommutative
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    IsMulCommutative
      (Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩)) :=
  ⟨⟨equalCharacteristicLubinTateLevelField_gal_comm F n⟩⟩

/-- Every explicit equal-characteristic Lubin--Tate level extension is
abelian Galois over the Laurent-series base. -/
instance equalCharacteristicLubinTateLevelField_isAbelianGalois
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    IsAbelianGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) where
  toIsGalois := equalCharacteristicLubinTateLevelField_isGalois F n
  toIsMulCommutative :=
    equalCharacteristicLubinTateLevelField_isMulCommutative F n

end EqualCharacteristic
end LubinTate
