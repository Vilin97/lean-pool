/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
/-!
# The completed theta-intertwining theorem: the fixed-field prime element and its norm

The fixed field of the prescribed completed Frobenius lift is the finite
Lubin--Tate level for the changed uniformizer `aT`.  Under this
identification its generator is the distinguished element
`pi_delta = theta(lambda)`.  Its minimal polynomial is the genuine changed
primitive Eisenstein polynomial, and the chosen sign convention gives
`N(-pi_delta) = aT`.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries Polynomial PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed unramified base is a Laurent-series algebra in the Frobenius fixed-field norm
comparison. -/
noncomputable local instance equalCharacteristicCompletedFrobeniusFixedNormBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra (LaurentSeries F.residueField)
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The completed level is a Laurent-series algebra through the completed base in the fixed-field
norm comparison. -/
noncomputable local instance equalCharacteristicCompletedFrobeniusFixedNormLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)))

local instance equalCharacteristicCompletedFrobeniusFixedNormScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The changed level field inherits its Laurent-series algebra structure from the selected
separable closure. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedNormChangedLevelAlgebra
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra (LaurentSeries F.residueField)
      (equalCharacteristicChangedLevelField F a n) :=
  letI : Algebra (LaurentSeries F.residueField)
      (SeparableClosure (LaurentSeries F.residueField)) :=
    (separableClosure (LaurentSeries F.residueField)
      (AlgebraicClosure (LaurentSeries F.residueField))).algebra'
  Subalgebra.algebra
    (equalCharacteristicChangedLevelField F a n).toSubalgebra

/-- Laurent-series scalar multiplication on the changed level field uses its selected
separable-closure algebra structure. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedNormChangedLevelSMul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    SMul (LaurentSeries F.residueField)
      (equalCharacteristicChangedLevelField F a n) :=
  @Algebra.toSMul _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedNormChangedLevelAlgebra
      F a n)

/-- The changed level field is a Laurent-series module through its selected separable-closure
algebra structure. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedNormChangedLevelModule
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Module (LaurentSeries F.residueField)
      (equalCharacteristicChangedLevelField F a n) :=
  @Algebra.toModule _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedNormChangedLevelAlgebra
      F a n)

/-- The target `aT` Lubin--Tate level is the fixed field of the prescribed
completed Frobenius lift. -/
noncomputable def equalCharacteristicCompletedFrobeniusTargetLevelEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedLevelField F a n
      ≃ₐ[LaurentSeries F.residueField]
        equalCharacteristicCompletedFrobeniusFixedField F a n := by
  let f := equalCharacteristicDirectTargetLevelFieldToFixedField F a n
  letI : FiniteDimensional (LaurentSeries F.residueField)
      (equalCharacteristicChangedLevelField F a n) :=
    equalCharacteristicChangedLevelField_finiteDimensional F a n
  letI : FiniteDimensional (LaurentSeries F.residueField)
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
    FiniteDimensional.of_finrank_pos (by
      rw [equalCharacteristicCompletedFrobeniusFixedField_finrank]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos))
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  have hdim : Module.finrank (LaurentSeries F.residueField)
      (equalCharacteristicChangedLevelField F a n) =
      Module.finrank (LaurentSeries F.residueField)
        (equalCharacteristicCompletedFrobeniusFixedField F a n) := by
    rw [equalCharacteristicChangedLevelField_finrank,
      equalCharacteristicCompletedFrobeniusFixedField_finrank]
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp
      f.injective

/-- States the theorem `equalCharacteristicCompletedFrobeniusTargetLevelEquiv_generator`. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusTargetLevelEquiv_generator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusTargetLevelEquiv F a n
        (equalCharacteristicChangedLevelGenerator F a n) =
      ⟨(equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
          equalCharacteristicCompletedLevelField F n),
        equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_mem_fixedField
          F a n⟩ := by
  simp only [equalCharacteristicCompletedFrobeniusTargetLevelEquiv]
  exact equalCharacteristicDirectTargetLevelFieldToFixedField_generator F a n

/-- The distinguished element `pi_delta = theta(lambda)`, regarded as an element of
the fixed field. -/
noncomputable def equalCharacteristicCompletedFrobeniusPrimeElement
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusFixedField F a n :=
  ⟨(equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
      equalCharacteristicCompletedLevelField F n),
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_mem_fixedField
      F a n⟩

/-- States the theorem `equalCharacteristicCompletedFrobeniusPrimeElement_eq_equiv_generator`. -/
theorem equalCharacteristicCompletedFrobeniusPrimeElement_eq_equiv_generator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusPrimeElement F a n =
      equalCharacteristicCompletedFrobeniusTargetLevelEquiv F a n
        (equalCharacteristicChangedLevelGenerator F a n) := by
  rw [equalCharacteristicCompletedFrobeniusTargetLevelEquiv_generator]
  rfl

/-- The minimal polynomial of the fixed-field generator is precisely the
target primitive polynomial for `aT`. -/
theorem equalCharacteristicCompletedFrobeniusPrimeElement_minpoly
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    minpoly (LaurentSeries F.residueField)
        (equalCharacteristicCompletedFrobeniusPrimeElement F a n) =
      equalCharacteristicChangedPrimitivePolynomial F a n := by
  rw [equalCharacteristicCompletedFrobeniusPrimeElement_eq_equiv_generator,
    minpoly.algEquiv_eq]
  simpa [equalCharacteristicChangedLevelGenerator,
    equalCharacteristicChangedLevelField,
    IntermediateField.minpoly_gen] using
    (equalCharacteristicChangedPrimitivePolynomial_eq_minpoly F a n).symm

/-- The genuine integral minimal polynomial is Eisenstein at `(T)`.  This is
the prime-element (uniformizer) certificate used in the proof of the completed
  theta-intertwining theorem. -/
theorem equalCharacteristicCompletedFrobeniusPrimeElement_eisenstein
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).IsEisensteinAt
        (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧)) ∧
      (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).map
          (algebraMap F.residueField⟦X⟧
            (LaurentSeries F.residueField)) =
        minpoly (LaurentSeries F.residueField)
          (equalCharacteristicCompletedFrobeniusPrimeElement F a n) := by
  constructor
  · exact
      equalCharacteristicChangedIntegralPrimitivePolynomial_isEisensteinAt
        F a n
  · change equalCharacteristicChangedPrimitivePolynomial F a n =
      minpoly (LaurentSeries F.residueField)
        (equalCharacteristicCompletedFrobeniusPrimeElement F a n)
    exact (equalCharacteristicCompletedFrobeniusPrimeElement_minpoly F a n).symm

/-- The completed theta-intertwining theorem, with the canonical sign:
`N_{Sigma/k((T))}(-pi_delta) = aT`. -/
theorem equalCharacteristicCompletedFrobenius_norm_neg_primeElement
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.norm (LaurentSeries F.residueField)
        (-equalCharacteristicCompletedFrobeniusPrimeElement F a n) =
      equalCharacteristicChangedLaurentUniformizer F a := by
  rw [equalCharacteristicCompletedFrobeniusPrimeElement_eq_equiv_generator,
    ← map_neg]
  rw [Algebra.norm_eq_of_algEquiv]
  exact equalCharacteristicChanged_norm_neg_levelGenerator F a n

end EqualCharacteristic
end LubinTate
