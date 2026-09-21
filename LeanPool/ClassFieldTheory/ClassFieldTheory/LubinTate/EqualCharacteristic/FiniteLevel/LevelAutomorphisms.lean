/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import Mathlib.FieldTheory.Galois.Basic
/-!
# The uniformizer norm identity: automorphisms of equal-characteristic Lubin--Tate level fields

The explicit Lubin--Tate brackets preserve the simple level field.  Each
finite unit parameter therefore gives a root of the generator's minimal
polynomial inside that field, hence an automorphism obtained from its power
basis.  The parameter action is faithful and has as many elements as the
degree of the extension.  Comparing this lower bound with the standard upper
bound for field automorphisms proves that the level extension is Galois.

No commutativity of the automorphism group is asserted here: that requires
the multiplicative composition law for the bracket action, not merely the
root-counting argument below.
-/

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The image of the Laurent-series uniformizer belongs to every level
field. -/
theorem equalCharacteristicSeparableUniformizer_mem_lubinTateLevelField
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicSeparableUniformizer F ∈
      equalCharacteristicLubinTateLevelField F n := by
  rw [equalCharacteristicSeparableUniformizer,
    equalCharacteristicSeparableBaseHom_eq_algebraMap]
  exact (equalCharacteristicLubinTateLevelField F n).algebraMap_mem _

/-- Embedded residue-field coefficients belong to every level field. -/
theorem equalCharacteristicSeparableCoefficient_mem_lubinTateLevelField
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) :
    equalCharacteristicSeparableCoefficientHom F c ∈
      equalCharacteristicLubinTateLevelField F n := by
  rw [equalCharacteristicSeparableCoefficientHom,
    RingHom.comp_apply, equalCharacteristicSeparableBaseHom_eq_algebraMap]
  exact (equalCharacteristicLubinTateLevelField F n).algebraMap_mem _

/-- The chosen primitive point belongs to its simple level field. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_mem_levelField
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    chosenEqualCharacteristicLubinTatePrimitiveRoot F n ∈
      equalCharacteristicLubinTateLevelField F n := by
  rw [equalCharacteristicLubinTateLevelField]
  exact IntermediateField.mem_adjoin_of_mem _ (Set.mem_singleton _)

/-- Every iterate of the distinguished Lubin--Tate endomorphism preserves a
level field. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_mem_levelField_of_mem
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n i : ℕ) {x : SeparableClosure F.residueField⸨X⸩}
    (hx : x ∈ equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicSeparableUniformizer F) i x ∈
      equalCharacteristicLubinTateLevelField F n := by
  induction i generalizing x with
  | zero => simpa using hx
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        equalCharacteristicLubinTateAmbientPiEnd_apply]
      apply ih
      exact (equalCharacteristicLubinTateLevelField F n).add_mem
        ((equalCharacteristicLubinTateLevelField F n).toSubalgebra.pow_mem hx _)
        ((equalCharacteristicLubinTateLevelField F n).mul_mem
          (equalCharacteristicSeparableUniformizer_mem_lubinTateLevelField F n) hx)

/-- In particular, every distinguished iterate of the chosen primitive point
lies in its level field. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_piIterate_mem_levelField
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n i : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicSeparableUniformizer F) i
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) ∈
      equalCharacteristicLubinTateLevelField F n :=
  equalCharacteristicLubinTateAmbientPiIterate_mem_levelField_of_mem F n i
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_mem_levelField F n)

/-- Every truncated Lubin--Tate bracket preserves the level field. -/
theorem equalCharacteristicLubinTateAmbientBracket_mem_levelField_of_mem
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    {x : SeparableClosure F.residueField⸨X⸩}
    (hx : x ∈ equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) m a x ∈
      equalCharacteristicLubinTateLevelField F n := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  apply (equalCharacteristicLubinTateLevelField F n).sum_mem
  intro i hi
  exact (equalCharacteristicLubinTateLevelField F n).mul_mem
    (equalCharacteristicSeparableCoefficient_mem_lubinTateLevelField F n _)
    (equalCharacteristicLubinTateAmbientPiIterate_mem_levelField_of_mem F n i hx)

/-- The explicit root attached to a finite unit parameter lies in the simple
level field generated by the chosen primitive point. -/
theorem equalCharacteristicLubinTateUnitParameterRoot_mem_levelField
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterRoot F n a ∈
      equalCharacteristicLubinTateLevelField F n := by
  rw [equalCharacteristicLubinTateUnitParameterRoot]
  exact equalCharacteristicLubinTateAmbientBracket_mem_levelField_of_mem F n (n + 1)
    (equalCharacteristicLubinTateUnitParameterSeries F n a)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_mem_levelField F n)

/-- The parameter root, regarded as an element of the level field. -/
noncomputable def equalCharacteristicLubinTateUnitParameterLevelRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateLevelField F n :=
  ⟨equalCharacteristicLubinTateUnitParameterRoot F n a,
    equalCharacteristicLubinTateUnitParameterRoot_mem_levelField F n a⟩

/-- States the theorem `equalCharacteristicLubinTateUnitParameterLevelRoot_coe`. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterLevelRoot_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    (equalCharacteristicLubinTateUnitParameterLevelRoot F n a :
      SeparableClosure F.residueField⸨X⸩) =
        equalCharacteristicLubinTateUnitParameterRoot F n a :=
  rfl

/-- Finite parameters remain distinct after their roots are regarded as
elements of the level field. -/
theorem equalCharacteristicLubinTateUnitParameterLevelRoot_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective
      (equalCharacteristicLubinTateUnitParameterLevelRoot F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameterRoot_injective F n
  exact congrArg Subtype.val hab

/-- The canonical power basis of the simple level extension. -/
noncomputable def equalCharacteristicLubinTateLevelPowerBasis
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    PowerBasis F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  IntermediateField.adjoin.powerBasis
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)

/-- The minimal polynomial of the power-basis generator is the primitive
division polynomial. -/
theorem equalCharacteristicLubinTateLevelPowerBasis_minpoly
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    minpoly F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTatePrimitivePolynomial F n := by
  change
    minpoly F.residueField⸨X⸩
      (IntermediateField.adjoin.powerBasis
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)).gen =
      equalCharacteristicLubinTatePrimitivePolynomial F n
  rw [IntermediateField.adjoin.powerBasis_gen,
    IntermediateField.minpoly_gen,
    equalCharacteristicLubinTatePrimitivePolynomial_eq_minpoly]

/-- A parameter root annihilates the minimal polynomial of the level-field
generator inside the level field itself. -/
theorem equalCharacteristicLubinTateUnitParameterLevelRoot_aeval_minpoly
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    Polynomial.aeval (equalCharacteristicLubinTateUnitParameterLevelRoot F n a)
        (minpoly F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) = 0 := by
  rw [equalCharacteristicLubinTateLevelPowerBasis_minpoly]
  let ι : equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      SeparableClosure F.residueField⸨X⸩ :=
    (equalCharacteristicLubinTateLevelField F n).val
  apply ι.injective
  change ι (Polynomial.aeval
    (equalCharacteristicLubinTateUnitParameterLevelRoot F n a)
    (equalCharacteristicLubinTatePrimitivePolynomial F n)) = ι 0
  rw [← Polynomial.aeval_algHom_apply (f := ι), map_zero]
  rw [Polynomial.aeval_def,
    ← equalCharacteristicSeparableBaseHom_eq_algebraMap]
  change Polynomial.eval₂
    (equalCharacteristicSeparableBaseHom F)
    (equalCharacteristicLubinTateUnitParameterRoot F n a)
    (equalCharacteristicLubinTatePrimitivePolynomial F n) = 0
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (equalCharacteristicLubinTateUnitParameterRoot_isRoot F n a)

/-- The algebra endomorphism sending the chosen primitive generator to the
explicit root attached to a finite unit parameter. -/
noncomputable def equalCharacteristicLubinTateUnitParameterAlgHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n :=
  (equalCharacteristicLubinTateLevelPowerBasis F n).lift
    (equalCharacteristicLubinTateUnitParameterLevelRoot F n a)
    (equalCharacteristicLubinTateUnitParameterLevelRoot_aeval_minpoly F n a)

/-- States the theorem `equalCharacteristicLubinTateUnitParameterAlgHom_apply_gen`. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterAlgHom_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterAlgHom F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
  exact (equalCharacteristicLubinTateLevelPowerBasis F n).lift_gen _ _

/-- The finite-dimensional algebra endomorphism is automatically an
automorphism. -/
noncomputable def equalCharacteristicLubinTateUnitParameterAlgEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateLevelField F n ≃ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n := by
  letI : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  exact AlgEquiv.ofBijective
    (equalCharacteristicLubinTateUnitParameterAlgHom F n a)
    (AlgHom.bijective (equalCharacteristicLubinTateUnitParameterAlgHom F n a))

/-- States the theorem `equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen`. -/
@[simp]
theorem equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateUnitParameterAlgEquiv F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateUnitParameterLevelRoot F n a := by
  rw [equalCharacteristicLubinTateUnitParameterAlgEquiv,
    AlgEquiv.ofBijective_apply,
    equalCharacteristicLubinTateUnitParameterAlgHom_apply_gen]

/-- The explicit map from finite unit parameters to the finite-level Galois
group. -/
noncomputable def equalCharacteristicLubinTateUnitParameterToGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateUnitParameter F n →
      Gal((equalCharacteristicLubinTateLevelField F n) /
        F.residueField⸨X⸩) :=
  equalCharacteristicLubinTateUnitParameterAlgEquiv F n

/-- Faithfulness of the bracket action makes the parameter-to-automorphism
map injective. -/
theorem equalCharacteristicLubinTateUnitParameterToGal_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective
      (equalCharacteristicLubinTateUnitParameterToGal F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameterLevelRoot_injective F n
  have hgen := congrArg
    (fun σ : Gal((equalCharacteristicLubinTateLevelField F n) /
      F.residueField⸨X⸩) =>
        σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen) hab
  simpa [equalCharacteristicLubinTateUnitParameterToGal] using hgen

/-- Provides the instance `equalCharacteristicLubinTateLevelField_galFinite`. -/
noncomputable instance equalCharacteristicLubinTateLevelField_galFinite
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Finite (Gal((equalCharacteristicLubinTateLevelField F n) /
      F.residueField⸨X⸩)) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : Module.Free F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    Module.Free.of_divisionRing _ _
  let : Finite
      ((equalCharacteristicLubinTateLevelField F n) →ₐ[
        F.residueField⸨X⸩]
        (equalCharacteristicLubinTateLevelField F n)) :=
    Finite.algHom _ _ _
  exact Finite.algEquiv

/-- The automorphism group of a level field has cardinality equal to the
degree of the extension. -/
theorem equalCharacteristicLubinTateLevelField_natCard_gal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Nat.card (Gal((equalCharacteristicLubinTateLevelField F n) /
        F.residueField⸨X⸩)) =
      Module.finrank F.residueField⸨X⸩
        (equalCharacteristicLubinTateLevelField F n) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  apply Nat.le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · calc
      Module.finrank F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n) =
          Nat.card (equalCharacteristicLubinTateUnitParameter F n) := by
            rw [equalCharacteristicLubinTateLevelField_finrank,
              equalCharacteristicLubinTateUnitParameter_natCard]
      _ ≤ Nat.card (Gal((equalCharacteristicLubinTateLevelField F n) /
          F.residueField⸨X⸩)) :=
        Nat.card_le_card_of_injective
          (equalCharacteristicLubinTateUnitParameterToGal F n)
          (equalCharacteristicLubinTateUnitParameterToGal_injective F n)

/-- Every equal-characteristic Lubin--Tate level field constructed here is
Galois over the Laurent-series base. -/
theorem equalCharacteristicLubinTateLevelField_isGalois
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  exact IsGalois.of_card_aut_eq_finrank F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
    (equalCharacteristicLubinTateLevelField_natCard_gal F n)

end EqualCharacteristic
end LubinTate
