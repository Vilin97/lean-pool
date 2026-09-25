/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
/-!
# The equal-characteristic Lubin–Tate action: the equal-characteristic Lubin--Tate endomorphism

After identifying an equal-characteristic local field with `κ((T))`, the
Lubin--Tate polynomial used in the equal-characteristic construction is

`e(Y) = Y ^ q + T * Y`, where `q = #κ`.

This file constructs `e` as an actual additive endomorphism and constructs
the finite bracket

`[a]_<n> = ∑_{i<n} a_i e^i`, for `a = ∑ a_i T^i`.

Thus the unit action used below is the genuine Lubin--Tate action, not
ordinary scalar multiplication in the ambient field.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private theorem addMonoidEnd_mul_apply
    {R : Type*} [AddCommMonoid R]
    (f g : AddMonoid.End R) (x : R) :
    (f * g) x = f (g x) :=
  rfl

private theorem addMonoidEnd_sum_apply
    {R : Type*} [AddCommMonoid R] {I : Type*}
    (s : Finset I) (f : I → AddMonoid.End R) (x : R) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change f i x + (∑ j ∈ s, f j) x = f i x + ∑ j ∈ s, f j x
      rw [ih]

private instance equalCharacteristicLaurentCharP
    (F : LocalField.{u, v} K)
    :
    CharP F.residueField⸨X⸩ F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField F.residueField⸨X⸩).injective
    F.residueCharacteristic

/-- The additive Lubin--Tate endomorphism `Y ↦ Y^q + T Y` on `κ((T))`.
The `q`-power map is the Frobenius iterate supplied by the residue-cardinality
formula from the general Lubin–Tate construction. -/
noncomputable def equalCharacteristicLubinTatePiEnd
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    AddMonoid.End F.residueField⸨X⸩ where
  toFun x :=
    iterateFrobenius F.residueField⸨X⸩ F.residueCharacteristic
        (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F) x +
      equalCharacteristicLaurentUniformizer F * x
  map_zero' := by simp
  map_add' x y := by
    rw [(iterateFrobenius F.residueField⸨X⸩ F.residueCharacteristic
      (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F)).map_add,
      mul_add]
    abel

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- The Lubin–Tate `π`-endomorphism is Frobenius plus uniformizer multiplication. -/
@[simp]
theorem equalCharacteristicLubinTatePiEnd_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiEnd F x =
      x ^ Nat.card F.residueField +
        equalCharacteristicLaurentUniformizer F * x := by
  change
    iterateFrobenius F.residueField⸨X⸩ F.residueCharacteristic
        (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F) x +
      equalCharacteristicLaurentUniformizer F * x = _
  rw [iterateFrobenius_def]
  rw [residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F]

/-- Multiplication by a residue-field coefficient, regarded as an additive
endomorphism of the Laurent-series field. -/
noncomputable def equalCharacteristicCoefficientEnd
    (F : LocalField.{u, v} K) (a : F.residueField) :
    AddMonoid.End F.residueField⸨X⸩ where
  toFun x :=
    algebraMap F.residueField F.residueField⸨X⸩ a * x
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- A residue coefficient endomorphism acts by scalar multiplication. -/
@[simp]
theorem equalCharacteristicCoefficientEnd_apply
    (F : LocalField.{u, v} K) (a : F.residueField)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicCoefficientEnd F a x =
      algebraMap F.residueField F.residueField⸨X⸩ a * x :=
  rfl

/-- The distinguished endomorphism commutes with the genuine coefficient
action. -/
theorem equalCharacteristicLubinTatePiEnd_coefficient_mul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField) (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiEnd F
        (algebraMap F.residueField F.residueField⸨X⸩ a * x) =
      algebraMap F.residueField F.residueField⸨X⸩ a *
        equalCharacteristicLubinTatePiEnd F x := by
  let : Fintype F.residueField := Fintype.ofFinite F.residueField
  rw [equalCharacteristicLubinTatePiEnd_apply,
    equalCharacteristicLubinTatePiEnd_apply, mul_pow, ← map_pow]
  have ha : a ^ Nat.card F.residueField = a := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  rw [ha]
  ring

/-- The `i`-fold iterate of the distinguished Lubin--Tate endomorphism. -/
noncomputable def equalCharacteristicLubinTatePiIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (i : ℕ) : AddMonoid.End F.residueField⸨X⸩ :=
  (equalCharacteristicLubinTatePiEnd F) ^ i

/-- The zeroth Lubin–Tate `π`-iterate is the identity. -/
@[simp]
theorem equalCharacteristicLubinTatePiIterate_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiIterate F 0 x = x := by
  simp [equalCharacteristicLubinTatePiIterate]

/-- A successor `π`-iterate applies one more Lubin–Tate `π`-endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTatePiIterate_succ
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (i : ℕ) (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiIterate F (i + 1) x =
      equalCharacteristicLubinTatePiIterate F i
        (equalCharacteristicLubinTatePiEnd F x) := by
  change
    ((equalCharacteristicLubinTatePiEnd F) ^ (i + 1)) x =
      ((equalCharacteristicLubinTatePiEnd F) ^ i)
        (equalCharacteristicLubinTatePiEnd F x)
  rw [pow_succ]
  rfl

/-- Every iterate of `e` commutes with multiplication by a residue-field
coefficient. -/
theorem equalCharacteristicLubinTatePiIterate_coefficient_mul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (i : ℕ) (a : F.residueField) (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiIterate F i
        (algebraMap F.residueField F.residueField⸨X⸩ a * x) =
      algebraMap F.residueField F.residueField⸨X⸩ a *
        equalCharacteristicLubinTatePiIterate F i x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [equalCharacteristicLubinTatePiIterate_succ,
        equalCharacteristicLubinTatePiEnd_coefficient_mul,
        ih,
        equalCharacteristicLubinTatePiIterate_succ]

/-- The genuine finite-level bracket
`[a]_<n> = ∑_{i<n} a_i e^i`. -/
noncomputable def equalCharacteristicLubinTateBracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) :
    AddMonoid.End F.residueField⸨X⸩ :=
    ∑ i ∈ Finset.range n,
      equalCharacteristicCoefficientEnd F (PowerSeries.coeff i a) *
        equalCharacteristicLubinTatePiIterate F i

/-- Lubin–Tate bracket evaluation expands as the coefficient-and-iterate sum. -/
theorem equalCharacteristicLubinTateBracket_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTateBracket F n a x =
      ∑ i ∈ Finset.range n,
        algebraMap F.residueField F.residueField⸨X⸩
            (PowerSeries.coeff i a) *
          equalCharacteristicLubinTatePiIterate F i x :=
  by
    rw [equalCharacteristicLubinTateBracket,
      addMonoidEnd_sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [addMonoidEnd_mul_apply,
      equalCharacteristicCoefficientEnd_apply]

/-- The Lubin–Tate bracket of the zero series is the zero endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTateBracket_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateBracket F n 0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateBracket F n 0 x =
      (0 : AddMonoid.End F.residueField⸨X⸩) x
  rw [equalCharacteristicLubinTateBracket_apply]
  simp

/-- The Lubin–Tate bracket is additive in its power-series parameter. -/
@[simp]
theorem equalCharacteristicLubinTateBracket_add
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateBracket F n (a + b) =
      equalCharacteristicLubinTateBracket F n a +
        equalCharacteristicLubinTateBracket F n b := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateBracket F n (a + b) x =
      equalCharacteristicLubinTateBracket F n a x +
        equalCharacteristicLubinTateBracket F n b x
  rw [equalCharacteristicLubinTateBracket_apply,
    equalCharacteristicLubinTateBracket_apply,
    equalCharacteristicLubinTateBracket_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(PowerSeries.coeff i).map_add,
    (algebraMap F.residueField F.residueField⸨X⸩).map_add,
    add_mul]

/-- The bracket of a constant power series is its coefficient endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTateBracket_C
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField) :
    equalCharacteristicLubinTateBracket F (n + 1) (PowerSeries.C a) =
      equalCharacteristicCoefficientEnd F a := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateBracket F (n + 1)
        (PowerSeries.C a) x =
      equalCharacteristicCoefficientEnd F a x
  rw [equalCharacteristicLubinTateBracket_apply,
    equalCharacteristicCoefficientEnd_apply]
  classical
  rw [Finset.sum_eq_single 0]
  · simp [PowerSeries.coeff_C,
      equalCharacteristicLubinTatePiIterate]
  · intro i hi hi0
    simp [PowerSeries.coeff_C, hi0]
  · simp

/-- The bracket of `X` is the Lubin–Tate `π`-endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTateBracket_X
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateBracket F (n + 2)
        (PowerSeries.X : F.residueField⟦X⟧) =
      equalCharacteristicLubinTatePiEnd F := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateBracket F (n + 2)
        (PowerSeries.X : F.residueField⟦X⟧) x =
      equalCharacteristicLubinTatePiEnd F x
  rw [equalCharacteristicLubinTateBracket_apply]
  simp [PowerSeries.coeff_X,
    equalCharacteristicLubinTatePiIterate]

end EqualCharacteristic
end LubinTate
