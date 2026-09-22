/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
/-!
# The finite Lubin–Tate bracket construction: Lubin--Tate brackets in an ambient extension field

Division points do not in general lie in the base Laurent-series field.  This
file therefore constructs the same genuine brackets in an arbitrary ambient
field `A` of the same characteristic, from a chosen coefficient embedding
`ι : κ →+* A` and the image `t : A` of the Laurent-series uniformizer.  The
construction will be specialized to a separable closure when forming the
Lubin--Tate level fields.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private theorem ambientAddMonoidEnd_mul_apply
    {A : Type*} [AddCommMonoid A]
    (f g : AddMonoid.End A) (x : A) :
    (f * g) x = f (g x) :=
  rfl

private theorem ambientAddMonoidEnd_sum_apply
    {A I : Type*} [AddCommMonoid A]
    (s : Finset I) (f : I → AddMonoid.End A) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change f i x + (∑ j ∈ s, f j) x = f i x + ∑ j ∈ s, f j x
      rw [ih]

private theorem ambientAddMonoidHom_map_finset_sum
    {A I : Type*} [AddCommMonoid A]
    (f : AddMonoid.End A) (s : Finset I) (g : I → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (f.map_add _ _).trans
        (congrArg (fun x ↦ f (g i) + x) ih)

/-- The distinguished endomorphism `Y ↦ Y^q + tY` in an ambient field. -/
noncomputable def equalCharacteristicLubinTateAmbientPiEnd
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) : AddMonoid.End A where
  toFun x :=
    iterateFrobenius A F.residueCharacteristic
        (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F) x +
      t * x
  map_zero' := by simp
  map_add' x y := by
    rw [(iterateFrobenius A F.residueCharacteristic
      (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F)).map_add,
      mul_add]
    abel

/-- The ambient `π`-endomorphism is Frobenius plus multiplication by `t`. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientPiEnd_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t x : A) :
    equalCharacteristicLubinTateAmbientPiEnd F t x =
      x ^ Nat.card F.residueField + t * x := by
  change
    iterateFrobenius A F.residueCharacteristic
        (CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F) x +
      t * x = _
  rw [iterateFrobenius_def]
  rw [CompleteDVF.higherPrincipalUnitGroup.residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F]

/-- Multiplication by an embedded residue-field coefficient. -/
noncomputable def equalCharacteristicLubinTateAmbientCoefficientEnd
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A]
    (ι : F.residueField →+* A) (a : F.residueField) :
    AddMonoid.End A where
  toFun x := ι a * x
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- A coefficient endomorphism acts by multiplication by the embedded coefficient. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientCoefficientEnd_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A]
    (ι : F.residueField →+* A) (a : F.residueField) (x : A) :
    equalCharacteristicLubinTateAmbientCoefficientEnd F ι a x = ι a * x :=
  rfl

/-- The distinguished endomorphism commutes with the embedded coefficient
field. -/
theorem equalCharacteristicLubinTateAmbientPiEnd_coefficient_mul
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (a : F.residueField) (x : A) :
    equalCharacteristicLubinTateAmbientPiEnd F t (ι a * x) =
      ι a * equalCharacteristicLubinTateAmbientPiEnd F t x := by
  let : Fintype F.residueField := Fintype.ofFinite F.residueField
  rw [equalCharacteristicLubinTateAmbientPiEnd_apply,
    equalCharacteristicLubinTateAmbientPiEnd_apply, mul_pow, ← ι.map_pow]
  have ha : a ^ Nat.card F.residueField = a := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  rw [ha]
  ring

/-- The `i`-fold iterate of the ambient distinguished endomorphism. -/
noncomputable def equalCharacteristicLubinTateAmbientPiIterate
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (i : ℕ) : AddMonoid.End A :=
  (equalCharacteristicLubinTateAmbientPiEnd F t) ^ i

/-- The zeroth ambient `π`-iterate is the identity. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientPiIterate_zero
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t 0 x = x := by
  simp [equalCharacteristicLubinTateAmbientPiIterate]

/-- A successor ambient `π`-iterate applies one more `π`-endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientPiIterate_succ
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (i : ℕ) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t (i + 1) x =
      equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
  change
    ((equalCharacteristicLubinTateAmbientPiEnd F t) ^ (i + 1)) x =
      ((equalCharacteristicLubinTateAmbientPiEnd F t) ^ i)
        (equalCharacteristicLubinTateAmbientPiEnd F t x)
  rw [pow_succ]
  rfl

/-- Ambient iterates commute with residue-field scalar multiplication. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_coefficient_mul
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (i : ℕ) (a : F.residueField) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t i (ι a * x) =
      ι a * equalCharacteristicLubinTateAmbientPiIterate F t i x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        equalCharacteristicLubinTateAmbientPiEnd_coefficient_mul,
        ih, equalCharacteristicLubinTateAmbientPiIterate_succ]

/-- The genuine finite bracket in the ambient field. -/
noncomputable def equalCharacteristicLubinTateAmbientBracket
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) : AddMonoid.End A :=
  ∑ i ∈ Finset.range n,
    equalCharacteristicLubinTateAmbientCoefficientEnd F ι
        (PowerSeries.coeff i a) *
      equalCharacteristicLubinTateAmbientPiIterate F t i

/-- Ambient bracket evaluation expands as the finite coefficient-and-iterate sum. -/
theorem equalCharacteristicLubinTateAmbientBracket_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientBracket F ι t n a x =
      ∑ i ∈ Finset.range n,
        ι (PowerSeries.coeff i a) *
          equalCharacteristicLubinTateAmbientPiIterate F t i x := by
  rw [equalCharacteristicLubinTateAmbientBracket,
    ambientAddMonoidEnd_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ambientAddMonoidEnd_mul_apply,
    equalCharacteristicLubinTateAmbientCoefficientEnd_apply]

/-- The ambient bracket of the zero series is the zero endomorphism. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientBracket_zero
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A) (n : ℕ) :
    equalCharacteristicLubinTateAmbientBracket F ι t n 0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateAmbientBracket F ι t n 0 x =
      (0 : AddMonoid.End A) x
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  simp

/-- The ambient bracket is additive in its power-series parameter. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientBracket_add
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a b : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateAmbientBracket F ι t n (a + b) =
      equalCharacteristicLubinTateAmbientBracket F ι t n a +
        equalCharacteristicLubinTateAmbientBracket F ι t n b := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateAmbientBracket F ι t n (a + b) x =
      equalCharacteristicLubinTateAmbientBracket F ι t n a x +
        equalCharacteristicLubinTateAmbientBracket F ι t n b x
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(PowerSeries.coeff i).map_add, ι.map_add, add_mul]

/-- The ambient bracket of a constant acts by the embedded scalar. -/
@[simp]
theorem equalCharacteristicLubinTateAmbientBracket_C
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField) :
    equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
        (PowerSeries.C a) =
      equalCharacteristicLubinTateAmbientCoefficientEnd F ι a := by
  apply AddMonoidHom.ext
  intro x
  change
    equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
        (PowerSeries.C a) x =
      equalCharacteristicLubinTateAmbientCoefficientEnd F ι a x
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientCoefficientEnd_apply]
  classical
  rw [Finset.sum_eq_single 0]
  · simp [PowerSeries.coeff_C,
      equalCharacteristicLubinTateAmbientPiIterate]
  · intro i hi hi0
    simp [PowerSeries.coeff_C, hi0]
  · simp

/-- Ambient iterates add their exponents under composition. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_add
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (i j : ℕ) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t (i + j) x =
      equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientPiIterate F t j x) := by
  change
    ((equalCharacteristicLubinTateAmbientPiEnd F t) ^ (i + j)) x =
      ((equalCharacteristicLubinTateAmbientPiEnd F t) ^ i)
        (((equalCharacteristicLubinTateAmbientPiEnd F t) ^ j) x)
  rw [pow_add]
  rfl

/-- A point in an ambient field killed by the level-`n` iterate. -/
def IsEqualCharacteristicLubinTateAmbientTorsion
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (n : ℕ) (x : A) : Prop :=
  equalCharacteristicLubinTateAmbientPiIterate F t n x = 0

/-- A level-`n` ambient torsion point is killed at every higher level. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_eq_zero_of_le
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) {n m : ℕ} (hnm : n ≤ m) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t n x) :
    equalCharacteristicLubinTateAmbientPiIterate F t m x = 0 := by
  rw [← Nat.sub_add_cancel hnm,
    equalCharacteristicLubinTateAmbientPiIterate_add, hx, map_zero]

/-- The image under `e` of level `n+1` torsion has level `n`. -/
theorem equalCharacteristicLubinTateAmbientPiEnd_torsion_pred
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (n : ℕ) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t (n + 1) x) :
    IsEqualCharacteristicLubinTateAmbientTorsion F t n
      (equalCharacteristicLubinTateAmbientPiEnd F t x) :=
  hx

/-- Recursive evaluation formula for an ambient bracket. -/
theorem equalCharacteristicLubinTateAmbientBracket_succ_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a x =
      ι (PowerSeries.coeff 0 a) * x +
        equalCharacteristicLubinTateAmbientBracket F ι t n
          (equalCharacteristicPowerSeriesTail a)
          (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    Finset.sum_range_succ', add_comm,
    equalCharacteristicLubinTateAmbientBracket_apply]
  apply congrArg₂ (fun y z : A ↦ y + z)
  · rfl
  · apply Finset.sum_congr rfl
    intro i hi
    rw [equalCharacteristicPowerSeriesTail_coeff,
      equalCharacteristicLubinTateAmbientPiIterate_succ]

/-- The first ambient `π`-iterate is the ambient `π`-endomorphism. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_one
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t 1 x =
      equalCharacteristicLubinTateAmbientPiEnd F t x := by
  simp [equalCharacteristicLubinTateAmbientPiIterate]

/-- The distinguished ambient endomorphism commutes with its iterates. -/
theorem equalCharacteristicLubinTateAmbientPiEnd_iterate
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (i : ℕ) (x : A) :
    equalCharacteristicLubinTateAmbientPiEnd F t
        (equalCharacteristicLubinTateAmbientPiIterate F t i x) =
      equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
  calc
    equalCharacteristicLubinTateAmbientPiEnd F t
        (equalCharacteristicLubinTateAmbientPiIterate F t i x) =
        equalCharacteristicLubinTateAmbientPiIterate F t 1
          (equalCharacteristicLubinTateAmbientPiIterate F t i x) :=
      (equalCharacteristicLubinTateAmbientPiIterate_one F t
        (equalCharacteristicLubinTateAmbientPiIterate F t i x)).symm
    _ = equalCharacteristicLubinTateAmbientPiIterate F t (1 + i) x :=
      (equalCharacteristicLubinTateAmbientPiIterate_add F t 1 i x).symm
    _ = equalCharacteristicLubinTateAmbientPiIterate F t (i + 1) x := by
      rw [Nat.one_add]
    _ = equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientPiIterate F t 1 x) :=
      equalCharacteristicLubinTateAmbientPiIterate_add F t i 1 x
    _ = equalCharacteristicLubinTateAmbientPiIterate F t i
        (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
      exact congrArg (equalCharacteristicLubinTateAmbientPiIterate F t i)
        (equalCharacteristicLubinTateAmbientPiIterate_one F t x)

/-- Ambient brackets are linear for the embedded coefficient action. -/
theorem equalCharacteristicLubinTateAmbientBracket_coefficient_mul_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (c : F.residueField) (x : A) :
    equalCharacteristicLubinTateAmbientBracket F ι t n a (ι c * x) =
      ι c * equalCharacteristicLubinTateAmbientBracket F ι t n a x := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [equalCharacteristicLubinTateAmbientPiIterate_coefficient_mul]
  ring

/-- Multiplication of coefficient series by `C(c)` scales an ambient
bracket by `ι(c)`. -/
theorem equalCharacteristicLubinTateAmbientBracket_C_mul_apply
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (c : F.residueField) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientBracket F ι t n
        (PowerSeries.C c * a) x =
      ι c * equalCharacteristicLubinTateAmbientBracket F ι t n a x := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_C_mul, ι.map_mul]
  ring

/-- The ambient bracket commutes with the distinguished endomorphism. -/
theorem equalCharacteristicLubinTateAmbientPiEnd_bracket
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A) :
    equalCharacteristicLubinTateAmbientPiEnd F t
        (equalCharacteristicLubinTateAmbientBracket F ι t n a x) =
      equalCharacteristicLubinTateAmbientBracket F ι t n a
        (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    ambientAddMonoidHom_map_finset_sum,
    equalCharacteristicLubinTateAmbientBracket_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [equalCharacteristicLubinTateAmbientPiEnd_coefficient_mul,
    equalCharacteristicLubinTateAmbientPiEnd_iterate]

/-- On level-`n` torsion, adding the `(n+1)`-st bracket term changes
nothing. -/
theorem equalCharacteristicLubinTateAmbientBracket_succ_eq_of_torsion
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t n x) :
    equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a x =
      equalCharacteristicLubinTateAmbientBracket F ι t n a x := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    Finset.sum_range_succ,
    equalCharacteristicLubinTateAmbientBracket_apply,
    hx, mul_zero, add_zero]

/-- Applying `e` to an `(n+1)`-term bracket on level `n+1` torsion drops
the bracket level by one. -/
theorem equalCharacteristicLubinTateAmbientPiEnd_bracket_succ_of_torsion
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t (n + 1) x) :
    equalCharacteristicLubinTateAmbientPiEnd F t
        (equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a x) =
      equalCharacteristicLubinTateAmbientBracket F ι t n a
        (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
  rw [equalCharacteristicLubinTateAmbientPiEnd_bracket]
  exact equalCharacteristicLubinTateAmbientBracket_succ_eq_of_torsion
    F ι t n a (equalCharacteristicLubinTateAmbientPiEnd F t x)
      (equalCharacteristicLubinTateAmbientPiEnd_torsion_pred F t n x hx)

/-- Multiplicativity of the genuine truncated brackets on ambient
`e^n`-division points. -/
theorem equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a b : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t n x) :
    equalCharacteristicLubinTateAmbientBracket F ι t n (a * b) x =
      equalCharacteristicLubinTateAmbientBracket F ι t n a
        (equalCharacteristicLubinTateAmbientBracket F ι t n b x) := by
  induction n generalizing a b x with
  | zero =>
      simp [equalCharacteristicLubinTateAmbientBracket_apply]
  | succ n ih =>
      have hxpred :
          IsEqualCharacteristicLubinTateAmbientTorsion F t n
            (equalCharacteristicLubinTateAmbientPiEnd F t x) :=
        equalCharacteristicLubinTateAmbientPiEnd_torsion_pred F t n x hx
      have hcoeff :
          PowerSeries.coeff 0 (a * b) =
            PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
          PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      calc
        equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) (a * b) x =
            ι (PowerSeries.coeff 0 (a * b)) * x +
              equalCharacteristicLubinTateAmbientBracket F ι t n
                (equalCharacteristicPowerSeriesTail (a * b))
                (equalCharacteristicLubinTateAmbientPiEnd F t x) :=
          equalCharacteristicLubinTateAmbientBracket_succ_apply
            F ι t n (a * b) x
        _ =
            ι (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              equalCharacteristicLubinTateAmbientBracket F ι t n
                (PowerSeries.C (PowerSeries.coeff 0 a) *
                    equalCharacteristicPowerSeriesTail b +
                  equalCharacteristicPowerSeriesTail a * b)
                (equalCharacteristicLubinTateAmbientPiEnd F t x) := by
          rw [hcoeff, equalCharacteristicPowerSeriesTail_mul]
        _ =
            ι (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              (equalCharacteristicLubinTateAmbientBracket F ι t n
                  (PowerSeries.C (PowerSeries.coeff 0 a) *
                    equalCharacteristicPowerSeriesTail b)
                  (equalCharacteristicLubinTateAmbientPiEnd F t x) +
                equalCharacteristicLubinTateAmbientBracket F ι t n
                  (equalCharacteristicPowerSeriesTail a * b)
                  (equalCharacteristicLubinTateAmbientPiEnd F t x)) := by
          congr 1
          exact congrArg
            (fun f : AddMonoid.End A ↦
              f (equalCharacteristicLubinTateAmbientPiEnd F t x))
            (equalCharacteristicLubinTateAmbientBracket_add F ι t n
              (PowerSeries.C (PowerSeries.coeff 0 a) *
                equalCharacteristicPowerSeriesTail b)
              (equalCharacteristicPowerSeriesTail a * b))
        _ =
            ι (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              (ι (PowerSeries.coeff 0 a) *
                  equalCharacteristicLubinTateAmbientBracket F ι t n
                    (equalCharacteristicPowerSeriesTail b)
                    (equalCharacteristicLubinTateAmbientPiEnd F t x) +
                equalCharacteristicLubinTateAmbientBracket F ι t n
                  (equalCharacteristicPowerSeriesTail a)
                  (equalCharacteristicLubinTateAmbientBracket F ι t n b
                    (equalCharacteristicLubinTateAmbientPiEnd F t x))) := by
          rw [equalCharacteristicLubinTateAmbientBracket_C_mul_apply,
            ih (equalCharacteristicPowerSeriesTail a) b
              (equalCharacteristicLubinTateAmbientPiEnd F t x) hxpred]
        _ =
            ι (PowerSeries.coeff 0 a) *
              (ι (PowerSeries.coeff 0 b) * x +
                equalCharacteristicLubinTateAmbientBracket F ι t n
                  (equalCharacteristicPowerSeriesTail b)
                  (equalCharacteristicLubinTateAmbientPiEnd F t x)) +
              equalCharacteristicLubinTateAmbientBracket F ι t n
                (equalCharacteristicPowerSeriesTail a)
                (equalCharacteristicLubinTateAmbientBracket F ι t n b
                  (equalCharacteristicLubinTateAmbientPiEnd F t x)) := by
          rw [ι.map_mul]
          ring
        _ =
            ι (PowerSeries.coeff 0 a) *
              equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) b x +
              equalCharacteristicLubinTateAmbientBracket F ι t n
                (equalCharacteristicPowerSeriesTail a)
                (equalCharacteristicLubinTateAmbientPiEnd F t
                  (equalCharacteristicLubinTateAmbientBracket F ι t
                    (n + 1) b x)) := by
          rw [equalCharacteristicLubinTateAmbientPiEnd_bracket_succ_of_torsion
              F ι t n b x hx,
            equalCharacteristicLubinTateAmbientBracket_succ_apply]
        _ =
            equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a
              (equalCharacteristicLubinTateAmbientBracket F ι t
                (n + 1) b x) :=
          (equalCharacteristicLubinTateAmbientBracket_succ_apply F ι t n a
            (equalCharacteristicLubinTateAmbientBracket F ι t
              (n + 1) b x)).symm

end EqualCharacteristic
end LubinTate
