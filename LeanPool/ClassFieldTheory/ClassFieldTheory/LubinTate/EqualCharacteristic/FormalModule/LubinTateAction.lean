/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
/-!
# Equal-characteristic Lubin--Tate action

This file proves the algebraic identities needed to turn the finite brackets
from `EqualCharacteristicLubinTateEnd` into the action of
`(κ⟦T⟧ / T^n)ˣ` on the `T^n`-division points.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private theorem addMonoidHom_map_finset_sum
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

/-- Delete the constant coefficient of a power series and shift all
remaining coefficients down by one place. -/
noncomputable def equalCharacteristicPowerSeriesTail
    {k : Type*} [Semiring k] (a : k⟦X⟧) : k⟦X⟧ :=
  PowerSeries.mk fun i ↦ PowerSeries.coeff (i + 1) a

/-- States the theorem `equalCharacteristicPowerSeriesTail_coeff`. -/
@[simp]
theorem equalCharacteristicPowerSeriesTail_coeff
    {k : Type*} [Semiring k] (a : k⟦X⟧) (i : ℕ) :
    PowerSeries.coeff i (equalCharacteristicPowerSeriesTail a) =
      PowerSeries.coeff (i + 1) a := by
  simp [equalCharacteristicPowerSeriesTail]

/-- Split a power series into its constant coefficient and shifted tail. -/
theorem equalCharacteristicPowerSeries_eq_X_mul_tail_add_C
    {k : Type*} [Semiring k] (a : k⟦X⟧) :
    a = PowerSeries.X * equalCharacteristicPowerSeriesTail a +
      PowerSeries.C (PowerSeries.coeff 0 a) := by
  simpa [equalCharacteristicPowerSeriesTail,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      PowerSeries.eq_X_mul_shift_add_const a

/-- Product rule for the shifted tail:
`tail(ab) = C(a₀) tail(b) + tail(a)b`. -/
theorem equalCharacteristicPowerSeriesTail_mul
    {k : Type*} [CommRing k] (a b : k⟦X⟧) :
    equalCharacteristicPowerSeriesTail (a * b) =
      PowerSeries.C (PowerSeries.coeff 0 a) *
          equalCharacteristicPowerSeriesTail b +
        equalCharacteristicPowerSeriesTail a * b := by
  apply PowerSeries.X_mul_injective
  have ha := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C a
  have hb := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C b
  have hab := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C (a * b)
  have hcoeff :
      PowerSeries.coeff 0 (a * b) =
        PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  calc
    PowerSeries.X * equalCharacteristicPowerSeriesTail (a * b) =
        a * b - PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by
      calc
        _ =
            (PowerSeries.X * equalCharacteristicPowerSeriesTail (a * b) +
                PowerSeries.C (PowerSeries.coeff 0 (a * b))) -
              PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by ring
        _ = a * b - PowerSeries.C (PowerSeries.coeff 0 (a * b)) := by
          rw [← hab]
    _ = a * b - PowerSeries.C
          (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := by
      rw [hcoeff]
    _ =
        (PowerSeries.X * equalCharacteristicPowerSeriesTail a +
            PowerSeries.C (PowerSeries.coeff 0 a)) * b -
          PowerSeries.C
            (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := by
      exact congrArg
        (fun z : k⟦X⟧ ↦
          z * b - PowerSeries.C
            (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) ha
    _ = PowerSeries.X * (equalCharacteristicPowerSeriesTail a * b) +
          (PowerSeries.C (PowerSeries.coeff 0 a) * b -
            PowerSeries.C
              (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) := by
      ring
    _ = PowerSeries.X * (equalCharacteristicPowerSeriesTail a * b) +
          PowerSeries.X *
            (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b) := by
      congr 1
      calc
        PowerSeries.C (PowerSeries.coeff 0 a) * b -
            PowerSeries.C
              (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) =
            PowerSeries.C (PowerSeries.coeff 0 a) *
                (PowerSeries.X * equalCharacteristicPowerSeriesTail b +
                  PowerSeries.C (PowerSeries.coeff 0 b)) -
              PowerSeries.C
                (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) := by
          exact congrArg
            (fun z : k⟦X⟧ ↦
              PowerSeries.C (PowerSeries.coeff 0 a) * z -
                PowerSeries.C
                  (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b)) hb
        _ = PowerSeries.X *
            (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b) := by
          rw [mul_add,
            ← map_mul (PowerSeries.C : k →+* k⟦X⟧)]
          ring
    _ = PowerSeries.X *
          (PowerSeries.C (PowerSeries.coeff 0 a) *
              equalCharacteristicPowerSeriesTail b +
            equalCharacteristicPowerSeriesTail a * b) := by
      ring

/-- A point killed by the `n`-fold distinguished endomorphism. -/
def IsEqualCharacteristicLubinTateTorsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩) : Prop :=
  equalCharacteristicLubinTatePiIterate F n x = 0

/-- Iterating `e` `i+j` times is the same as first iterating `j` times and
then `i` times. -/
theorem equalCharacteristicLubinTatePiIterate_add
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (i j : ℕ) (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiIterate F (i + j) x =
      equalCharacteristicLubinTatePiIterate F i
        (equalCharacteristicLubinTatePiIterate F j x) := by
  change
    ((equalCharacteristicLubinTatePiEnd F) ^ (i + j)) x =
      ((equalCharacteristicLubinTatePiEnd F) ^ i)
        (((equalCharacteristicLubinTatePiEnd F) ^ j) x)
  rw [pow_add]
  rfl

/-- A point killed at level `n` is killed at every higher level. -/
theorem equalCharacteristicLubinTatePiIterate_eq_zero_of_le
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {n m : ℕ} (hnm : n ≤ m) (x : F.residueField⸨X⸩)
    (hx : IsEqualCharacteristicLubinTateTorsion F n x) :
    equalCharacteristicLubinTatePiIterate F m x = 0 := by
  rw [← Nat.sub_add_cancel hnm,
    equalCharacteristicLubinTatePiIterate_add, hx, map_zero]

/-- If `x` is killed at level `n+1`, then `e(x)` is killed at level `n`. -/
theorem equalCharacteristicLubinTatePiEnd_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩)
    (hx : IsEqualCharacteristicLubinTateTorsion F (n + 1) x) :
    IsEqualCharacteristicLubinTateTorsion F n
      (equalCharacteristicLubinTatePiEnd F x) := by
  exact hx

/-- Recursive evaluation formula for a finite bracket. -/
theorem equalCharacteristicLubinTateBracket_succ_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTateBracket F (n + 1) a x =
      algebraMap F.residueField F.residueField⸨X⸩
          (PowerSeries.coeff 0 a) * x +
        equalCharacteristicLubinTateBracket F n
          (equalCharacteristicPowerSeriesTail a)
          (equalCharacteristicLubinTatePiEnd F x) := by
  rw [equalCharacteristicLubinTateBracket_apply,
    Finset.sum_range_succ', add_comm,
    equalCharacteristicLubinTateBracket_apply]
  apply congrArg₂
    (fun y z : F.residueField⸨X⸩ ↦ y + z)
  · rfl
  · apply Finset.sum_congr rfl
    intro i hi
    rw [equalCharacteristicPowerSeriesTail_coeff,
      equalCharacteristicLubinTatePiIterate_succ]

/-- States the theorem `equalCharacteristicLubinTatePiIterate_one`. -/
theorem equalCharacteristicLubinTatePiIterate_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiIterate F 1 x =
      equalCharacteristicLubinTatePiEnd F x := by
  simp [equalCharacteristicLubinTatePiIterate]

/-- The distinguished endomorphism commutes with all of its iterates. -/
theorem equalCharacteristicLubinTatePiEnd_iterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (i : ℕ) (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiEnd F
        (equalCharacteristicLubinTatePiIterate F i x) =
      equalCharacteristicLubinTatePiIterate F i
        (equalCharacteristicLubinTatePiEnd F x) := by
  calc
    equalCharacteristicLubinTatePiEnd F
        (equalCharacteristicLubinTatePiIterate F i x) =
        equalCharacteristicLubinTatePiIterate F 1
          (equalCharacteristicLubinTatePiIterate F i x) :=
      (equalCharacteristicLubinTatePiIterate_one F
        (equalCharacteristicLubinTatePiIterate F i x)).symm
    _ = equalCharacteristicLubinTatePiIterate F (1 + i) x :=
      (equalCharacteristicLubinTatePiIterate_add F 1 i x).symm
    _ = equalCharacteristicLubinTatePiIterate F (i + 1) x := by
      rw [Nat.one_add]
    _ = equalCharacteristicLubinTatePiIterate F i
        (equalCharacteristicLubinTatePiIterate F 1 x) :=
      equalCharacteristicLubinTatePiIterate_add F i 1 x
    _ = equalCharacteristicLubinTatePiIterate F i
        (equalCharacteristicLubinTatePiEnd F x) := by
      exact congrArg (equalCharacteristicLubinTatePiIterate F i)
        (equalCharacteristicLubinTatePiIterate_one F x)

/-- A bracket is linear for the residue-field coefficient action on its
argument. -/
theorem equalCharacteristicLubinTateBracket_coefficient_mul_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) (c : F.residueField)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTateBracket F n a
        (algebraMap F.residueField F.residueField⸨X⸩ c * x) =
      algebraMap F.residueField F.residueField⸨X⸩ c *
        equalCharacteristicLubinTateBracket F n a x := by
  rw [equalCharacteristicLubinTateBracket_apply,
    equalCharacteristicLubinTateBracket_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [equalCharacteristicLubinTatePiIterate_coefficient_mul]
  ring

/-- Multiplying the coefficient series by the constant series `C(c)` has
the same effect as multiplying the bracket value by `c`. -/
theorem equalCharacteristicLubinTateBracket_C_mul_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (c : F.residueField) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTateBracket F n (PowerSeries.C c * a) x =
      algebraMap F.residueField F.residueField⸨X⸩ c *
        equalCharacteristicLubinTateBracket F n a x := by
  rw [equalCharacteristicLubinTateBracket_apply,
    equalCharacteristicLubinTateBracket_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_C_mul,
    (algebraMap F.residueField F.residueField⸨X⸩).map_mul]
  ring

/-- The bracket commutes with the distinguished endomorphism. -/
theorem equalCharacteristicLubinTatePiEnd_bracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLubinTatePiEnd F
        (equalCharacteristicLubinTateBracket F n a x) =
      equalCharacteristicLubinTateBracket F n a
        (equalCharacteristicLubinTatePiEnd F x) := by
  rw [equalCharacteristicLubinTateBracket_apply,
    addMonoidHom_map_finset_sum,
    equalCharacteristicLubinTateBracket_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [equalCharacteristicLubinTatePiEnd_coefficient_mul,
    equalCharacteristicLubinTatePiEnd_iterate]

/-- On a point killed by `e^n`, the `(n+1)`-term bracket equals the
`n`-term bracket. -/
theorem equalCharacteristicLubinTateBracket_succ_eq_of_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩)
    (hx : IsEqualCharacteristicLubinTateTorsion F n x) :
    equalCharacteristicLubinTateBracket F (n + 1) a x =
      equalCharacteristicLubinTateBracket F n a x := by
  rw [equalCharacteristicLubinTateBracket_apply,
    Finset.sum_range_succ, equalCharacteristicLubinTateBracket_apply,
    hx, mul_zero, add_zero]

/-- If `x` is killed by `e^(n+1)`, applying `e` to an `(n+1)`-term bracket
drops it to the `n`-term bracket at `e(x)`. -/
theorem equalCharacteristicLubinTatePiEnd_bracket_succ_of_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩)
    (hx : IsEqualCharacteristicLubinTateTorsion F (n + 1) x) :
    equalCharacteristicLubinTatePiEnd F
        (equalCharacteristicLubinTateBracket F (n + 1) a x) =
      equalCharacteristicLubinTateBracket F n a
        (equalCharacteristicLubinTatePiEnd F x) := by
  rw [equalCharacteristicLubinTatePiEnd_bracket]
  exact equalCharacteristicLubinTateBracket_succ_eq_of_torsion
    F n a (equalCharacteristicLubinTatePiEnd F x)
      (equalCharacteristicLubinTatePiEnd_torsion_pred F n x hx)

/-- Multiplicativity of the genuine truncated Lubin--Tate brackets on
`e^n`-division points. -/
theorem equalCharacteristicLubinTateBracket_mul_apply_of_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : F.residueField⟦X⟧)
    (x : F.residueField⸨X⸩)
    (hx : IsEqualCharacteristicLubinTateTorsion F n x) :
    equalCharacteristicLubinTateBracket F n (a * b) x =
      equalCharacteristicLubinTateBracket F n a
        (equalCharacteristicLubinTateBracket F n b x) := by
  induction n generalizing a b x with
  | zero =>
      simp [equalCharacteristicLubinTateBracket_apply]
  | succ n ih =>
      have hxpred :
          IsEqualCharacteristicLubinTateTorsion F n
            (equalCharacteristicLubinTatePiEnd F x) :=
        equalCharacteristicLubinTatePiEnd_torsion_pred F n x hx
      have hcoeff :
          PowerSeries.coeff 0 (a * b) =
            PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
          PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      calc
        equalCharacteristicLubinTateBracket F (n + 1) (a * b) x =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 (a * b)) * x +
              equalCharacteristicLubinTateBracket F n
                (equalCharacteristicPowerSeriesTail (a * b))
                (equalCharacteristicLubinTatePiEnd F x) :=
          equalCharacteristicLubinTateBracket_succ_apply F n (a * b) x
        _ =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              equalCharacteristicLubinTateBracket F n
                (PowerSeries.C (PowerSeries.coeff 0 a) *
                    equalCharacteristicPowerSeriesTail b +
                  equalCharacteristicPowerSeriesTail a * b)
                (equalCharacteristicLubinTatePiEnd F x) := by
          rw [hcoeff, equalCharacteristicPowerSeriesTail_mul]
        _ =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              (equalCharacteristicLubinTateBracket F n
                  (PowerSeries.C (PowerSeries.coeff 0 a) *
                    equalCharacteristicPowerSeriesTail b)
                  (equalCharacteristicLubinTatePiEnd F x) +
                equalCharacteristicLubinTateBracket F n
                  (equalCharacteristicPowerSeriesTail a * b)
                  (equalCharacteristicLubinTatePiEnd F x)) := by
          congr 1
          exact congrArg
            (fun f : AddMonoid.End F.residueField⸨X⸩ ↦
              f (equalCharacteristicLubinTatePiEnd F x))
            (equalCharacteristicLubinTateBracket_add F n
              (PowerSeries.C (PowerSeries.coeff 0 a) *
                equalCharacteristicPowerSeriesTail b)
              (equalCharacteristicPowerSeriesTail a * b))
        _ =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 a * PowerSeries.coeff 0 b) * x +
              (algebraMap F.residueField F.residueField⸨X⸩
                    (PowerSeries.coeff 0 a) *
                  equalCharacteristicLubinTateBracket F n
                    (equalCharacteristicPowerSeriesTail b)
                    (equalCharacteristicLubinTatePiEnd F x) +
                equalCharacteristicLubinTateBracket F n
                  (equalCharacteristicPowerSeriesTail a)
                  (equalCharacteristicLubinTateBracket F n b
                    (equalCharacteristicLubinTatePiEnd F x))) := by
          rw [equalCharacteristicLubinTateBracket_C_mul_apply,
            ih (equalCharacteristicPowerSeriesTail a) b
              (equalCharacteristicLubinTatePiEnd F x) hxpred]
        _ =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 a) *
              (algebraMap F.residueField F.residueField⸨X⸩
                    (PowerSeries.coeff 0 b) * x +
                equalCharacteristicLubinTateBracket F n
                  (equalCharacteristicPowerSeriesTail b)
                  (equalCharacteristicLubinTatePiEnd F x)) +
              equalCharacteristicLubinTateBracket F n
                (equalCharacteristicPowerSeriesTail a)
                (equalCharacteristicLubinTateBracket F n b
                  (equalCharacteristicLubinTatePiEnd F x)) := by
          rw [(algebraMap F.residueField
            F.residueField⸨X⸩).map_mul]
          ring
        _ =
            algebraMap F.residueField F.residueField⸨X⸩
                (PowerSeries.coeff 0 a) *
              equalCharacteristicLubinTateBracket F (n + 1) b x +
              equalCharacteristicLubinTateBracket F n
                (equalCharacteristicPowerSeriesTail a)
                (equalCharacteristicLubinTatePiEnd F
                  (equalCharacteristicLubinTateBracket F (n + 1) b x)) := by
          rw [equalCharacteristicLubinTatePiEnd_bracket_succ_of_torsion
              F n b x hx,
            equalCharacteristicLubinTateBracket_succ_apply]
        _ =
            equalCharacteristicLubinTateBracket F (n + 1) a
              (equalCharacteristicLubinTateBracket F (n + 1) b x) :=
          (equalCharacteristicLubinTateBracket_succ_apply F n a
            (equalCharacteristicLubinTateBracket F (n + 1) b x)).symm

end EqualCharacteristic
end LubinTate
