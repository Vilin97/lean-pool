/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Mathlib.FieldTheory.Finite.Basic
/-!
# The uniformizer norm identity: the unit action on primitive division points

The genuine truncated Lubin--Tate bracket attached to a unit power series
sends a primitive level-`n+1` point to another root of the same Eisenstein
polynomial.  This is the source of the finite-level Galois action; no
automorphism or normality is assumed here.
-/

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- On a level-one torsion point, every longer bracket only sees the
constant coefficient of the power series. -/
theorem equalCharacteristicLubinTateAmbientBracket_apply_of_levelOne_torsion
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (m : ℕ) (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t 1 x) :
    equalCharacteristicLubinTateAmbientBracket F ι t (m + 1) a x =
      ι (PowerSeries.coeff 0 a) * x := by
  induction m with
  | zero =>
      rw [equalCharacteristicLubinTateAmbientBracket_apply]
      simp [equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ m ih =>
      have hxm :
          IsEqualCharacteristicLubinTateAmbientTorsion F t (m + 1) x := by
        exact equalCharacteristicLubinTateAmbientPiIterate_eq_zero_of_le
          F t (Nat.succ_le_succ (Nat.zero_le m)) x hx
      rw [show m.succ + 1 = (m + 1) + 1 by omega,
        equalCharacteristicLubinTateAmbientBracket_succ_eq_of_torsion
          F ι t (m + 1) a x hxm,
        ih]

/-- Applying `e^n` after a bracket scales the level-one predecessor of any
primitive level-`n+1` point by the bracket's constant coefficient. -/
theorem equalCharacteristicLubinTateAmbientPrimitive_iterate_bracket
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t (n + 1) x) :
    equalCharacteristicLubinTateAmbientPiIterate F t n
        (equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a x) =
      ι (PowerSeries.coeff 0 a) *
        equalCharacteristicLubinTateAmbientPiIterate F t n x := by
  rw [equalCharacteristicLubinTateAmbientPiIterate_bracket]
  apply equalCharacteristicLubinTateAmbientBracket_apply_of_levelOne_torsion
  change equalCharacteristicLubinTateAmbientPiIterate F t 1
      (equalCharacteristicLubinTateAmbientPiIterate F t n x) = 0
  rw [← equalCharacteristicLubinTateAmbientPiIterate_add]
  rw [Nat.add_comm 1 n]
  exact hx

/-- Applying `e^n` after a unit bracket scales the primitive level-one
predecessor by the unit's constant coefficient. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_iterate_bracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicSeparableUniformizer F) n
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) a
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) =
      equalCharacteristicSeparableCoefficientHom F
          (PowerSeries.coeff 0 a) *
        equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) n
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  exact equalCharacteristicLubinTateAmbientPrimitive_iterate_bracket F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) n a
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)

/-- The constant coefficient of a unit power series is nonzero. -/
theorem powerSeries_unit_coeff_zero_ne_zero
    {k : Type*} [Field k] (a : k⟦X⟧ˣ) :
    PowerSeries.coeff 0 (a : k⟦X⟧) ≠ 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (PowerSeries.isUnit_iff_constantCoeff.mp a.isUnit).ne_zero

/-- The ambient bracket is additive in its power-series coordinate, in
subtraction form. -/
theorem equalCharacteristicLubinTateAmbientBracket_sub
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (m : ℕ) (a b : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateAmbientBracket F ι t m (a - b) =
      equalCharacteristicLubinTateAmbientBracket F ι t m a -
        equalCharacteristicLubinTateAmbientBracket F ι t m b := by
  apply AddMonoidHom.ext
  intro x
  change equalCharacteristicLubinTateAmbientBracket F ι t m (a - b) x =
    equalCharacteristicLubinTateAmbientBracket F ι t m a x -
      equalCharacteristicLubinTateAmbientBracket F ι t m b x
  rw [equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply,
    equalCharacteristicLubinTateAmbientBracket_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(PowerSeries.coeff (R := F.residueField) i).map_sub a b,
    ι.map_sub, sub_mul]

/-- Faithfulness of the truncated bracket on any primitive level-`n+1`
point.  This is the intrinsic Lubin--Tate statement used both before and
after passage to the completed maximal-unramified base. -/
theorem equalCharacteristicLubinTateAmbientPrimitive_bracket_eq_coeff
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    (n : ℕ) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t (n + 1) x)
    (hxpred : ¬ IsEqualCharacteristicLubinTateAmbientTorsion F t n x)
    (a b : F.residueField⟦X⟧)
    (hbracket :
      equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) a x =
        equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) b x) :
    ∀ i ≤ n, PowerSeries.coeff i a = PowerSeries.coeff i b := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
      let d := a - b
      have hdx :
          equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) d x = 0 := by
        change equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
          (a - b) x = 0
        rw [equalCharacteristicLubinTateAmbientBracket_sub]
        exact sub_eq_zero.mpr hbracket
      have hshift :
          equalCharacteristicLubinTateAmbientBracket F ι t (n + 1) d
              (equalCharacteristicLubinTateAmbientPiIterate F t (n - i) x) = 0 := by
        rw [← equalCharacteristicLubinTateAmbientPiIterate_bracket]
        rw [hdx, map_zero]
      have hynonzero :
          equalCharacteristicLubinTateAmbientPiIterate F t n x ≠ 0 :=
        hxpred
      rw [equalCharacteristicLubinTateAmbientBracket_apply] at hshift
      have hsum :
          (∑ j ∈ Finset.range (n + 1),
              ι (PowerSeries.coeff j d) *
                equalCharacteristicLubinTateAmbientPiIterate F t j
                  (equalCharacteristicLubinTateAmbientPiIterate F t (n - i) x)) =
            ι (PowerSeries.coeff i d) *
              equalCharacteristicLubinTateAmbientPiIterate F t n x := by
        classical
        rw [Finset.sum_eq_single i]
        · rw [← equalCharacteristicLubinTateAmbientPiIterate_add,
            Nat.add_sub_of_le hi]
        · intro j hj hji
          by_cases hji' : j < i
          · have hcoeff : PowerSeries.coeff j d = 0 := by
              change PowerSeries.coeff j (a - b) = 0
              rw [map_sub, ih j hji' (by omega), sub_self]
            rw [hcoeff, map_zero, zero_mul]
          · have hij : i < j := lt_of_le_of_ne (Nat.le_of_not_gt hji')
              (Ne.symm hji)
            have hkill :
                equalCharacteristicLubinTateAmbientPiIterate F t j
                    (equalCharacteristicLubinTateAmbientPiIterate F t (n - i) x) =
                  0 := by
              rw [← equalCharacteristicLubinTateAmbientPiIterate_add]
              apply equalCharacteristicLubinTateAmbientPiIterate_eq_zero_of_le
                F t (n := n + 1) (m := j + (n - i)) _ x hx
              omega
            rw [hkill, mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr
            (Nat.lt_succ_iff.mpr hi))).elim
      rw [hsum] at hshift
      have hcoeffMap : ι (PowerSeries.coeff i d) = 0 :=
        (mul_eq_zero.mp hshift).resolve_right hynonzero
      have hcoeff : PowerSeries.coeff i d = 0 := by
        apply ι.injective
        simpa using hcoeffMap
      simpa [d, sub_eq_zero] using hcoeff

/-- Faithfulness on a primitive level-`n+1` point: equality of two bracket
images forces equality of all coefficients visible at that level. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_bracket_eq_coeff
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : F.residueField⟦X⟧)
    (hbracket :
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) a
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) b
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) :
    ∀ i ≤ n, PowerSeries.coeff i a = PowerSeries.coeff i b := by
  exact equalCharacteristicLubinTateAmbientPrimitive_bracket_eq_coeff F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) n
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_not_torsion_pred F n)
    a b hbracket

/-- Every unit bracket of the chosen primitive point is again a root of
the primitive division polynomial. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_isRoot_bracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
      (equalCharacteristicSeparableBaseHom F)).IsRoot
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          (a : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) := by
  let z := equalCharacteristicLubinTateAmbientBracket F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (n + 1)
    (a : F.residueField⟦X⟧)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
  let y := equalCharacteristicLubinTateAmbientPiIterate F
    (equalCharacteristicSeparableUniformizer F) n
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
  let c := PowerSeries.coeff 0 (a : F.residueField⟦X⟧)
  have hc : c ≠ 0 := powerSeries_unit_coeff_zero_ne_zero a
  have hcpow : c ^ (Nat.card F.residueField - 1) = 1 := by
    let := Fintype.ofFinite F.residueField
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one c hc
  have hziterate :
      equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) n z =
        equalCharacteristicSeparableCoefficientHom F c * y := by
    simpa [z, y, c] using
      chosenEqualCharacteristicLubinTatePrimitiveRoot_iterate_bracket F n
        (a : F.residueField⟦X⟧)
  have hy := chosenEqualCharacteristicLubinTatePrimitiveRoot_equation F n
  have hzEquation :
      equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) n z ^
            (Nat.card F.residueField - 1) +
        equalCharacteristicSeparableUniformizer F = 0 := by
    rw [hziterate, mul_pow, ← map_pow,
      hcpow, map_one, one_mul]
    exact hy
  change Polynomial.eval
      z
      ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (equalCharacteristicSeparableBaseHom F)) = 0
  rw [Polynomial.eval_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂]
  exact hzEquation

end EqualCharacteristic
end LubinTate
