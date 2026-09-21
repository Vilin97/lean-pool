/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
/-!
# The completed theta-intertwining theorem: evaluation of changed Lubin--Tate polynomials

This small interface identifies the changed polynomials over `k((T))`
with their ambient Lubin--Tate endomorphisms.  Keeping the evaluation layer
separate avoids rebuilding the larger algebraic changed-uniformizer
construction when it is used at completed points.
-/

noncomputable section

open scoped LaurentSeries PowerSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Evaluation of the changed Lubin--Tate polynomial in any compatible
ambient field is the corresponding distinguished endomorphism. -/
theorem equalCharacteristicChangedPiPolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (x : A) :
    Polynomial.eval₂ φ x (equalCharacteristicChangedPiPolynomial F a) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) x := by
  rw [equalCharacteristicChangedPiPolynomial_eq]
  simp [equalCharacteristicLubinTateAmbientPiEnd_apply]

/-- Evaluation commutes with every compositional iterate of the changed
Lubin--Tate polynomial. -/
theorem equalCharacteristicChangedPiPolynomialIterate_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPiPolynomialIterate F a n) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) n x := by
  have hfun :
      (fun y : A ↦ Polynomial.eval₂ φ y
        (equalCharacteristicChangedPiPolynomial F a)) =
      (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) y) := by
    funext y
    exact equalCharacteristicChangedPiPolynomial_eval₂ F a φ y
  calc
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPiPolynomialIterate F a n) =
        (fun y : A ↦ Polynomial.eval₂ φ y
          (equalCharacteristicChangedPiPolynomial F a))^[n] x := by
      rw [equalCharacteristicChangedPiPolynomialIterate,
        Polynomial.iterate_comp_eval₂, Polynomial.eval₂_X]
    _ = (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) y)^[n] x := by
      exact congrArg (fun f : A → A ↦ f^[n] x) hfun
    _ = equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) n x :=
      (equalCharacteristicLubinTateAmbientPiIterate_eq_function_iterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F a)) n x).symm

/-- The changed primitive polynomial evaluates to the defining primitive
Lubin--Tate equation in every compatible ambient field. -/
theorem equalCharacteristicChangedPrimitivePolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPrimitivePolynomial F a n) =
      equalCharacteristicLubinTateAmbientPiIterate F
          (φ (equalCharacteristicChangedLaurentUniformizer F a)) n x ^
          (Nat.card F.residueField - 1) +
        φ (equalCharacteristicChangedLaurentUniformizer F a) := by
  rw [equalCharacteristicChangedPrimitivePolynomial_eq,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    equalCharacteristicChangedPiPolynomialIterate_eval₂,
    Polynomial.eval₂_C]

/-- A point killed exactly at division level `n + 1` is a root of the changed
primitive polynomial indexed by `n`. -/
theorem equalCharacteristicChangedPrimitivePolynomial_isRoot_of_primitive
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A)
    (htors : IsEqualCharacteristicLubinTateAmbientTorsion F
      (φ (equalCharacteristicChangedLaurentUniformizer F a)) (n + 1) x)
    (hprimitive : ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (φ (equalCharacteristicChangedLaurentUniformizer F a)) n x) :
    ((equalCharacteristicChangedPrimitivePolynomial F a n).map φ).IsRoot x := by
  let t := φ (equalCharacteristicChangedLaurentUniformizer F a)
  let z := equalCharacteristicLubinTateAmbientPiIterate F t n x
  have hz : z ≠ 0 := hprimitive
  have hend : equalCharacteristicLubinTateAmbientPiEnd F t z = 0 := by
    rw [show equalCharacteristicLubinTateAmbientPiEnd F t z =
        equalCharacteristicLubinTateAmbientPiIterate F t (1 + n) x by
      rw [equalCharacteristicLubinTateAmbientPiIterate_add,
        equalCharacteristicLubinTateAmbientPiIterate_one]]
    rw [Nat.add_comm 1 n]
    exact htors
  have hfactor : z * (z ^ (Nat.card F.residueField - 1) + t) = 0 := by
    rw [equalCharacteristicLubinTateAmbientPiEnd_apply] at hend
    rw [mul_add, mul_comm z t, ← pow_succ']
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')]
    exact hend
  have hequation : z ^ (Nat.card F.residueField - 1) + t = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hz
  change Polynomial.eval x
      ((equalCharacteristicChangedPrimitivePolynomial F a n).map φ) = 0
  rw [Polynomial.eval_map,
    equalCharacteristicChangedPrimitivePolynomial_eval₂]
  exact hequation

end EqualCharacteristic
end LubinTate
