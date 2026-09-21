/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
/-!
# The uniformizer norm identity: primitive equal-characteristic division points

The primitive factor `Q_(n+1)` constructed in the preceding file has roots
which are killed by the `(n+1)`-st Lubin--Tate iterate but not by the `n`-th
iterate.  This file chooses one such root in the fixed separable closure and
records that exact-level property.  No irreducibility or Galois assertion is
used here.
-/

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A chosen root of the primitive level-`n+1` division polynomial in the
fixed separable closure of `κ((T))`. -/
noncomputable def chosenEqualCharacteristicLubinTatePrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) : SeparableClosure F.residueField⸨X⸩ :=
  Classical.choose
    (exists_equalCharacteristicLubinTatePrimitivePolynomial_root F n)

/-- The chosen primitive division point is a root of `Q_(n+1)`. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
      (equalCharacteristicSeparableBaseHom F)).IsRoot
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) :=
  Classical.choose_spec
    (exists_equalCharacteristicLubinTatePrimitivePolynomial_root F n)

/-- Evaluation of `Q_(n+1)` is the defining primitive-division equation. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicLubinTatePrimitivePolynomial F n) =
      equalCharacteristicLubinTateAmbientPiIterate F
          (φ (equalCharacteristicLaurentUniformizer F)) n x ^
          (Nat.card F.residueField - 1) +
        φ (equalCharacteristicLaurentUniformizer F) := by
  rw [equalCharacteristicLubinTatePrimitivePolynomial,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    equalCharacteristicLubinTatePiPolynomialIterate_eval₂,
    Polynomial.eval₂_C]

/-- The chosen root satisfies the primitive-division equation. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_equation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicSeparableUniformizer F) n
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) ^
          (Nat.card F.residueField - 1) +
      equalCharacteristicSeparableUniformizer F = 0 := by
  have hroot := chosenEqualCharacteristicLubinTatePrimitiveRoot_isRoot F n
  change Polynomial.eval
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (equalCharacteristicSeparableBaseHom F)) = 0 at hroot
  rw [Polynomial.eval_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂] at hroot
  exact hroot

/-- A primitive level-`n+1` point is killed by the next division
polynomial. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) = 0
  have hroot := chosenEqualCharacteristicLubinTatePrimitiveRoot_isRoot F n
  have hfactor := congrArg
    (Polynomial.eval₂ (equalCharacteristicSeparableBaseHom F)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
    (equalCharacteristicLubinTatePiPolynomialIterate_succ_factor F n)
  rw [Polynomial.eval₂_mul] at hfactor
  have hQ : Polynomial.eval₂ (equalCharacteristicSeparableBaseHom F)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (equalCharacteristicLubinTatePrimitivePolynomial F n) = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using hroot
  rw [hQ, mul_zero] at hfactor
  rw [equalCharacteristicLubinTatePiPolynomialIterate_eval₂] at hfactor
  exact hfactor

/-- The chosen root is not already a level-`n` division point. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_not_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicSeparableUniformizer F) n
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  intro hpred
  have heq := chosenEqualCharacteristicLubinTatePrimitiveRoot_equation F n
  rw [hpred, zero_pow, zero_add] at heq
  · apply equalCharacteristicLaurentUniformizer_ne_zero F
    apply (equalCharacteristicSeparableBaseHom F).injective
    simpa [equalCharacteristicSeparableUniformizer] using heq
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- In particular, a primitive division point is nonzero. -/
theorem chosenEqualCharacteristicLubinTatePrimitiveRoot_ne_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    chosenEqualCharacteristicLubinTatePrimitiveRoot F n ≠ 0 := by
  intro hzero
  apply chosenEqualCharacteristicLubinTatePrimitiveRoot_not_torsion_pred F n
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicSeparableUniformizer F) n
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) = 0
  rw [hzero, map_zero]

end EqualCharacteristic
end LubinTate
