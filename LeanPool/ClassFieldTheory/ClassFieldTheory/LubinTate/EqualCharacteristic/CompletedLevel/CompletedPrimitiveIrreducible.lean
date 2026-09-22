/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
/-!
# The completed theta-intertwining theorem: irreducibility after completed unramified base change

The primitive Lubin--Tate polynomial remains Eisenstein after replacing the
finite residue field `κ` by its algebraic closure.  Consequently it remains
irreducible over `(AlgebraicClosure κ)((T))`.  This is the algebraic input
needed to prescribe the image of a primitive point when arithmetic Frobenius
is extended to the completed level field.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed base carries the Laurent-series algebra structure used in the
primitive-polynomial irreducibility argument. -/
noncomputable local instance equalCharacteristicCompletedPrimitiveIrreducibleBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- Coefficientwise extension of the integral primitive polynomial from
`κ[[T]]` to `(AlgebraicClosure κ)[[T]]`. -/
noncomputable def equalCharacteristicCompletedIntegralPrimitivePolynomial
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial (AlgebraicClosure F.residueField)⟦X⟧ :=
  (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
    (PowerSeries.map
      (algebraMap F.residueField (AlgebraicClosure F.residueField)))

/-- States the theorem `equalCharacteristicCompletedIntegralPrimitivePolynomial_monic`. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).Monic := by
  exact (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).map _

/-- States the theorem `equalCharacteristicCompletedIntegralPrimitivePolynomial_natDegree`. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicCompletedIntegralPrimitivePolynomial,
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).natDegree_map,
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_natDegree]

/-- The power-series coefficient map commutes with passage to Laurent
series. -/
theorem equalCharacteristicPowerSeriesLaurent_baseChange_commutes
    (F : LocalField.{u, v} K) :
    (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
        (equalCharacteristicCompletedUnramifiedField F.residueField)).comp
        (PowerSeries.map
          (algebraMap F.residueField (AlgebraicClosure F.residueField))) =
      (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField)).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) := by
  ext f m
  cases m with
  | ofNat i =>
      simp [RingHom.comp_apply]
  | negSucc i =>
      simp only [RingHom.comp_apply]
      change
        ((↑(PowerSeries.map
              (algebraMap F.residueField (AlgebraicClosure F.residueField)) f) :
            (AlgebraicClosure F.residueField)⸨X⸩).coeff (Int.negSucc i)) =
          algebraMap F.residueField (AlgebraicClosure F.residueField)
            ((↑f : F.residueField⸨X⸩).coeff (Int.negSucc i))
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
      simp

/-- Passing the integral polynomial to the Laurent fraction field gives
exactly the completed primitive polynomial. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_map
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).map
        (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField F.residueField)) =
      equalCharacteristicCompletedPrimitivePolynomial F n := by
  rw [equalCharacteristicCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map,
    equalCharacteristicPowerSeriesLaurent_baseChange_commutes,
    ← Polynomial.map_map,
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_map]
  rfl

/-- Reduction modulo `T` is the single leading monomial. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).map
        (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)) =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n) := by
  rw [equalCharacteristicCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map]
  have hcomp :
      (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)).comp
          (PowerSeries.map
            (algebraMap F.residueField (AlgebraicClosure F.residueField))) =
        (algebraMap F.residueField (AlgebraicClosure F.residueField)).comp
          (PowerSeries.constantCoeff (R := F.residueField)) := by
    ext f
    simp only [RingHom.comp_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
  rw [hcomp, ← Polynomial.map_map,
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_map_constantCoeff]
  simp

/-- States the theorem `equalCharacteristicCompletedIntegralPrimitivePolynomial_coeff_zero`. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).coeff 0 =
      (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧) := by
  rw [equalCharacteristicCompletedIntegralPrimitivePolynomial,
    Polynomial.coeff_map,
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_coeff_zero,
    PowerSeries.map_X]

/-- The completed integral primitive polynomial is Eisenstein at `(T)`. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_isEisensteinAt
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n).IsEisensteinAt
      (Ideal.span
        ({PowerSeries.X} :
          Set (AlgebraicClosure F.residueField)⟦X⟧)) := by
  let Q := equalCharacteristicCompletedIntegralPrimitivePolynomial F n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    equalCharacteristicCompletedIntegralPrimitivePolynomial_monic F n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    PowerSeries.span_X_isPrime.ne_top ?_ ?_
  · intro i hi
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have hcoeff :
        PowerSeries.constantCoeff
            ((equalCharacteristicCompletedIntegralPrimitivePolynomial F n).coeff i) =
          (Polynomial.X ^ d :
            Polynomial (AlgebraicClosure F.residueField)).coeff i := by
      simpa only [Polynomial.coeff_map, d] using
        congrArg
          (fun p : Polynomial (AlgebraicClosure F.residueField) ↦ p.coeff i)
          (equalCharacteristicCompletedIntegralPrimitivePolynomial_map_constantCoeff
            F n)
    have hid : i < d := by
      simpa [Q, d,
        equalCharacteristicCompletedIntegralPrimitivePolynomial_natDegree] using hi
    simpa [d, Polynomial.coeff_X_pow, ne_of_lt hid] using hcoeff
  · rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_coeff_zero]
    exact powerSeries_X_notMem_span_X_sq
      (AlgebraicClosure F.residueField)

/-- States the theorem `equalCharacteristicCompletedIntegralPrimitivePolynomial_irreducible`. -/
theorem equalCharacteristicCompletedIntegralPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (n : ℕ) :
    Irreducible (equalCharacteristicCompletedIntegralPrimitivePolynomial F n) := by
  apply
    (equalCharacteristicCompletedIntegralPrimitivePolynomial_isEisensteinAt F n).irreducible
      PowerSeries.span_X_isPrime
      (equalCharacteristicCompletedIntegralPrimitivePolynomial_monic F n).isPrimitive
  rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- The primitive polynomial remains irreducible over the completed maximal
unramified Laurent field. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (n : ℕ) :
    Irreducible (equalCharacteristicCompletedPrimitivePolynomial F n) := by
  have hmap :
      Irreducible
        ((equalCharacteristicCompletedIntegralPrimitivePolynomial F n).map
          (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
            (equalCharacteristicCompletedUnramifiedField F.residueField))) :=
    (equalCharacteristicCompletedIntegralPrimitivePolynomial_monic F
      n).irreducible_iff_irreducible_map_fraction_map.mp
      (equalCharacteristicCompletedIntegralPrimitivePolynomial_irreducible F n)
  rwa [equalCharacteristicCompletedIntegralPrimitivePolynomial_map] at hmap

end EqualCharacteristic
end LubinTate
