/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
/-!
# The uniformizer norm identity: irreducibility of the equal-characteristic primitive polynomial

The primitive level-`n+1` polynomial is lifted from `κ((T))` to `κ[[T]]`.
Modulo `T` this lift is the single monomial `Y ^ ((q - 1) * q ^ n)`, while
its constant coefficient is exactly `T`.  It is therefore Eisenstein at
`(T)`, and Gauss's lemma gives irreducibility over `κ((T))`.
-/

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The integral lift `Y ^ q + T * Y` of the equal-characteristic
Lubin--Tate polynomial. -/
noncomputable def equalCharacteristicLubinTateIntegralPiPolynomial
    (F : LocalField.{u, v} K) :
    Polynomial F.residueField⟦X⟧ :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C (PowerSeries.X : F.residueField⟦X⟧) * Polynomial.X

/-- The integral Lubin–Tate `π`-polynomial is monic. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomial_monic
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTateIntegralPiPolynomial F).Monic := by
  rw [equalCharacteristicLubinTateIntegralPiPolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  rw [Polynomial.degree_C_mul_X (PowerSeries.X_ne_zero),
    Polynomial.degree_X_pow]
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The integral Lubin–Tate `π`-polynomial has degree equal to the residue-field cardinality. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomial_natDegree
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTateIntegralPiPolynomial F).natDegree =
      Nat.card F.residueField := by
  rw [equalCharacteristicLubinTateIntegralPiPolynomial]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow,
      Polynomial.natDegree_C_mul_X _ (PowerSeries.X_ne_zero)]
    exact (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The compositional division polynomial over `κ[[T]]`. -/
noncomputable def equalCharacteristicLubinTateIntegralPiPolynomialIterate
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial F.residueField⟦X⟧ :=
  (equalCharacteristicLubinTateIntegralPiPolynomial F).comp^[n] Polynomial.X

/-- The `n`-fold integral `π`-iterate has degree `q ^ n`. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    equalCharacteristicLubinTateIntegralPiPolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- A successor integral `π`-iterate is obtained by one further composition. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_succ
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateIntegralPiPolynomialIterate F (n + 1) =
      (equalCharacteristicLubinTateIntegralPiPolynomial F).comp
        (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n) := by
  rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- Every iterate of the integral Lubin–Tate `π`-polynomial is monic. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n).Monic := by
  induction n with
  | zero => simp [equalCharacteristicLubinTateIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate_succ]
      exact (equalCharacteristicLubinTateIntegralPiPolynomial_monic F).comp ih
        (by
          rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate_natDegree]
          exact pow_ne_zero n (ne_of_gt
            (Nat.zero_lt_one.trans
              (Finite.one_lt_card : 1 < Nat.card F.residueField))))

/-- Base change carries the integral `π`-polynomial to the Laurent-field `π`-polynomial. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomial_map
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTateIntegralPiPolynomial F).map
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      equalCharacteristicLubinTatePiPolynomial F := by
  simp [equalCharacteristicLubinTateIntegralPiPolynomial,
    equalCharacteristicLubinTatePiPolynomial,
    equalCharacteristicLaurentUniformizer]

/-- Base change commutes with iteration of the integral `π`-polynomial. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_map
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n).map
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      equalCharacteristicLubinTatePiPolynomialIterate F n := by
  induction n with
  | zero =>
      simp [equalCharacteristicLubinTateIntegralPiPolynomialIterate,
        equalCharacteristicLubinTatePiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate_succ,
        equalCharacteristicLubinTatePiPolynomialIterate_succ,
        Polynomial.map_comp,
        equalCharacteristicLubinTateIntegralPiPolynomial_map, ih]

/-- Reducing coefficients sends the integral `π`-polynomial to `X ^ q`. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTateIntegralPiPolynomial F).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^ Nat.card F.residueField := by
  simp [equalCharacteristicLubinTateIntegralPiPolynomial]

/-- Reducing coefficients sends the `n`-fold integral `π`-iterate to `X ^ (q ^ n)`. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_map_constantCoeff
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^ (Nat.card F.residueField ^ n) := by
  induction n with
  | zero =>
      simp [equalCharacteristicLubinTateIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate_succ,
        Polynomial.map_comp,
        equalCharacteristicLubinTateIntegralPiPolynomial_map_constantCoeff,
        ih]
      simp [← pow_mul, pow_succ]

/-- Every integral `π`-iterate vanishes at zero. -/
theorem equalCharacteristicLubinTateIntegralPiPolynomialIterate_eval_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPiPolynomialIterate F n).eval 0 = 0 := by
  induction n with
  | zero =>
      simp [equalCharacteristicLubinTateIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicLubinTateIntegralPiPolynomialIterate_succ,
        Polynomial.eval_comp, ih]
      simp [equalCharacteristicLubinTateIntegralPiPolynomial,
        ne_of_gt (Nat.zero_lt_one.trans
          (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The integral lift of the primitive level-`n+1` polynomial. -/
noncomputable def equalCharacteristicLubinTateIntegralPrimitivePolynomial
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial F.residueField⟦X⟧ :=
  equalCharacteristicLubinTateIntegralPiPolynomialIterate F n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C (PowerSeries.X : F.residueField⟦X⟧)

/-- The integral primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicLubinTateIntegralPrimitivePolynomial]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicLubinTateIntegralPiPolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicLubinTateIntegralPiPolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- The integral primitive polynomial is monic. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).Monic := by
  rw [equalCharacteristicLubinTateIntegralPrimitivePolynomial]
  let A := equalCharacteristicLubinTateIntegralPiPolynomialIterate F n
  have hA : A.Monic :=
    equalCharacteristicLubinTateIntegralPiPolynomialIterate_monic F n
  have hmain : (A ^ (Nat.card F.residueField - 1)).Monic :=
    hA.pow _
  refine hmain.add_of_left ?_
  rw [Polynomial.degree_C (PowerSeries.X_ne_zero),
    Polynomial.degree_eq_natDegree hmain.ne_zero,
    Polynomial.natDegree_pow,
    equalCharacteristicLubinTateIntegralPiPolynomialIterate_natDegree]
  exact_mod_cast Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- Base change carries the integral primitive polynomial to its Laurent-field counterpart. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_map
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      equalCharacteristicLubinTatePrimitivePolynomial F n := by
  simp [equalCharacteristicLubinTateIntegralPrimitivePolynomial,
    equalCharacteristicLubinTatePrimitivePolynomial,
    equalCharacteristicLubinTateIntegralPiPolynomialIterate_map,
    equalCharacteristicLaurentUniformizer]

/-- Reducing the integral primitive polynomial yields its leading monomial. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n) := by
  simp [equalCharacteristicLubinTateIntegralPrimitivePolynomial,
    equalCharacteristicLubinTateIntegralPiPolynomialIterate_map_constantCoeff,
    ← pow_mul, Nat.mul_comm]

/-- The integral primitive polynomial has constant coefficient `X`. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).coeff 0 =
      (PowerSeries.X : F.residueField⟦X⟧) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [equalCharacteristicLubinTateIntegralPrimitivePolynomial,
    equalCharacteristicLubinTateIntegralPiPolynomialIterate_eval_zero,
    ne_of_gt (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The power-series parameter `X` does not lie in the square of its principal ideal. -/
theorem powerSeries_X_notMem_span_X_sq
    (k : Type*) [Field k] :
    (PowerSeries.X : k⟦X⟧) ∉
      (Ideal.span ({PowerSeries.X} : Set k⟦X⟧)) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  obtain ⟨a, ha⟩ := h
  have hunit : IsUnit (PowerSeries.X : k⟦X⟧) := by
    rw [isUnit_iff_dvd_one]
    refine ⟨a, ?_⟩
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k))
    simpa [pow_two, mul_assoc] using ha.symm
  exact PowerSeries.X_prime.not_isUnit hunit

/-- The integral primitive polynomial is Eisenstein at `(T)`. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_isEisensteinAt
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).IsEisensteinAt
      (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧)) := by
  let Q := equalCharacteristicLubinTateIntegralPrimitivePolynomial F n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    PowerSeries.span_X_isPrime.ne_top ?_ ?_
  · intro i hi
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have hcoeff :
        PowerSeries.constantCoeff
            ((equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).coeff i) =
          (Polynomial.X ^ d : Polynomial F.residueField).coeff i := by
      simpa only [Polynomial.coeff_map, d] using
        congrArg (fun p : Polynomial F.residueField ↦ p.coeff i)
          (equalCharacteristicLubinTateIntegralPrimitivePolynomial_map_constantCoeff F n)
    have hid : i < d := by
      simpa [Q, d,
        equalCharacteristicLubinTateIntegralPrimitivePolynomial_natDegree] using hi
    simpa [d, Polynomial.coeff_X_pow, ne_of_lt hid] using hcoeff
  · rw [equalCharacteristicLubinTateIntegralPrimitivePolynomial_coeff_zero]
    exact powerSeries_X_notMem_span_X_sq F.residueField

/-- The integral primitive polynomial is irreducible by Eisenstein's criterion. -/
theorem equalCharacteristicLubinTateIntegralPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (n : ℕ) :
    Irreducible (equalCharacteristicLubinTateIntegralPrimitivePolynomial F n) := by
  apply (equalCharacteristicLubinTateIntegralPrimitivePolynomial_isEisensteinAt F n).irreducible
    PowerSeries.span_X_isPrime
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).isPrimitive
  rw [equalCharacteristicLubinTateIntegralPrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- The primitive polynomial over `κ((T))` is monic. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomial F n).Monic := by
  rw [← equalCharacteristicLubinTateIntegralPrimitivePolynomial_map]
  exact (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).map _

/-- The primitive level-`n+1` polynomial over `κ((T))` is irreducible. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (n : ℕ) :
    Irreducible (equalCharacteristicLubinTatePrimitivePolynomial F n) := by
  have hmap :
      Irreducible
        ((equalCharacteristicLubinTateIntegralPrimitivePolynomial F n).map
          (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩)) :=
    (equalCharacteristicLubinTateIntegralPrimitivePolynomial_monic F n).irreducible_iff_irreducible_map_fraction_map.mp
      (equalCharacteristicLubinTateIntegralPrimitivePolynomial_irreducible F n)
  simpa [equalCharacteristicLubinTateIntegralPrimitivePolynomial_map] using hmap

end EqualCharacteristic
end LubinTate
