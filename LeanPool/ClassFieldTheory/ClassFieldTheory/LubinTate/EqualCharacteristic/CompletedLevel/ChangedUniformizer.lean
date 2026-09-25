/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import Mathlib.FieldTheory.IsSepClosed
/-!
# The completed theta-intertwining theorem: changing the equal-characteristic uniformizer

If `u` is a unit of `κ[[T]]`, then `uT` is again a uniformizer.  This file
repeats the mechanical part of the Lubin--Tate construction with

`P_{uT}(Y) = Y^q + uT Y`.

The primitive level polynomial is monic and Eisenstein at `(T)`, hence
irreducible over `κ((T))`; its simple root extension has degree
`(q - 1)q^n`, and the norm of the negative generator is exactly `uT`.
This is the changed-uniformizer algebra used in the proof of the completed theta-intertwining
  theorem.
-/

@[expose] public section

noncomputable
section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The changed integral uniformizer `uT`, for `u ∈ κ[[T]]ˣ`. -/
noncomputable def equalCharacteristicChangedIntegralUniformizer
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    F.residueField⟦X⟧ :=
  (a : F.residueField⟦X⟧) * PowerSeries.X

/-- The changed uniformizer `uT` in `κ((T))`. -/
noncomputable def equalCharacteristicChangedLaurentUniformizer
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    F.residueField⸨X⸩ :=
  algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
    (equalCharacteristicChangedIntegralUniformizer F a)

/-- The Laurent-series unit corresponding to the integral unit `a`. -/
noncomputable def equalCharacteristicChangedLaurentUnit
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    F.residueField⸨X⸩ˣ :=
  Units.map (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) a

/-- The changed parameter really is the changed parameter `uT`. -/
theorem equalCharacteristicChangedLaurentUniformizer_eq_unit_mul
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedLaurentUniformizer F a =
      (equalCharacteristicChangedLaurentUnit F a : F.residueField⸨X⸩) *
        equalCharacteristicLaurentUniformizer F := by
  simp [equalCharacteristicChangedLaurentUniformizer,
    equalCharacteristicChangedIntegralUniformizer,
    equalCharacteristicChangedLaurentUnit,
    equalCharacteristicLaurentUniformizer]

/-- Changing the Laurent uniformizer by the unit one leaves it unchanged. -/
@[simp]
theorem equalCharacteristicChangedLaurentUniformizer_one
    (F : LocalField.{u, v} K) :
    equalCharacteristicChangedLaurentUniformizer F 1 =
      equalCharacteristicLaurentUniformizer F := by
  simp [equalCharacteristicChangedLaurentUniformizer_eq_unit_mul,
    equalCharacteristicChangedLaurentUnit]

/-- A unit multiple of the integral uniformizer is nonzero. -/
theorem equalCharacteristicChangedIntegralUniformizer_ne_zero
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedIntegralUniformizer F a ≠ 0 := by
  exact mul_ne_zero a.ne_zero PowerSeries.X_ne_zero

/-- The changed Laurent uniformizer is nonzero. -/
theorem equalCharacteristicChangedLaurentUniformizer_ne_zero
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedLaurentUniformizer F a ≠ 0 := by
  rw [equalCharacteristicChangedLaurentUniformizer]
  intro h
  apply equalCharacteristicChangedIntegralUniformizer_ne_zero F a
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F.residueField)
  rw [map_zero]
  change (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩)
      (equalCharacteristicChangedIntegralUniformizer F a) = 0
  exact h

/-- The integral Lubin--Tate polynomial attached to `uT`. -/
noncomputable def equalCharacteristicChangedIntegralPiPolynomial
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    Polynomial F.residueField⟦X⟧ :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C (equalCharacteristicChangedIntegralUniformizer F a) *
      Polynomial.X

/-- The changed integral `π`-polynomial is monic. -/
theorem equalCharacteristicChangedIntegralPiPolynomial_monic
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedIntegralPiPolynomial F a).Monic := by
  rw [equalCharacteristicChangedIntegralPiPolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  rw [Polynomial.degree_C_mul_X
      (equalCharacteristicChangedIntegralUniformizer_ne_zero F a),
    Polynomial.degree_X_pow]
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The changed integral `π`-polynomial has degree equal to the residue-field cardinality. -/
theorem equalCharacteristicChangedIntegralPiPolynomial_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedIntegralPiPolynomial F a).natDegree =
      Nat.card F.residueField := by
  rw [equalCharacteristicChangedIntegralPiPolynomial,
    Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow,
      Polynomial.natDegree_C_mul_X _
        (equalCharacteristicChangedIntegralUniformizer_ne_zero F a)]
    exact (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The compositional iterate of `P_{uT}` over `κ[[T]]`. -/
noncomputable def equalCharacteristicChangedIntegralPiPolynomialIterate
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial F.residueField⟦X⟧ :=
  (equalCharacteristicChangedIntegralPiPolynomial F a).comp^[n] Polynomial.X

/-- The `n`-fold changed integral `π`-polynomial has degree `q ^ n`. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPiPolynomialIterate F a n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedIntegralPiPolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    equalCharacteristicChangedIntegralPiPolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- The successor iterate is obtained by one more composition with the changed `π`-polynomial. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_succ
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedIntegralPiPolynomialIterate F a (n + 1) =
      (equalCharacteristicChangedIntegralPiPolynomial F a).comp
        (equalCharacteristicChangedIntegralPiPolynomialIterate F a n) := by
  rw [equalCharacteristicChangedIntegralPiPolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- Every iterate of the changed integral `π`-polynomial is monic. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_monic
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPiPolynomialIterate F a n).Monic := by
  induction n with
  | zero => simp [equalCharacteristicChangedIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicChangedIntegralPiPolynomialIterate_succ]
      exact (equalCharacteristicChangedIntegralPiPolynomial_monic F a).comp ih
        (by
          rw [equalCharacteristicChangedIntegralPiPolynomialIterate_natDegree]
          exact pow_ne_zero n (ne_of_gt
            (Nat.zero_lt_one.trans
              (Finite.one_lt_card : 1 < Nat.card F.residueField))))

/-- Reducing coefficients sends the changed integral `π`-polynomial to `X ^ q`. -/
theorem equalCharacteristicChangedIntegralPiPolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedIntegralPiPolynomial F a).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^ Nat.card F.residueField := by
  simp [equalCharacteristicChangedIntegralPiPolynomial,
    equalCharacteristicChangedIntegralUniformizer]

/-- Reducing coefficients sends the `n`-fold changed `π`-iterate to `X ^ (q ^ n)`. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_map_constantCoeff
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPiPolynomialIterate F a n).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^ (Nat.card F.residueField ^ n) := by
  induction n with
  | zero =>
      simp [equalCharacteristicChangedIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicChangedIntegralPiPolynomialIterate_succ,
        Polynomial.map_comp,
        equalCharacteristicChangedIntegralPiPolynomial_map_constantCoeff,
        ih]
      simp [← pow_mul, pow_succ]

/-- Every changed integral `π`-iterate vanishes at zero. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_eval_zero
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPiPolynomialIterate F a n).eval 0 = 0 := by
  induction n with
  | zero =>
      simp [equalCharacteristicChangedIntegralPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicChangedIntegralPiPolynomialIterate_succ,
        Polynomial.eval_comp, ih]
      simp [equalCharacteristicChangedIntegralPiPolynomial,
        ne_of_gt (Nat.zero_lt_one.trans
          (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The integral primitive level-`n+1` polynomial for `uT`. -/
noncomputable def equalCharacteristicChangedIntegralPrimitivePolynomial
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial F.residueField⟦X⟧ :=
  equalCharacteristicChangedIntegralPiPolynomialIterate F a n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C (equalCharacteristicChangedIntegralUniformizer F a)

/-- The changed integral primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedIntegralPrimitivePolynomial]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicChangedIntegralPiPolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicChangedIntegralPiPolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- The changed integral primitive polynomial is monic. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).Monic := by
  rw [equalCharacteristicChangedIntegralPrimitivePolynomial]
  let A := equalCharacteristicChangedIntegralPiPolynomialIterate F a n
  have hA : A.Monic :=
    equalCharacteristicChangedIntegralPiPolynomialIterate_monic F a n
  have hmain : (A ^ (Nat.card F.residueField - 1)).Monic := hA.pow _
  refine hmain.add_of_left ?_
  rw [Polynomial.degree_C
      (equalCharacteristicChangedIntegralUniformizer_ne_zero F a),
    Polynomial.degree_eq_natDegree hmain.ne_zero,
    Polynomial.natDegree_pow,
    equalCharacteristicChangedIntegralPiPolynomialIterate_natDegree]
  exact_mod_cast Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- Reducing the changed integral primitive polynomial yields the expected monomial. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).map
        (PowerSeries.constantCoeff (R := F.residueField)) =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n) := by
  simp [equalCharacteristicChangedIntegralPrimitivePolynomial,
    equalCharacteristicChangedIntegralPiPolynomialIterate_map_constantCoeff,
    equalCharacteristicChangedIntegralUniformizer, ← pow_mul, Nat.mul_comm]

/-- The constant coefficient of the changed integral primitive polynomial is the changed
uniformizer. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).coeff 0 =
      equalCharacteristicChangedIntegralUniformizer F a := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [equalCharacteristicChangedIntegralPrimitivePolynomial,
    equalCharacteristicChangedIntegralPiPolynomialIterate_eval_zero,
    ne_of_gt (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The changed integral uniformizer does not lie in the square of the `X`-adic ideal. -/
theorem equalCharacteristicChangedIntegralUniformizer_notMem_span_X_sq
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedIntegralUniformizer F a ∉
      (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧)) ^ 2 := by
  intro h
  have hmul :=
    (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧) ^ 2).mul_mem_left
      (↑a⁻¹ : F.residueField⟦X⟧) h
  apply powerSeries_X_notMem_span_X_sq F.residueField
  simpa [equalCharacteristicChangedIntegralUniformizer, mul_assoc] using hmul

/-- The changed primitive polynomial is Eisenstein at `(T)`. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_isEisensteinAt
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).IsEisensteinAt
      (Ideal.span ({PowerSeries.X} : Set F.residueField⟦X⟧)) := by
  let Q := equalCharacteristicChangedIntegralPrimitivePolynomial F a n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    equalCharacteristicChangedIntegralPrimitivePolynomial_monic F a n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    PowerSeries.span_X_isPrime.ne_top ?_ ?_
  · intro i hi
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have hcoeff :
        PowerSeries.constantCoeff
            ((equalCharacteristicChangedIntegralPrimitivePolynomial F a n).coeff i) =
          (Polynomial.X ^ d : Polynomial F.residueField).coeff i := by
      simpa only [Polynomial.coeff_map, d] using
        congrArg (fun p : Polynomial F.residueField ↦ p.coeff i)
          (equalCharacteristicChangedIntegralPrimitivePolynomial_map_constantCoeff
            F a n)
    have hid : i < d := by
      simpa [Q, d,
        equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree] using hi
    simpa [d, Polynomial.coeff_X_pow, ne_of_lt hid] using hcoeff
  · rw [equalCharacteristicChangedIntegralPrimitivePolynomial_coeff_zero]
    exact equalCharacteristicChangedIntegralUniformizer_notMem_span_X_sq F a

/-- The changed integral primitive polynomial is irreducible by Eisenstein's criterion. -/
theorem equalCharacteristicChangedIntegralPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible (equalCharacteristicChangedIntegralPrimitivePolynomial F a n) := by
  apply (equalCharacteristicChangedIntegralPrimitivePolynomial_isEisensteinAt
    F a n).irreducible
    PowerSeries.span_X_isPrime
    (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F a n).isPrimitive
  rw [equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- The Laurent-series Lubin--Tate polynomial for the changed uniformizer. -/
noncomputable def equalCharacteristicChangedPiPolynomial
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    Polynomial F.residueField⸨X⸩ :=
  (equalCharacteristicChangedIntegralPiPolynomial F a).map
    (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩)

/-- Expands the changed Laurent `π`-polynomial as `X ^ q + π * X`. -/
theorem equalCharacteristicChangedPiPolynomial_eq
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedPiPolynomial F a =
      Polynomial.X ^ Nat.card F.residueField +
        Polynomial.C (equalCharacteristicChangedLaurentUniformizer F a) *
          Polynomial.X := by
  simp [equalCharacteristicChangedPiPolynomial,
    equalCharacteristicChangedIntegralPiPolynomial,
    equalCharacteristicChangedLaurentUniformizer]

/-- The changed Laurent `π`-polynomial has degree equal to the residue-field cardinality. -/
theorem equalCharacteristicChangedPiPolynomial_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedPiPolynomial F a).natDegree =
      Nat.card F.residueField := by
  rw [equalCharacteristicChangedPiPolynomial,
    (equalCharacteristicChangedIntegralPiPolynomial_monic F a).natDegree_map,
    equalCharacteristicChangedIntegralPiPolynomial_natDegree]

/-- The compositional iterate of `P_{uT}` over `κ((T))`. -/
noncomputable def equalCharacteristicChangedPiPolynomialIterate
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial F.residueField⸨X⸩ :=
  (equalCharacteristicChangedPiPolynomial F a).comp^[n] Polynomial.X

/-- The `n`-fold changed Laurent `π`-iterate has degree `q ^ n`. -/
theorem equalCharacteristicChangedPiPolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPiPolynomialIterate F a n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedPiPolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    equalCharacteristicChangedPiPolynomial_natDegree,
      Polynomial.natDegree_X, mul_one]

/-- A successor Laurent `π`-iterate is one further composition. -/
theorem equalCharacteristicChangedPiPolynomialIterate_succ
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedPiPolynomialIterate F a (n + 1) =
      (equalCharacteristicChangedPiPolynomial F a).comp
        (equalCharacteristicChangedPiPolynomialIterate F a n) := by
  rw [equalCharacteristicChangedPiPolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- Base change carries the integral `π`-iterate to the Laurent `π`-iterate. -/
theorem equalCharacteristicChangedIntegralPiPolynomialIterate_map
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedIntegralPiPolynomialIterate F a n).map
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      equalCharacteristicChangedPiPolynomialIterate F a n := by
  induction n with
  | zero =>
      simp [equalCharacteristicChangedIntegralPiPolynomialIterate,
        equalCharacteristicChangedPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicChangedIntegralPiPolynomialIterate_succ,
        equalCharacteristicChangedPiPolynomialIterate_succ,
        Polynomial.map_comp, equalCharacteristicChangedPiPolynomial, ih]

/-- The Laurent-series primitive polynomial for the changed uniformizer. -/
noncomputable def equalCharacteristicChangedPrimitivePolynomial
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial F.residueField⸨X⸩ :=
  (equalCharacteristicChangedIntegralPrimitivePolynomial F a n).map
    (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩)

/-- Expands the changed primitive polynomial using the changed `π`-iterate. -/
theorem equalCharacteristicChangedPrimitivePolynomial_eq
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedPrimitivePolynomial F a n =
      equalCharacteristicChangedPiPolynomialIterate F a n ^
          (Nat.card F.residueField - 1) +
        Polynomial.C (equalCharacteristicChangedLaurentUniformizer F a) := by
  simp [equalCharacteristicChangedPrimitivePolynomial,
    equalCharacteristicChangedIntegralPrimitivePolynomial,
    equalCharacteristicChangedIntegralPiPolynomialIterate_map,
    equalCharacteristicChangedLaurentUniformizer]

/-- The changed primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPrimitivePolynomial F a n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedPrimitivePolynomial,
    (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F a n).natDegree_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree]

/-- The changed primitive polynomial over the Laurent field is monic. -/
theorem equalCharacteristicChangedPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPrimitivePolynomial F a n).Monic := by
  exact (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F a n).map _

/-- The changed primitive polynomial over the Laurent field is irreducible. -/
theorem equalCharacteristicChangedPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible (equalCharacteristicChangedPrimitivePolynomial F a n) := by
  exact
    (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F a
      n).irreducible_iff_irreducible_map_fraction_map.mp
      (equalCharacteristicChangedIntegralPrimitivePolynomial_irreducible F a n)

/-- The changed Laurent uniformizer is the primitive polynomial's constant coefficient. -/
theorem equalCharacteristicChangedPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPrimitivePolynomial F a n).coeff 0 =
      equalCharacteristicChangedLaurentUniformizer F a := by
  rw [equalCharacteristicChangedPrimitivePolynomial, Polynomial.coeff_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_coeff_zero]
  rfl

/-- The derivative of the changed `π`-polynomial is the constant changed uniformizer. -/
theorem equalCharacteristicChangedPiPolynomial_derivative
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedPiPolynomial F a).derivative =
      Polynomial.C (equalCharacteristicChangedLaurentUniformizer F a) := by
  simp [equalCharacteristicChangedPiPolynomial_eq,
    Polynomial.derivative_pow, residueField_natCard_cast_eq_zero F]

/-- The derivative of the `n`-fold changed `π`-iterate is the `n`th uniformizer power. -/
theorem equalCharacteristicChangedPiPolynomialIterate_derivative
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPiPolynomialIterate F a n).derivative =
      Polynomial.C (equalCharacteristicChangedLaurentUniformizer F a ^ n) := by
  induction n with
  | zero => simp [equalCharacteristicChangedPiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicChangedPiPolynomialIterate_succ,
        Polynomial.derivative_comp, ih,
        equalCharacteristicChangedPiPolynomial_derivative]
      simp [pow_succ]

/-- Every iterate of the changed Laurent `π`-polynomial is separable. -/
theorem equalCharacteristicChangedPiPolynomialIterate_separable
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPiPolynomialIterate F a n).Separable := by
  rw [Polynomial.separable_def']
  refine ⟨0,
    Polynomial.C ((equalCharacteristicChangedLaurentUniformizer F a ^ n)⁻¹), ?_⟩
  rw [equalCharacteristicChangedPiPolynomialIterate_derivative]
  simp only [zero_mul, zero_add]
  rw [← map_mul,
    inv_mul_cancel₀ (pow_ne_zero n
      (equalCharacteristicChangedLaurentUniformizer_ne_zero F a)), map_one]

/-- The successor `π`-iterate factors through the current iterate and primitive factor. -/
theorem equalCharacteristicChangedPiPolynomialIterate_succ_factor
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedPiPolynomialIterate F a (n + 1) =
      equalCharacteristicChangedPiPolynomialIterate F a n *
        equalCharacteristicChangedPrimitivePolynomial F a n := by
  have hq : Nat.card F.residueField ≠ 0 :=
    ne_of_gt (Nat.zero_lt_one.trans
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
  rw [equalCharacteristicChangedPiPolynomialIterate_succ,
    equalCharacteristicChangedPiPolynomial_eq,
    equalCharacteristicChangedPrimitivePolynomial_eq]
  simp only [Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [← pow_sub_one_mul hq]
  ring

/-- The changed primitive polynomial is separable. -/
theorem equalCharacteristicChangedPrimitivePolynomial_separable
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedPrimitivePolynomial F a n).Separable := by
  apply Polynomial.Separable.of_dvd
    (equalCharacteristicChangedPiPolynomialIterate_separable F a (n + 1))
  exact ⟨equalCharacteristicChangedPiPolynomialIterate F a n,
    by simpa [mul_comm] using
      (equalCharacteristicChangedPiPolynomialIterate_succ_factor F a n)⟩

/-- The changed primitive polynomial has a root in the separable closure. -/
theorem exists_equalCharacteristicChangedPrimitivePolynomial_root
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    (n : ℕ) :
    ∃ x : SeparableClosure F.residueField⸨X⸩,
      ((equalCharacteristicChangedPrimitivePolynomial F a n).map
        (equalCharacteristicSeparableBaseHom F)).IsRoot x := by
  let φ := equalCharacteristicSeparableBaseHom F
  let Q := equalCharacteristicChangedPrimitivePolynomial F a n
  have hdeg : (Q.map φ).degree ≠ 0 := by
    have hnat : 0 < (Q.map φ).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective φ.injective,
        equalCharacteristicChangedPrimitivePolynomial_natDegree]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos)
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hnat)
  have hsep : (Q.map φ).Separable :=
    (equalCharacteristicChangedPrimitivePolynomial_separable F a n).map
  exact IsSepClosed.exists_root (Q.map φ) hdeg hsep

/-- A chosen changed-uniformizer primitive level root. -/
noncomputable def chosenEqualCharacteristicChangedPrimitiveRoot
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    SeparableClosure F.residueField⸨X⸩ :=
  Classical.choose (exists_equalCharacteristicChangedPrimitivePolynomial_root F a n)

/-- The chosen changed primitive element is a root of the base-changed polynomial. -/
theorem chosenEqualCharacteristicChangedPrimitiveRoot_isRoot
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    ((equalCharacteristicChangedPrimitivePolynomial F a n).map
      (equalCharacteristicSeparableBaseHom F)).IsRoot
        (chosenEqualCharacteristicChangedPrimitiveRoot F a n) :=
  Classical.choose_spec
    (exists_equalCharacteristicChangedPrimitivePolynomial_root F a n)

/-- The chosen changed primitive root is integral over the Laurent base field. -/
theorem chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    IsIntegral F.residueField⸨X⸩
      (chosenEqualCharacteristicChangedPrimitiveRoot F a n) := by
  refine ⟨equalCharacteristicChangedPrimitivePolynomial F a n,
    equalCharacteristicChangedPrimitivePolynomial_monic F a n, ?_⟩
  rw [← equalCharacteristicSeparableBaseHom_eq_algebraMap]
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (chosenEqualCharacteristicChangedPrimitiveRoot_isRoot F a n)

/-- The changed primitive polynomial is the minimal polynomial of the chosen root. -/
theorem equalCharacteristicChangedPrimitivePolynomial_eq_minpoly
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicChangedPrimitivePolynomial F a n =
      minpoly F.residueField⸨X⸩
        (chosenEqualCharacteristicChangedPrimitiveRoot F a n) := by
  apply minpoly.eq_of_irreducible_of_monic
    (equalCharacteristicChangedPrimitivePolynomial_irreducible F a n)
    _ (equalCharacteristicChangedPrimitivePolynomial_monic F a n)
  rw [Polynomial.aeval_def, ← equalCharacteristicSeparableBaseHom_eq_algebraMap]
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (chosenEqualCharacteristicChangedPrimitiveRoot_isRoot F a n)

/-- The simple level field for the changed uniformizer. -/
@[reducible]
noncomputable def equalCharacteristicChangedLevelField
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    IntermediateField F.residueField⸨X⸩
      (SeparableClosure F.residueField⸨X⸩) :=
  IntermediateField.adjoin F.residueField⸨X⸩
    {chosenEqualCharacteristicChangedPrimitiveRoot F a n}

/-- The changed Lubin–Tate level field is finite-dimensional over the Laurent field. -/
theorem equalCharacteristicChangedLevelField_finiteDimensional
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicChangedLevelField F a n) :=
  IntermediateField.adjoin.finiteDimensional
    (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)

/-- The changed level field has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedLevelField_finrank
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    Module.finrank F.residueField⸨X⸩
      (equalCharacteristicChangedLevelField F a n) =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  calc
    Module.finrank F.residueField⸨X⸩
        (equalCharacteristicChangedLevelField F a n) =
        (minpoly F.residueField⸨X⸩
          (chosenEqualCharacteristicChangedPrimitiveRoot F a n)).natDegree := by
      unfold equalCharacteristicChangedLevelField
      exact IntermediateField.adjoin.finrank
        (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)
    _ = (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
      rw [← equalCharacteristicChangedPrimitivePolynomial_eq_minpoly,
        equalCharacteristicChangedPrimitivePolynomial_natDegree]

/-- The chosen root as a generator of its changed-uniformizer level field. -/
noncomputable def equalCharacteristicChangedLevelGenerator
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicChangedLevelField F a n :=
  IntermediateField.AdjoinSimple.gen F.residueField⸨X⸩
    (chosenEqualCharacteristicChangedPrimitiveRoot F a n)

/-- The chosen changed level generator agrees with the generator of its power basis. -/
theorem equalCharacteristicChangedLevelGenerator_eq_powerBasis_gen
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicChangedLevelGenerator F a n =
      (IntermediateField.adjoin.powerBasis
        (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)).gen := by
  apply Subtype.ext
  simp [equalCharacteristicChangedLevelGenerator,
    equalCharacteristicChangedLevelField,
    IntermediateField.adjoin.powerBasis_gen]

/-- The norm of a negative element, separated from the changed level field's
large concrete type. -/
private theorem changedAlgebraNorm_neg
    {R S : Type*} [Field R] [Field S] [Algebra R S] (x : S) :
    Algebra.norm R (-x) = (-1) ^ Module.finrank R S * Algebra.norm R x := by
  rw [show -x = algebraMap R S (-1) * x by simp]
  rw [map_mul, Algebra.norm_algebraMap]

/-- The completed theta-intertwining theorem, changed-uniformizer norm identity:
`N(-λ_{uT,n+1}) = uT`. -/
theorem equalCharacteristicChanged_norm_neg_levelGenerator
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    Algebra.norm F.residueField⸨X⸩
        (-equalCharacteristicChangedLevelGenerator F a n) =
      equalCharacteristicChangedLaurentUniformizer F a := by
  let pb := IntermediateField.adjoin.powerBasis
    (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)
  have hmin : minpoly F.residueField⸨X⸩ pb.gen =
      equalCharacteristicChangedPrimitivePolynomial F a n := by
    simpa [pb, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen] using
      (equalCharacteristicChangedPrimitivePolynomial_eq_minpoly F a n).symm
  have hfinrank : Module.finrank F.residueField⸨X⸩
      (equalCharacteristicChangedLevelField F a n) = pb.dim := by
    unfold equalCharacteristicChangedLevelField
    exact pb.finrank
  rw [changedAlgebraNorm_neg,
    equalCharacteristicChangedLevelGenerator_eq_powerBasis_gen,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  change (-1) ^ Module.finrank F.residueField⸨X⸩
      (equalCharacteristicChangedLevelField F a n) *
      ((-1) ^ pb.dim *
        (minpoly F.residueField⸨X⸩ pb.gen).coeff 0) =
    equalCharacteristicChangedLaurentUniformizer F a
  rw [hmin, equalCharacteristicChangedPrimitivePolynomial_coeff_zero]
  rw [hfinrank]
  simp only [pb, IntermediateField.adjoin.powerBasis_dim]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end EqualCharacteristic
end LubinTate
