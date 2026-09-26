/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import Mathlib.FieldTheory.IsSepClosed
/-!
# The uniformizer norm identity: equal-characteristic Lubin--Tate division polynomials

Let `P(Y)=Y^q+TY`.  Its `n`-fold compositional iterate has degree `q^n`.
The polynomial

`Q_(n+1)(Y) = P^[n](Y)^(q-1) + T`

cuts out the primitive level-`n+1` division points.  Here we construct these
polynomials over `κ((T))`, prove the degree calculation, and choose an actual
primitive root in the separable closure.
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

private instance equalCharacteristicDivisionBaseCharP
    (F : LocalField.{u, v} K)
    :
    CharP F.residueField⸨X⸩ F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField F.residueField⸨X⸩).injective
    F.residueCharacteristic

private instance equalCharacteristicDivisionClosureCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] :
    CharP (SeparableClosure F.residueField⸨X⸩)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField⸨X⸩
      (SeparableClosure F.residueField⸨X⸩)).injective
    F.residueCharacteristic

/-- The base Lubin--Tate polynomial `Y^q + TY` over `κ((T))`. -/
noncomputable def equalCharacteristicLubinTatePiPolynomial
    (F : LocalField.{u, v} K) :
    Polynomial F.residueField⸨X⸩ :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C (equalCharacteristicLaurentUniformizer F) * Polynomial.X

/-- The Laurent-series parameter `T` is nonzero. -/
theorem equalCharacteristicLaurentUniformizer_ne_zero
    (F : LocalField.{u, v} K) :
    equalCharacteristicLaurentUniformizer F ≠ 0 := by
  rw [equalCharacteristicLaurentUniformizer]
  change HahnSeries.ofPowerSeries ℤ F.residueField PowerSeries.X ≠ 0
  intro hX
  apply (PowerSeries.X_ne_zero (R := F.residueField))
  apply (HahnSeries.ofPowerSeries_injective
    (Γ := ℤ) (R := F.residueField))
  simpa only [map_zero] using hX

/-- The base Lubin--Tate polynomial has degree `q`. -/
theorem equalCharacteristicLubinTatePiPolynomial_natDegree
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTatePiPolynomial F).natDegree =
      Nat.card F.residueField := by
  rw [equalCharacteristicLubinTatePiPolynomial]
  calc
    (Polynomial.X ^ Nat.card F.residueField +
        Polynomial.C (equalCharacteristicLaurentUniformizer F) *
          Polynomial.X).natDegree =
        (Polynomial.X ^ Nat.card F.residueField).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by
        rw [Polynomial.natDegree_X_pow,
          Polynomial.natDegree_C_mul_X _
            (equalCharacteristicLaurentUniformizer_ne_zero F)]
        exact (Finite.one_lt_card : 1 < Nat.card F.residueField))
    _ = Nat.card F.residueField := Polynomial.natDegree_X_pow _

/-- The `n`-fold compositional iterate of the base Lubin--Tate polynomial,
starting from `Y`. -/
noncomputable def equalCharacteristicLubinTatePiPolynomialIterate
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial F.residueField⸨X⸩ :=
  (equalCharacteristicLubinTatePiPolynomial F).comp^[n] Polynomial.X

/-- The `n`-fold iterate has degree `q^n`. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePiPolynomialIterate F n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [equalCharacteristicLubinTatePiPolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    equalCharacteristicLubinTatePiPolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- The polynomial whose roots are exactly the primitive level-`n+1`
division points. -/
noncomputable def equalCharacteristicLubinTatePrimitivePolynomial
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial F.residueField⸨X⸩ :=
  equalCharacteristicLubinTatePiPolynomialIterate F n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C (equalCharacteristicLaurentUniformizer F)

/-- The primitive level-`n+1` polynomial has the expected positive degree
`(q-1)q^n`. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomial F n).natDegree =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [equalCharacteristicLubinTatePrimitivePolynomial]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicLubinTatePiPolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      equalCharacteristicLubinTatePiPolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- Evaluation of the base polynomial in any ambient field is the ambient
distinguished endomorphism. -/
theorem equalCharacteristicLubinTatePiPolynomial_eval₂
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (x : A) :
    Polynomial.eval₂ φ x (equalCharacteristicLubinTatePiPolynomial F) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicLaurentUniformizer F)) x := by
  simp [equalCharacteristicLubinTatePiPolynomial,
    equalCharacteristicLubinTateAmbientPiEnd_apply]

/-- The additive-endomorphism iterate agrees with ordinary function
iteration. -/
theorem equalCharacteristicLubinTateAmbientPiIterate_eq_function_iterate
    (F : LocalField.{u, v} K)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (t : A) (n : ℕ) (x : A) :
    equalCharacteristicLubinTateAmbientPiIterate F t n x =
      (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F t y)^[n] x := by
  induction n generalizing x with
  | zero => simp [equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ n ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        Function.iterate_succ_apply, ih]

/-- Evaluation of the compositional division polynomial is the actual
ambient iterate of `e`. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicLubinTatePiPolynomialIterate F n) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicLaurentUniformizer F)) n x := by
  have hfun :
      (fun y : A ↦ Polynomial.eval₂ φ y
        (equalCharacteristicLubinTatePiPolynomial F)) =
      (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicLaurentUniformizer F)) y) := by
    funext y
    exact equalCharacteristicLubinTatePiPolynomial_eval₂ F φ y
  calc
    Polynomial.eval₂ φ x
        (equalCharacteristicLubinTatePiPolynomialIterate F n) =
        (fun y : A ↦ Polynomial.eval₂ φ y
          (equalCharacteristicLubinTatePiPolynomial F))^[n] x := by
      rw [equalCharacteristicLubinTatePiPolynomialIterate,
        Polynomial.iterate_comp_eval₂, Polynomial.eval₂_X]
    _ =
        (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
          (φ (equalCharacteristicLaurentUniformizer F)) y)^[n] x := by
      exact congrArg (fun f : A → A ↦ f^[n] x) hfun
    _ = equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicLaurentUniformizer F)) n x :=
      (equalCharacteristicLubinTateAmbientPiIterate_eq_function_iterate
        F (φ (equalCharacteristicLaurentUniformizer F)) n x).symm

/-- The residue-field cardinality is zero in the Laurent-series base field. -/
theorem residueField_natCard_cast_eq_zero
    (F : LocalField.{u, v} K) :
    (Nat.card F.residueField : F.residueField⸨X⸩) = 0 := by
  let := Fintype.ofFinite F.residueField
  rw [Nat.card_eq_fintype_card]
  rw [← map_natCast
      (algebraMap F.residueField F.residueField⸨X⸩)
      (Fintype.card F.residueField),
    Nat.cast_card_eq_zero F.residueField, map_zero]

/-- The derivative of `Y^q+TY` is the nonzero constant `T`. -/
theorem equalCharacteristicLubinTatePiPolynomial_derivative
    (F : LocalField.{u, v} K) :
    (equalCharacteristicLubinTatePiPolynomial F).derivative =
      Polynomial.C (equalCharacteristicLaurentUniformizer F) := by
  simp [equalCharacteristicLubinTatePiPolynomial,
    Polynomial.derivative_pow, residueField_natCard_cast_eq_zero F]

/-- Recursive description of the compositional iterates. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_succ
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTatePiPolynomialIterate F (n + 1) =
      (equalCharacteristicLubinTatePiPolynomial F).comp
        (equalCharacteristicLubinTatePiPolynomialIterate F n) := by
  rw [equalCharacteristicLubinTatePiPolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- The derivative of the `n`-fold division polynomial is the nonzero
constant `T^n`. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_derivative
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePiPolynomialIterate F n).derivative =
      Polynomial.C (equalCharacteristicLaurentUniformizer F ^ n) := by
  induction n with
  | zero =>
      simp [equalCharacteristicLubinTatePiPolynomialIterate]
  | succ n ih =>
      rw [equalCharacteristicLubinTatePiPolynomialIterate_succ,
        Polynomial.derivative_comp, ih,
        equalCharacteristicLubinTatePiPolynomial_derivative]
      simp [pow_succ]

/-- Every iterated division polynomial is separable. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_separable
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePiPolynomialIterate F n).Separable := by
  rw [Polynomial.separable_def']
  refine ⟨0,
    Polynomial.C ((equalCharacteristicLaurentUniformizer F ^ n)⁻¹), ?_⟩
  rw [equalCharacteristicLubinTatePiPolynomialIterate_derivative]
  simp only [zero_mul, zero_add]
  rw [← map_mul,
    inv_mul_cancel₀ (pow_ne_zero n
      (equalCharacteristicLaurentUniformizer_ne_zero F)), map_one]

/-- The next division polynomial factors as the preceding one times the
primitive factor. -/
theorem equalCharacteristicLubinTatePiPolynomialIterate_succ_factor
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTatePiPolynomialIterate F (n + 1) =
      equalCharacteristicLubinTatePiPolynomialIterate F n *
        equalCharacteristicLubinTatePrimitivePolynomial F n := by
  have hq : Nat.card F.residueField ≠ 0 :=
    ne_of_gt (Nat.zero_lt_one.trans
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
  rw [equalCharacteristicLubinTatePiPolynomialIterate_succ,
    equalCharacteristicLubinTatePiPolynomial,
    equalCharacteristicLubinTatePrimitivePolynomial]
  simp only [Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [← pow_sub_one_mul hq]
  ring

/-- The primitive factor is separable because it divides the next separable
division polynomial. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_separable
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomial F n).Separable := by
  apply Polynomial.Separable.of_dvd
    (equalCharacteristicLubinTatePiPolynomialIterate_separable F (n + 1))
  exact ⟨equalCharacteristicLubinTatePiPolynomialIterate F n,
    by simpa [mul_comm] using
      (equalCharacteristicLubinTatePiPolynomialIterate_succ_factor F n)⟩

/-- The canonical base embedding into the chosen separable closure. -/
noncomputable def equalCharacteristicSeparableBaseHom
    (F : LocalField.{u, v} K) :
    F.residueField⸨X⸩ →+* SeparableClosure F.residueField⸨X⸩ where
  toFun x :=
    ⟨algebraMap F.residueField⸨X⸩
        (AlgebraicClosure F.residueField⸨X⸩) x,
      (separableClosure F.residueField⸨X⸩
        (AlgebraicClosure F.residueField⸨X⸩)).algebraMap_mem x⟩
  map_zero' := by
    apply Subtype.ext
    exact (algebraMap F.residueField⸨X⸩
      (AlgebraicClosure F.residueField⸨X⸩)).map_zero
  map_one' := by
    apply Subtype.ext
    exact (algebraMap F.residueField⸨X⸩
      (AlgebraicClosure F.residueField⸨X⸩)).map_one
  map_add' x y := by
    apply Subtype.ext
    exact (algebraMap F.residueField⸨X⸩
      (AlgebraicClosure F.residueField⸨X⸩)).map_add x y
  map_mul' x y := by
    apply Subtype.ext
    exact (algebraMap F.residueField⸨X⸩
      (AlgebraicClosure F.residueField⸨X⸩)).map_mul x y

/-- The coefficient embedding of the residue field into the chosen
separable closure of `κ((T))`. -/
noncomputable def equalCharacteristicSeparableCoefficientHom
    (F : LocalField.{u, v} K) :
    F.residueField →+* SeparableClosure F.residueField⸨X⸩ :=
  (equalCharacteristicSeparableBaseHom F).comp
    (algebraMap F.residueField F.residueField⸨X⸩)

/-- The image of `T` in the chosen separable closure. -/
noncomputable def equalCharacteristicSeparableUniformizer
    (F : LocalField.{u, v} K) :
    SeparableClosure F.residueField⸨X⸩ :=
  equalCharacteristicSeparableBaseHom F
      (equalCharacteristicLaurentUniformizer F)

/-- A primitive level-`n+1` division polynomial has a root in the separable
closure.  Separability of this polynomial is established below before the
root is used to define the level field. -/
theorem exists_equalCharacteristicLubinTatePrimitivePolynomial_root
    (F : LocalField.{u, v} K)
    (n : ℕ) :
    ∃ x : SeparableClosure F.residueField⸨X⸩,
      ((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (equalCharacteristicSeparableBaseHom F)).IsRoot x := by
  let φ := equalCharacteristicSeparableBaseHom F
  let Q := equalCharacteristicLubinTatePrimitivePolynomial F n
  have hnat : 0 < (Q.map φ).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective φ.injective,
      equalCharacteristicLubinTatePrimitivePolynomial_natDegree]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  have hdeg : (Q.map φ).degree ≠ 0 := by
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hnat)
  have hsep : (Q.map φ).Separable :=
    (equalCharacteristicLubinTatePrimitivePolynomial_separable F n).map
  exact IsSepClosed.exists_root (Q.map φ) hdeg hsep

end EqualCharacteristic
end LubinTate
