/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
/-!
# Primitive Lubin--Tate torsion points

This file records the exact torsion level of the primitive roots chosen in
`PrimitiveRoot`.  The standard division-polynomial iterates are first mapped
from the valuation ring to the base field and to its fixed separable closure.
Their evaluations satisfy the expected additivity under composition.

For a root of the primitive level-`n + 1` factor, the factorization of the
next iterate shows that the level-`n + 1` iterate vanishes.  The primitive
equation and nonvanishing of the uniformizer show that the level-`n` iterate
does not vanish.  All arguments are characteristic-independent.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `n`-fold standard iterate after extending coefficients from the
valuation ring to the base field. -/
noncomputable def standardLubinTatePolynomialIterateOverField
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial K :=
  (standardLubinTatePolynomialIterate F π n).map
    (algebraMap F.valuationSubring K)

/-- The `n`-fold standard iterate after extending coefficients to the fixed
separable closure of the base field. -/
noncomputable def standardLubinTatePolynomialIterateOverSeparableClosure
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial (SeparableClosure K) :=
  (standardLubinTatePolynomialIterate F π n).map
    ((algebraMap K (SeparableClosure K)).comp
      (algebraMap F.valuationSubring K))

/-- Evaluation of the field-valued iterate is evaluation over the valuation
ring with the coefficient embedding. -/
@[simp]
theorem standardLubinTatePolynomialIterateOverField_eval
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (n : ℕ) (x : K) :
    (standardLubinTatePolynomialIterateOverField F π n).eval x =
      Polynomial.eval₂ (algebraMap F.valuationSubring K) x
        (standardLubinTatePolynomialIterate F π n) := by
  rw [standardLubinTatePolynomialIterateOverField,
    Polynomial.eval_map]

/-- Evaluation of the separable-closure-valued iterate is evaluation over
the valuation ring with the composite coefficient embedding. -/
@[simp]
theorem standardLubinTatePolynomialIterateOverSeparableClosure_eval
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (n : ℕ) (x : SeparableClosure K) :
    (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval x =
      Polynomial.eval₂
        ((algebraMap K (SeparableClosure K)).comp
          (algebraMap F.valuationSubring K))
        x (standardLubinTatePolynomialIterate F π n) := by
  rw [standardLubinTatePolynomialIterateOverSeparableClosure,
    Polynomial.eval_map]

/-- Evaluating a compositional iterate is the corresponding iterate of the
evaluation function. -/
theorem standardLubinTatePolynomialIterate_eval₂_eq_iterate
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    {A : Type*} [CommSemiring A]
    (φ : F.valuationSubring →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (standardLubinTatePolynomialIterate F π n) =
      (fun y : A =>
        Polynomial.eval₂ φ y (standardLubinTatePolynomial F π))^[n] x := by
  simp [standardLubinTatePolynomialIterate]

/-- Standard iterate indices add under evaluated composition. -/
theorem standardLubinTatePolynomialIterate_eval₂_add
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    {A : Type*} [CommSemiring A]
    (φ : F.valuationSubring →+* A) (m n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (standardLubinTatePolynomialIterate F π (m + n)) =
      Polynomial.eval₂ φ
        (Polynomial.eval₂ φ x
          (standardLubinTatePolynomialIterate F π n))
        (standardLubinTatePolynomialIterate F π m) := by
  let g : A → A := fun y =>
    Polynomial.eval₂ φ y (standardLubinTatePolynomial F π)
  calc
    Polynomial.eval₂ φ x
        (standardLubinTatePolynomialIterate F π (m + n)) =
        g^[m + n] x := by
      exact
        standardLubinTatePolynomialIterate_eval₂_eq_iterate
          F π φ (m + n) x
    _ = g^[m] (g^[n] x) := by
      rw [Function.iterate_add_apply]
    _ = Polynomial.eval₂ φ
        (Polynomial.eval₂ φ x
          (standardLubinTatePolynomialIterate F π n))
        (standardLubinTatePolynomialIterate F π m) := by
      simp only [g,
        standardLubinTatePolynomialIterate_eval₂_eq_iterate]

/-- In the fixed separable closure, evaluation of standard iterates is
additive in the iterate index. -/
theorem standardLubinTatePolynomialIterateOverSeparableClosure_eval_add
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (m n : ℕ) (x : SeparableClosure K) :
    (standardLubinTatePolynomialIterateOverSeparableClosure
        F π (m + n)).eval x =
      (standardLubinTatePolynomialIterateOverSeparableClosure F π m).eval
        ((standardLubinTatePolynomialIterateOverSeparableClosure
          F π n).eval x) := by
  simpa only [
    standardLubinTatePolynomialIterateOverSeparableClosure_eval] using
      standardLubinTatePolynomialIterate_eval₂_add F π
        ((algebraMap K (SeparableClosure K)).comp
          (algebraMap F.valuationSubring K))
        m n x

/-- Evaluation of the primitive polynomial after a further coefficient map
is the primitive division equation for the mapped iterate. -/
theorem standardLubinTatePrimitivePolynomialOverField_eval₂
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    {A : Type*} [CommRing A] (φ : K →+* A)
    (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (standardLubinTatePrimitivePolynomialOverField F π n) =
      Polynomial.eval₂
          (φ.comp (algebraMap F.valuationSubring K)) x
          (standardLubinTatePolynomialIterate F π n) ^
          (Nat.card F.residueField - 1) +
        φ (π : K) := by
  rw [standardLubinTatePrimitivePolynomialOverField_formula,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_map, Polynomial.eval₂_C]

/-- The chosen primitive root satisfies its primitive division equation in
the fixed separable closure. -/
theorem chosenStandardLubinTatePrimitiveRoot_equation
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval
          (chosenStandardLubinTatePrimitiveRoot hπ n) ^
        (Nat.card F.residueField - 1) +
      algebraMap K (SeparableClosure K) (π : K) = 0 := by
  have hroot :=
    chosenStandardLubinTatePrimitiveRoot_isRoot hπ n
  change Polynomial.eval
      (chosenStandardLubinTatePrimitiveRoot hπ n)
      ((standardLubinTatePrimitivePolynomialOverField F π n).map
        (algebraMap K (SeparableClosure K))) = 0 at hroot
  rw [Polynomial.eval_map,
    standardLubinTatePrimitivePolynomialOverField_eval₂] at hroot
  simpa only [
    standardLubinTatePolynomialIterateOverSeparableClosure_eval] using
      hroot

/-- The chosen primitive level-`n + 1` root is killed by the
level-`n + 1` standard iterate. -/
theorem chosenStandardLubinTatePrimitiveRoot_iterate_succ_eq_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePolynomialIterateOverSeparableClosure
        F π (n + 1)).eval
      (chosenStandardLubinTatePrimitiveRoot hπ n) = 0 := by
  let φ : F.valuationSubring →+* SeparableClosure K :=
    (algebraMap K (SeparableClosure K)).comp
      (algebraMap F.valuationSubring K)
  let x := chosenStandardLubinTatePrimitiveRoot hπ n
  have hfactor := congrArg
    (Polynomial.eval₂ φ x)
    (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [Polynomial.eval₂_mul] at hfactor
  have hQ :
      Polynomial.eval₂ φ x
          (standardLubinTatePrimitivePolynomial F π n) = 0 := by
    have hroot :=
      chosenStandardLubinTatePrimitiveRoot_isRoot hπ n
    simpa [Polynomial.IsRoot,
      standardLubinTatePrimitivePolynomialOverField,
      Polynomial.eval_map, Polynomial.eval₂_map, φ, x] using hroot
  rw [hQ, mul_zero] at hfactor
  simpa only [
    standardLubinTatePolynomialIterateOverSeparableClosure_eval,
    φ, x] using hfactor

/-- The chosen primitive level-`n + 1` root is not already killed by the
level-`n` standard iterate. -/
theorem chosenStandardLubinTatePrimitiveRoot_iterate_ne_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval
        (chosenStandardLubinTatePrimitiveRoot hπ n) ≠ 0 := by
  intro hzero
  have hequation :=
    chosenStandardLubinTatePrimitiveRoot_equation hπ n
  rw [hzero, zero_pow, zero_add] at hequation
  · apply hπ.ne_zero
    apply (algebraMap K (SeparableClosure K)).injective
    simpa using hequation
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- In particular, the chosen primitive root is nonzero. -/
theorem chosenStandardLubinTatePrimitiveRoot_ne_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    chosenStandardLubinTatePrimitiveRoot hπ n ≠ 0 := by
  intro hzero
  apply chosenStandardLubinTatePrimitiveRoot_iterate_ne_zero hπ n
  rw [hzero,
    standardLubinTatePolynomialIterateOverSeparableClosure,
    Polynomial.eval_zero_map,
    standardLubinTatePolynomialIterate_eval_zero,
    map_zero]

/-- Applying the `(n - m)`-fold standard iterate to a primitive
level-`n + 1` point gives a root of the primitive level-`m + 1`
polynomial. -/
theorem chosenStandardLubinTatePrimitivePredecessor_isRoot
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {m n : ℕ} (hmn : m ≤ n) :
    let y :=
      (standardLubinTatePolynomialIterateOverSeparableClosure
        F π (n - m)).eval
          (chosenStandardLubinTatePrimitiveRoot hπ n)
    ((standardLubinTatePrimitivePolynomialOverField F π m).map
      (algebraMap K (SeparableClosure K))).IsRoot y := by
  let y :=
    (standardLubinTatePolynomialIterateOverSeparableClosure
      F π (n - m)).eval
        (chosenStandardLubinTatePrimitiveRoot hπ n)
  have hyIterate :
      (standardLubinTatePolynomialIterateOverSeparableClosure F π m).eval
          y =
        (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval
          (chosenStandardLubinTatePrimitiveRoot hπ n) := by
    calc
      (standardLubinTatePolynomialIterateOverSeparableClosure F π m).eval
          y =
          (standardLubinTatePolynomialIterateOverSeparableClosure
            F π (m + (n - m))).eval
              (chosenStandardLubinTatePrimitiveRoot hπ n) :=
        (standardLubinTatePolynomialIterateOverSeparableClosure_eval_add
          F π m (n - m)
          (chosenStandardLubinTatePrimitiveRoot hπ n)).symm
      _ =
          (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval
            (chosenStandardLubinTatePrimitiveRoot hπ n) := by
        rw [Nat.add_sub_of_le hmn]
  have hyEquation :
      (standardLubinTatePolynomialIterateOverSeparableClosure F π m).eval
            y ^ (Nat.card F.residueField - 1) +
        algebraMap K (SeparableClosure K) (π : K) = 0 := by
    rw [hyIterate]
    exact chosenStandardLubinTatePrimitiveRoot_equation hπ n
  change Polynomial.eval y
      ((standardLubinTatePrimitivePolynomialOverField F π m).map
        (algebraMap K (SeparableClosure K))) = 0
  rw [Polynomial.eval_map,
    standardLubinTatePrimitivePolynomialOverField_eval₂]
  simpa only [
    standardLubinTatePolynomialIterateOverSeparableClosure_eval] using
      hyEquation

end LubinTate

end
