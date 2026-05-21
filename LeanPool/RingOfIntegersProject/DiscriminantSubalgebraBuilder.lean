/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.Discriminant
import LeanPool.RingOfIntegersProject.CertifyAdjoinRoot
import LeanPool.RingOfIntegersProject.DedekindCriteria
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

open Polynomial

section Part1
variable {n : ℕ} [NeZero n] {K : Type*}
[Field K] [CharZero K] {T : ℤ[X]}
{l : List ℤ}

--example : Algebra ℚ K := by apply?


lemma algebraBuilder_discr_eq_mul_polynomial_discr (hi : Irreducible T)
(A : SubalgebraBuilderLists n ℤ ℚ K T l) :
   algebraMap ℤ ℚ ((Algebra.discr ℤ (basisOfBuilderLists T l A) )) =
    ((algebraMap ℤ ℚ (A.d ^ n))⁻¹ * (algebraMap ℤ ℚ (∏ i, (A.B i i)))) ^ 2 *
    (algebraMap ℤ ℚ) (T.discriminant) := by
  have aux : (Polynomial.map (algebraMap ℤ ℚ) T).discriminant  = (algebraMap ℤ ℚ) (T.discriminant) := by
    rw [discriminant_map']
    exact RingHom.injective_int (algebraMap ℤ ℚ)
  have hm : Monic T := by
    simp only [Monic, leadingCoeff, (SubalgebraBuilderOfList T l A).hdeg,
      (SubalgebraBuilderOfList T l A).hm]
  have : Irreducible (Polynomial.map (algebraMap ℤ ℚ) T) := by
    exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (hm)).1 hi
  rw [← aux, ← Algebra.discr_of_isAdjoinRootMonic (isAMK A) this]
  exact OfBuilderList_discr_eq_prod_discr' A


lemma algebraBuilder_discr_eq_mul_polynomial_discr' (hi : Irreducible T)
(A : SubalgebraBuilderLists n ℤ ℚ K T l) :
    (Algebra.discr ℤ (basisOfBuilderLists T l A) ) =
      ((∏ i, (A.B i i)) ^ 2 * T.discriminant) / A.d ^ (2 * n) := by
  symm
  have haux : A.d ^ (2 * n) ≠ 0 := by
    simp only [ne_eq, pow_eq_zero_iff', A.hd, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    false_and, not_false_eq_true]
  refine Int.ediv_eq_of_eq_mul_left haux ?_
  apply_fun (algebraMap ℤ ℚ)
  rw [map_mul, map_mul, algebraBuilder_discr_eq_mul_polynomial_discr hi A, mul_pow]
  simp only [algebraMap_int_eq, Int.reduceNeg, map_pow, map_neg, map_one, map_prod, eq_intCast,
    inv_pow]
  cancel_denoms
  ring_nf
  nth_rw 2 [mul_assoc]
  rw [inv_pow]
  simp only [← mul_assoc, mul_eq_mul_right_iff, pow_eq_zero_iff',
   neg_eq_zero, one_ne_zero, ne_eq,
    false_and, or_false]
  rw [mul_assoc, mul_inv_cancel₀, mul_one]
  · rw [mul_comm]
    exact Rat.num_ne_zero.mp haux
  · exact RingHom.injective_int (algebraMap ℤ ℚ)

variable [NumberField K]

lemma discr_numberField_eq_discrSubalgebraBuilder (hi : Irreducible T)
(A : SubalgebraBuilderLists n ℤ ℚ K T l)
  (heq : subalgebraOfBuilderLists T l A = integralClosure ℤ K ) :
  NumberField.discr K = ((∏ i, (A.B i i)) ^ 2 * T.discriminant) / A.d ^ (2 * n) := by
  have hdeg : (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree := by
    apply Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int _
  rw [← algebraBuilder_discr_eq_mul_polynomial_discr' hi]
  have  f := Subalgebra.equivOfEq _ _ heq
  have icongr: Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin n := by
    refine Fintype.equivOfCardEq  ?_
    rw  [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, Fintype.card_fin]
    have :=  (Module.finrank_eq_card_basis (IsAdjoinRootMonic.powerBasis (isAMK A)).basis )
    rw [IsAdjoinRootMonic.powerBasis_dim, hdeg, (SubalgebraBuilderOfList T l A).hdeg, Fintype.card_fin] at this
    convert this
  let Bi := Basis.map (M' := integralClosure ℤ K) (basisOfBuilderLists T l A) f
  let Baux : Basis (Fin n) ℤ (NumberField.RingOfIntegers K) :=  Bi
  let Baux' := Basis.reindex Baux icongr.symm
  unfold NumberField.discr
  rw [Algebra.discr_eq_discr (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers.basis K) Baux',
  ← Algebra.discr_reindex ℤ (basisOfBuilderLists T l A) icongr.symm ,
  Algebra.discr_eq_discr_of_algEquiv _ f]
  congr
  simp only [Basis.coe_reindex, Equiv.symm_symm, Baux', Baux, Bi]
  rfl
