/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.LeftPBW


/-!
# Commuting derivations and the next Ore stage

This file contains the coefficientwise lift needed in the iterated Ore tower.
If two coefficient derivations commute, the second one extends through the
first derivation-Ore extension by differentiating every coefficient in left
normal form.  The formulas at the coefficient embedding and at the Ore
variable are part of the interface used by later tower stages.
-/

@[expose] public section

namespace AlgebraicAnalysis.OreTower

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section


variable {B : Type*} [Ring B]

/-! ## Commuting iterates -/

lemma iterate_apply_commute (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) (n : ℕ) (b : B) :
    E ((D^[n]) b) = (D^[n]) (E b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        E (D ((D^[n]) b)) = D (E ((D^[n]) b)) := (hcomm _).symm
        _ = D ((D^[n]) (E b)) := congrArg D ih

lemma coefficientDerivation_commute (E F : OreDivisionDerivation B)
    (hcomm : ∀ b : B, E (F b) = F (E b)) (p : Polynomial B) :
    coefficientDerivation E (coefficientDerivation F p) =
      coefficientDerivation F (coefficientDerivation E p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
  | monomial i b =>
      rw [coefficientDerivation_monomial, coefficientDerivation_monomial,
        coefficientDerivation_monomial, coefficientDerivation_monomial,
        hcomm]

lemma coefficientDerivation_rightTerm (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b))
    (i : ℕ) (a b : B) (j : ℕ) :
    coefficientDerivation E (rightTerm D i a b j) =
      rightTerm D i (E a) b j + rightTerm D i a (E b) j := by
  rw [rightTerm]
  simp only [map_sum, coefficientDerivation_monomial]
  simp only [rightTerm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [OreDivisionDerivation.leibniz]
  rw [OreDivisionDerivation.map_nsmul]
  rw [iterate_apply_commute D E hcomm]
  rw [map_add]
  exact add_comm _ _

lemma coefficientDerivation_rightMulMonomial (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) (p : Polynomial B)
    (b : B) (j : ℕ) :
    coefficientDerivation E (rightMulMonomial D p b j) =
      rightMulMonomial D (coefficientDerivation E p) b j +
        rightMulMonomial D p (E b) j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [rightMulMonomial_add_left, map_add, hp, hq, map_add,
        rightMulMonomial_add_left D p q (E b) j]
      rw [rightMulMonomial_add_left D (coefficientDerivation E p)
        (coefficientDerivation E q) b j]
      abel
  | monomial i a =>
      simp? [rightMulMonomial, Polynomial.sum_monomial_index, rightTerm_zero]
      exact coefficientDerivation_rightTerm D E hcomm i a b j

lemma coefficientDerivation_rightMul (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) (p q : Polynomial B) :
    coefficientDerivation E (rightMul D p q) =
      rightMul D (coefficientDerivation E p) q +
        rightMul D p (coefficientDerivation E q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [rightMul_add, map_add, hq, hr, map_add, rightMul_add, rightMul_add]
      abel
  | monomial j b =>
      simp only [rightMul_monomial, coefficientDerivation_monomial]
      exact coefficientDerivation_rightMulMonomial D E hcomm p b j

/-! ## The lifted derivation -/

/-- Differentiate the coefficients of a left-normal Ore polynomial. -/
def liftDerivation (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) :
    OreDivisionDerivation (NormalOre D) where
  toFun z :=
    normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm z))
  map_zero' := by
    change normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm 0)) = 0
    rw [(normalFormAddEquiv D).symm.map_zero, map_zero, normalForm_zero]
  map_add' z w := by
    have h := (normalFormAddEquiv D).symm.toAddHom.map_add z w
    change (normalFormAddEquiv D).symm (z + w) =
      (normalFormAddEquiv D).symm z + (normalFormAddEquiv D).symm w at h
    change normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm (z + w))) = _
    rw [h, map_add, normalForm_add]
  leibniz' := by
    intro z w
    rcases normalForm_surjective D z with ⟨p, rfl⟩
    rcases normalForm_surjective D w with ⟨q, rfl⟩
    rw [← normalForm_mul]
    have hs (r : Polynomial B) :
        (normalFormAddEquiv D).symm (normalForm D r) = r := by
      change (normalFormAddEquiv D).symm ((normalFormAddEquiv D) r) = r
      exact (normalFormAddEquiv D).symm_apply_apply r
    rw [hs, hs, hs]
    rw [coefficientDerivation_rightMul D E hcomm]
    rw [normalForm_add, normalForm_mul, normalForm_mul]
    rw [add_comm]

@[simp]
theorem liftDerivation_apply_normalForm
    (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) (p : Polynomial B) :
    liftDerivation D E hcomm (normalForm D p) =
      normalForm D (coefficientDerivation E p) := by
  change normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm (normalForm D p))) =
    normalForm D (coefficientDerivation E p)
  have hs : (normalFormAddEquiv D).symm (normalForm D p) = p := by
    change (normalFormAddEquiv D).symm ((normalFormAddEquiv D) p) = p
    exact (normalFormAddEquiv D).symm_apply_apply p
  rw [hs]

@[simp]
theorem liftDerivation_apply_coefficient (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) (b : B) :
    liftDerivation D E hcomm (normalCoefficient D b) =
      normalCoefficient D (E b) := by
  rw [← normalForm_C, ← normalForm_C]
  change normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm ((normalFormAddEquiv D) (C b)))) =
    normalForm D (C (E b))
  rw [(normalFormAddEquiv D).symm_apply_apply]
  rw [← monomial_zero_left, coefficientDerivation_monomial]
  rw [monomial_zero_left, normalForm_C]

@[simp]
theorem liftDerivation_apply_variable (D E : OreDivisionDerivation B)
    (hcomm : ∀ b : B, D (E b) = E (D b)) :
    liftDerivation D E hcomm (normalVariable D) = 0 := by
  change normalForm D (coefficientDerivation E
      ((normalFormAddEquiv D).symm ((normalFormAddEquiv D) Polynomial.X))) = 0
  rw [(normalFormAddEquiv D).symm_apply_apply]
  rw [← Polynomial.monomial_one_one_eq_X, coefficientDerivation_monomial,
    derivation_one E, monomial_zero_right,
    normalForm_zero]

theorem liftDerivation_commute
    (D E F : OreDivisionDerivation B)
    (hDE : ∀ b : B, D (E b) = E (D b))
    (hDF : ∀ b : B, D (F b) = F (D b))
    (hEF : ∀ b : B, E (F b) = F (E b)) (z : NormalOre D) :
    liftDerivation D E hDE (liftDerivation D F hDF z) =
      liftDerivation D F hDF (liftDerivation D E hDE z) := by
  rcases normalForm_surjective D z with ⟨p, rfl⟩
  rw [liftDerivation_apply_normalForm, liftDerivation_apply_normalForm,
    liftDerivation_apply_normalForm, liftDerivation_apply_normalForm,
    coefficientDerivation_commute E F hEF]


end
end AlgebraicAnalysis.OreTower
