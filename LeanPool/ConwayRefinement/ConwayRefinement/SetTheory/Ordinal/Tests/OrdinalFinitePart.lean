/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

import Mathlib.Tactic.NormNum

/-!
# API checks for finite Cantor coefficients

The first two fixtures have constant Cantor coefficients five and seven. Their Hessenberg sum has
constant coefficient twelve; ordinary ordinal addition would instead discard the first constant
coefficient and produce seven. The first fixture is also checked directly against Mathlib's
Cantor-normal-form coefficient.

Finite removal is exercised away from both zero and the entire constant coefficient. The product
fixture has exact value `ω ^ 3 * 6`: it satisfies the proved `ω ^ 4` bound but is not below
`ω ^ 3`, distinguishing the required `p + q + 1` exponent from the nearby off-by-one bound.
-/

public noncomputable section

namespace Tests

/-- A natural ordinal with a nonzero degree-two term and constant coefficient five. -/
def degreeTwoWithFive : NatOrdinal :=
  ω^ (2 : NatOrdinal) + 5

/-- A natural ordinal with a nonzero degree-one term and constant coefficient seven. -/
def degreeOneWithSeven : NatOrdinal :=
  ω^ (1 : NatOrdinal) + 7

theorem degreeTwoWithFive_constantCoeff : degreeTwoWithFive.constantCoeff = 5 := by
  rw [degreeTwoWithFive]
  change (ω^ (2 : NatOrdinal) + (5 : ℕ)).constantCoeff = 5
  rw [NatOrdinal.constantCoeff_add_natCast,
    NatOrdinal.constantCoeff_wpow]
  norm_num

theorem degreeOneWithSeven_constantCoeff : degreeOneWithSeven.constantCoeff = 7 := by
  rw [degreeOneWithSeven]
  change (ω^ (1 : NatOrdinal) + (7 : ℕ)).constantCoeff = 7
  rw [NatOrdinal.constantCoeff_add_natCast,
    NatOrdinal.constantCoeff_wpow]
  norm_num

/-- Hessenberg addition adds both nonzero constant Cantor coefficients. -/
theorem asymmetricSum_constantCoeff :
    (degreeTwoWithFive + degreeOneWithSeven).constantCoeff = 12 := by
  rw [NatOrdinal.constantCoeff_add, degreeTwoWithFive_constantCoeff,
    degreeOneWithSeven_constantCoeff]

/-- The remainder agrees concretely with Mathlib's Cantor-normal-form
coefficient. -/
theorem degreeTwoWithFive_CNF_coeff_zero :
    Ordinal.CNF.coeff Ordinal.omega0 degreeTwoWithFive.val 0 = 5 := by
  rw [← NatOrdinal.coe_constantCoeff_eq_CNF_coeff,
    degreeTwoWithFive_constantCoeff]
  norm_num

/-- Removing three constant terms leaves exactly two constant terms. -/
theorem degreeTwoWithFive_removeThree :
    degreeTwoWithFive.removeNat 3 = ω^ (2 : NatOrdinal) + 2 := by
  symm
  apply (NatOrdinal.eq_removeNat_iff_add_natCast_eq (a := degreeTwoWithFive)
    (eta := ω^ (2 : NatOrdinal) + 2) (n := 3) (by
      rw [degreeTwoWithFive_constantCoeff]
      norm_num)).mpr
  rw [degreeTwoWithFive]
  rw [add_assoc]
  congr 1
  norm_num

/-- Removing the predecessor term from the left summand commutes with adding the right
summand. -/
theorem asymmetricSum_removeOne :
    (degreeTwoWithFive + degreeOneWithSeven).removeNat 1 =
      degreeTwoWithFive.removeNat 1 + degreeOneWithSeven := by
  apply NatOrdinal.removeOne_add_right
  rw [degreeTwoWithFive_constantCoeff]
  norm_num

/-- A degree-two natural ordinal with leading coefficient two. -/
def productLeft : NatOrdinal :=
  ω^ (2 : NatOrdinal) * 2

/-- A degree-one natural ordinal with leading coefficient three. -/
def productRight : NatOrdinal :=
  ω^ (1 : NatOrdinal) * 3

theorem productLeft_lt_wpow_three : productLeft < ω^ (3 : NatOrdinal) := by
  rw [productLeft]
  exact NatOrdinal.wpow_mul_natCast_lt (by norm_num) 2

theorem productRight_lt_wpow_two : productRight < ω^ (2 : NatOrdinal) := by
  rw [productRight]
  exact NatOrdinal.wpow_mul_natCast_lt (by norm_num) 3

/-- The asymmetric product has a nonzero term at exponent three. -/
theorem product_exact :
    productLeft * productRight = ω^ (3 : NatOrdinal) * 6 := by
  rw [productLeft, productRight]
  calc
    (ω^ (2 : NatOrdinal) * 2) * (ω^ (1 : NatOrdinal) * 3) =
        (ω^ (2 : NatOrdinal) * ω^ (1 : NatOrdinal)) * (2 * 3) := by
      ac_rfl
    _ = ω^ ((2 : NatOrdinal) + 1) * 6 := by
      rw [NatOrdinal.wpow_add]
      norm_num
    _ = ω^ (3 : NatOrdinal) * 6 := by norm_num

/-- The product is not below the nearby incorrect ceiling `ω ^ 3`. -/
theorem product_not_lt_wpow_three :
    ¬productLeft * productRight < ω^ (3 : NatOrdinal) := by
  rw [product_exact]
  apply not_lt_of_ge
  calc
    ω^ (3 : NatOrdinal) = ω^ (3 : NatOrdinal) * 1 := (mul_one _).symm
    _ ≤ ω^ (3 : NatOrdinal) * 6 :=
      mul_le_mul_right (show (1 : NatOrdinal) ≤ 6 by norm_num) _

/-- The finite-degree product estimate places the same product strictly below `ω ^ 4`. -/
theorem product_lt_wpow_four :
    productLeft * productRight < ω^ (4 : NatOrdinal) := by
  have h := NatOrdinal.mul_lt_wpow_natCast_add_one
    (p := 2) (q := 1) productLeft_lt_wpow_three productRight_lt_wpow_two
  norm_num at h
  exact h

end Tests
