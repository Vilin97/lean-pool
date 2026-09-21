/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity

/-!
# The central-coordinate Ore stage

The zero-derivation Ore product is ordinary polynomial multiplication.  This
identifies the first stage in the recursive Weyl construction with a central
polynomial extension and transports ordinary differentiation to it.
-/

namespace Stafford38.OreCoordinateStage

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section

variable {B : Type*} [Ring B]

/-- The zero derivation on a ring. -/
def zeroDerivation : OreDivisionDerivation B where
  toFun := 0
  map_zero' := rfl
  map_add' := by simp
  leibniz' := by simp

@[simp]
theorem zeroDerivation_apply (b : B) : zeroDerivation b = 0 := rfl

@[simp]
theorem zeroDerivation_iterate_succ (n : ℕ) (b : B) :
    ((zeroDerivation : B → B)^[n + 1]) b = 0 := by
  rw [Function.iterate_succ_apply']
  rfl

theorem rightTerm_zeroDerivation (i : ℕ) (a b : B) (j : ℕ) :
    rightTerm zeroDerivation i a b j = monomial (i + j) (a * b) := by
  rw [rightTerm, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hkpos
    have hzero : ((zeroDerivation : B → B)^[1 + l]) b = 0 := by
      rw [Nat.add_comm]
      exact zeroDerivation_iterate_succ l b
    rw [hzero, nsmul_zero, mul_zero, monomial_zero_right]
  · simp

theorem rightMulMonomial_zeroDerivation (p : Polynomial B) (b : B) (j : ℕ) :
    rightMulMonomial zeroDerivation p b j = p * monomial j b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [rightMulMonomial_add_left, hp, hq, add_mul]
  | monomial i a =>
      rw [rightMulMonomial,
        Polynomial.sum_monomial_index a _ (rightTerm_zero zeroDerivation i b j)]
      rw [rightTerm_zeroDerivation, monomial_mul_monomial]

/-- With zero derivation, the Ore normal-form product is the ordinary central
polynomial product, even for a noncommutative coefficient ring. -/
theorem rightMul_zeroDerivation_eq_mul (p q : Polynomial B) :
    rightMul zeroDerivation p q = p * q := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [rightMul_add, hq, hr, mul_add]
  | monomial j b =>
      rw [rightMul_monomial, rightMulMonomial_zeroDerivation]

/-- The central-coordinate extension of `B`. -/
abbrev CoordinateStage := NormalOre (zeroDerivation : OreDivisionDerivation B)

@[simp]
theorem normalForm_mul_zeroDerivation (p q : Polynomial B) :
    normalForm zeroDerivation (p * q) =
      normalForm zeroDerivation p * normalForm zeroDerivation q := by
  rw [← rightMul_zeroDerivation_eq_mul, normalForm_mul]

@[simp]
theorem normalFormAddEquiv_symm_normalForm (p : Polynomial B) :
    (normalFormAddEquiv zeroDerivation).symm (normalForm zeroDerivation p) = p := by
  rw [show normalForm zeroDerivation p =
    (normalFormAddEquiv zeroDerivation) p by rfl]
  exact (normalFormAddEquiv zeroDerivation).symm_apply_apply p

/-- Ordinary polynomial differentiation, transported to the central Ore
stage. -/
def coordinateDerivation : OreDivisionDerivation (CoordinateStage (B := B)) where
  toFun z := normalForm zeroDerivation
    (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm z))
  map_zero' := by
    change normalForm zeroDerivation
      (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm 0)) = 0
    rw [(normalFormAddEquiv zeroDerivation).symm.map_zero,
      Polynomial.derivative_zero, normalForm_zero]
  map_add' z w := by
    have h := (normalFormAddEquiv zeroDerivation).symm.toAddHom.map_add z w
    change (normalFormAddEquiv zeroDerivation).symm (z + w) =
      (normalFormAddEquiv zeroDerivation).symm z +
        (normalFormAddEquiv zeroDerivation).symm w at h
    change normalForm zeroDerivation
      (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm (z + w))) =
        normalForm zeroDerivation
            (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm z)) +
          normalForm zeroDerivation
            (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm w))
    rw [h, Polynomial.derivative_add, normalForm_add]
  leibniz' := by
    intro z w
    rcases normalForm_surjective zeroDerivation z with ⟨p, rfl⟩
    rcases normalForm_surjective zeroDerivation w with ⟨q, rfl⟩
    rw [← normalForm_mul_zeroDerivation]
    change normalForm zeroDerivation
      (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm
        (normalForm zeroDerivation (p * q)))) =
      normalForm zeroDerivation p *
          normalForm zeroDerivation
            (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm
              (normalForm zeroDerivation q))) +
        normalForm zeroDerivation
            (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm
              (normalForm zeroDerivation p))) *
          normalForm zeroDerivation q
    rw [normalFormAddEquiv_symm_normalForm,
      normalFormAddEquiv_symm_normalForm, normalFormAddEquiv_symm_normalForm]
    rw [Polynomial.derivative_mul, normalForm_add,
      normalForm_mul_zeroDerivation, normalForm_mul_zeroDerivation]
    exact add_comm _ _

@[simp]
theorem coordinateDerivation_normalForm (p : Polynomial B) :
    coordinateDerivation (normalForm zeroDerivation p) =
      normalForm zeroDerivation (Polynomial.derivative p) := by
  change normalForm zeroDerivation
    (Polynomial.derivative ((normalFormAddEquiv zeroDerivation).symm
      (normalForm zeroDerivation p))) = _
  rw [normalFormAddEquiv_symm_normalForm]

@[simp]
theorem coordinateDerivation_coefficient (b : B) :
    coordinateDerivation (normalCoefficient zeroDerivation b) = 0 := by
  rw [← normalForm_C, coordinateDerivation_normalForm,
    Polynomial.derivative_C, normalForm_zero]

@[simp]
theorem coordinateDerivation_variable :
    coordinateDerivation (normalVariable zeroDerivation : CoordinateStage (B := B)) = 1 := by
  rw [normalVariable, coordinateDerivation_normalForm,
    Polynomial.derivative_X, normalForm_one]


end
end Stafford38.OreCoordinateStage
