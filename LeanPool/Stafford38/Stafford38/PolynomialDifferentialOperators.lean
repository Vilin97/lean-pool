/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import LeanPool.Stafford38.Stafford38.DifferentialOperators
import LeanPool.Stafford38.Stafford38.Weyl.Universal
import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence

/-!
# The polynomial representation of the Weyl algebra

The canonical coordinates act by multiplication and the canonical momenta by
formal partial differentiation.  The target is the intrinsic algebra of
finite-order differential operators, so this construction does not assume an
identification of that algebra with the Weyl algebra.
-/

namespace Stafford38.PolynomialDifferentialOperators

open Stafford
open Stafford38.DifferentialOperators
open Stafford38.WeylUniversal
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable (k : Type*) [Field k] (n : ℕ)

/-- The polynomial algebra in `n` variables over `k`. -/
abbrev PolynomialRing := MvPolynomial (Fin n) k

/-- Multiplication by a polynomial coordinate, regarded as a linear endomorphism. -/
def coordinateEnd (i : Fin n) : End (k := k) (R := PolynomialRing k n) :=
  multiplication (MvPolynomial.X i)

/-- Partial differentiation in a polynomial coordinate, regarded as a linear endomorphism. -/
def momentumEnd (i : Fin n) : End (k := k) (R := PolynomialRing k n) :=
  (MvPolynomial.pderiv i).toLinearMap

theorem coordinateEnd_mem_order_zero (i : Fin n) :
    coordinateEnd k n i ∈ order (k := k) (R := PolynomialRing k n) 0 := by
  rw [mem_order_zero_iff_eq_multiplication]
  ext f
  simp [coordinateEnd, multiplication_apply]

theorem momentumEnd_mem_order_one (i : Fin n) :
    momentumEnd k n i ∈ order (k := k) (R := PolynomialRing k n) 1 := by
  rw [show 1 = 0 + 1 by rfl, mem_order_succ_iff]
  intro f
  rw [mem_order_zero_iff_eq_multiplication]
  apply LinearMap.ext
  intro g
  simp? [commutator_apply, momentumEnd, multiplication_apply]
  exact mul_comm _ _

/-- The polynomial multiplication and differentiation operators satisfying the Weyl relations. -/
def differentialGenerator :
    (Fin n ⊕ Fin n) → algebra (k := k) (R := PolynomialRing k n)
  | .inl i => ⟨coordinateEnd k n i, 0, coordinateEnd_mem_order_zero k n i⟩
  | .inr i => ⟨momentumEnd k n i, 1, momentumEnd_mem_order_one k n i⟩

theorem pderiv_comm (i j : Fin n) (f : PolynomialRing k n) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  by_cases hij : i = j
  · subst j
    rfl
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f a hf =>
      classical
      simp only [MvPolynomial.pderiv_mul, map_add]
      rw [hf]
      simp only [MvPolynomial.pderiv_X]
      by_cases hai : a = i <;> by_cases haj : a = j <;>
        simp [hai, haj, hij, Ne.symm hij]

theorem differentialGenerator_commutator (i j : Fin n ⊕ Fin n) :
    Stafford.commutator (differentialGenerator k n i)
        (differentialGenerator k n j) =
      algebraMap k (algebra (k := k) (R := PolynomialRing k n))
        (Matrix.J (Fin n) k i j) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [Stafford.commutator, differentialGenerator, coordinateEnd,
          Module.End.mul_apply, Matrix.J, mul_comm, mul_assoc, mul_left_comm]
      | inr j =>
          by_cases h : i = j
          · subst j
            simp [Stafford.commutator, differentialGenerator, coordinateEnd, momentumEnd,
              Module.End.mul_apply, Matrix.J]
          · simp [Stafford.commutator, differentialGenerator, coordinateEnd, momentumEnd,
              Module.End.mul_apply, Matrix.J, h]
  | inr i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst j
            simp [Stafford.commutator, differentialGenerator, coordinateEnd, momentumEnd,
              Module.End.mul_apply, Matrix.J]
          · simp [Stafford.commutator, differentialGenerator, coordinateEnd, momentumEnd,
              Module.End.mul_apply, Matrix.J, h]
      | inr j =>
          simp [Stafford.commutator, differentialGenerator, momentumEnd, Module.End.mul_apply,
            Matrix.J, pderiv_comm k n i j]

/-- The polynomial action, valued in genuine finite-order differential operators. -/
def polynomialDifferentialAction :
    PresentedWeyl k n →ₐ[k] algebra (k := k) (R := PolynomialRing k n) :=
  freeWeylLift (Matrix.J (Fin n) k) (differentialGenerator k n)
    (differentialGenerator_commutator k n)

@[simp]
theorem polynomialDifferentialAction_generator (i : Fin n ⊕ Fin n) :
    polynomialDifferentialAction k n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) = differentialGenerator k n i :=
  freeWeylLift_generator _ _ _ i

theorem polynomialDifferentialAction_mem (d : PresentedWeyl k n) :
    (polynomialDifferentialAction k n d : End (k := k) (R := PolynomialRing k n)) ∈
      algebra (k := k) (R := PolynomialRing k n) :=
  (polynomialDifferentialAction k n d).property

end
end Stafford38.PolynomialDifferentialOperators
