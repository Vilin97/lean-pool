/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.PolynomialOperatorCommutators
import LeanPool.Stafford38.AlgebraicAnalysis.LinearAlgebra.FiniteTaylorReconstruction

/-!
# One-coordinate Taylor projection for polynomial operators

This file constructs the finite Taylor projection using the actual polynomial
operator representation.  Products are compositions and the powers of the
partial derivative stay on the right.
-/

namespace Stafford38.PolynomialOperatorTaylorProjection

open scoped BigOperators
open Stafford38.PolynomialDifferentialOperators
open Stafford38.PolynomialOperatorCommutators

noncomputable section

variable (k : Type*) [Field k] [CharZero k] (n : ℕ)

/-- The polynomial coefficient algebra for the finite Taylor projection. -/
abbrev PolynomialRing := MvPolynomial (Fin n) k
/-- Linear operators on the polynomial coefficient algebra. -/
abbrev Operator := Module.End k (PolynomialRing k n)
/-- Linear transformations of the space of polynomial operators. -/
abbrev OperatorEnd := Module.End k (Operator k n)

/-- The actual finite Taylor projection in coordinate `i`. -/
def projection (i : Fin n) (m : ℕ) (P : Operator k n) : Operator k n :=
  ∑ j ∈ Finset.range (m + 1),
    ((-1 : k) ^ j / (j.factorial : k)) •
      ((coordinateCommutator k n i ^ j) P * momentumEnd k n i ^ j)

omit [CharZero k] in
private theorem coordinateCommutator_mul (i : Fin n) (P Q : Operator k n) :
    coordinateCommutator k n i (P * Q) =
      coordinateCommutator k n i P * Q + P * coordinateCommutator k n i Q := by
  apply LinearMap.ext
  intro f
  simp [coordinateCommutator, Stafford38.DifferentialOperators.commutator_apply,
    Module.End.mul_apply]

omit [CharZero k] in
theorem coordinateCommutator_momentum (i : Fin n) :
    coordinateCommutator k n i (momentumEnd k n i) = 1 := by
  apply LinearMap.ext
  intro f
  simp [coordinateCommutator, Stafford38.DifferentialOperators.commutator_apply,
    momentumEnd]

omit [CharZero k] in
@[simp]
theorem commutator_momentum_coordinate (i : Fin n) :
    Stafford38.DifferentialOperators.commutator (momentumEnd k n i) (MvPolynomial.X i) = 1 := by
  simpa only [coordinateCommutator_apply] using coordinateCommutator_momentum k n i

private theorem coordinateCommutator_momentum_pow (i : Fin n) : ∀ j : ℕ,
    coordinateCommutator k n i (momentumEnd k n i ^ j) =
      (j : k) • momentumEnd k n i ^ (j - 1)
  | 0 => by
      apply LinearMap.ext
      intro f
      simp [coordinateCommutator, Stafford38.DifferentialOperators.commutator_apply]
  | j + 1 => by
      rw [pow_succ, coordinateCommutator_mul, coordinateCommutator_momentum]
      rw [coordinateCommutator_momentum_pow]
      cases j with
      | zero => simp
      | succ j => simp [pow_succ, add_mul,  add_smul]

omit [CharZero k] in
private theorem iterate_succ_apply (T : OperatorEnd k n) (j : ℕ) (P : Operator k n) :
    (T ^ (j + 1)) P = T ((T ^ j) P) := by
  rw [pow_succ']
  rfl

/-- Applying the coordinate commutator to the Taylor projection kills all
adjacent terms; the last term vanishes by the stated nilpotence hypothesis. -/
theorem coordinateCommutator_projection_eq_zero (i : Fin n) (m : ℕ)
    (P : Operator k n)
    (hnil : (coordinateCommutator k n i ^ (m + 1)) P = 0) :
    coordinateCommutator k n i (projection k n i m P) = 0 := by
  simp only [projection, map_sum]
  have hterm (j : ℕ) :
      coordinateCommutator k n i
          (((-1 : k) ^ j / (j.factorial : k)) •
            ((coordinateCommutator k n i ^ j) P * momentumEnd k n i ^ j)) =
        ((-1 : k) ^ j / (j.factorial : k)) •
          (((coordinateCommutator k n i ^ (j + 1)) P * momentumEnd k n i ^ j) +
            ((j : k) •
              ((coordinateCommutator k n i ^ j) P *
                momentumEnd k n i ^ (j - 1)))) := by
    rw [map_smul, coordinateCommutator_mul,
      coordinateCommutator_momentum_pow, iterate_succ_apply]
    simp only [smul_add]
    rw [mul_smul_comm, smul_smul]
  simp_rw [hterm]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ]
  rw [hnil]
  simp only [zero_mul, smul_zero, add_zero]
  -- Shift the derivative-of-the-right-factor sum by one.  Its coefficient is
  -- the negative of the next term in the first sum.
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_smul]
  have hcancel (j : ℕ) :
      ((-1 : k) ^ j / (j.factorial : k)) •
          ((coordinateCommutator k n i ^ (j + 1)) P * momentumEnd k n i ^ j) +
        ((-1 : k) ^ (j + 1) / ((j + 1).factorial : k)) •
          ((j + 1 : k) •
            ((coordinateCommutator k n i ^ (j + 1)) P *
              momentumEnd k n i ^ j)) = 0 := by
    have hj : ((j + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hfac : ((j.factorial : ℕ) : k) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    have hc :
        ((-1 : k) ^ j / (j.factorial : k)) +
          ((-1 : k) ^ (j + 1) / ((j + 1).factorial : k)) * (j + 1 : k) = 0 := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      field_simp [hfac, hj]
      ring
    rw [smul_smul, ← add_smul, hc, zero_smul]
  -- `sum_range_succ` exposes exactly the paired adjacent coefficients.
  simp only [smul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  simpa [Nat.succ_sub_one] using hcancel j

end
end Stafford38.PolynomialOperatorTaylorProjection

namespace Stafford.AllDegreeSliceTaylor.Field

/- Compatibility export for the application-independent Taylor projector. -/
export AlgebraicAnalysis.FiniteTaylorReconstruction (projectorMapG reconstruction_all)

end Stafford.AllDegreeSliceTaylor.Field

namespace Stafford38.PolynomialOperatorTaylorProjection

open Stafford38.PolynomialDifferentialOperators
open Stafford38.PolynomialOperatorCommutators
open Stafford.AllDegreeSliceTaylor.Field

noncomputable section

variable (k : Type*) [Field k] [CharZero k] (n : ℕ)

private def rightMomentum (i : Fin n) :
    Operator k n →ₗ[k] Operator k n :=
  LinearMap.mulRight k (momentumEnd k n i)

omit [CharZero k] in
private theorem rightMomentum_pow_apply (i : Fin n) (j : ℕ) (P : Operator k n) :
    (rightMomentum k n i ^ j) P = P * momentumEnd k n i ^ j := by
  induction j with
  | zero => simp [rightMomentum]
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [rightMomentum, pow_succ, mul_assoc]

omit [CharZero k] in
private theorem projectorMapG_apply_eq_projection (i : Fin n) (m : ℕ)
    (P : Operator k n) :
    projectorMapG m (rightMomentum k n i) (coordinateCommutator k n i) P =
      projection k n i m P := by
  unfold projectorMapG projection
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change ((-1 : k) ^ j / (j.factorial : k)) •
      ((rightMomentum k n i ^ j * coordinateCommutator k n i ^ j) P) = _
  rw [Module.End.mul_apply, rightMomentum_pow_apply]

/-- Finite Taylor reconstruction for the actual polynomial operator.  Every
power of the partial derivative occurs as a right factor. -/
theorem reconstruction (i : Fin n) (m : ℕ) (P : Operator k n)
    (hnil : (coordinateCommutator k n i ^ (m + 1)) P = 0) :
    P = ∑ a ∈ Finset.range (m + 1),
      ((1 : k) / (a.factorial : k)) •
        (projection k n i m ((coordinateCommutator k n i ^ a) P) *
          momentumEnd k n i ^ a) := by
  have h := reconstruction_all m (rightMomentum k n i)
    (coordinateCommutator k n i) P hnil
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [Module.End.mul_apply, Module.End.mul_apply, rightMomentum_pow_apply,
    projectorMapG_apply_eq_projection]

end
end Stafford38.PolynomialOperatorTaylorProjection
