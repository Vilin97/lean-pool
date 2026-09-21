/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The polynomial commutant after localization

An endomorphism of a localization which commutes with the coordinate
multiplications is multiplication by its value at `1`.  The argument only
uses the localization presentation; it does not use a finite-order
hypothesis.
-/

namespace AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialCommutant

open AlgebraicAnalysis.DifferentialOperators

noncomputable section

variable {k : Type*} [CommRing k]
variable {n : ℕ}
variable (B : Type*) [CommRing B]
variable [Algebra k B]
variable (S : Submonoid (MvPolynomial (Fin n) k))
variable [Algebra (MvPolynomial (Fin n) k) B]
variable [IsScalarTower k (MvPolynomial (Fin n) k) B]
variable [IsLocalization S B]

theorem eq_multiplication_of_commute_coordinate
    (S : Submonoid (MvPolynomial (Fin n) k))
    [IsLocalization S B]
    (P : Module.End k B)
    (hcoord : ∀ i : Fin n, ∀ b : B,
      P (algebraMap (MvPolynomial (Fin n) k) B (MvPolynomial.X i) * b) =
        algebraMap (MvPolynomial (Fin n) k) B (MvPolynomial.X i) * P b) :
    P = multiplication (k := k) (P 1) := by
  have hpoly : ∀ a : MvPolynomial (Fin n) k, ∀ b : B,
      P (algebraMap (MvPolynomial (Fin n) k) B a * b) =
        algebraMap (MvPolynomial (Fin n) k) B a * P b := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
        intro b
        have hc : algebraMap (MvPolynomial (Fin n) k) B (MvPolynomial.C c) =
            algebraMap k B c := by
          calc
            algebraMap (MvPolynomial (Fin n) k) B (MvPolynomial.C c) =
                algebraMap (MvPolynomial (Fin n) k) B
                  (algebraMap k (MvPolynomial (Fin n) k) c) := by
                    rw [MvPolynomial.algebraMap_eq]
            _ = algebraMap k B c := by
              exact (IsScalarTower.algebraMap_apply k
                (MvPolynomial (Fin n) k) B c).symm
        rw [hc]
        simpa [Algebra.smul_def] using P.map_smul c b
    | add a a' ha ha' =>
        intro b
        simp only [map_add, map_mul, ha b, ha' b, add_mul]
    | mul_X a i ha =>
        intro b
        calc
          P (algebraMap _ B (a * MvPolynomial.X i) * b) =
              P (algebraMap (MvPolynomial (Fin n) k) B a *
                (algebraMap (MvPolynomial (Fin n) k) B (MvPolynomial.X i) * b)) := by
            rw [map_mul (algebraMap (MvPolynomial (Fin n) k) B)]
            simp [mul_assoc]
          _ = algebraMap _ B a *
              P (algebraMap _ B (MvPolynomial.X i) * b) := ha _
          _ = algebraMap _ B a *
              (algebraMap _ B (MvPolynomial.X i) * P b) := by
            rw [hcoord]
          _ = algebraMap _ B (a * MvPolynomial.X i) * P b := by
            rw [map_mul (algebraMap (MvPolynomial (Fin n) k) B)]
            simp [mul_assoc]
  apply LinearMap.ext
  intro b
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj S b
  have hsa : IsUnit (algebraMap (MvPolynomial (Fin n) k) B (s : _)) :=
    IsLocalization.map_units B s
  refine hsa.mul_left_cancel ?_
  simp only [multiplication_apply]
  rw [← hpoly (s : MvPolynomial (Fin n) k) b]
  rw [← mul_comm b, hs]
  have ha1 : P (algebraMap (MvPolynomial (Fin n) k) B a) =
      algebraMap (MvPolynomial (Fin n) k) B a * P 1 := by
    simpa using hpoly a 1
  rw [ha1]
  rw [← hs]
  simp [mul_assoc, mul_comm, mul_left_comm]

end
end AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialCommutant
