/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Algebra.DifferentialWronskian
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Change of parameter for ordinary Wronskians

If two derivations on a field satisfy `D = a • E`, then the `i`-th iterate of
`D` is `a^i` times the `i`-th iterate of `E`, up to lower-order iterates of
`E`.  Thus the corresponding Wronskian matrices differ by a lower-triangular
matrix whose diagonal is `1, a, a^2, ...`.  This file records that argument;
in particular it does not make the false simplification `(a • E)^i = a^i • E^i`.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix
open Finset

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- Coefficients expressing the iterates of `a • E` in terms of the iterates
of `E`.  The recurrence is the Leibniz rule written coefficientwise. -/
private def changeParameterCoeff (E : Derivation C L L) (a : L) : ℕ → ℕ → L
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      a * (E (changeParameterCoeff E a n k) +
        if k = 0 then 0 else changeParameterCoeff E a n (k - 1))

private lemma changeParameterCoeff_of_lt (E : Derivation C L L) (a : L)
    {n k : ℕ} (h : n < k) : changeParameterCoeff E a n k = 0 := by
  induction n generalizing k with
  | zero =>
      simp [changeParameterCoeff, Nat.ne_of_gt h]
  | succ n ih =>
      have hk : k ≠ 0 := by omega
      have hnk : n < k := by omega
      have hnkp : n < k - 1 := by omega
      rw [changeParameterCoeff]
      simp [hk, ih hnk, ih hnkp]

private lemma changeParameterCoeff_diag (E : Derivation C L L) (a : L) (n : ℕ) :
    changeParameterCoeff E a n n = a ^ n := by
  induction n with
  | zero => simp [changeParameterCoeff]
  | succ n ih =>
      rw [changeParameterCoeff]
      simp [changeParameterCoeff_of_lt E a (Nat.lt_succ_self n), ih, pow_succ,
        mul_comm]

private lemma derivation_iterate_succ (E : Derivation C L L) (n : ℕ) (x : L) :
    E ((E.toLinearMap ^ n) x) = (E.toLinearMap ^ (n + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]
  rfl

private lemma changeParameterCoeff_sum_succ (E : Derivation C L L) (a x : L) (n : ℕ) :
    ∑ k ∈ range (n + 2),
        changeParameterCoeff E a (n + 1) k * (E.toLinearMap ^ k) x =
      (∑ k ∈ range (n + 1),
        (a * E (changeParameterCoeff E a n k)) * (E.toLinearMap ^ k) x) +
      ∑ k ∈ range (n + 1),
        (a * changeParameterCoeff E a n k) * (E.toLinearMap ^ (k + 1)) x := by
  simp_rw [changeParameterCoeff]
  have hsplit (k : ℕ) :
      (a *
          (E (changeParameterCoeff E a n k) +
            if k = 0 then 0 else changeParameterCoeff E a n (k - 1))) *
          (E.toLinearMap ^ k) x =
        (a * E (changeParameterCoeff E a n k)) * (E.toLinearMap ^ k) x +
          (a * (if k = 0 then 0 else changeParameterCoeff E a n (k - 1))) *
            (E.toLinearMap ^ k) x := by
    ring
  simp_rw [hsplit, sum_add_distrib]
  congr 1
  · rw [sum_range_succ]
    simp [changeParameterCoeff_of_lt E a (Nat.lt_succ_self n)]
  · rw [sum_range_succ']
    simp

private lemma derivation_iterate_eq_changeParameterCoeff_sum
    (D E : Derivation C L L) (a : L) (hD : D = a • E) (n : ℕ) (x : L) :
    (D.toLinearMap ^ n) x =
      ∑ k ∈ range (n + 1),
        changeParameterCoeff E a n k * (E.toLinearMap ^ k) x := by
  induction n with
  | zero => simp [changeParameterCoeff]
  | succ n ih =>
      calc
        (D.toLinearMap ^ (n + 1)) x = D ((D.toLinearMap ^ n) x) := by
          rw [pow_succ', Module.End.mul_apply]
          rfl
        _ = D (∑ k ∈ range (n + 1),
            changeParameterCoeff E a n k * (E.toLinearMap ^ k) x) := by rw [ih]
        _ = a * E (∑ k ∈ range (n + 1),
            changeParameterCoeff E a n k * (E.toLinearMap ^ k) x) := by
          rw [hD]
          rfl
        _ = ∑ k ∈ range (n + 1),
            ((a * E (changeParameterCoeff E a n k)) *
                (E.toLinearMap ^ k) x +
              (a * changeParameterCoeff E a n k) *
                (E.toLinearMap ^ (k + 1)) x) := by
          rw [map_sum, mul_sum]
          apply sum_congr rfl
          intro k hk
          rw [E.leibniz, derivation_iterate_succ]
          simp only [smul_eq_mul]
          ring
        _ = (∑ k ∈ range (n + 1),
              (a * E (changeParameterCoeff E a n k)) *
                (E.toLinearMap ^ k) x) +
            ∑ k ∈ range (n + 1),
              (a * changeParameterCoeff E a n k) *
                (E.toLinearMap ^ (k + 1)) x := by
          rw [sum_add_distrib]
        _ = ∑ k ∈ range (n + 2),
            changeParameterCoeff E a (n + 1) k *
              (E.toLinearMap ^ k) x :=
          (changeParameterCoeff_sum_succ E a x n).symm

/-- The lower-triangular matrix relating the two lists of iterated
derivations. -/
private def changeParameterMatrix (E : Derivation C L L) (a : L) (n : ℕ) :
    Matrix (Fin n) (Fin n) L :=
  fun i k => changeParameterCoeff E a i k

private lemma derivation_iterate_eq_changeParameterMatrix_sum
    (D E : Derivation C L L) (a : L) (hD : D = a • E) {n : ℕ}
    (i : Fin n) (x : L) :
    (D.toLinearMap ^ (i : ℕ)) x =
      ∑ k : Fin n, changeParameterMatrix E a n i k *
        (E.toLinearMap ^ (k : ℕ)) x := by
  let g : ℕ → L := fun k =>
    changeParameterCoeff E a (i : ℕ) k * (E.toLinearMap ^ k) x
  have hsubset : range ((i : ℕ) + 1) ⊆ range n :=
    range_subset_range.mpr (Nat.succ_le_iff.mpr i.isLt)
  have hsum : ∑ k ∈ range ((i : ℕ) + 1), g k = ∑ k ∈ range n, g k := by
    apply sum_subset hsubset
    intro k hkn hki
    have hik : (i : ℕ) < k := by
      rw [mem_range] at hkn
      rw [mem_range] at hki
      omega
    simp [g, changeParameterCoeff_of_lt E a hik]
  calc
    (D.toLinearMap ^ (i : ℕ)) x = ∑ k ∈ range ((i : ℕ) + 1), g k :=
      derivation_iterate_eq_changeParameterCoeff_sum D E a hD i x
    _ = ∑ k ∈ range n, g k := hsum
    _ = ∑ k : Fin n, changeParameterMatrix E a n i k *
          (E.toLinearMap ^ (k : ℕ)) x := by
      simpa [g, changeParameterMatrix] using
        (Fin.sum_univ_eq_sum_range g n).symm

private lemma changeParameterMatrix_lowerTriangular
    (E : Derivation C L L) (a : L) (n : ℕ) :
    (changeParameterMatrix E a n).BlockTriangular OrderDual.toDual := by
  intro i k hik
  apply changeParameterCoeff_of_lt E a
  exact OrderDual.toDual_lt_toDual.mp hik

private lemma changeParameterMatrix_det
    (E : Derivation C L L) (a : L) (n : ℕ) :
    (changeParameterMatrix E a n).det = a ^ n.choose 2 := by
  rw [Matrix.det_of_isLowerTriangular _ (changeParameterMatrix_lowerTriangular E a n)]
  simp only [changeParameterMatrix, changeParameterCoeff_diag]
  calc
    ∏ i : Fin n, a ^ (i : ℕ) = a ^ ∑ i : Fin n, (i : ℕ) := by
      simpa using (prod_pow_eq_pow_sum univ (fun i : Fin n => (i : ℕ)) a)
    _ = a ^ n.choose 2 := by
      congr 1
      rw [show (∑ i : Fin n, (i : ℕ)) = ∑ i ∈ range n, i from
        Fin.sum_univ_eq_sum_range (fun i => i) n]
      rw [sum_range_id, Nat.choose_two_right]

private lemma derivationWronskian_eq_changeParameterMatrix_mul
    (D E : Derivation C L L) (a : L) (hD : D = a • E)
    {n : ℕ} (f : Fin n → L) :
    BGS.Algebra.derivationWronskian D f =
      changeParameterMatrix E a n * BGS.Algebra.derivationWronskian E f := by
  ext i j
  rw [Matrix.mul_apply]
  simpa [BGS.Algebra.derivationWronskian] using
    derivation_iterate_eq_changeParameterMatrix_sum D E a hD i (f j)

/-- Change-of-parameter formula for an ordinary Wronskian.

The triangular exponent is `n.choose 2 = 0 + 1 + ... + (n - 1)`.  The proof
keeps all lower-order terms arising from differentiating `a`; they form the
strictly lower-triangular part of `changeParameterMatrix` and hence do not
affect its determinant. -/
theorem derivationWronskian_det_changeParameter
    (D E : Derivation C L L) (a : L) (hD : D = a • E)
    {n : ℕ} (f : Fin n → L) :
    (BGS.Algebra.derivationWronskian D f).det =
      a ^ n.choose 2 * (BGS.Algebra.derivationWronskian E f).det := by
  rw [derivationWronskian_eq_changeParameterMatrix_mul D E a hD f,
    Matrix.det_mul, changeParameterMatrix_det]

end

end BGS.CorvajaZannier
