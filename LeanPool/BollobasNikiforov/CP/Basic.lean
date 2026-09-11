/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Completely positive matrices

A real matrix is completely positive if it is a finite sum of rank-one
matrices `vecMulVec p p` with entrywise nonnegative `p`.
-/

open Matrix

namespace BollobasNikiforov

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real matrix is completely positive if it is a sum of outer products of
entrywise nonnegative vectors. -/
def IsCompletelyPositive (C : Matrix n n ℝ) : Prop :=
  ∃ (q : ℕ) (p : Fin q → n → ℝ),
    (∀ a i, 0 ≤ p a i) ∧ C = ∑ a, vecMulVec (p a) (p a)

omit [Fintype n] [DecidableEq n] in
lemma isCompletelyPositive_vecMulVec {p : n → ℝ} (hp : 0 ≤ p) :
    IsCompletelyPositive (vecMulVec p p) :=
  ⟨1, fun _ ↦ p, fun _ i ↦ hp i, by simp⟩

omit [Fintype n] [DecidableEq n] in
lemma IsCompletelyPositive.smul {C : Matrix n n ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hC : IsCompletelyPositive C) : IsCompletelyPositive (r • C) := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  refine ⟨q, fun a ↦ √r • p a, ?_, ?_⟩
  · intro a i
    exact mul_nonneg (Real.sqrt_nonneg r) (hp a i)
  · simp [Finset.smul_sum, smul_vecMulVec, vecMulVec_smul, smul_smul,
      Real.mul_self_sqrt hr]

omit [Fintype n] [DecidableEq n] in
lemma IsCompletelyPositive.add {C D : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) (hD : IsCompletelyPositive D) :
    IsCompletelyPositive (C + D) := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  obtain ⟨q', p', hp', rfl⟩ := hD
  refine ⟨q + q', Fin.addCases p p', ?_, ?_⟩
  · intro a i
    induction a using Fin.addCases with
    | left a => simp [hp a i]
    | right a => simp [hp' a i]
  · rw [Fin.sum_univ_add]
    simp

omit [Fintype n] [DecidableEq n] in
lemma mul_transpose_eq_sum_vecMulVec {r : Type*} [Fintype r] (A : Matrix n r ℝ) :
    A * Aᵀ = ∑ a, vecMulVec (A.col a) (A.col a) := by
  ext i j
  simp [mul_apply, transpose_apply, Matrix.sum_apply, vecMulVec_apply, col_apply]

omit [Fintype n] [DecidableEq n] in
lemma isCompletelyPositive_iff_exists_mul_transpose {C : Matrix n n ℝ} :
    IsCompletelyPositive C ↔
      ∃ (r : ℕ) (A : Matrix n (Fin r) ℝ), (∀ i j, 0 ≤ A i j) ∧ C = A * Aᵀ := by
  constructor
  · rintro ⟨q, p, hp, rfl⟩
    refine ⟨q, .of fun i a ↦ p a i, fun i a ↦ hp a i, ?_⟩
    rw [mul_transpose_eq_sum_vecMulVec]
    congr!
  · rintro ⟨r, A, hA, rfl⟩
    exact ⟨r, A.col, fun a i ↦ hA i a, mul_transpose_eq_sum_vecMulVec A⟩

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
lemma posSemidef_vecMulVec_self (p : n → ℝ) : (vecMulVec p p).PosSemidef := by
  cases nonempty_fintype n
  refine .of_dotProduct_mulVec_nonneg (by
    rw [isHermitian_iff_isSymm]
    exact transpose_vecMulVec p p) fun x ↦ ?_
  have : x ⬝ᵥ (vecMulVec p p *ᵥ x) = (p ⬝ᵥ x) ^ 2 := by
    simp [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_comm, sq]
  simpa [this] using sq_nonneg (p ⬝ᵥ x)

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
lemma IsCompletelyPositive.posSemidef {C : Matrix n n ℝ} (hC : IsCompletelyPositive C) :
    C.PosSemidef := by
  obtain ⟨_, p, _, rfl⟩ := hC
  exact posSemidef_sum _ fun a _ ↦ posSemidef_vecMulVec_self (p a)

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
lemma IsCompletelyPositive.isHermitian {C : Matrix n n ℝ} (hC : IsCompletelyPositive C) :
    C.IsHermitian :=
  hC.posSemidef.isHermitian

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
lemma IsCompletelyPositive.isSymm {C : Matrix n n ℝ} (hC : IsCompletelyPositive C) :
    C.IsSymm :=
  isHermitian_iff_isSymm.mp hC.isHermitian

omit [Fintype n] [DecidableEq n] in
lemma IsCompletelyPositive.nonneg {C : Matrix n n ℝ} (hC : IsCompletelyPositive C)
    (i j : n) : 0 ≤ C i j := by
  obtain ⟨_, p, hp, rfl⟩ := hC
  simp only [Matrix.sum_apply, vecMulVec_apply]
  exact Finset.sum_nonneg fun a _ ↦ mul_nonneg (hp a i) (hp a j)

omit [Fintype n] [DecidableEq n] in
lemma IsCompletelyPositive.submatrix {ι : Type*} {C : Matrix n n ℝ}
    (hC : IsCompletelyPositive C) (e : ι → n) :
    IsCompletelyPositive (C.submatrix e e) := by
  obtain ⟨r, A, hA, rfl⟩ := isCompletelyPositive_iff_exists_mul_transpose.1 hC
  refine isCompletelyPositive_iff_exists_mul_transpose.2
    ⟨r, A.submatrix e id, fun i j ↦ hA (e i) j, ?_⟩
  ext i j
  simp [mul_apply, submatrix_apply, transpose_apply]

end BollobasNikiforov
