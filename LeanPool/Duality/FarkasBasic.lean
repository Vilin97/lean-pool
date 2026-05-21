/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Sum
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin
import LeanPool.Duality.FarkasBartl


/- Let's move from linear maps to matrices, which give more familiar
(albeit less general) formulations of the theorems of alternative. -/

variable {I J F : Type*} [Fintype I] [Fintype J] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open scoped Matrix

/-- `finishit` is a helper tactic used by `equalityFarkas` to discharge the residual
    matrix-vector equality after the main Farkas-Bartl bijection: it unfolds the matrix
    products, swaps the order of summation, and closes the goal with `ring`. -/
macro "finishit" : tactic => `(tactic| -- should be `private macro` which Lean does not allow
  unfold Matrix.mulVec Matrix.vecMul dotProduct <;>
  simp_rw [Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
  congr <;> ext <;> congr <;> ext <;> ring)

/-- A system of linear equalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the inequalities. -/
theorem equalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  convert
    coordinateFarkasBartl Aᵀ.mulVecLin ⟨⟨(b ⬝ᵥ ·), dotProduct_add b⟩, (dotProduct_smul · b)⟩
      using 3
  · constructor <;> intro ⟨hx, hAx⟩ <;> refine ⟨hx, ?_⟩
    · intro
      simp only [Matrix.mulVecLin_transpose, LinearMap.flip_apply, Matrix.vecMulBilin_apply,
        smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]
      rw [←hAx]
      finishit
    · simp only [Matrix.mulVecLin_transpose, LinearMap.flip_apply, Matrix.vecMulBilin_apply,
        smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk] at hAx
      apply dotProduct_eq
      intro w
      rw [←hAx w]
      finishit

/- The following two theorems could be given in much more generality.
In our work, however, this is the only setting we provide.
This special case of the Fredholm alternative is not our main focus
but a byproduct of the other theorems we prove.
You can use `basicLinearAlgebra_lt` to gain intuition for understanding
what `equalityFarkas` says. -/

/-- A system of linear equalities has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the equalities. -/
theorem basicLinearAlgebra_lt (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0) := by
  convert equalityFarkas (Matrix.fromCols A (-A)) b using 1
  · constructor
    · intro ⟨x, hAx⟩
      exact ⟨Sum.elim x⁺ x⁻, Sum.nonneg_elim_iff.mpr ⟨posPart_nonneg x, negPart_nonneg x⟩, by
        rw [Matrix.fromCols_mulVec_sumElim, Matrix.neg_mulVec, ←Matrix.mulVec_neg,
          ←Matrix.mulVec_add, ←sub_eq_add_neg]
        convert hAx
        aesop⟩
    · intro ⟨x, _, hAx⟩
      exact ⟨x ∘ Sum.inl - x ∘ Sum.inr, by
        rw [Matrix.mulVec_sub]
        rwa [←Sum.elim_comp_inl_inr x, Matrix.fromCols_mulVec_sumElim, Matrix.neg_mulVec,
          ←sub_eq_add_neg] at hAx⟩
  · constructor
    · rintro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff, hAy]
      exact ⟨rfl, by rw [Matrix.transpose_neg, Matrix.neg_mulVec, hAy, neg_zero]⟩
    · intro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff] at hAy
      obtain ⟨hAyp, hAyn⟩ := hAy
      exact le_antisymm (fun i => by
        specialize hAyn i
        rwa [Matrix.transpose_neg, Matrix.neg_mulVec, Pi.zero_apply, Pi.neg_apply,
          Right.nonneg_neg_iff] at hAyn) hAyp

/-- A system of linear equalities has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the equalities;
midly reformulated. -/
theorem basicLinearAlgebra (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, A *ᵥ x = b) ≠ (∃ y : I → F, Aᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y ≠ 0) := by
  convert basicLinearAlgebra_lt A b using 1
  refine ⟨fun ⟨y, hAy, hby⟩ => ?_, by aesop⟩
  if hlt : b ⬝ᵥ y < 0 then
    aesop
  else
    exact ⟨-y, by rw [Matrix.mulVec_neg, hAy, neg_zero, dotProduct_neg, neg_lt_zero]
      exact ⟨rfl, lt_of_le_of_ne (not_lt.mp hlt) hby.symm⟩⟩

/- Let's move to the "symmetric" variants now. They will also be used in the upcoming extended
setting and in the upcoming theory of linear programming. -/

/-- A system of linear inequalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a nonnegative linear combination of the inequalities. -/
theorem inequalityFarkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  classical
  let A' : Matrix I (I ⊕ J) F := Matrix.fromCols 1 A
  convert equalityFarkas A' b using 1 <;> constructor
  · intro ⟨x, hx, hAxb⟩
    exact ⟨Sum.elim (b - A *ᵥ x) x, Sum.nonneg_elim_iff.mpr ⟨fun i : I => sub_nonneg_of_le (hAxb i), hx⟩, by aesop⟩
  · rintro ⟨x, hx, hAxb⟩
    refine ⟨x ∘ Sum.inr, (hx ·), fun i => le_of_nneg_add (congr_fun hAxb i) ?_⟩
    simp only [A', Matrix.mulVec, dotProduct, Matrix.fromCols, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type]
    exact Fintype.sum_nonneg (fun j _ => mul_nonneg (Matrix.zero_le_one_elem _ _) (hx j))
  · intro ⟨y, hy, hAy, hby⟩
    exact ⟨y, fun k => k.casesOn (fun i => by simpa [A', Matrix.neg_mulVec] using
      dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy) (fun j => hAy j), hby⟩
  · intro ⟨y, hAy, hby⟩
    simp only [A', Matrix.transpose_fromCols, Matrix.transpose_one] at hAy
    exact ⟨y, fun i : I => by simpa using hAy (Sum.inl i), fun j : J => hAy (Sum.inr j), hby⟩

/-- A system of linear inequalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a nonnegative linear combination of the inequalities;
midly reformulated. -/
theorem inequalityFarkas_neg (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  convert inequalityFarkas A b using 5
  simp [Matrix.neg_mulVec]
