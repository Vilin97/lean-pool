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

/-!
# LeanPool.Duality.FarkasBasic
-/

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
  · rfl

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
      use Sum.elim x⁺ x⁻
      constructor
      · rw [Sum.nonneg_elim_iff]
        exact ⟨posPart_nonneg x, negPart_nonneg x⟩
      · rw [Matrix.fromCols_mulVec_sumElim, Matrix.neg_mulVec, ←Matrix.mulVec_neg,
          ←Matrix.mulVec_add, ←sub_eq_add_neg]
        have hxx : x⁺ - x⁻ = x := by
          funext j
          simp only [Pi.sub_apply, Pi.posPart_apply, Pi.negPart_apply]
          exact posPart_sub_negPart (x j)
        rw [hxx]
        exact hAx
    · intro ⟨x, _, hAx⟩
      use x ∘ Sum.inl - x ∘ Sum.inr
      rw [Matrix.mulVec_sub]
      rwa [←Sum.elim_comp_inl_inr x, Matrix.fromCols_mulVec_sumElim, Matrix.neg_mulVec,
        ←sub_eq_add_neg] at hAx
  · constructor
    · intro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff]
      constructor
      · rw [hAy]
      · rw [Matrix.transpose_neg, Matrix.neg_mulVec, hAy, neg_zero]
    · intro ⟨y, hAy, hby⟩
      refine ⟨y, ?_, hby⟩
      rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Sum.nonneg_elim_iff] at hAy
      obtain ⟨hAyp, hAyn⟩ := hAy
      refine le_antisymm ?_ hAyp
      intro i
      specialize hAyn i
      rwa [Matrix.transpose_neg, Matrix.neg_mulVec, Pi.zero_apply, Pi.neg_apply,
        Right.nonneg_neg_iff] at hAyn

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
    use -y
    rw [Matrix.mulVec_neg, hAy, neg_zero, dotProduct_neg, neg_lt_zero]
    push Not at hlt
    exact ⟨rfl, lt_of_le_of_ne hlt hby.symm⟩

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
    use Sum.elim (b - A *ᵥ x) x
    constructor
    · rw [Sum.nonneg_elim_iff]
      exact ⟨fun i : I => sub_nonneg_of_le (hAxb i), hx⟩
    · aesop
  · intro ⟨x, hx, hAxb⟩
    use x ∘ Sum.inr
    constructor
    · intro
      apply hx
    · intro i
      have hi := congr_fun hAxb i
      simp only [A', Matrix.mulVec, dotProduct, Matrix.fromCols, Matrix.of_apply,
        Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type] at hi
      apply le_of_nneg_add hi
      apply Fintype.sum_nonneg
      rw [Pi.le_def]
      intro
      rw [Pi.zero_apply]
      apply mul_nonneg
      · apply Matrix.zero_le_one_elem
      · apply hx
  · intro ⟨y, hy, hAy, hby⟩
    refine ⟨y, ?_, hby⟩
    intro k
    cases k with
    | inl i => exact dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy
    | inr j => apply hAy
  · intro ⟨y, hAy, hby⟩
    have h1Ay : 0 ≤ (Matrix.fromRows (1 : Matrix I I F) Aᵀ *ᵥ y) := by
      intro k
      simp only [A', Matrix.transpose_fromCols, Matrix.transpose_one] at hAy
      apply hAy
    refine ⟨y, fun i : I => ?_, fun j : J => h1Ay (Sum.inr j), hby⟩
    simpa using h1Ay (Sum.inl i)

/-- A system of linear inequalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a nonnegative linear combination of the inequalities;
midly reformulated. -/
theorem inequalityFarkas_neg (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  convert inequalityFarkas A b using 5
  rw [Matrix.neg_mulVec, ←neg_zero]
  constructor <;> intro hAx i <;> simpa using hAx i
