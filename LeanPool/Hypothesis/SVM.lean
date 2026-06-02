/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Support vector machines

as in `s4cs`
-/

/-- Two sets `A`, `B` in `ℝ^k` are linearly separable (with margin) if there is a
hyperplane `w ⬝ x = b` with `A` on the `≤ -1` side and `B` on the `≥ 1` side. -/
def separable {k : ℕ} (A B : Set (Fin k → ℝ)) := ∃ b : ℝ, ∃ w : Fin k → ℝ,
  (∀ x ∈ A, w ⬝ᵥ x - b ≤ -1) ∧
  (∀ x ∈ B, w ⬝ᵥ x - b ≥ 1)

/-- From Section 8.7 in `s4cs`.
 The first example we think of is
`b=1`, `(w₁,w₂)=(0,2)` which has `√(w₁^2+w₂^2)=2`.

Book claims that minimizing `√(w₁^2+w₂^2)`
will maximize the distance between the lines
![w₁,w₂] ⬝ᵥ x - b = -1
![w₁,w₂] ⬝ᵥ x - b = 1


Book claims `w₁=w₂=b=1` minimizes `√(w₁^2+w₂^2)`
subject to
`(1 ≤ b + w₁ ∧ 1 ≤ b) ∧ 1 ≤ w₁ + w₂ - b`
Let's first check that `w₁=w₂=b=1` satisfies our constrains:
-/
example : separable ({![-1,0], ![0,0]} : Set (Fin 2 → ℝ)) ({![1,1]} : Set (Fin 2 → ℝ)) := by
  simp only [
    separable, Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.vec2_dotProduct, Fin.isValue, tsub_le_iff_right, le_neg_add_iff_add_le, forall_eq_or_imp,
    Matrix.cons_val_zero, mul_neg, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero,
    add_zero, add_neg_le_iff_le_add, forall_eq, ge_iff_le]
  use 1
  simp only [Fin.isValue, le_add_iff_nonneg_right, Std.le_refl, and_true]
  use ![1,1]
  simp

lemma tooHardForChatGPT (x y : ℝ) (h₀ : 2 ≤ x + y) : 2 ≤ x^2 + y^2 := by
  have : 2 ≤ x + |y| := by
    apply le_trans h₀
    rw [add_le_add_iff_left]
    exact le_abs_self y
  suffices 2 ≤ x^2 + |y|^2 by simp at this;tauto
  by_cases h : x ≤ 2
  · have : |y|^2 ≥ (2-x)^2 := by
      repeat rw [pow_two]
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ (by simp) <;> linarith
    calc 2 ≤ x^2 + (2-x)^2 := by
          suffices 0 ≤ (x - 1)^2 by
            rw [sub_sq] at this; linarith
          positivity
        _ ≤ _ := by simp only [sq_abs, ge_iff_le, add_le_add_iff_left] at this ⊢;exact this
  · suffices 2 ≤ x^2 by apply le_trans this;simp only [sq_abs, le_add_iff_nonneg_right];positivity
    have : 2 < x := by linarith
    suffices 4 < x^2 by linarith
    rw [pow_two]
    calc _ = (2:ℝ) * 2 := by linarith
         _ < _ := by
          refine mul_lt_mul_of_pos_of_nonneg' this ?_ ?_ ?_
          <;> linarith

lemma tooHardForChatGPT₁ {x y : ℝ} (h₀ : 2 < x + y) : 2 < x^2 + y^2 := by
  have : 2 < x + |y| := by
    calc _ < _ := h₀
    _ ≤ _ := by
          rw [add_le_add_iff_left]
          exact le_abs_self y
  suffices 2 < x^2 + |y|^2 by simp at this;tauto
  by_cases h : x ≤ 2
  · have : |y|^2 > (2-x)^2 := by
      repeat rw [pow_two]
      refine mul_lt_mul_of_nonneg ?_ ?_ ?_ (by linarith) <;> linarith
    calc 2 ≤ x^2 + (2-x)^2 := by
          suffices 0 ≤ (x - 1)^2 by
            rw [sub_sq] at this; linarith
          positivity
        _ < _ := by linarith
  · suffices 2 < x^2 by
      calc _ < _ := this
           _ ≤ _ := by simp only [sq_abs, le_add_iff_nonneg_right];positivity
    have : 2 < x := by linarith
    suffices 4 < x^2 by linarith
    rw [pow_two]
    calc _ = (2:ℝ) * 2 := by linarith
         _ < _ := by
          refine mul_lt_mul_of_pos_of_nonneg' this ?_ ?_ ?_
          <;> linarith


/-- Then the minimizing claim: -/
example (b w₁ w₂ : ℝ) (h : (1 ≤ b + w₁ ∧ 1 ≤ b) ∧ 1 ≤ w₁ + w₂ - b) :
  2 ≤ w₁ ^ 2 + w₂ ^ 2 := by
  have : 2 ≤ w₁ + w₂ := by linarith
  apply tooHardForChatGPT; tauto


lemma uniqueClaim₂ (x y : ℝ) (h₀ : 2 ≤ x + y) (h₁ : x ^ 2 + y ^ 2 ≤ 2) :
    (x,y) = (1,1) := by
  have u (x y : ℝ) (h₀ : 2 = x + y) (h₁ : 2 = x^2 + y^2) :
      (x,y) = (1,1) := by
    simp only [Prod.mk.injEq]
    have h : y = 2 - x := by linarith
    rw [h] at h₁
    have hx : x = 1 := by
      suffices x - 1 = 0 by linarith
      suffices (x-1)^2 = 0 by simp at this;tauto
      rw [sub_sq]
      simp
      rw [sub_sq] at h₁
      linarith
    constructor
    · suffices x - 1 = 0 by linarith
      suffices (x-1)^2 = 0 by simp at this;tauto
      rw [sub_sq]
      simp
      rw [sub_sq] at h₁
      linarith
    · linarith
  have : 2 ≤ x^2+y^2 := tooHardForChatGPT x y h₀
  apply u
  · linarith
  · by_contra hc
    have : 2 < x + y := lt_of_le_of_ne h₀ hc
    have := tooHardForChatGPT₁ (lt_of_le_of_ne h₀ hc)
    linarith

/-- Now let's consider the non-example.
`linarith` enables us to avoid thinking here.
-/
example : ¬ ∃ b w₁ w₂ : ℝ,
    (∀ x ∈ ({![0,0], ![1,1]} : Set (Fin 2 → ℝ)), ![w₁,w₂] ⬝ᵥ x - b ≤ -1) ∧
    (∀ x ∈ ({![0,1], ![1,0]} : Set (Fin 2 → ℝ)),          ![w₁,w₂] ⬝ᵥ x - b ≥ 1) := by
  push Not
  intro b w₁ w₂ h
  simp only [
    Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.cons_dotProduct, Matrix.dotProduct_of_isEmpty, add_zero, tsub_le_iff_right,
    le_neg_add_iff_add_le, forall_eq_or_imp, Matrix.head_cons, mul_zero, Matrix.tail_cons,
    forall_eq, mul_one, exists_eq_or_imp, zero_add, ↓existsAndEq, true_and] at h ⊢
  contrapose! h
  intro h₀
  linarith

/-- The XOR "0-class" `{(0,0), (1,1)}`, a standard non-separable example. -/
def A₀ := ({![0,0], ![1,1]} : Set (Fin 2 → ℝ))
/-- The XOR "1-class" `{(0,1), (1,0)}`. -/
def A₁ := ({![0,1], ![1,0]} : Set (Fin 2 → ℝ))

example : ¬ separable A₀ A₁ := by
  simp only [
    separable, A₀, Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.vec2_dotProduct, Fin.isValue, tsub_le_iff_right, le_neg_add_iff_add_le, forall_eq_or_imp,
    Matrix.cons_val_zero, mul_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero,
    forall_eq, mul_one, A₁, ge_iff_le, zero_add, not_exists, not_and, not_le, and_imp]
  intro b w₁ w₂ h h'
  linarith

-- But we can transform the data to be separable:
/-- A feature map lifting `ℝ²` into `ℝ³` that makes the XOR data separable. -/
def svmFeatureMap : (Fin 2 → ℝ) → (Fin 3 → ℝ) := fun x => ![x 0,x 1, (x 0 + x 1 - 1)^2]

example : separable (svmFeatureMap '' A₀) (svmFeatureMap '' A₁) := by
  simp only [
    separable, svmFeatureMap, Fin.isValue, A₀, Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_image,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, zero_sub, even_two, Even.neg_pow,
    one_pow, ↓existsAndEq, add_sub_cancel_right, true_and, tsub_le_iff_right, le_neg_add_iff_add_le,
    A₁, zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ge_iff_le]
  use -1
  use ![0,0,-2]
  constructor
  · intro x hx
    cases hx with
    | inl h => rw [← h];simp;linarith
    | inr h => rw [← h];simp;linarith
  · intro x hx
    cases hx with
    | inl h => rw [← h];simp
    | inr h => rw [← h];simp

/-- The "kernel trick" means we forget about the data just map
"without the computational burden of explicitly performing the transformation"
-/
def xorFeatureMap : (Fin 2 → ℝ) → (Fin 1 → ℝ) := fun x => ![(x 0 + x 1 - 1)^2]

example : separable (xorFeatureMap '' A₀) (xorFeatureMap '' A₁) := by
  simp only [
    separable, xorFeatureMap, Fin.isValue, A₀, Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_image,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, zero_sub, even_two, Even.neg_pow,
    one_pow, ↓existsAndEq, add_sub_cancel_right, true_and, or_self, tsub_le_iff_right,
    le_neg_add_iff_add_le, forall_eq', Matrix.dotProduct_cons, mul_one,
    Matrix.dotProduct_of_isEmpty, A₁, zero_add, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, ge_iff_le,
    mul_zero, exists_and_right]
  use -1
  simp only [neg_neg, Std.le_refl, and_true]
  use -2
  simp only [Matrix.head_neg, add_neg_le_iff_le_add, le_neg_add_iff_add_le]
  conv =>
    right
    change 2
  linarith


/-- If x₁ and x₂ are on the same side of the line then so is
s x₁ + (1-s)x₁. This fact in part explains the previous example:
there the segments connecting points on the same side intersect.
-/
example (b w₁ w₂ : ℝ) (u v : Fin 2 → ℝ) (h : (∀ x ∈ ({u, v} : Set (Fin 2 → ℝ)),
  ![w₁, w₂] ⬝ᵥ x - b ≥ 1)) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    ![w₁, w₂] ⬝ᵥ (s • u + (1 - s) • v) - b ≥ 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
   ge_iff_le, forall_eq_or_imp,
    forall_eq] at h
  unfold dotProduct at h
  simp only [
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Set.mem_Icc] at h hs
  unfold dotProduct
  simp only [
    Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ge_iff_le]
  cases h with
  | intro left right =>
    suffices  1 ≤ s * (w₁ * u 0 + w₂ * u 1 - b) + (1 - s) * (w₁ * v 0 + w₂ * v 1 - b) by
      linarith
    generalize  w₁ * u 0 + w₂ * u 1 - b = A at *
    generalize w₁ * v 0 + w₂ * v 1 - b = B at *
    calc 1 = s * 1 + (1 - s) * 1 := by linarith
         _ ≤ _ := by
          refine add_le_add ?_ ?_
          refine mul_le_mul_of_nonneg ?_ left ?_ ?_ <;> linarith
          refine mul_le_mul_of_nonneg ?_ right ?_ ?_ <;> linarith
