/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Tactic

@[expose] public section

/-!
# A factorial-square bound for the partitions in Faà di Bruno's formula

The estimate is uniform in the order.  Extending a partition either creates a
singleton or increases one old part, so the factorial-square weight grows by
at most `(n + 1)^2 * (x + 2)`.  This avoids replacing every derivative in the
composition formula by the largest derivative bound.
-/

noncomputable section

open scoped BigOperators

namespace EulerGevreyComposition

variable {n : ℕ}

lemma sum_partSize (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr c.equivSigma

lemma sum_partSize_real (c : OrderedFinpartition n) :
    ∑ i, (c.partSize i : ℝ) = n := by
  exact_mod_cast sum_partSize c

lemma sum_partSize_succ_sq_le (c : OrderedFinpartition n) :
    ∑ i, ((c.partSize i : ℝ) + 1)^2 ≤ 2 * ((n : ℝ) + 1)^2 := by
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  calc
    _ ≤ ∑ i, ((n : ℝ) + 1) * ((c.partSize i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (c.partSize i : ℝ) ≤ n := by exact_mod_cast c.partSize_le i
      nlinarith [mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ (c.partSize i : ℝ) + 1 by positivity)]
    _ = ((n : ℝ) + 1) * ((n : ℝ) + c.length) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_partSize_real]
      simp
    _ ≤ _ := by nlinarith

def factorialProduct (c : OrderedFinpartition n) : ℝ :=
  ∏ i, ((c.partSize i).factorial : ℝ)

def partitionWeight (x : ℝ) (c : OrderedFinpartition n) : ℝ :=
  x^c.length * ((c.length.factorial : ℝ) * factorialProduct c)^2

def partitionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, partitionWeight x c

lemma partitionWeight_nonneg (x : ℝ) (hx : 0 ≤ x) (c : OrderedFinpartition n) :
    0 ≤ partitionWeight x c := by
  unfold partitionWeight
  positivity

lemma factorialProduct_extendLeft (c : OrderedFinpartition n) :
    factorialProduct c.extendLeft = factorialProduct c := by
  change (∏ i : Fin (c.length+1),
    (Nat.factorial (Fin.cons (α := fun _ => ℕ) 1 c.partSize i) : ℝ)) =
    ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)
  rw [Fin.prod_univ_succ]
  simp

lemma factorialProduct_extendMiddle (c : OrderedFinpartition n) (i : Fin c.length) :
    factorialProduct (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1) * factorialProduct c := by
  change (∏ j : Fin c.length,
    ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      ((c.partSize i : ℝ) + 1) * ∏ j : Fin c.length, ((c.partSize j).factorial : ℝ)
  have he : (fun j : Fin c.length =>
      ((Function.update c.partSize i (c.partSize i+1) j).factorial : ℝ)) =
      fun j => (if j = i then (c.partSize i : ℝ) + 1 else 1) *
        ((c.partSize j).factorial : ℝ) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [Nat.factorial_succ]
    · simp [h]
  rw [he, Finset.prod_mul_distrib]
  simp

lemma partitionWeight_extendLeft (x : ℝ) (c : OrderedFinpartition n) :
    partitionWeight x c.extendLeft =
      (x * ((c.length : ℝ) + 1)^2) * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendLeft_length,
    factorialProduct_extendLeft, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  ring

lemma partitionWeight_extendMiddle (x : ℝ) (c : OrderedFinpartition n) (i : Fin c.length) :
    partitionWeight x (c.extendMiddle i) =
      ((c.partSize i : ℝ) + 1)^2 * partitionWeight x c := by
  simp only [partitionWeight, OrderedFinpartition.extendMiddle_length,
    factorialProduct_extendMiddle]
  ring

lemma partitionSum_succ (n : ℕ) (x : ℝ) :
    partitionSum (n+1) x =
      ∑ c : OrderedFinpartition n,
        (x * ((c.length : ℝ) + 1)^2 + ∑ i, ((c.partSize i : ℝ) + 1)^2) *
          partitionWeight x c := by
  unfold partitionSum
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_option, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    partitionWeight_extendLeft, partitionWeight_extendMiddle, ← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma partitionSum_succ_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum (n+1) x ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x := by
  rw [partitionSum_succ, partitionSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hl : (c.length : ℝ) ≤ n := by exact_mod_cast c.length_le
  have hs : ((c.length : ℝ) + 1)^2 ≤ ((n : ℝ) + 1)^2 := by gcongr
  apply mul_le_mul_of_nonneg_right _ (partitionWeight_nonneg x hx c)
  calc
    _ ≤ x * ((n : ℝ) + 1)^2 + 2 * ((n : ℝ) + 1)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hs hx) (sum_partSize_succ_sq_le c)
    _ = _ := by ring

/-- The entire factorial-square Faà di Bruno partition sum has one fixed
exponential radius, independent of the differentiation order. -/
theorem partitionSum_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum n x ≤ (x+2)^n * (n.factorial : ℝ)^2 := by
  induction n with
  | zero =>
    simp [partitionSum, partitionWeight, factorialProduct,
      OrderedFinpartition.default_eq]
  | succ n ih =>
    calc
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * partitionSum n x :=
        partitionSum_succ_le n x hx
      _ ≤ ((n : ℝ) + 1)^2 * (x+2) * ((x+2)^n * (n.factorial : ℝ)^2) := by
        gcongr
      _ = _ := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

end EulerGevreyComposition
