/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Entropy
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! # Sequential Normalization -/

open scoped BigOperators

namespace BeyondBethe

/-- Total weight still available to position `t` when the columns are exposed
in the order `θ`.  This is the position-indexed version of `suffixMass`. -/
noncomputable def orderedSuffixWeight
    {n : ℕ} (W : Fin n → Fin n → ℝ)
    (θ : Equiv.Perm (Fin n)) (t : Fin n) : ℝ :=
  ∑ s, if t ≤ s then W t (θ s) else 0

/-- The probability of one complete outcome of sequential sampling without
replacement, with rows processed in their natural order. -/
noncomputable def orderedSequentialLikelihood
    {n : ℕ} (W : Fin n → Fin n → ℝ)
    (θ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ t, W t (θ t) / orderedSuffixWeight W θ t

/-- After the first column `p` is chosen, `tailWeight W p` is the smaller
instance obtained by deleting the first row and that column.  The swap is the
one used by Mathlib's canonical decomposition of a permutation of `Fin (n+1)`.
-/
def tailWeight {n : ℕ}
    (W : Fin (n + 1) → Fin (n + 1) → ℝ) (p : Fin (n + 1)) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ W i.succ ((Equiv.swap 0 p) j.succ)

theorem orderedSuffixWeight_zero
    {n : ℕ} (W : Fin (n + 1) → Fin (n + 1) → ℝ)
    (θ : Equiv.Perm (Fin (n + 1))) :
    orderedSuffixWeight W θ 0 = ∑ j, W 0 j := by
  unfold orderedSuffixWeight
  simp only [Fin.zero_le, ↓reduceIte]
  exact Equiv.sum_comp θ (W 0)

theorem orderedSuffixWeight_decompose_succ
    {n : ℕ} (W : Fin (n + 1) → Fin (n + 1) → ℝ)
    (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    orderedSuffixWeight W (Equiv.Perm.decomposeFin.symm (p, e)) i.succ =
      orderedSuffixWeight (tailWeight W p) e i := by
  unfold orderedSuffixWeight tailWeight
  rw [Fin.sum_univ_succ]
  simp

theorem orderedSequentialLikelihood_decompose
    {n : ℕ} (W : Fin (n + 1) → Fin (n + 1) → ℝ)
    (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    orderedSequentialLikelihood W (Equiv.Perm.decomposeFin.symm (p, e)) =
      (W 0 p / ∑ j, W 0 j) * orderedSequentialLikelihood (tailWeight W p) e := by
  rw [orderedSequentialLikelihood, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    orderedSuffixWeight_zero, orderedSequentialLikelihood]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Equiv.Perm.decomposeFin_symm_apply_succ,
    orderedSuffixWeight_decompose_succ]
  rfl

/-- Sequential choice probabilities sum to one.  The proof is the chain rule:
split a permutation according to its first chosen column and apply induction to
the remaining rows and columns. -/
theorem orderedSequentialLikelihood_sum_eq_one :
    ∀ (n : ℕ) (W : Fin n → Fin n → ℝ),
      (∀ i j, 0 < W i j) →
      ∑ θ : Equiv.Perm (Fin n), orderedSequentialLikelihood W θ = 1 := by
  intro n
  induction n with
  | zero =>
      intro W _
      simp [orderedSequentialLikelihood]
  | succ n ih =>
      intro W hW
      have htail : ∀ p i j, 0 < tailWeight W p i j := by
        intro p i j
        exact hW i.succ ((Equiv.swap 0 p) j.succ)
      have hrow : 0 < ∑ j, W 0 j :=
        Finset.sum_pos (fun j _ ↦ hW 0 j) ⟨0, Finset.mem_univ 0⟩
      calc
        ∑ θ : Equiv.Perm (Fin (n + 1)), orderedSequentialLikelihood W θ =
            ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n),
              orderedSequentialLikelihood W
                (Equiv.Perm.decomposeFin.symm pe) :=
          (Equiv.sum_comp Equiv.Perm.decomposeFin.symm
            (orderedSequentialLikelihood W)).symm
        _ = ∑ p, ∑ e,
              orderedSequentialLikelihood W
                (Equiv.Perm.decomposeFin.symm (p, e)) :=
          Fintype.sum_prod_type _
        _ = ∑ p, ∑ e,
              (W 0 p / ∑ j, W 0 j) *
                orderedSequentialLikelihood (tailWeight W p) e := by
          simp_rw [orderedSequentialLikelihood_decompose]
        _ = ∑ p, (W 0 p / ∑ j, W 0 j) *
              (∑ e, orderedSequentialLikelihood (tailWeight W p) e) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.mul_sum]
        _ = ∑ p, W 0 p / ∑ j, W 0 j := by
          apply Finset.sum_congr rfl
          intro p _
          rw [ih (tailWeight W p) (htail p), mul_one]
        _ = 1 := by
          rw [← Finset.sum_div, div_self hrow.ne']

end BeyondBethe
