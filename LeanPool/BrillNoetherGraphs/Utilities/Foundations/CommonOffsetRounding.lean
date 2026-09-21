/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Lean.Elab.Tactic.Omega

/-!
# A common offset for integer rounding

Signed Euclidean division by a positive integer is floor division. Averaging
over all offsets recovers the original integer, and the total rounded
absolute difference recovers the original absolute difference. Consequently
a family of endpoint differences with total absolute value less than the
denominator has an offset that rounds every pair to equal integers.

The endpoint-slope bounds used in finite graph specialization are preserved
by this same rounding, including negative heights and negative slopes.
-/

namespace Utilities.CommonOffsetRounding

open Finset

/-- Floor an integer after adding the chosen residue offset. -/
def round (N : ℕ) (k : Fin N) (a : ℤ) : ℤ :=
  (a + (k.val : ℤ)) / (N : ℤ)

theorem round_mono (N : ℕ) (hN : 0 < N) (k : Fin N)
    {a b : ℤ} (hab : a ≤ b) : round N k a ≤ round N k b := by
  apply Int.ediv_le_ediv (by exact_mod_cast hN)
  omega

/-- An integral translation before rounding remains exact. -/
theorem round_add_mul (N : ℕ) (hN : 0 < N) (k : Fin N) (a c : ℤ) :
    round N k (a + (N : ℤ) * c) = round N k a + c := by
  unfold round
  rw [add_right_comm a ((N : ℤ) * c) (k.val : ℤ)]
  exact Int.add_mul_ediv_left _ _ (by exact_mod_cast hN.ne')

private theorem sum_range_shifted_ediv (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (∑ k ∈ range N, (a + (k : ℤ)) / (N : ℤ)) = a := by
  let S : ℤ → ℤ := fun x => ∑ k ∈ range N, (x + (k : ℤ)) / (N : ℤ)
  have hNInt : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hstep (x : ℤ) : S (x + 1) = S x + 1 := by
    have hlast := sum_range_succ (fun k : ℕ => (x + (k : ℤ)) / (N : ℤ)) N
    have hfirst := sum_range_succ' (fun k : ℕ => (x + (k : ℤ)) / (N : ℤ)) N
    have htranslate : (x + (N : ℤ)) / (N : ℤ) = x / (N : ℤ) + 1 := by
      simpa only [mul_one] using Int.add_mul_ediv_left x 1 hNInt
    have hshift : (∑ k ∈ range N, (x + ((k + 1 : ℕ) : ℤ)) / (N : ℤ)) =
        S (x + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      push_cast
      omega
    rw [hshift] at hfirst
    rw [htranslate] at hlast
    change _ = S x + (x / (N : ℤ) + 1) at hlast
    simp only [Nat.cast_zero, add_zero] at hfirst
    omega
  have hzero : S 0 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Int.ediv_eq_zero_of_lt
    · omega
    · have hkN := Finset.mem_range.mp hk
      simpa using (show (k : ℤ) < (N : ℤ) by exact_mod_cast hkN)
  have hnat : ∀ m : ℕ, S (m : ℤ) = (m : ℤ) := by
    intro m
    induction m with
    | zero => exact hzero
    | succ m ih =>
      rw [Nat.cast_add, Nat.cast_one, hstep, ih]
  have hneg : ∀ m : ℕ, S (-(m : ℤ)) = -(m : ℤ) := by
    intro m
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      have hs := hstep (-((m + 1 : ℕ) : ℤ))
      have harg : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
      rw [harg, ih] at hs
      omega
  change S a = a
  cases a with
  | ofNat m => exact hnat m
  | negSucc m =>
    simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using hneg (m + 1)

/-- The sum over all residue offsets is the original signed integer. -/
theorem sum_round (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (∑ k : Fin N, round N k a) = a := by
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (a + (k : ℤ)) / (N : ℤ)) N).trans
    (sum_range_shifted_ediv N hN a)

/-- The total absolute rounding discrepancy over all offsets equals the
original absolute discrepancy. No bound on that discrepancy is required. -/
theorem sum_abs_round_sub (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    (∑ k : Fin N, |round N k a - round N k b|) = |a - b| := by
  by_cases hab : a ≤ b
  · have habs (k : Fin N) : |round N k a - round N k b| =
        round N k b - round N k a := by
      rw [abs_of_nonpos (sub_nonpos.mpr (round_mono N hN k hab))]
      omega
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, sum_round N hN b, sum_round N hN a,
      abs_of_nonpos (sub_nonpos.mpr hab)]
    omega
  · have hba : b ≤ a := le_of_not_ge hab
    have habs (k : Fin N) : |round N k a - round N k b| =
        round N k a - round N k b :=
      abs_of_nonneg (sub_nonneg.mpr (round_mono N hN k hba))
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, sum_round N hN a, sum_round N hN b,
      abs_of_nonneg (sub_nonneg.mpr hba)]

/-- If the total discrepancy of finitely many endpoint pairs is less than
`N`, one common residue offset rounds all those pairs to equal integers. -/
theorem exists_common_offset {ι : Type*} (N : ℕ) (hN : 0 < N)
    (F : Finset ι) (A B : ι → ℤ)
    (hBudget : (∑ e ∈ F, |A e - B e|) < (N : ℤ)) :
    ∃ k : Fin N, ∀ e ∈ F, round N k (A e) = round N k (B e) := by
  classical
  let cost : Fin N → ℤ := fun k => ∑ e ∈ F, |round N k (A e) - round N k (B e)|
  have hsum : (∑ k : Fin N, cost k) = ∑ e ∈ F, |A e - B e| := by
    dsimp only [cost]
    rw [Finset.sum_comm]
    simp_rw [sum_abs_round_sub N hN]
  have hsmall : ∃ k : Fin N, cost k < 1 := by
    by_contra! h
    have hlarge : (N : ℤ) ≤ ∑ k : Fin N, cost k := by
      calc
        (N : ℤ) = ∑ _k : Fin N, (1 : ℤ) := by simp
        _ ≤ ∑ k : Fin N, cost k := Finset.sum_le_sum (fun k _ => h k)
    omega
  obtain ⟨k, hk⟩ := hsmall
  refine ⟨k, ?_⟩
  intro e he
  have hle : |round N k (A e) - round N k (B e)| ≤ cost k := by
    change |round N k (A e) - round N k (B e)| ≤
      ∑ j ∈ F, |round N k (A j) - round N k (B j)|
    exact Finset.single_le_sum
      (f := fun j : ι => |round N k (A j) - round N k (B j)|)
      (fun j _ => abs_nonneg _) he
  have hnonneg := abs_nonneg (round N k (A e) - round N k (B e))
  have hzero : |round N k (A e) - round N k (B e)| = 0 := by omega
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Common-offset rounding preserves any integral lower and upper slope
bounds on an endpoint difference across a path of length `N`. -/
theorem round_sub_bounds (N : ℕ) (hN : 0 < N) (k : Fin N)
    (A B a b : ℤ) (hlower : (N : ℤ) * a ≤ B - A)
    (hupper : B - A ≤ (N : ℤ) * b) :
    a ≤ round N k B - round N k A ∧ round N k B - round N k A ≤ b := by
  have hlo := round_mono N hN k (a := A + (N : ℤ) * a) (b := B) (by omega)
  have hhi := round_mono N hN k (a := B) (b := A + (N : ℤ) * b) (by omega)
  rw [round_add_mul N hN k A a] at hlo
  rw [round_add_mul N hN k A b] at hhi
  omega

end Utilities.CommonOffsetRounding
