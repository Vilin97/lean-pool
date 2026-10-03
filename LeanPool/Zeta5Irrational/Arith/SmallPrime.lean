/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.BinomBasis
public import LeanPool.Zeta5Irrational.Arith.Val
public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.Arith.TauBound
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # Small primes: generic tools for the bound (3.12)

* integer values of the binomial polynomials at all integers;
* a polynomial of degree `≤ d` whose values at `d + 1` consecutive integers have valuation `≥ β`
  has valuation `≥ β` at every integer (`VG_eval_int_of_window`);
* Kummer's bound `v_p(C(n, k)) ≤ log_p n`;
* `v_p(H^{(5)}_m) ≥ -5 log_p m`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- Values of `bin k` at integers are integers. -/
lemma bin_eval_int (k : ℕ) (z : ℤ) : ∃ w : ℤ, (bin k).eval (z : ℚ) = w := by
  induction k generalizing z with
  | zero => exact ⟨1, by simp [bin_zero]⟩
  | succ k
    ih =>
    have hstep : ∀ y : ℚ, (bin (k + 1)).eval (y + 1) = (bin (k + 1)).eval y + (bin k).eval y := by
      intro y
      have := congrArg (eval y) (bin_comp_add_one k)
      rw [eval_comp, eval_add, eval_X, eval_one, eval_add] at this
      exact this
    induction z using Int.induction_on with
    | zero => exact ⟨0, by rw [Int.cast_zero, bin_eval_zero (by omega)]⟩
    | succ i hi =>
      obtain ⟨w, hw⟩ := hi
      obtain ⟨w', hw'⟩ := ih (i : ℤ)
      refine ⟨w + w', ?_⟩
      push_cast at hw hw' ⊢
      rw [hstep, hw, hw']
    | pred i hi =>
      obtain ⟨w, hw⟩ := hi
      obtain ⟨w', hw'⟩ := ih (-(i : ℤ) - 1)
      refine ⟨w - w', ?_⟩
      have := hstep ((-(i : ℤ) - 1 : ℤ) : ℚ)
      push_cast at this hw hw' ⊢
      rw [show (-(i : ℚ) - 1 + 1) = -(i : ℚ) by ring, hw] at this
      linarith

omit hp in
lemma VG_bin_eval_int (k : ℕ) (z : ℤ) : VG p ((bin k).eval (z : ℚ)) 0 := by
  obtain ⟨w, hw⟩ := bin_eval_int k z
  rw [hw]; exact VG.intCast w

/-- **Window lemma**: values at `s, …, s + d` control the values at all integers. -/
theorem VG_eval_int_of_window {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) (s : ℤ) {β : ℚ}
    (hv : ∀ i ≤ d, VG p (P.eval ((s + i : ℤ) : ℚ)) β) (z : ℤ) : VG p (P.eval (z : ℚ)) β := by
  set Q := P.comp (X + C (s : ℚ)) with hQ
  have hQd : Q.natDegree ≤ d := by
    rw [hQ]
    refine (natDegree_comp_le).trans ?_
    have : (X + C (s : ℚ)).natDegree ≤ 1 := by rw [natDegree_X_add_C]
    calc
      P.natDegree * (X + C (s : ℚ)).natDegree ≤ d * 1 := Nat.mul_le_mul hd this
      _ = d := by ring
  have hQv : ∀ m ≤ d, VG p (Q.eval (m : ℚ)) β := by
    intro m hm
    have := hv m hm
    rw [hQ, eval_comp]
    simp only [eval_add, eval_X, eval_C]
    push_cast at this ⊢
    rwa [add_comm]
  obtain ⟨e, he, hev⟩ := binRep_of_values hQd hQv
  have hPz : P.eval (z : ℚ) = Q.eval ((z - s : ℤ) : ℚ) := by rw [hQ, eval_comp]; simp
  rw [hPz, he, eval_finsetSum]
  refine VG.sum _ fun m hm => ?_
  rw [eval_mul, eval_C]
  have :=
    (hev m (by have := Finset.mem_range.mp hm; omega)).mul (VG_bin_eval_int (p := p) m (z - s))
  simpa using this

/-- **Kummer**: `v_p(C(n, k)⁻¹) ≥ -log_p n`. -/
lemma VG_choose_inv {n k : ℕ} (hk : k ≤ n) : VG p ((n.choose k : ℚ)⁻¹) (-(Nat.log p n : ℚ)) := by
  apply VG.inv (by exact_mod_cast (Nat.choose_pos hk).ne')
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp.out]
  exact_mod_cast Nat.factorization_choose_le_log

/-- `v_p(H^{(5)}_m) ≥ -5 log_p m`. -/
lemma VG_H5_log (m : ℕ) : VG p (H5 m) (-5 * (Nat.log p m : ℚ)) := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  have hv' := Finset.mem_Icc.mp hv
  have h := (VG.inv_nat (p := p) hv'.1 hv'.2).pow 5
  rw [inv_pow] at h
  rw [one_div]
  refine h.mono ?_
  push_cast; linarith

omit hp in
lemma log_mono {a b : ℕ} (h : a ≤ b) : (Nat.log p a : ℚ) ≤ Nat.log p b := by
  exact_mod_cast Nat.log_mono_right h

end Zeta5Irrational
