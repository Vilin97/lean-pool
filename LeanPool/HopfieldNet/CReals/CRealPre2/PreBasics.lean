/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Regular
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Star
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Foundational Definitions for Computable Real Numbers
-/

namespace Computable

/--
`CReal.Pre` is the pre-quotient representation of a computable real number.
It is a regular Cauchy sequence: |approx n - approx m| ≤ 1/2^n for n ≤ m.
(Bounds are derivable from regularity).
-/
structure CReal.Pre where
  approx : ℕ → ℚ
  is_regular : ∀ n m, n ≤ m → |approx n - approx m| ≤ (1 : ℚ) / (2 ^ n)

-- Helper for transitivity: existence of powers.
theorem exists_pow_gt {x : ℚ} (_ : 0 < x) : ∃ n : ℕ, x < (2 : ℚ) ^ n := by
  have one_lt_two : (1 : ℚ) < 2 := by norm_num
  simpa using pow_unbounded_of_one_lt x one_lt_two

lemma abs_add_four (a b c d : ℚ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d|
      = |(a + b) + (c + d)| := by simp [add_assoc]
  _ ≤ |a + b| + |c + d| := abs_add_le (a + b) (c + d)
  _ ≤ (|a| + |b|) + (|c| + |d|) := add_le_add (abs_add_le a b) (abs_add_le c d)
  _ = |a| + |b| + |c| + |d| := by simp [add_assoc]

namespace CReal.Pre

/-! ### Equivalence Relation -/

/--
Two pre-reals `x` and `y` are equivalent if |x.approx (n + 1) - y.approx (n + 1)| ≤ 1 / 2 ^ n.
-/
protected def Equiv (x y : CReal.Pre) : Prop :=
  ∀ n : ℕ, |x.approx (n + 1) - y.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ n

infix:50 " ≈ " => CReal.Pre.Equiv

theorem equiv_refl (x : CReal.Pre) : x ≈ x := by
  intro n; simp

theorem equiv_symm {x y : CReal.Pre} (h : x ≈ y) : y ≈ x := by
  intro n; rw [abs_sub_comm]; exact h n

/--
Transitivity of the equivalence relation.
Uses the epsilon-delta approach (le_of_forall_pos_le_add).
-/
theorem equiv_trans {x y z : CReal.Pre} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  intro k
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ε < (2 : ℚ) ^ m := exists_pow_gt (one_div_pos.mpr hε)
  have h_eps_bound : (1:ℚ) / 2^m < ε := (one_div_lt (pow_pos (by norm_num) m) hε).mpr hm
  let m_idx := max (k + 1) (m + 2)
  have h_k_le_midx : k + 1 ≤ m_idx := le_max_left _ _
  have h_m_le_midx : m + 2 ≤ m_idx := le_max_right _ _
  have h_midx_ge_one : 1 ≤ m_idx := le_trans (by norm_num) h_k_le_midx
  have h₁ := x.is_regular (k+1) m_idx h_k_le_midx
  have h₄ : |z.approx m_idx - z.approx (k + 1)| ≤ (1 : ℚ) / 2 ^ (k + 1) := by
    rw [abs_sub_comm]; exact z.is_regular (k+1) m_idx h_k_le_midx
  have h₂ : |x.approx m_idx - y.approx m_idx| ≤ (1 : ℚ) / 2 ^ (m_idx - 1) := by
    simpa [Nat.sub_add_cancel h_midx_ge_one] using hxy (m_idx - 1)
  have h₃ : |y.approx m_idx - z.approx m_idx| ≤ (1 : ℚ) / 2 ^ (m_idx - 1) := by
    simpa [Nat.sub_add_cancel h_midx_ge_one] using hyz (m_idx - 1)
  have h_error_bound : (1 : ℚ) / 2 ^ (m_idx - 2) ≤ (1 : ℚ) / 2 ^ m := by
    have h_le_m : m ≤ m_idx - 2 := Nat.le_sub_of_add_le h_m_le_midx
    rw [one_div_le_one_div (by positivity) (by positivity)]
    exact (pow_le_pow_iff_right₀ rfl).mpr h_le_m
  calc |x.approx (k + 1) - z.approx (k + 1)|
      ≤ |x.approx (k + 1) - x.approx m_idx|
        + |x.approx m_idx - y.approx m_idx|
        + |y.approx m_idx - z.approx m_idx|
        + |z.approx m_idx - z.approx (k + 1)| := by
          rw [show x.approx (k+1) - z.approx (k+1) = (x.approx (k+1) - x.approx m_idx) + (x.approx m_idx - y.approx m_idx) + (y.approx m_idx - z.approx m_idx) + (z.approx m_idx - z.approx (k+1)) by ring]
          exact abs_add_four _ _ _ _
    _ ≤ (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(k+1) := by
        gcongr
    _ = (1:ℚ) / 2^k + (1:ℚ) / 2^(m_idx-2) := by
        have h₁ : (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(k+1) = (1:ℚ) / 2^k := by
          field_simp [pow_succ]
          ring
        have h₂ : (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) = (1:ℚ) / 2^(m_idx-2) := by
          have h : (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) = (2:ℚ) / 2^(m_idx-1) := by
            rw [← add_div]; rw [@one_add_one_eq_two]
          rw [h]
          have h_midx_ge_two : 2 ≤ m_idx := le_trans (by norm_num) h_m_le_midx
          have h_exp : m_idx - 1 = (m_idx - 2) + 1 := by omega
          rw [h_exp, pow_succ]
          field_simp
        calc
          (1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(k+1)
          = ((1:ℚ) / 2^(k+1) + (1:ℚ) / 2^(k+1)) + ((1:ℚ) / 2^(m_idx-1) + (1:ℚ) / 2^(m_idx-1)) := by
              ring_nf
          _ = (1:ℚ) / 2^k + (1:ℚ) / 2^(m_idx-2) := by
              rw [h₁, h₂]
    _ ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ m := by gcongr;
    _ ≤ (1 : ℚ) / 2 ^ k + ε := by linarith [h_eps_bound]

instance setoid : Setoid CReal.Pre where
  r := CReal.Pre.Equiv
  iseqv := {
    refl  := equiv_refl
    symm  := equiv_symm
    trans := equiv_trans
  }

/-! ### Boundedness and Canonical Bounds -/

/--
Canonical Bound (cBound): `⌈|x₀|⌉ + 1`. Strictly positive and constructively defined.
-/
def cBound (x : CReal.Pre) : ℕ := Nat.ceil |x.approx 0| + 1

lemma cBound_pos (x : CReal.Pre) : 0 < x.cBound := Nat.succ_pos _

/-- Proof that `cBound` is a uniform bound. -/
lemma abs_approx_le_cBound (x : CReal.Pre) (n : ℕ) : |x.approx n| ≤ x.cBound := by
  dsimp [cBound]
  have h_reg : |x.approx n - x.approx 0| ≤ (1 : ℚ) := by
    simpa [abs_sub_comm, pow_zero, one_div] using x.is_regular 0 n (Nat.zero_le _)
  have h_ceil : |x.approx 0| ≤ (Nat.ceil |x.approx 0| : ℚ) := Nat.le_ceil _
  have h_triangle : |x.approx n| ≤ |x.approx n - x.approx 0| + |x.approx 0| :=
    calc |x.approx n|
      = |(x.approx n - x.approx 0) + x.approx 0| := by ring_nf
    _ ≤ |x.approx n - x.approx 0| + |x.approx 0| := abs_add_le (x.approx n - x.approx 0) (x.approx 0)
  calc
    |x.approx n| ≤ |x.approx n - x.approx 0| + |x.approx 0| := h_triangle
    _ ≤ 1 + |x.approx 0| := by linarith [h_reg]
    _ ≤ 1 + (Nat.ceil |x.approx 0| : ℚ) := by linarith [h_ceil]
    _ = (Nat.ceil |x.approx 0| : ℚ) + 1 := by rw [add_comm]
    _ = (↑(Nat.ceil |x.approx 0|) + 1 : ℚ) := by norm_cast
    _ = (↑(Nat.ceil |x.approx 0| + 1) : ℚ) := by norm_cast

end CReal.Pre

end Computable
