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

/--
The type of computable real numbers.
-/
abbrev CReal := Quotient (CReal.Pre.setoid)

namespace CReal

/-! ### Basic Arithmetic (Zero, Neg, Add) -/

/-- The `CReal.Pre` representation of `0`. -/
protected def Pre.zero : CReal.Pre where
  approx := fun _ ↦ 0
  is_regular := by intro n m _; simp

instance : Zero CReal := ⟨⟦CReal.Pre.zero⟧⟩

/-- Negation of a `CReal.Pre`. -/
protected def Pre.neg (x : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ -x.approx n
  is_regular := by
    intro n m h_le; rw [neg_sub_neg, abs_sub_comm]; exact x.is_regular n m h_le

theorem neg_respects_equiv (x y : CReal.Pre) (h : CReal.Pre.Equiv x y) :
    CReal.Pre.Equiv (CReal.Pre.neg x) (CReal.Pre.neg y) := by
  intro n
  dsimp [CReal.Pre.neg, CReal.Pre.Equiv]
  simp only [neg_sub_neg, abs_sub_comm]
  exact h n

instance : Neg CReal := ⟨Quotient.map Pre.neg neg_respects_equiv⟩

/--
Addition of two `CReal.Pre`s. Shifted by 1 to maintain regularity.
-/
protected def Pre.add (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ x.approx (n + 1) + y.approx (n + 1)
  is_regular := by
    intro n m h_le
    have h_le_succ : n + 1 ≤ m + 1 := Nat.succ_le_succ h_le
    calc
      |(x.approx (n + 1) + y.approx (n + 1)) - (x.approx (m + 1) + y.approx (m + 1))|
        = |(x.approx (n + 1) - x.approx (m + 1)) + (y.approx (n + 1) - y.approx (m + 1))| := by ring_nf
      _ ≤ |x.approx (n + 1) - x.approx (m + 1)| + |y.approx (n + 1) - y.approx (m + 1)| :=
          abs_add_le (x.approx (n + 1) - x.approx (m + 1)) (y.approx (n + 1) - y.approx (m + 1))
      _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
        gcongr
        · exact x.is_regular (n + 1) (m + 1) h_le_succ
        · exact y.is_regular (n + 1) (m + 1) h_le_succ
      _ = (1 : ℚ) / 2 ^ n := by field_simp [pow_succ]; ring

theorem add_respects_equiv {x₁ x₂ y₁ y₂ : CReal.Pre} (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.add x₁ y₁) (CReal.Pre.add x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.add, CReal.Pre.Equiv]
  calc
    _ = |(x₁.approx (n + 2) - x₂.approx (n + 2)) + (y₁.approx (n + 2) - y₂.approx (n + 2))| := by ring_nf
    _ ≤ |x₁.approx (n + 2) - x₂.approx (n + 2)| + |y₁.approx (n + 2) - y₂.approx (n + 2)| :=
      abs_add_le (x₁.approx (n + 2) - x₂.approx (n + 2)) (y₁.approx (n + 2) - y₂.approx (n + 2))
    _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
        gcongr
        · exact h_x (n + 1)
        · exact h_y (n + 1)
    _ = (1 : ℚ) / 2 ^ n := by field_simp [pow_succ]; ring

/-- Addition on `CReal`. -/
instance : Add CReal := by
  refine ⟨Quotient.map₂ CReal.Pre.add ?_⟩
  intro a₁ a₂ h₁ b₁ b₂ h₂
  exact add_respects_equiv h₁ h₂

/-! ### Multiplication -/

-- Helper lemmas for bounding and logarithms.

/-- `B ≤ 2^(log₂ B + 1)` for B > 0. -/
lemma le_pow_log_succ (B : ℕ) (_ : 0 < B) :
    (B : ℚ) ≤ 2 ^ (Nat.log 2 B + 1) := by
  exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) B).le

/-- `2^a + 2^b ≤ 2^(max a b + 1)`. -/
lemma two_pow_add_le_pow_max_add_one (a b : ℕ) :
    (2 : ℚ) ^ a + 2 ^ b ≤ 2 ^ (max a b + 1) := by
  have h_max : (2:ℚ)^a ≤ (2:ℚ)^(max a b) := (pow_le_pow_iff_right₀ (by norm_num)).mpr (le_max_left a b)
  have h_max' : (2:ℚ)^b ≤ (2:ℚ)^(max a b) := (pow_le_pow_iff_right₀ (by norm_num)).mpr (le_max_right a b)
  calc
    _ ≤ (2:ℚ)^(max a b) + (2:ℚ)^(max a b) := add_le_add h_max h_max'
    _ = 2 ^ (max a b + 1) := by rw [pow_succ, ← two_mul]; exact Rat.mul_comm 2 (2 ^ max a b)

/-- Bounds Bx + By by a power of 2 based on their logs. -/
lemma add_bounds_le_power_of_two (Bx By : ℕ) (hBx : 0 < Bx) (hBy : 0 < By) :
    (Bx + By : ℚ) ≤ 2 ^ (max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1) := by
  calc
    (Bx + By : ℚ) ≤ 2 ^ (Nat.log 2 Bx + 1) + 2 ^ (Nat.log 2 By + 1) :=
      add_le_add (le_pow_log_succ Bx hBx) (le_pow_log_succ By hBy)
    _ ≤ 2 ^ (max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1) :=
      two_pow_add_le_pow_max_add_one _ _

/--
The precision shift S for multiplication. S = `max (log Bx + 1) (log By + 1) + 1`.
-/
def Pre.mulShift (x y : CReal.Pre) : ℕ :=
  let Bx := x.cBound
  let By := y.cBound
  max (Nat.log 2 Bx + 1) (Nat.log 2 By + 1) + 1

/-- Key property: Bx + By ≤ 2^S. -/
lemma Pre.sum_cBound_le_pow_mulShift (x y : CReal.Pre) :
    (x.cBound + y.cBound : ℚ) ≤ 2 ^ (x.mulShift y) := by
  dsimp [mulShift]
  apply add_bounds_le_power_of_two <;> apply CReal.Pre.cBound_pos

/--
**Core Product Estimate**.
`|xₙ yₙ - xₘ yₘ| ≤ (Bx + By) * (1 / 2 ^ n)` whenever
• `kₙ ≤ kₘ`
• `|xₙ| ≤ Bx` and `|yₘ| ≤ By`.
-/
lemma product_diff_bound
    (x y : CReal.Pre) {kₙ kₘ : ℕ} (h_le : kₙ ≤ kₘ)
    (Bx By : ℚ) (hxB : |x.approx kₙ| ≤ Bx) (hyB : |y.approx kₘ| ≤ By) :
    |x.approx kₙ * y.approx kₙ - x.approx kₘ * y.approx kₘ| ≤
      (Bx + By) * (1 / 2 ^ kₙ) := by
  -- Regularity (Cauchy) bounds for the two sequences.
  have h_xreg : |x.approx kₙ - x.approx kₘ| ≤ (1 : ℚ) / 2 ^ kₙ :=
    x.is_regular kₙ kₘ h_le
  have h_yreg : |y.approx kₙ - y.approx kₘ| ≤ (1 : ℚ) / 2 ^ kₙ :=
    y.is_regular kₙ kₘ h_le
  -- Non-negativity of the bounding constants.
  have hBx_nonneg : (0 : ℚ) ≤ Bx := le_trans (abs_nonneg _) hxB
  have hBy_nonneg : (0 : ℚ) ≤ By := le_trans (abs_nonneg _) hyB
  calc
    |x.approx kₙ * y.approx kₙ - x.approx kₘ * y.approx kₘ|
        = |x.approx kₙ * (y.approx kₙ - y.approx kₘ) +
            y.approx kₘ * (x.approx kₙ - x.approx kₘ)| := by
          ring_nf
    _ ≤ |x.approx kₙ * (y.approx kₙ - y.approx kₘ)| +
        |y.approx kₘ * (x.approx kₙ - x.approx kₘ)| := by
          exact abs_add_le _ _
    _ = |x.approx kₙ| * |y.approx kₙ - y.approx kₘ| +
        |y.approx kₘ| * |x.approx kₙ - x.approx kₘ| := by
          simp [abs_mul]
    _ ≤ Bx * (1 / 2 ^ kₙ) + By * (1 / 2 ^ kₙ) := by
      have h1 : |x.approx kₙ| * |y.approx kₙ - y.approx kₘ| ≤
          Bx * (1 / 2 ^ kₙ) := by
        have := mul_le_mul hxB h_yreg (abs_nonneg _) hBx_nonneg
        simpa using this
      have h2 : |y.approx kₘ| * |x.approx kₙ - x.approx kₘ| ≤
          By * (1 / 2 ^ kₙ) := by
        have := mul_le_mul hyB h_xreg (abs_nonneg _) hBy_nonneg
        simpa using this
      linarith
    _ = (Bx + By) * (1 / 2 ^ kₙ) := by ring

/--
The product of two `CReal.Pre`s. (x*y)_n := x_{n+S} * y_{n+S}.
-/
protected def Pre.mul (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦
    let S := x.mulShift y
    x.approx (n + S) * y.approx (n + S)
  is_regular := by
    intro n m hnm
    let S := x.mulShift y
    let kₙ := n + S; let kₘ := m + S
    have hknm : kₙ ≤ kₘ := add_le_add_right hnm S
    let Bx := x.cBound; let By := y.cBound
    have h_core := product_diff_bound x y hknm (Bx:ℚ) (By:ℚ) (x.abs_approx_le_cBound kₙ) (y.abs_approx_le_cBound kₘ)
    have h_S := x.sum_cBound_le_pow_mulShift y
    calc
      _ ≤ (Bx + By : ℚ) * (1 / 2 ^ kₙ) := h_core
      _ ≤ (2 ^ S : ℚ) * (1 / 2 ^ kₙ) := mul_le_mul_of_nonneg_right h_S (by positivity)
      _ = (1 : ℚ) / 2 ^ n := by
        dsimp [kₙ]; rw [pow_add]; field_simp [pow_ne_zero]

/--
First half of the product estimate used in `mul_equiv_same_index`.
`|x₁ₖ|` is controlled by a bound `Bx₁`, while the difference
`|y₁ₖ − y₂ₖ|` is controlled by the `Equiv` relation.
-/
lemma prod_diff_bound_left
    {x₁ y₁ y₂ : CReal.Pre} {K : ℕ}
    (Bx₁ : ℚ) (h_x_bound : |x₁.approx K| ≤ Bx₁)
    (h_y_diff : |y₁.approx K - y₂.approx K| ≤ 1 / 2 ^ (K - 1)) :
    |x₁.approx K| * |y₁.approx K - y₂.approx K| ≤
      Bx₁ * (1 / 2 ^ (K - 1)) := by
  have hBx_nonneg : (0 : ℚ) ≤ Bx₁ := le_trans (abs_nonneg _) h_x_bound
  exact mul_le_mul h_x_bound h_y_diff (abs_nonneg _) hBx_nonneg

/--
Second half of the product estimate (roles of the factors swapped).
-/
lemma prod_diff_bound_right
    {y₂ x₁ x₂ : CReal.Pre} {K : ℕ}
    (By₂ : ℚ) (h_y_bound : |y₂.approx K| ≤ By₂)
    (h_x_diff : |x₁.approx K - x₂.approx K| ≤ 1 / 2 ^ (K - 1)) :
    |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
      By₂ * (1 / 2 ^ (K - 1)) := by
  have hBy_nonneg : (0 : ℚ) ≤ By₂ := le_trans (abs_nonneg _) h_y_bound
  exact mul_le_mul h_y_bound h_x_diff (abs_nonneg _) hBy_nonneg

/--
Add the two previous bounds and rewrite the right-hand side
into the convenient form `(Bx₁ + By₂)/2^(K-1)`.
-/
lemma prod_diff_sum_bound
    {x₁ x₂ y₁ y₂ : CReal.Pre} {K : ℕ}
    {Bx₁ By₂ : ℚ}
    (h₁ :
      |x₁.approx K| * |y₁.approx K - y₂.approx K| ≤
        Bx₁ * (1 / 2 ^ (K - 1)))
    (h₂ :
      |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
        By₂ * (1 / 2 ^ (K - 1))) :
    |x₁.approx K| * |y₁.approx K - y₂.approx K| +
      |y₂.approx K| * |x₁.approx K - x₂.approx K| ≤
      (Bx₁ + By₂) / 2 ^ (K - 1) := by
  have : (Bx₁ + By₂) / 2 ^ (K - 1) =
          Bx₁ * (1 / 2 ^ (K - 1)) +
          By₂ * (1 / 2 ^ (K - 1)) := by ring
  simpa [this] using add_le_add h₁ h₂

lemma mul_equiv_same_index
    (x₁ x₂ y₁ y₂ : CReal.Pre) (K : ℕ) (hK : 0 < K)
    (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    |x₁.approx K * y₁.approx K - x₂.approx K * y₂.approx K| ≤
      (x₁.cBound + y₂.cBound : ℚ) / 2 ^ (K - 1) := by
  set Bx₁ : ℚ := (x₁.cBound : ℚ) with hBx₁
  set By₂ : ℚ := (y₂.cBound : ℚ) with hBy₂
  have hK_eq : K = (K - 1) + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have h_y_diff : |y₁.approx K - y₂.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    convert h_y (K - 1) using 2
    rw [hK_eq]; rw [Nat.add_succ_sub_one]
  have h_x_diff : |x₁.approx K - x₂.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    convert h_x (K - 1) using 2
    rw [hK_eq]; rw [Nat.add_succ_sub_one]
  have h_x_bound : |x₁.approx K| ≤ Bx₁ := by
    simpa [hBx₁] using x₁.abs_approx_le_cBound K
  have h_y_bound : |y₂.approx K| ≤ By₂ := by
    simpa [hBy₂] using y₂.abs_approx_le_cBound K
  have hBx_nonneg : (0 : ℚ) ≤ Bx₁ := by
    have : (0 : ℚ) ≤ (x₁.cBound : ℚ) := by exact_mod_cast (Nat.zero_le _)
    simp [hBx₁]
  have hBy_nonneg : (0 : ℚ) ≤ By₂ := by
    have : (0 : ℚ) ≤ (y₂.cBound : ℚ) := by exact_mod_cast (Nat.zero_le _)
    simp [hBy₂]
  have h_prod₁ := prod_diff_bound_left  Bx₁ h_x_bound h_y_diff
  have h_prod₂ := prod_diff_bound_right By₂ h_y_bound h_x_diff
  have := prod_diff_sum_bound (x₁:=x₁) (x₂:=x₂) (y₁:=y₁) (y₂:=y₂)
            h_prod₁ h_prod₂
  calc
    |x₁.approx K * y₁.approx K - x₂.approx K * y₂.approx K|
        = |x₁.approx K * (y₁.approx K - y₂.approx K) +
            y₂.approx K * (x₁.approx K - x₂.approx K)| := by ring_nf
    _ ≤ |x₁.approx K * (y₁.approx K - y₂.approx K)| +
        |y₂.approx K * (x₁.approx K - x₂.approx K)| :=
          abs_add_le _ _
    _ = |x₁.approx K| * |y₁.approx K - y₂.approx K| +
        |y₂.approx K| * |x₁.approx K - x₂.approx K| := by
          simp  [abs_mul]
    _ ≤ Bx₁ * (1 / 2 ^ (K - 1)) + By₂ * (1 / 2 ^ (K - 1)) := by
          linarith [h_prod₁, h_prod₂]
    _ = (Bx₁ + By₂) / 2 ^ (K - 1) := by
          rw [div_eq_mul_inv]; ring

lemma div_lt_iff {a b c : ℚ} (hb : 0 < b) : a / b < c ↔ a < c * b := by
  change a * b⁻¹ < c ↔ a < c * b
  rw [← mul_lt_mul_iff_left₀ hb]
  field_simp [hb.ne']

lemma div_le_div_of_le_of_nonneg {a _ c d : ℚ} (ha : 0 ≤ a) (hc : 0 < c) (_ : 0 < d) (h_le : c ≤ d) :
    a / d ≤ a / c := by
  gcongr

lemma lt_div_iff_mul_lt {a b c : ℚ} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv]
  exact lt_mul_inv_iff₀ hc

lemma div_lt_iff' {a b c : ℚ} (hc : 0 < c) : a / c < b ↔ a < b * c :=
  by exact div_lt_iff₀ hc

/-- Regularity bound :
for any indices `k_small ≤ k_big` we control
`|(x*y)ₖsmall  -  xₖbig * yₖbig|`. -/
lemma mul_regularity_bound
    (x y : CReal.Pre) {k_small k_big : ℕ} (h_le : k_small ≤ k_big) :
    |(x.mul y).approx k_small - (x.mul y).approx k_big|
      ≤ 1 / 2 ^ k_small := by
  dsimp [CReal.Pre.mul]
  set S := x.mulShift y
  let ks   := k_small + S
  let kbS  := k_big + S
  have h_le' : ks ≤ kbS := add_le_add_right h_le S
  have h_core :=
    product_diff_bound x y h_le' (x.cBound) (y.cBound)
      (x.abs_approx_le_cBound ks) (y.abs_approx_le_cBound kbS)
  have h_sum := x.sum_cBound_le_pow_mulShift y
  have : |x.approx ks * y.approx ks - x.approx kbS * y.approx kbS|
        ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) := by
    have h_pow_pos : 0 < (2 : ℚ) ^ ks := pow_pos (by norm_num) ks
    have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ ks := by
      have h1 : 0 ≤ (1 : ℚ) := by norm_num
      exact div_nonneg h1 (le_of_lt h_pow_pos)
    have h_mul : (x.cBound + y.cBound : ℚ) * (1 / 2 ^ ks)
             ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) :=
      mul_le_mul_of_nonneg_right h_sum h_nonneg
    exact h_core.trans h_mul
  simpa [ks, pow_add, mul_comm, mul_left_comm,
        mul_assoc, one_mul] using
    (calc
      |x.approx ks * y.approx ks - x.approx kbS * y.approx kbS|
          ≤ (2 ^ S : ℚ) * (1 / 2 ^ ks) := this
      _ = (1 : ℚ) / 2 ^ k_small := by
        dsimp [ks]; field_simp [pow_add]; ring)

/--  Equivalence (“middle”) bound at a *single* index `K`.  -/
alias mul_middle_bound := mul_equiv_same_index

/--  Given a positive ε, we can find an index `K` such that
`B / 2^(K-1) < ε`  -/
lemma mul_find_index
    {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, B / 2 ^ (K - 1) < ε := by
  rcases exists_pow_gt (div_pos hB hε) with ⟨K₀, hK₀⟩
  have h_step : B / 2 ^ K₀ < ε := by
    have h1 : B < ε * 2 ^ K₀ := by
      have : B / ε < 2 ^ K₀ := hK₀
      have := (div_lt_iff hε).1 this
      simpa [mul_comm] using this
    have h_pow_pos : (0 : ℚ) < 2 ^ K₀ := pow_pos (by norm_num) _
    have : B / 2 ^ K₀ < ε := (div_lt_iff h_pow_pos).2 h1
    simpa using this
  refine ⟨K₀ + 1, ?_⟩
  simpa [Nat.add_sub_cancel] using h_step

lemma div_le_div_of_le {a b c : ℚ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hc))

lemma Nat.le_add_of_le_right {a b n : ℕ} (h : a ≤ b) : a ≤ b + n :=
  le_add_right h

lemma Nat.le_add_right_of_le {a b n : ℕ} (h : a ≤ b) : a ≤ b + n :=
  Nat.le_trans h (Nat.le_add_right _ _)

/--  If the numerator is non–negative and the denominators are
positive with `c ≤ d`, then `a / d ≤ a / c`. -/
lemma div_le_div_of_le_left
    {a c d : ℚ} (ha : 0 ≤ a) (hc : 0 < c) (h_le : c ≤ d) :
    a / d ≤ a / c := by
  have hd : 0 < d := lt_of_lt_of_le hc h_le
  -- `1/d ≤ 1/c`
  have h_inv : (1 : ℚ) / d ≤ 1 / c := by exact one_div_le_one_div_of_le hc h_le
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h_inv ha

lemma div_le_div_of_le_right
    {a b c : ℚ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hc))

lemma abs_approx_diff_le
    (x : CReal.Pre) (i j : ℕ) :
    |x.approx i - x.approx j| ≤ (1 : ℚ) / 2 ^ (min i j) := by
  cases le_total i j with
  | inl h_le =>
      simpa [min_eq_left h_le] using x.is_regular i j h_le
  | inr h_le' =>
      have h_le : j ≤ i := h_le'
      have := x.is_regular j i h_le
      simpa [abs_sub_comm, min_eq_right h_le] using this

/-- 1.  Triangle–inequality + Cauchy estimates:
gives the bound with the *minimum* index in the denominator. -/
lemma mul_approx_bound_min
    (x y : CReal.Pre) {ks kb : ℕ} :
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb| ≤
      (x.cBound + y.cBound) * (1 / 2 ^ (min ks kb)) := by
  have h_x : |x.approx ks - x.approx kb| ≤ (1 : ℚ) / 2 ^ (min ks kb) :=
    abs_approx_diff_le x _ _
  have h_y : |y.approx ks - y.approx kb| ≤ (1 : ℚ) / 2 ^ (min ks kb) :=
    abs_approx_diff_le y _ _
  have hxB : |x.approx kb| ≤ x.cBound := x.abs_approx_le_cBound kb
  have hyB : |y.approx ks| ≤ y.cBound := y.abs_approx_le_cBound ks
  calc
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb|
      = |(x.approx ks - x.approx kb) * y.approx ks + x.approx kb * (y.approx ks - y.approx kb)| := by ring_nf
    _ ≤ |(x.approx ks - x.approx kb) * y.approx ks| + |x.approx kb * (y.approx ks - y.approx kb)| :=
      abs_add_le ((x.approx ks - x.approx kb) * y.approx ks) (x.approx kb * (y.approx ks - y.approx kb))
    _ = |x.approx ks - x.approx kb| * |y.approx ks| + |x.approx kb| * |y.approx ks - y.approx kb| := by simp [abs_mul]
    _ ≤ (1 / 2 ^ (min ks kb)) * |y.approx ks| + |x.approx kb| * (1 / 2 ^ (min ks kb)) := by
        gcongr
    _ ≤ (1 / 2 ^ (min ks kb)) * y.cBound + x.cBound * (1 / 2 ^ (min ks kb)) := by
        gcongr
    _ = (x.cBound + y.cBound) * (1 / 2 ^ (min ks kb)) := by ring

/-- 2.  Replace `1/2^{min ks kb}` by `1/2^{k_small}` when
      `k_small ≤ min ks kb`. -/
lemma one_div_pow_le_of_le_min
    {k_small ks kb : ℕ} (h : k_small ≤ min ks kb) :
    (1 : ℚ) / 2 ^ (min ks kb) ≤ 1 / 2 ^ k_small := by
  have : (2 : ℚ) ^ k_small ≤ 2 ^ (min ks kb) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) h
  have hp : 0 < (2 : ℚ) ^ k_small := pow_pos (by norm_num) _
  have hp' : 0 < (2 : ℚ) ^ (min ks kb) := pow_pos (by norm_num) _
  exact one_div_pow_le_one_div_pow_of_le rfl h

/-- 3.  Final wrapper: bound at `k_small`, then widen the numerator
      with the harmless `+ 1`. -/
lemma mul_approx_bound_k_small
    (x y : CReal.Pre) {k_small ks kb : ℕ} (h₁ : k_small ≤ min ks kb) :
    |x.approx ks * y.approx ks - x.approx kb * y.approx kb| ≤
      (x.cBound + y.cBound) / 2 ^ k_small := by
  have h_core := mul_approx_bound_min x y (ks := ks) (kb := kb)
  have h_pow := one_div_pow_le_of_le_min h₁
  have h_nonneg : (0 : ℚ) ≤ x.cBound + y.cBound := by
    have : (0 : ℚ) ≤ (x.cBound : ℚ) := by exact_mod_cast Nat.zero_le _
    have : (0 : ℚ) ≤ (y.cBound : ℚ) := by exact_mod_cast Nat.zero_le _
    linarith
  have : (x.cBound + y.cBound : ℚ) * (1 / 2 ^ (min ks kb))
        ≤ (x.cBound + y.cBound) * (1 / 2 ^ k_small) :=
    mul_le_mul_of_nonneg_left h_pow h_nonneg
  simpa [div_eq_mul_inv] using h_core.trans this

/-! Regularity of the product-/
lemma mul_approx_regularity
    (x y : CReal.Pre) {k_small k_big : ℕ} (h_le : k_small ≤ k_big) :
    |(x.mul y).approx k_small - x.approx k_big * y.approx k_big| ≤
      (x.cBound + y.cBound + 1) / 2 ^ k_small := by
  dsimp [CReal.Pre.mul]
  let S  := x.mulShift y
  let ks := k_small + S
  let kb := k_big
  have h_min : k_small ≤ min ks kb := by
    have : k_small ≤ ks := by
      dsimp [ks]; exact Nat.le_add_right _ _
    have : k_small ≤ kb := by
      dsimp [kb]; exact h_le
    exact le_min ‹_› ‹_›
  have h_core :=
    mul_approx_bound_k_small x y h_min
  have h_num : (x.cBound + y.cBound : ℚ) ≤ x.cBound + y.cBound + 1 := by linarith
  have h_final : (x.cBound + y.cBound : ℚ) / 2 ^ k_small
               ≤ (x.cBound + y.cBound + 1) / 2 ^ k_small := by
    apply div_le_div_of_le_right
    · exact pow_pos (by norm_num) k_small
    · exact h_num
  exact h_core.trans h_final

lemma abs_add_three (a b c : ℚ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| = |(a + b) + c| := by ring
    _ ≤ |a + b| + |c|           := abs_add_le (a + b) c
    _ ≤ |a| + |b| + |c|         := by
      have h₁ : |a + b| ≤ |a| + |b| := abs_add_le a b
      linarith

/-- Given a positive ε, we can find an index `K` such that `B / 2^(K-1) < ε`. -/
lemma mul_find_index'
    {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ B / 2 ^ (K - 1) < ε := by
  rcases exists_pow_gt (div_pos hB hε) with ⟨K₀, hK₀⟩
  have h_step : B / 2 ^ K₀ < ε := by
    have h1 : B < ε * 2 ^ K₀ := by
      have := (div_lt_iff hε).1 hK₀
      simpa [mul_comm] using this
    have h_pow_pos : (0 : ℚ) < 2 ^ K₀ := pow_pos (by norm_num) K₀
    exact (div_lt_iff h_pow_pos).2 h1
  refine ⟨K₀ + 1, Nat.succ_pos _, ?_⟩
  simpa [Nat.add_sub_cancel] using h_step

open CReal.Pre

/--
Multiplication respects equivalence.
-/
theorem mul_respects_equiv {x₁ x₂ y₁ y₂ : CReal.Pre}
    (h_x : CReal.Pre.Equiv x₁ x₂) (h_y : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (x₁.mul y₁) (x₂.mul y₂) := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  let Bx₁ := (x₁.cBound : ℚ); let By₁ := (y₁.cBound : ℚ)
  let Bx₂ := (x₂.cBound : ℚ); let By₂ := (y₂.cBound : ℚ)
  let B_mid : ℚ := Bx₁ + By₂
  let B_tails : ℚ := max (Bx₁ + By₁) (Bx₂ + By₂)
  have hB_mid_pos : 0 < B_mid := by
    dsimp [B_mid, Bx₁, By₂]
    apply add_pos <;> (exact_mod_cast cBound_pos _)
  have hB_tails_pos : 0 < B_tails := by
    dsimp [B_tails, Bx₁, By₁, Bx₂, By₂]
    apply lt_max_of_lt_left
    apply add_pos <;> (exact_mod_cast cBound_pos _)
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨K₁, hK₁_pos, hK₁_bound⟩ := mul_find_index' hB_mid_pos hε3
  obtain ⟨K₂, hK₂⟩ := exists_pow_gt (div_pos hB_tails_pos hε3)
  have hK₂_bound' : B_tails / (2^K₂) < ε/3 := by
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    rw [mul_comm]; exact (div_lt_iff' hε3).mp hK₂
  let K := max K₁ K₂
  let k := n + 1
  let A := (x₁.mul y₁).approx k          -- (x₁y₁)ₖ
  let D := (x₂.mul y₂).approx k          -- (x₂y₂)ₖ
  let B_bridge := x₁.approx K * y₁.approx K  -- x₁ₖy₁ₖ
  let C_bridge := x₂.approx K * y₂.approx K  -- x₂ₖy₂ₖ
  have h_tri : |A - D| ≤ |A - B_bridge| + |B_bridge - C_bridge| + |C_bridge - D| := by
    calc |A - D| = |(A - B_bridge) + (B_bridge - C_bridge) + (C_bridge - D)| := by ring_nf
               _ ≤ _ := abs_add_three _ _ _
  have h_term2 : |B_bridge - C_bridge| < ε / 3 := by
    have hK_pos : 0 < K := Nat.lt_of_lt_of_le hK₁_pos (le_max_left _ _)
    have h_mid := mul_equiv_same_index x₁ x₂ y₁ y₂ K hK_pos h_x h_y
    have h_K_le : K₁ - 1 ≤ K - 1 := Nat.sub_le_sub_right (le_max_left K₁ K₂) 1
    have h_pow_le : (2:ℚ)^(K₁-1) ≤ (2:ℚ)^(K-1) := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
    have h_bound_K : B_mid / 2^(K-1) ≤ B_mid / 2^(K₁-1) := by
      apply div_le_div_of_le_left (le_of_lt hB_mid_pos) (pow_pos (by norm_num) _) h_pow_le
    calc |B_bridge - C_bridge| ≤ B_mid / 2^(K-1) := h_mid
      _ ≤ B_mid / 2^(K₁-1) := h_bound_K
      _ < ε / 3 := hK₁_bound
  have h_term1 : |A - B_bridge| ≤ 1/2^k + ε/3 := by
    let S₁ := x₁.mulShift y₁
    let Bxy₁ := Bx₁ + By₁
    have h_near : |A - B_bridge| ≤ Bxy₁ * (1 / 2^(min (k+S₁) K)) := by
      dsimp [A, B_bridge, CReal.Pre.mul]
      simpa [Bxy₁, Bx₁, By₁] using
        (mul_approx_bound_min x₁ y₁ (ks := k + S₁) (kb := K))
    cases le_or_gt (k+S₁) K with
    | inl h_le =>
      have h_min_eq : min (k+S₁) K = k+S₁ := min_eq_left h_le
      rw [h_min_eq] at h_near
      have h_S_bound : Bxy₁ ≤ 2^S₁ := x₁.sum_cBound_le_pow_mulShift y₁
      have h_case1 := calc |A - B_bridge| ≤ Bxy₁ * (1 / 2^(k+S₁)) := h_near
        _ ≤ 2^S₁ * (1 / 2^(k+S₁)) := mul_le_mul_of_nonneg_right h_S_bound (by positivity)
        _ = 1/2^k := by rw [pow_add]; field_simp [pow_ne_zero]
      have h_eps_nonneg : 0 ≤ ε / 3 := (le_of_lt hε3)
      have h_lift : (1 : ℚ) / 2 ^ k ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simpa [add_comm] using add_le_add_left h_eps_nonneg ((1 : ℚ) / 2 ^ k)
      exact le_trans h_case1 h_lift
    | inr h_lt =>
      have h_min_eq : min (k+S₁) K = K := min_eq_right (le_of_lt h_lt)
      rw [h_min_eq] at h_near
      have h_B_le : Bxy₁ ≤ B_tails := le_max_left _ _
      have h_K_le : K₂ ≤ K := le_max_right _ _
      have h_pow_le : (2:ℚ)^K₂ ≤ (2:ℚ)^K := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
      have h_bound_K : B_tails / 2^K ≤ B_tails / 2^K₂ := by
        apply div_le_div_of_le_left (le_of_lt hB_tails_pos) (pow_pos (by norm_num) _) h_pow_le
      have h_case2 := calc |A - B_bridge| ≤ Bxy₁ / 2^K := by simpa using h_near
        _ ≤ B_tails / 2^K := div_le_div_of_le_right (pow_pos (by norm_num) _) h_B_le
        _ ≤ B_tails / 2^K₂ := h_bound_K
        _ < ε/3 := hK₂_bound'
      have h_pos_div : 0 ≤ (1 : ℚ) / 2 ^ k := by
        have hpow : 0 < (2 : ℚ) ^ k := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hpow)
      have h_eps_mono : ε / 3 ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simp
      exact le_trans h_case2.le h_eps_mono
  have h_term3 : |C_bridge - D| ≤ 1/2^k + ε/3 := by
    rw [abs_sub_comm]
    let S₂ := x₂.mulShift y₂
    let Bxy₂ := Bx₂ + By₂
    have h_near : |D - C_bridge| ≤ Bxy₂ * (1 / 2^(min (k+S₂) K)) := by
       dsimp [D, C_bridge, CReal.Pre.mul]
       simpa [Bxy₂, Bx₂, By₂] using
         (mul_approx_bound_min x₂ y₂ (ks := k + S₂) (kb := K))
    cases le_or_gt (k+S₂) K with
    | inl h_le =>
      have h_min_eq : min (k+S₂) K = k+S₂ := min_eq_left h_le
      rw [h_min_eq] at h_near
      have h_S_bound : Bxy₂ ≤ 2^S₂ := x₂.sum_cBound_le_pow_mulShift y₂
      have h_case1 := calc |D - C_bridge| ≤ Bxy₂ * (1 / 2^(k+S₂)) := h_near
        _ ≤ 2^S₂ * (1 / 2^(k+S₂)) := mul_le_mul_of_nonneg_right h_S_bound (by positivity)
        _ = 1/2^k := by rw [pow_add]; field_simp [pow_ne_zero]
      have h_eps_nonneg : 0 ≤ ε / 3 := (le_of_lt hε3)
      have h_lift : (1 : ℚ) / 2 ^ k ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simpa [add_comm] using add_le_add_left h_eps_nonneg ((1 : ℚ) / 2 ^ k)
      exact le_trans h_case1 h_lift
    | inr h_lt =>
      have h_min_eq : min (k+S₂) K = K := min_eq_right (le_of_lt h_lt)
      rw [h_min_eq] at h_near
      have h_B_le : Bxy₂ ≤ B_tails := le_max_right _ _
      have h_K_le : K₂ ≤ K := le_max_right _ _
      have h_pow_le : (2:ℚ)^K₂ ≤ (2:ℚ)^K := (pow_le_pow_iff_right₀ rfl).mpr h_K_le
      have h_bound_K : B_tails / 2^K ≤ B_tails / 2^K₂ := by
        apply div_le_div_of_le_left (le_of_lt hB_tails_pos) (pow_pos (by norm_num) _) h_pow_le
      have h_case2 := calc |D - C_bridge| ≤ Bxy₂ / 2^K := by simpa using h_near
        _ ≤ B_tails / 2^K := div_le_div_of_le_right (pow_pos (by norm_num) _) h_B_le
        _ ≤ B_tails / 2^K₂ := h_bound_K
        _ < ε/3 := hK₂_bound'
      have h_pos_div : 0 ≤ (1 : ℚ) / 2 ^ k := by
        have hpow : 0 < (2 : ℚ) ^ k := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hpow)
      have h_eps_mono : ε / 3 ≤ (1 : ℚ) / 2 ^ k + ε / 3 := by
        simp
      exact le_trans h_case2.le h_eps_mono
  have h_final := calc |A - D| ≤ |A - B_bridge| + |B_bridge - C_bridge| + |C_bridge - D| := h_tri
    _ ≤ (1/2^k + ε/3) + ε/3 + (1/2^k + ε/3) := by linarith [h_term1, h_term2.le, h_term3]
    _ = 1/2^(k-1) + ε := by
      have h_eps : (ε/3) + ε/3 + ε/3 = ε := by ring
      have h_pow : (1 : ℚ) / 2 ^ k + 1 / 2 ^ k = 1 / 2 ^ (k - 1) := by
        have h₁ : (1 : ℚ) / 2 ^ k + 1 / 2 ^ k = (2 : ℚ) / 2 ^ k := by
          field_simp; ring
        have hk : 0 < k := by
          have : 1 ≤ k := by
            dsimp [k]; exact Nat.succ_le_succ (Nat.zero_le n)
          exact this
        have h₂ : (2 : ℚ) / 2 ^ k = 1 / 2 ^ (k - 1) := by
          have hk' : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk).symm
          field_simp [hk', pow_succ]
          exact Eq.symm (pow_succ' 2 n)
        rw [h₁, h₂]
      rw [← h_pow, ← h_eps]
      ring
    _ = 1/2^n + ε := by simp [k]
  exact h_final

/-- The product of two computable real numbers. -/
instance : Mul CReal := by
  refine ⟨Quotient.map₂ Pre.mul ?_⟩
  intro x₁ x₂ hx y₁ y₂ hy
  exact mul_respects_equiv hx hy

@[simp] theorem mul_def (x y : CReal.Pre) : (⟦x⟧ : CReal) * ⟦y⟧ = ⟦x.mul y⟧ := rfl

lemma add_assoc_diff_rewrite
    (x y z : CReal.Pre) (n : ℕ) :
  |(x.approx (n + 3) + y.approx (n + 3) + z.approx (n + 2)) -
    (x.approx (n + 2) + y.approx (n + 3) + z.approx (n + 3))|
    =
  |(x.approx (n + 3) - x.approx (n + 2)) +
    (z.approx (n + 2) - z.approx (n + 3))| := by
  ring_nf

lemma adjacent_reg (w : CReal.Pre) (n : ℕ) :
  |w.approx (n + 3) - w.approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
  rw [abs_sub_comm]
  exact w.is_regular (n + 2) (n + 3) (Nat.le_succ _)

lemma two_halves_to_succ (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 2) + (1 : ℚ) / 2 ^ (n + 2) = (1 : ℚ) / 2 ^ (n + 1) := by
  field_simp [pow_succ]
  ring

-- A convenient subtraction form derived from two_halves_to_succ.
lemma two_halves_to_succ_sub (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) - (1 : ℚ) / 2 ^ (n + 2) = (1 : ℚ) / 2 ^ (n + 2) := by
  have h := two_halves_to_succ n
  calc
    (1 : ℚ) / 2 ^ (n + 1) - (1 : ℚ) / 2 ^ (n + 2)
        = ((1 : ℚ) / 2 ^ (n + 2) + (1 : ℚ) / 2 ^ (n + 2)) - (1 : ℚ) / 2 ^ (n + 2) := by
            simp_all only [one_div]
    _ = (1 : ℚ) / 2 ^ (n + 2) := by ring

lemma inv_pow_antitone_succ (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ n := by
  apply one_div_le_one_div_of_le
  · exact pow_pos (by norm_num) n
  · exact (pow_le_pow_iff_right₀ rfl).mpr (Nat.le_succ n)

theorem add_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv ((x.add y).add z) (x.add (y.add z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add]
  have h_rewrite := add_assoc_diff_rewrite x y z n
  have hx := adjacent_reg x n
  have hz := by
    rw [abs_sub_comm] at hx
    exact (adjacent_reg z n)
  calc
    |x.approx (n + 1 + 1 + 1) + y.approx (n + 1 + 1 + 1) + z.approx (n + 1 + 1) -
      (x.approx (n + 1 + 1) + (y.approx (n + 1 + 1 + 1) + z.approx (n + 1 + 1 + 1)))|
        = |(x.approx (n + 3) - x.approx (n + 2)) +
            (z.approx (n + 2) - z.approx (n + 3))| := by
          simp only [add_assoc]; ring_nf
    _ ≤ |x.approx (n + 3) - x.approx (n + 2)| +
        |z.approx (n + 2) - z.approx (n + 3)| := abs_add_le _ _
    _ ≤ (1 : ℚ) / 2 ^ (n + 2) + (1 : ℚ) / 2 ^ (n + 2) := add_le_add (adjacent_reg x n) (by
          simpa [abs_sub_comm] using (adjacent_reg z n))
    _ = (1 : ℚ) / 2 ^ (n + 1) := two_halves_to_succ n
    _ ≤ (1 : ℚ) / 2 ^ n := inv_pow_antitone_succ n

theorem add_comm_pre (x y : CReal.Pre) : CReal.Pre.Equiv (x.add y) (y.add x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add]
  ring_nf; simp

lemma adjacent_reg_succ (x : CReal.Pre) (n : ℕ) :
  |x.approx (n + 2) - x.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
  rw [abs_sub_comm]
  exact x.is_regular (n + 1) (n + 2) (Nat.le_succ _)

theorem zero_add_pre (x : CReal.Pre) : CReal.Pre.Equiv (CReal.Pre.zero.add x) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.zero]
  simp only [zero_add]
  exact (adjacent_reg_succ x n).trans (inv_pow_antitone_succ n)

theorem add_zero_pre (x : CReal.Pre) : CReal.Pre.Equiv (x.add CReal.Pre.zero) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.zero]
  simp only [add_zero]
  exact (adjacent_reg_succ x n).trans (inv_pow_antitone_succ n)

theorem add_left_neg_pre (x : CReal.Pre) : CReal.Pre.Equiv (x.neg.add x) CReal.Pre.zero := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.add, CReal.Pre.neg, CReal.Pre.zero]
  simp only [neg_add_cancel, sub_zero, abs_zero]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  exact div_nonneg (by norm_num) (le_of_lt hpow)

open Rat

instance : AddCommGroup CReal where
  add := (· + ·)
  add_assoc := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    simpa [add_def] using Quot.sound (add_assoc_pre x y z)
  zero := (0 : CReal)
  zero_add := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (zero_add_pre x)
  add_zero := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (add_zero_pre x)
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  neg := Neg.neg
  sub := fun a b => a + (-b)
  sub_eq_add_neg := by intros; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  neg_add_cancel := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [add_def] using Quot.sound (add_left_neg_pre x)
  add_comm := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    simpa [add_def] using Quot.sound (add_comm_pre x y)

/-- The `CReal.Pre` representation of `1`. -/
protected def Pre.one : CReal.Pre where
  approx := fun _ ↦ 1
  is_regular := by intro n m _; simp

theorem mul_comm_pre (x y : CReal.Pre) : CReal.Pre.Equiv (x.mul y) (y.mul x) := by
  have h_shift : x.mulShift y = y.mulShift x := by
    dsimp [CReal.Pre.mulShift]; rw [max_comm]
  intro n
  dsimp [CReal.Pre.mul, CReal.Pre.Equiv]
  rw [h_shift, mul_comm]
  simp

lemma approx_regular_step (x : CReal.Pre) (i j : ℕ) (hij : i ≤ j) :
  |x.approx j - x.approx i| ≤ (1 : ℚ) / 2 ^ i := by
  rw [abs_sub_comm]
  exact x.is_regular i j hij

theorem one_mul_pre (x : CReal.Pre) : CReal.Pre.Equiv (CReal.Pre.one.mul x) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.mul, CReal.Pre.one]
  let S := CReal.Pre.one.mulShift x
  have h_le : n + 1 ≤ n + 1 + S := Nat.le_add_right _ _
  have h_step :
      |x.approx (n + 1 + S) - x.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n + 1) :=
    approx_regular_step x (n + 1) (n + 1 + S) h_le
  calc
    |1 * x.approx (n + 1 + S) - x.approx (n + 1)|
        = |x.approx (n + 1 + S) - x.approx (n + 1)| := by simp [one_mul]
    _ ≤ (1 : ℚ) / 2 ^ (n + 1) := h_step
    _ ≤ (1 : ℚ) / 2 ^ n := inv_pow_antitone_succ n

/-! ### Associativity of Multiplication -/

open Rat

/--
**Ternary Product Estimate**. Bounds the difference between two ternary products at different indices.
|aₙbₙcₙ - aₘbₘcₘ| ≤ (Ba*Bc + Bb*Bc + Ba*Bb) * (1 / 2 ^ n) for n ≤ m.
-/
lemma ternary_product_diff_bound
    (a b c : CReal.Pre) {kₙ kₘ : ℕ} (h_le : kₙ ≤ kₘ) :
    |a.approx kₙ * b.approx kₙ * c.approx kₙ - a.approx kₘ * b.approx kₘ * c.approx kₘ| ≤
      (a.cBound*c.cBound + b.cBound*c.cBound + a.cBound*b.cBound : ℚ) * (1 / 2 ^ kₙ) := by
  let Ba : ℚ := a.cBound; let Bb : ℚ := b.cBound; let Bc : ℚ := c.cBound
  have h_ab_diff : |a.approx kₙ * b.approx kₙ - a.approx kₘ * b.approx kₘ| ≤ (Ba + Bb) * (1 / 2 ^ kₙ) :=
    product_diff_bound a b h_le Ba Bb (a.abs_approx_le_cBound kₙ) (b.abs_approx_le_cBound kₘ)
  have h_creg : |c.approx kₙ - c.approx kₘ| ≤ (1 : ℚ) / 2 ^ kₙ := c.is_regular kₙ kₘ h_le
  calc
    |a.approx kₙ * b.approx kₙ * c.approx kₙ - a.approx kₘ * b.approx kₘ * c.approx kₘ|
      = |(a.approx kₙ * b.approx kₙ - a.approx kₘ * b.approx kₘ) * c.approx kₙ +
         (a.approx kₘ * b.approx kₘ) * (c.approx kₙ - c.approx kₘ)| := by ring_nf
    _ ≤ |a.approx kₙ * b.approx kₙ - a.approx kₘ * b.approx kₘ| * |c.approx kₙ| +
         |a.approx kₘ * b.approx kₘ| * |c.approx kₙ - c.approx kₘ| := by
          rw [← abs_mul, ← abs_mul]; exact
            abs_add_le ((a.approx kₙ * b.approx kₙ - a.approx kₘ * b.approx kₘ) * c.approx kₙ)
              (a.approx kₘ * b.approx kₘ * (c.approx kₙ - c.approx kₘ))
    _ ≤ ((Ba + Bb) * (1 / 2 ^ kₙ)) * Bc + (Ba * Bb) * (1 / 2 ^ kₙ) := by
      have h_c_bound : |c.approx kₙ| ≤ Bc := by simpa using c.abs_approx_le_cBound kₙ
      have h_c_nonneg : (0 : ℚ) ≤ |c.approx kₙ| := abs_nonneg _
      have h_factor_nonneg : (0 : ℚ) ≤ (Ba + Bb) * (1 / 2 ^ kₙ) := by
        have hBa : (0 : ℚ) ≤ Ba := natCast_nonneg
        have hBb : (0 : ℚ) ≤ Bb := natCast_nonneg
        have hpow : 0 < (2 : ℚ) ^ kₙ := pow_pos (by norm_num) _
        have hdiv : (0 : ℚ) ≤ 1 / 2 ^ kₙ := le_of_lt (div_pos (by norm_num) hpow)
        exact mul_nonneg (add_nonneg hBa hBb) hdiv
      have term1 :
          |a.approx kₙ * b.approx kₙ - a.approx kₘ * b.approx kₘ| * |c.approx kₙ|
          ≤ ((Ba + Bb) * (1 / 2 ^ kₙ)) * Bc := by
        have h := mul_le_mul_of_nonneg_right h_ab_diff h_c_nonneg
        have h' := h.trans (mul_le_mul_of_nonneg_left h_c_bound h_factor_nonneg)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
      have ha : |a.approx kₘ| ≤ Ba := by simpa using a.abs_approx_le_cBound kₘ
      have hb : |b.approx kₘ| ≤ Bb := by simpa using b.abs_approx_le_cBound kₘ
      have hBa_nonneg : (0 : ℚ) ≤ Ba := natCast_nonneg
      have hBb_nonneg : (0 : ℚ) ≤ Bb := natCast_nonneg
      have h_absb_nonneg : (0 : ℚ) ≤ |b.approx kₘ| := abs_nonneg _
      have h_abkm : |a.approx kₘ * b.approx kₘ| ≤ Ba * Bb := by
        have h1 : |a.approx kₘ| * |b.approx kₘ| ≤ Ba * |b.approx kₘ| :=
          mul_le_mul_of_nonneg_right ha h_absb_nonneg
        have h2 : Ba * |b.approx kₘ| ≤ Ba * Bb :=
          mul_le_mul_of_nonneg_left hb hBa_nonneg
        have h12 := h1.trans h2
        simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h12
      have h_creg_nonneg : (0 : ℚ) ≤ |c.approx kₙ - c.approx kₘ| := abs_nonneg _
      have h_BaBb_nonneg : (0 : ℚ) ≤ Ba * Bb := mul_nonneg hBa_nonneg hBb_nonneg
      have term2 :
          |a.approx kₘ * b.approx kₘ| * |c.approx kₙ - c.approx kₘ|
          ≤ (Ba * Bb) * (1 / 2 ^ kₙ) := by
        have h := mul_le_mul_of_nonneg_right h_abkm h_creg_nonneg
        have h' := h.trans (mul_le_mul_of_nonneg_left h_creg h_BaBb_nonneg)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
      exact add_le_add term1 term2
    _ = (Ba*Bc + Bb*Bc + Ba*Bb) * (1 / 2 ^ kₙ) := by ring_nf

/--
Provides a bound on the difference between the two ways of associating a product.
|((a*b)*c)ₖ - (a*(b*c))ₖ| ≤ B_assoc / 2ᵏ.
-/
lemma mul_assoc_bound (a b c : CReal.Pre) (k : ℕ) :
  |((a.mul b).mul c).approx k - (a.mul (b.mul c)).approx k| ≤
    (c.cBound * (a.cBound + b.cBound) + a.cBound * (b.cBound + c.cBound) +
    (a.cBound*c.cBound + b.cBound*c.cBound + a.cBound*b.cBound) : ℚ) / 2^k := by
  let Ba : ℚ := a.cBound; let Bb : ℚ := b.cBound; let Bc : ℚ := c.cBound
  let B_ternary : ℚ := Ba*Bc + Bb*Bc + Ba*Bb
  let P1 := (a.mul b).mul c; let P2 := a.mul (b.mul c)
  let S1 := (a.mul b).mulShift c; let S2 := a.mulShift (b.mul c)
  let K1 := k + S1; let K2 := k + S2
  have h_diff1 : |P1.approx k - a.approx K1 * b.approx K1 * c.approx K1| ≤ Bc * (Ba+Bb) / 2^K1 := by
    dsimp [P1, CReal.Pre.mul]
    have h_ab_diff : |(a.mul b).approx K1 - a.approx K1 * b.approx K1| ≤ (Ba+Bb) / 2^K1 := by
      dsimp [CReal.Pre.mul]
      let Sab := a.mulShift b; let K_ab := K1 + Sab
      have h_le : K1 ≤ K_ab := Nat.le_add_right _ _
      rw [abs_sub_comm]
      have h_core := product_diff_bound a b h_le Ba Bb (a.abs_approx_le_cBound K1) (b.abs_approx_le_cBound K_ab)
      exact (le_trans h_core (by simp only [one_div]; exact Rat.le_refl))
    calc
      |(a.mul b).approx K1 * c.approx K1 - a.approx K1 * b.approx K1 * c.approx K1|
          = |((a.mul b).approx K1 - a.approx K1 * b.approx K1) * c.approx K1| := by ring_nf
      _ = |(a.mul b).approx K1 - a.approx K1 * b.approx K1| * |c.approx K1| := by simp [abs_mul]
      _ ≤ ((Ba + Bb) / 2 ^ K1) * |c.approx K1| := by
          exact mul_le_mul_of_nonneg_right h_ab_diff (abs_nonneg _)
      _ ≤ ((Ba + Bb) / 2 ^ K1) * Bc := by
          have h_nonneg : 0 ≤ (Ba + Bb) / 2 ^ K1 := by
            have hBa : 0 ≤ Ba := natCast_nonneg
            have hBb : 0 ≤ Bb := natCast_nonneg
            have hden : 0 ≤ (2 : ℚ) ^ K1 := by
              have : (0 : ℚ) ≤ 2 := by norm_num
              exact pow_nonneg this _
            exact div_nonneg (add_nonneg hBa hBb) hden
          exact mul_le_mul_of_nonneg_left (c.abs_approx_le_cBound K1) h_nonneg
      _ = Bc * (Ba + Bb) / 2 ^ K1 := by simp [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  have h_diff2 : |P2.approx k - a.approx K2 * b.approx K2 * c.approx K2| ≤ Ba * (Bb+Bc) / 2^K2 := by
    dsimp [P2, CReal.Pre.mul]
    let Sbc := b.mulShift c
    have hP2 :
      a.approx (k + S2) * (b.mul c).approx (k + S2)
        = a.approx K2 * (b.approx (K2 + Sbc) * c.approx (K2 + Sbc)) := by
      dsimp [K2, S2]
      dsimp [CReal.Pre.mul]
    have h_goal_form :
      |a.approx (k + S2) * (b.mul c).approx (k + S2) - a.approx K2 * b.approx K2 * c.approx K2|
        =
      |a.approx K2 * (b.approx (K2 + Sbc) * c.approx (K2 + Sbc))
          - a.approx K2 * (b.approx K2 * c.approx K2)| := by
      simp [hP2, K2, mul_assoc]
    have h_rw :
      a.approx K2 * (b.approx (K2 + Sbc) * c.approx (K2 + Sbc)) -
        a.approx K2 * (b.approx K2 * c.approx K2)
        = a.approx K2 * ((b.approx (K2 + Sbc) * c.approx (K2 + Sbc)) - (b.approx K2 * c.approx K2)) := by
      ring_nf
    have h_bc_core :
      |(b.approx (K2 + Sbc) * c.approx (K2 + Sbc)) - (b.approx K2 * c.approx K2)| ≤
        (Bb + Bc) * (1 / 2 ^ K2) := by
      have h_le : K2 ≤ K2 + Sbc := Nat.le_add_right _ _
      have h := product_diff_bound b c h_le (Bb) (Bc)
                  (b.abs_approx_le_cBound K2) (c.abs_approx_le_cBound (K2 + Sbc))
      simpa [abs_sub_comm, mul_comm, mul_left_comm, mul_assoc] using h
    have h_nonneg : 0 ≤ |a.approx K2| := abs_nonneg _
    have h_main :
      |a.approx K2 * (b.approx (K2 + Sbc) * c.approx (K2 + Sbc)) -
        a.approx K2 * (b.approx K2 * c.approx K2)|
        ≤ |a.approx K2| * ((Bb + Bc) * (1 / 2 ^ K2)) := by
      simpa [h_rw, abs_mul, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left h_bc_core h_nonneg)
    have hM_nonneg : (0 : ℚ) ≤ (Bb + Bc) * (1 / 2 ^ K2) := by
      have hb : (0 : ℚ) ≤ Bb := natCast_nonneg
      have hc : (0 : ℚ) ≤ Bc := natCast_nonneg
      have hpow : 0 < (2 : ℚ) ^ K2 := pow_pos (by norm_num) _
      have hdiv : (0 : ℚ) ≤ 1 / 2 ^ K2 := le_of_lt (div_pos (by norm_num) hpow)
      exact mul_nonneg (add_nonneg hb hc) hdiv
    have h_a_bound : |a.approx K2| ≤ Ba := a.abs_approx_le_cBound K2
    have h_bound := mul_le_mul_of_nonneg_right h_a_bound hM_nonneg
    have h_bound' : |a.approx K2| * ((Bb + Bc) * (1 / 2 ^ K2)) ≤ Ba * (Bb + Bc) / 2 ^ K2 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_bound
    calc
      |P2.approx k - a.approx K2 * b.approx K2 * c.approx K2|
          = |a.approx (k + S2) * (b.mul c).approx (k + S2) - a.approx K2 * b.approx K2 * c.approx K2| := by
              rfl
      _ = |a.approx K2 * (b.approx (K2 + Sbc) * c.approx (K2 + Sbc))
              - a.approx K2 * (b.approx K2 * c.approx K2)| := h_goal_form
      _ ≤ |a.approx K2| * ((Bb + Bc) * (1 / 2 ^ K2)) := h_main
      _ ≤ Ba * (Bb + Bc) / 2 ^ K2 := h_bound'
  have h_diff_ternary :
      |a.approx K1 * b.approx K1 * c.approx K1 - a.approx K2 * b.approx K2 * c.approx K2|
        ≤ B_ternary / 2^(min K1 K2) := by
    cases le_total K1 K2 with
    | inl h_le =>
        rw [min_eq_left h_le]
        have h_core := ternary_product_diff_bound a b c h_le
        exact (le_trans h_core (by 
          simp_all only [add_le_add_iff_left, one_div, P1, K1, S1, Bc, Ba, Bb, P2, K2, S2, B_ternary]
          rfl))
    | inr h_le =>
        rw [min_eq_right h_le, abs_sub_comm]
        have h_core := ternary_product_diff_bound a b c h_le
        exact (le_trans h_core (by 
          simp_all only [add_le_add_iff_left, one_div, P1, K1, S1, Bc, Ba, Bb, P2, K2, S2, B_ternary]
          rfl))
  have h_K1_ge_k : k ≤ K1 := Nat.le_add_right k S1
  have h_K2_ge_k : k ≤ K2 := Nat.le_add_right k S2
  have h_minK_ge_k : k ≤ min K1 K2 := le_min h_K1_ge_k h_K2_ge_k
  have h_bound1_weak : Bc * (Ba+Bb) / 2^K1 ≤ Bc * (Ba+Bb) / 2^k := by
    apply div_le_div_of_le_left (by positivity) (by positivity)
    exact (pow_le_pow_iff_right₀ rfl).mpr h_K1_ge_k
  have h_bound2_weak : B_ternary / 2^(min K1 K2) ≤ B_ternary / 2^k := by
    apply div_le_div_of_le_left (by positivity) (by positivity)
    exact (pow_le_pow_iff_right₀ rfl).mpr h_minK_ge_k
  have h_bound3_weak : Ba * (Bb+Bc) / 2^K2 ≤ Ba * (Bb+Bc) / 2^k := by
    apply div_le_div_of_le_left (by positivity) (by positivity)
    exact (pow_le_pow_iff_right₀ rfl).mpr h_K2_ge_k
  calc
    |P1.approx k - P2.approx k|
      ≤ |P1.approx k - a.approx K1 * b.approx K1 * c.approx K1|
        + |a.approx K1 * b.approx K1 * c.approx K1
            - a.approx K2 * b.approx K2 * c.approx K2|
        + |a.approx K2 * b.approx K2 * c.approx K2 - P2.approx k| := by
          have : P1.approx k - P2.approx k =
            (P1.approx k - a.approx K1 * b.approx K1 * c.approx K1)
              + (a.approx K1 * b.approx K1 * c.approx K1
                  - a.approx K2 * b.approx K2 * c.approx K2)
              + (a.approx K2 * b.approx K2 * c.approx K2 - P2.approx k) := by ring_nf
          simp_rw [this]
          exact
            abs_add_three (P1.approx k - a.approx K1 * b.approx K1 * c.approx K1)
              (a.approx K1 * b.approx K1 * c.approx K1 - a.approx K2 * b.approx K2 * c.approx K2)
              (a.approx K2 * b.approx K2 * c.approx K2 - P2.approx k)
    _ ≤ Bc*(Ba+Bb)/2^K1 + B_ternary/2^(min K1 K2) + Ba*(Bb+Bc)/2^K2 := by
      have := abs_sub_comm (a.approx K2 * b.approx K2 * c.approx K2) (P2.approx k)
      gcongr
      simp_all only [Nat.add_min_add_left, le_add_iff_nonneg_right, zero_le, le_inf_iff, and_self, P1, K1, S1, Bc, Ba,
        Bb, P2, K2, S2, B_ternary]
    _ ≤ Bc*(Ba+Bb)/2^k + B_ternary/2^k + Ba*(Bb+Bc)/2^k := by
      gcongr
    _ = (Bc*(Ba+Bb) + Ba*(Bb+Bc) + B_ternary) / 2^k := by
      field_simp [div_eq_mul_inv]; ring
    _ = (c.cBound * (a.cBound + b.cBound) + a.cBound * (b.cBound + c.cBound) +
          (a.cBound*c.cBound + b.cBound*c.cBound + a.cBound*b.cBound) : ℚ) / 2^k := by
      simp [B_ternary, Ba, Bb, Bc, mul_add, add_comm, add_left_comm, add_assoc]

theorem mul_assoc_pre (a b c : CReal.Pre) :
    CReal.Pre.Equiv ((a.mul b).mul c) (a.mul (b.mul c)) := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  let P1 := (a.mul b).mul c
  let P2 := a.mul (b.mul c)
  let Ba : ℚ := a.cBound; let Bb : ℚ := b.cBound; let Bc : ℚ := c.cBound
  let B_target : ℚ := (Bc * (Ba+Bb) + Ba * (Bb+Bc) + (Ba*Bc + Bb*Bc + Ba*Bb))
  have hB_target_pos : 0 < B_target := by
    have hBa_pos : 0 < Ba := by
      have : (0 : ℚ) < (a.cBound : ℚ) := by exact_mod_cast (cBound_pos a)
      simpa [Ba] using this
    have hBb_pos : 0 < Bb := by
      have : (0 : ℚ) < (b.cBound : ℚ) := by exact_mod_cast (cBound_pos b)
      simpa [Bb] using this
    have hBc_pos : 0 < Bc := by
      have : (0 : ℚ) < (c.cBound : ℚ) := by exact_mod_cast (cBound_pos c)
      simpa [Bc] using this
    have h1 : 0 < Bc * (Ba + Bb) := mul_pos hBc_pos (add_pos hBa_pos hBb_pos)
    have h2 : 0 < Ba * (Bb + Bc) := mul_pos hBa_pos (add_pos hBb_pos hBc_pos)
    have h3 : 0 < Ba * Bc := mul_pos hBa_pos hBc_pos
    have h4 : 0 < Bb * Bc := mul_pos hBb_pos hBc_pos
    have h5 : 0 < Ba * Bb := mul_pos hBa_pos hBb_pos
    have hsum12 : 0 < Bc * (Ba + Bb) + Ba * (Bb + Bc) := add_pos h1 h2
    have hsum3 : 0 < Ba * Bc + Bb * Bc + Ba * Bb := by
      have h12 : 0 < Ba * Bc + Bb * Bc := add_pos h3 h4
      exact add_pos h12 h5
    simpa [B_target] using add_pos hsum12 hsum3
  rcases exists_pow_gt (div_pos hB_target_pos hε) with ⟨m, hK₀⟩
  have hm_bound : B_target / 2 ^ m < ε := by
    have h1 : B_target < ε * 2 ^ m := (Rat.div_lt_iff' hε).mp hK₀
    have hpow : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
    exact (div_lt_iff hpow).2 (by simpa [mul_comm] using h1)
  let m_idx := max (n + 1) m
  have h_n_le_midx : n + 1 ≤ m_idx := le_max_left _ _
  have h_m_le_midx : m ≤ m_idx := le_max_right _ _
  have h_mid_lt_eps : |P1.approx m_idx - P2.approx m_idx| < ε := by
    have h_bound := mul_assoc_bound a b c m_idx
    have h_pow_bound : B_target / 2^m_idx ≤ B_target / 2^m := by
      apply div_le_div_of_le_left (le_of_lt hB_target_pos) (by positivity)
      exact (pow_le_pow_iff_right₀ rfl).mpr h_m_le_midx
    calc
      |P1.approx m_idx - P2.approx m_idx| ≤ B_target / 2^m_idx := h_bound
      _ ≤ B_target / 2^m := h_pow_bound
      _ < ε := hm_bound
  have h_reg1 : |P1.approx (n+1) - P1.approx m_idx| ≤ 1 / 2^(n+1) :=
    P1.is_regular (n+1) m_idx h_n_le_midx
  have h_reg3 : |P2.approx m_idx - P2.approx (n+1)| ≤ 1 / 2^(n+1) := by
    rw [abs_sub_comm]; exact P2.is_regular (n+1) m_idx h_n_le_midx
  calc
    |P1.approx (n+1) - P2.approx (n+1)|
      ≤ |P1.approx (n+1) - P1.approx m_idx| + |P1.approx m_idx - P2.approx m_idx| + |P2.approx m_idx - P2.approx (n+1)| := by
        have h_eq :
          P1.approx (n + 1) - P2.approx (n + 1)
            = (P1.approx (n + 1) - P1.approx m_idx)
              + (P1.approx m_idx - P2.approx m_idx)
              + (P2.approx m_idx - P2.approx (n + 1)) := by
          ring
        have h := abs_add_three
          (P1.approx (n + 1) - P1.approx m_idx)
          (P1.approx m_idx - P2.approx m_idx)
          (P2.approx m_idx - P2.approx (n + 1))
        simp_all only [le_sup_left, le_sup_right, one_div, sub_add_sub_cancel, B_target, Bc, Ba, Bb, m_idx, P1, P2]
    _ ≤ 1/2^(n+1) + ε + 1/2^(n+1) := by
        gcongr
    _ = 1/2^n + ε := by
        have h_add : (1:ℚ)/2^(n+1) + (1:ℚ)/2^(n+1) = (1:ℚ)/2^n := by
          field_simp [pow_succ]; ring
        ring_nf

lemma two_halves_to_pred (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) = (1 : ℚ) / 2 ^ n := by
  have : (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) = (2 : ℚ) / 2 ^ (n + 1) := by ring
  have hpow : (2 : ℚ) ^ (n + 1) = (2 : ℚ) ^ n * 2 := by
    simp [pow_succ, mul_comm]
  calc
    (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1)
        = (2 : ℚ) / 2 ^ (n + 1) := this
    _ = (2 : ℚ) / ((2 : ℚ) ^ n * 2) := by simp [hpow]
    _ = ((2 : ℚ) / 2) / (2 : ℚ) ^ n := by field_simp
    _ = (1 : ℚ) / 2 ^ n := by simp

/--
Proof that multiplication distributes over addition: x*(y+z) ≈ (x*y)+(x*z).
We use the synchronization method, which elegantly avoids epsilon-delta arguments by
aligning the indices such that the errors cancel out due to the definitions of the shifts.
-/
theorem left_distrib_pre (x y z : CReal.Pre) :
  CReal.Pre.Equiv (x.mul (y.add z)) ((x.mul y).add (x.mul z)) := by
  intro n
  let Bx : ℚ := x.cBound; let By : ℚ := y.cBound; let Bz : ℚ := z.cBound
  let A := y.add z -- A = y+z
  let Ba : ℚ := A.cBound
  let L := x.mul A -- LHS: x*(y+z)
  let Ry := x.mul y; let Rz := x.mul z
  let R := Ry.add Rz -- RHS: (x*y)+(x*z)
  let Sy := x.mulShift y; let Sz := x.mulShift z; let Sl := x.mulShift A
  let Ky := n + 2 + Sy
  let Kz := n + 2 + Sz
  let Kl := n + 1 + Sl
  let K := max (max Ky Kz) (Kl + 1)
  let T := x.approx K * y.approx K + x.approx K * z.approx K
  have hKy_le_K : Ky ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKz_le_K : Kz ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKl_lt_K : Kl < K := lt_of_lt_of_le (Nat.lt_succ_self Kl) (le_max_right _ _)
  have hKl1_le_K : Kl + 1 ≤ K := le_max_right _ _
  have h_R_diff : |R.approx (n+1) - T| ≤ 1 / 2^(n+1) := by
    dsimp [R, CReal.Pre.add, Ry, Rz, CReal.Pre.mul]
    have h_near_y :
        |x.approx Ky * y.approx Ky - x.approx K * y.approx K|
        ≤ (Bx + By) * (1 / 2 ^ Ky) := by
      simpa [Bx, By, min_eq_left hKy_le_K] using
        (mul_approx_bound_min x y (ks := Ky) (kb := K))
    have h_near_z :
        |x.approx Kz * z.approx Kz - x.approx K * z.approx K|
        ≤ (Bx + Bz) * (1 / 2 ^ Kz) := by
      simpa [Bx, Bz, min_eq_left hKz_le_K] using
        (mul_approx_bound_min x z (ks := Kz) (kb := K))
    have h_Sy_prop : (Bx + By) ≤ 2^Sy := CReal.Pre.sum_cBound_le_pow_mulShift x y
    have h_Sz_prop : (Bx + Bz) ≤ 2^Sz := CReal.Pre.sum_cBound_le_pow_mulShift x z
    have h_div_y_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Ky := by
      have hpow : 0 < (2 : ℚ) ^ Ky := pow_pos (by norm_num) _
      exact div_nonneg (by norm_num) (le_of_lt hpow)
    have h_div_z_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kz := by
      have hpow : 0 < (2 : ℚ) ^ Kz := pow_pos (by norm_num) _
      exact div_nonneg (by norm_num) (le_of_lt hpow)
    calc
      |(x.approx Ky * y.approx Ky + x.approx Kz * z.approx Kz) - T|
        = |(x.approx Ky * y.approx Ky - x.approx K * y.approx K) +
            (x.approx Kz * z.approx Kz - x.approx K * z.approx K)| := by
              dsimp [T]; ring_nf
      _ ≤ |x.approx Ky * y.approx Ky - x.approx K * y.approx K| +
          |x.approx Kz * z.approx Kz - x.approx K * z.approx K| := by
            exact
              abs_add_le (x.approx Ky * y.approx Ky - x.approx K * y.approx K)
                (x.approx Kz * z.approx Kz - x.approx K * z.approx K)
      _ ≤ (Bx + By) * (1/2^Ky) + (Bx + Bz) * (1/2^Kz) := add_le_add h_near_y h_near_z
      _ ≤ 2^Sy * (1/2^Ky) + 2^Sz * (1/2^Kz) := by
        have hY := mul_le_mul_of_nonneg_right h_Sy_prop h_div_y_nonneg
        have hZ := mul_le_mul_of_nonneg_right h_Sz_prop h_div_z_nonneg
        exact add_le_add hY hZ
      _ = 1/2^(n+2) + 1/2^(n+2) := by
        dsimp [Ky, Kz]; simp [pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = 1/2^(n+1) := two_halves_to_succ n
  have h_L_diff : |L.approx (n+1) - T| ≤ 1 / 2^(n+1) := by
    dsimp [L, CReal.Pre.mul, A, CReal.Pre.add]
    have h_T_eq : T = x.approx K * (y.approx K + z.approx K) := by dsimp [T]; ring
    let P1 := x.approx Kl * (y.approx (Kl+1) + z.approx (Kl+1))
    let P_mid := x.approx K * (y.approx (Kl+1) + z.approx (Kl+1))
    have h_term1 : |P1 - P_mid| ≤ (1/2^Kl) * Ba := by
      rw [← sub_mul, abs_mul]
      have hx : |x.approx Kl - x.approx K| ≤ (1 : ℚ) / 2 ^ Kl :=
        x.is_regular Kl K (le_of_lt hKl_lt_K)
      have hA : |y.approx (Kl+1) + z.approx (Kl+1)| ≤ Ba := by
        have := A.abs_approx_le_cBound Kl
        simpa [CReal.Pre.add] using this
      have hx' : |x.approx Kl - x.approx K| ≤ 1 / 2 ^ Kl := hx
      have hA_nonneg : 0 ≤ Ba := by
        have : (0 : ℚ) ≤ (A.cBound : ℚ) := by exact_mod_cast (Nat.zero_le _)
        simp [Ba]
      have hmul :=
        mul_le_mul_of_nonneg_right
          hx' (abs_nonneg (y.approx (Kl+1) + z.approx (Kl+1)))
      have h_div_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kl := by
        have hp : 0 < (2 : ℚ) ^ Kl := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hp)
      have hbound := hmul.trans (mul_le_mul_of_nonneg_left hA h_div_nonneg)
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, Ba] using hbound
    have h_term2 : |P_mid - T| ≤ Bx * (1/2^Kl) := by
      rw [h_T_eq, ← mul_sub, abs_mul]
      have hxB : |x.approx K| ≤ Bx := x.abs_approx_le_cBound K
      have hxB_nonneg : 0 ≤ Bx := le_trans (abs_nonneg _) hxB
      have hy : |y.approx (Kl+1) - y.approx K| ≤ 1 / 2 ^ (Kl+1) :=
        y.is_regular (Kl+1) K hKl1_le_K
      have hz : |z.approx (Kl+1) - z.approx K| ≤ 1 / 2 ^ (Kl+1) :=
        z.is_regular (Kl+1) K hKl1_le_K
      have h_sum : |(y.approx (Kl+1) - y.approx K) + (z.approx (Kl+1) - z.approx K)|
                   ≤ 1/2^(Kl+1) + 1/2^(Kl+1) := by
        have := abs_add_le (y.approx (Kl + 1) - y.approx K) (z.approx (Kl + 1) - z.approx K)
        exact this.trans (add_le_add hy hz)
      have h_sum' : |(y.approx (Kl+1) + z.approx (Kl+1)) - (y.approx K + z.approx K)|
                    ≤ 1/2^(Kl+1) + 1/2^(Kl+1) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_sum
      have h_sum'' : |(y.approx (Kl+1) + z.approx (Kl+1)) - (y.approx K + z.approx K)|
                    ≤ 1/2^Kl := by
        simpa using (le_trans h_sum' (by
          have := two_halves_to_pred Kl
          simpa using this.le))
      have hx_mul :
          |x.approx K| * |(y.approx (Kl+1) + z.approx (Kl+1)) - (y.approx K + z.approx K)|
          ≤ |x.approx K| * (1 / 2 ^ Kl) :=
        mul_le_mul_of_nonneg_left h_sum'' (abs_nonneg (x.approx K))
      have hden_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kl := by
        have hp : 0 < (2 : ℚ) ^ Kl := pow_pos (by norm_num) _
        exact le_of_lt (div_pos (by norm_num) hp)
      have hx_mul' :
          |x.approx K| * (1 / 2 ^ Kl) ≤ Bx * (1 / 2 ^ Kl) :=
        mul_le_mul_of_nonneg_right hxB hden_nonneg
      exact le_trans hx_mul hx_mul'
    have h_Sl_prop : (Bx + Ba) ≤ 2^Sl := CReal.Pre.sum_cBound_le_pow_mulShift x A
    calc |P1 - T| ≤ |P1 - P_mid| + |P_mid - T| := by apply abs_sub_le
         _ ≤ (1/2^Kl) * Ba + Bx * (1/2^Kl) := add_le_add h_term1 h_term2
         _ = (Ba + Bx) * (1/2^Kl) := by ring
         _ ≤ 2^Sl * (1/2^Kl) := by
           have hdiv_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kl := by
             have hp : 0 < (2 : ℚ) ^ Kl := pow_pos (by norm_num) _
             exact div_nonneg (by norm_num) (le_of_lt hp)
           have h_sum_le : (Ba + Bx : ℚ) ≤ 2 ^ Sl := by
             simpa [add_comm] using h_Sl_prop
           exact mul_le_mul_of_nonneg_right h_sum_le hdiv_nonneg
         _ = 1/2^(n+1) := by
           dsimp [Kl]; simp [pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  calc
    |L.approx (n+1) - R.approx (n+1)|
      ≤ |L.approx (n+1) - T| + |T - R.approx (n+1)| := by apply abs_sub_le
    _ ≤ 1/2^(n+1) + 1/2^(n+1) := by
        have h_R_diff' : |T - R.approx (n + 1)| ≤ 1 / 2 ^ (n + 1) := by
          simpa [abs_sub_comm] using h_R_diff
        exact add_le_add h_L_diff h_R_diff'
    _ = 1/2^n := two_halves_to_pred n

theorem zero_mul_pre (x : CReal.Pre) :
  CReal.Pre.Equiv (CReal.Pre.zero.mul x) CReal.Pre.zero := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.mul, CReal.Pre.zero]
  simp only [zero_mul, sub_zero, abs_zero]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  exact div_nonneg (by norm_num) (le_of_lt hpow)

theorem mul_zero_pre (x : CReal.Pre) :
  CReal.Pre.Equiv (x.mul CReal.Pre.zero) CReal.Pre.zero := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.mul, CReal.Pre.zero]
  simp only [mul_zero, sub_zero, abs_zero]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  exact div_nonneg (by norm_num) (le_of_lt hpow)

instance : CommRing CReal where
  add := (· + ·)
  add_assoc := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    simpa [add_def] using Quot.sound (add_assoc_pre x y z)
  zero := (0 : CReal)
  zero_add := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simp
  add_zero := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simp
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  neg := Neg.neg
  sub := fun a b => a + (-b)
  sub_eq_add_neg := by intros; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  add_comm := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    simpa [add_def] using Quot.sound (add_comm_pre x y)
  neg_add_cancel := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simp
  mul := (· * ·)
  one := ⟦CReal.Pre.one⟧
  mul_assoc := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    simpa [mul_def] using Quot.sound (mul_assoc_pre x y z)
  one_mul := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [mul_def] using Quot.sound (one_mul_pre x)
  mul_one := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [mul_def] using
      Quot.sound (CReal.Pre.equiv_trans (mul_comm_pre x CReal.Pre.one) (one_mul_pre x))
  left_distrib := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    simpa [add_def, mul_def] using Quot.sound (left_distrib_pre x y z)
  right_distrib := by
    intro a b c
    refine Quot.induction_on₃ a b c (fun x y z => ?_)
    have h₁ := mul_comm_pre (CReal.Pre.add x y) z
    have h₂ := left_distrib_pre z x y
    have h₃ := add_respects_equiv (mul_comm_pre z x) (mul_comm_pre z y)
    simpa [add_def, mul_def] using
      Quot.sound (CReal.Pre.equiv_trans h₁ (CReal.Pre.equiv_trans h₂ h₃))
  mul_comm := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    simpa [mul_def] using Quot.sound (mul_comm_pre x y)
  zero_mul := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [mul_def] using Quot.sound (zero_mul_pre x)
  mul_zero := by
    intro a
    refine Quot.induction_on a (fun x => ?_)
    simpa [mul_def] using Quot.sound (mul_zero_pre x)

/-! ### Order Structure -/

/--
Definition of the order relation on CReal.Pre (Constructive Definition).
x ≤ y if ∀ n, x_{n+1} ≤ y_{n+1} + 1/2ⁿ.
-/
protected def Pre.le (x y : CReal.Pre) : Prop :=
  ∀ n : ℕ, x.approx (n + 1) ≤ y.approx (n + 1) + (1 : ℚ) / 2 ^ n

-- Helper for Epsilon-Delta arguments.
lemma find_index_for_bound {B ε : ℚ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℕ, B / 2 ^ K < ε := by
  rcases exists_pow_gt (div_pos hB hε) with ⟨K, hK⟩
  have h_step : B / 2 ^ K < ε := by
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    rw [mul_comm]; apply (div_lt_iff hε).mp hK
  exact ⟨K, h_step⟩

-- Reusable small algebra lemmas for combining fractions with equal denominators.
lemma one_plus_two_over_pow (t : ℕ) :
  (1 : ℚ) / 2 ^ t + 2 / 2 ^ t = 3 / 2 ^ t := by
  ring

lemma sum_two_halves (n : ℕ) :
  (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) = 2 / 2 ^ (n + 1) := by
  ring

lemma le_well_defined_forward
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂)
    (h_le : CReal.Pre.le x₁ y₁) : CReal.Pre.le x₂ y₂ := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm_bound⟩ := find_index_for_bound (by norm_num : 0 < (3 : ℚ)) hε
  let k := max (n+1) (m+1)
  have h_n_le_k : n+1 ≤ k := le_max_left _ _
  have h_m_le_k : m+1 ≤ k := le_max_right _ _
  have h_k_sub_1_ge_m : m ≤ k-1 := Nat.le_sub_of_add_le h_m_le_k
  have hkpos : 1 ≤ k := le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have h_error_bound : 3 / 2^(k-1) < ε := by
    have h_pow_bound : (2:ℚ)^m ≤ 2^(k-1) :=
      (pow_le_pow_iff_right₀ rfl).mpr h_k_sub_1_ge_m
    have h_div_le : (3:ℚ) / 2^(k-1) ≤ 3 / 2^m := by
      have hc : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
      exact div_le_div_of_le_left (by norm_num) hc h_pow_bound
    linarith [hm_bound]
  have h_hyp0 := h_le (k-1)
  have h_hyp : x₁.approx k ≤ y₁.approx k + 1 / 2^(k-1) := by
    simpa [hk1] using h_hyp0
  have hx_equiv := hx (k-1)
  have hy_equiv := hy (k-1)
  have hx_reg : |x₂.approx (n+1) - x₂.approx k| ≤ 1/2^(n+1) :=
    x₂.is_regular (n+1) k h_n_le_k
  have hy_reg : |y₂.approx (n+1) - y₂.approx k| ≤ 1/2^(n+1) :=
    y₂.is_regular (n+1) k h_n_le_k
  have h1 : x₂.approx (n+1) ≤ x₂.approx k + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h2 : x₂.approx k ≤ x₁.approx k + 1/2^(k-1) := by
    have h := (abs_sub_le_iff).1 hx_equiv
    have h' : x₂.approx k - x₁.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.right
    have : x₂.approx k ≤ (1 / 2 ^ (k - 1)) + x₁.approx k :=
      (sub_le_iff_le_add).1 h'
    simpa [add_comm] using this
  have h4 : y₁.approx k ≤ y₂.approx k + 1/2 ^ (k - 1) := by
    have h := (abs_sub_le_iff).1 hy_equiv
    have h' : y₁.approx k - y₂.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.left
    linarith
  have h5 : y₂.approx k ≤ y₂.approx (n+1) + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hy_reg
    linarith [h.right]
  have h_mid : x₂.approx k ≤ y₁.approx k + 2 / 2^(k-1) := by
    calc
      x₂.approx k ≤ x₁.approx k + 1/2^(k-1) := h2
      _ ≤ (y₁.approx k + 1/2^(k-1)) + 1/2^(k-1) := by
            exact add_le_add_right h_hyp _
      _ = y₁.approx k + (1/2^(k-1) + 1/2^(k-1)) := by ring_nf
      _ = y₁.approx k + 2 / 2^(k-1) := by ring_nf
  have h_mid' : x₂.approx k ≤ y₂.approx k + 3 / 2^(k-1) := by
    have step : y₁.approx k + 2 / 2^(k-1)
                ≤ y₂.approx k + (1/2^(k-1) + 2 / 2^(k-1)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h4 (2 / 2^(k-1))
    have : y₁.approx k + 2 / 2^(k-1)
          ≤ y₂.approx k + 3 / 2^(k-1) := by
      rw [one_plus_two_over_pow (k - 1)] at step
      exact step
    exact le_trans h_mid this
  have h_le_to_k :
      x₂.approx (n+1) ≤ y₂.approx k + 1/2^(n+1) + 3 / 2^(k-1) := by
    have step := add_le_add_right h_mid' (1 / 2^(n+1))
    exact le_trans h1 (by simpa [add_comm, add_left_comm, add_assoc] using step)
  have h_to_target :
      y₂.approx k + 1/2^(n+1) + 3 / 2^(k-1)
        ≤ y₂.approx (n+1) + 2/2^(n+1) + 3 / 2^(k-1) := by
    have step1 : y₂.approx k + 1/2^(n+1)
                 ≤ y₂.approx (n+1) + 1/2^(n+1) + 1/2^(n+1) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h5 (1 / 2^(n+1))
    have step1a : y₂.approx k + 1/2^(n+1)
                 ≤ y₂.approx (n+1) + 2/2^(n+1) := by
      have h_two_halves : 1/2^(n+1) + 1/2^(n+1) = (2:ℚ)/2^(n+1) := by ring
      rw [add_assoc] at step1
      rw [h_two_halves] at step1
      exact step1
    exact add_le_add_right step1a (3 / 2^(k-1))
  have h_two : (2 : ℚ) / 2^(n+1) = (1 : ℚ) / 2^n := by
    field_simp [pow_succ]; ring
  calc
    x₂.approx (n+1)
        ≤ y₂.approx (n+1) + 2/2^(n+1) + 3/2^(k-1) := by
          exact (le_trans h_le_to_k h_to_target)
    _ = y₂.approx (n+1) + 1/2^n + 3/2^(k-1) := by
          simp [h_two]
    _ ≤ y₂.approx (n+1) + 1/2^n + ε := by
          have h_err_le : 3 / 2^(k-1) ≤ ε := le_of_lt h_error_bound
          linarith

lemma le_well_defined_backward
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂)
    (h_le : CReal.Pre.le x₂ y₂) : CReal.Pre.le x₁ y₁ := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm_bound⟩ := find_index_for_bound (by norm_num : 0 < (3 : ℚ)) hε
  let k := max (n+1) (m+1)
  have h_n_le_k : n+1 ≤ k := le_max_left _ _
  have h_m_le_k : m+1 ≤ k := le_max_right _ _
  have h_k_sub_1_ge_m : m ≤ k-1 := Nat.le_sub_of_add_le h_m_le_k
  have hkpos : 1 ≤ k := le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have h_error_bound : 3 / 2^(k-1) < ε := by
    have h_pow_bound : (2:ℚ)^m ≤ 2^(k-1) :=
      (pow_le_pow_iff_right₀ rfl).mpr h_k_sub_1_ge_m
    have h_div_le : (3:ℚ) / 2^(k-1) ≤ 3 / 2^m := by
      have hc : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
      exact div_le_div_of_le_left (by norm_num) hc h_pow_bound
    linarith [hm_bound]
  have h_hyp0 := h_le (k-1)
  have h_hyp : x₂.approx k ≤ y₂.approx k + 1 / 2^(k-1) := by
    simpa [hk1] using h_hyp0
  have hx_equiv := hx (k-1)
  have hy_equiv := hy (k-1)
  have hx_reg : |x₁.approx (n+1) - x₁.approx k| ≤ 1/2^(n+1) :=
    x₁.is_regular (n+1) k h_n_le_k
  have hy_reg : |y₁.approx (n+1) - y₁.approx k| ≤ 1/2^(n+1) :=
    y₁.is_regular (n+1) k h_n_le_k
  have h1 : x₁.approx (n+1) ≤ x₁.approx k + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h2 : x₁.approx k ≤ x₂.approx k + 1/2^(k-1) := by
    have h := (abs_sub_le_iff).1 hx_equiv
    have h' : x₁.approx k - x₂.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.left
    linarith
  have h4 : y₂.approx k ≤ y₁.approx k + 1/2^(k-1) := by
    have h := (abs_sub_le_iff).1 hy_equiv
    have h' : y₂.approx k - y₁.approx k ≤ 1 / 2 ^ (k - 1) := by
      simpa [hk1] using h.right
    linarith
  have h5 : y₁.approx k ≤ y₁.approx (n+1) + 1/2^(n+1) := by
    have h := (abs_sub_le_iff).1 hy_reg
    linarith [h.left]
  have h_mid : x₁.approx k ≤ y₂.approx k + 2 / 2^(k-1) := by
    calc
      x₁.approx k ≤ x₂.approx k + 1/2^(k-1) := h2
      _ ≤ (y₂.approx k + 1/2^(k-1)) + 1/2^(k-1) := by
            exact add_le_add_right h_hyp _
      _ = y₂.approx k + (1/2^(k-1) + 1/2^(k-1)) := by ring
      _ = y₂.approx k + 2 / 2^(k-1) := by ring
  have h_mid' : x₁.approx k ≤ y₁.approx k + 3 / 2^(k-1) := by
    calc
      x₁.approx k ≤ y₂.approx k + 2 / 2^(k-1) := h_mid
      _ ≤ y₁.approx k + 1/2^(k-1) + 2 / 2^(k-1) := add_le_add_right h4 _
      _ = y₁.approx k + 3 / 2^(k-1) := by field_simp; ring
  have h_le_to_k :
      x₁.approx (n+1) ≤ y₁.approx k + 1/2^(n+1) + 3 / 2^(k-1) := by
    have step := add_le_add_right h_mid' (1 / 2^(n+1))
    exact le_trans h1 (by simpa [add_comm, add_left_comm, add_assoc] using step)
  have h_to_target :
      y₁.approx k + 1/2^(n+1) + 3 / 2^(k-1)
        ≤ y₁.approx (n+1) + 2/2^(n+1) + 3 / 2^(k-1) := by
    have step1 : y₁.approx k + 1/2^(n+1)
                 ≤ y₁.approx (n+1) + 1/2^(n+1) + 1/2^(n+1) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right h5 (1 / 2^(n+1))
    have step2 := add_le_add_right step1 (3 / 2^(k-1))
    have h_rhs : y₁.approx (n+1) + 1/2^(n+1) + 1/2^(n+1) + 3 / 2^(k-1) = y₁.approx (n+1) + 2/2^(n+1) + 3 / 2^(k-1) := by ring
    linarith
  have h_two : (2 : ℚ) / 2^(n+1) = (1 : ℚ) / 2^n := by
    field_simp [pow_succ]; ring
  calc
    x₁.approx (n+1)
        ≤ y₁.approx (n+1) + 2/2^(n+1) + 3/2^(k-1) := by
          exact (le_trans h_le_to_k h_to_target)
    _ = y₁.approx (n+1) + 1/2^n + 3/2^(k-1) := by
          simp [h_two]
    _ ≤ y₁.approx (n+1) + 1/2^n + ε := by
          have h_err_le : 3 / 2^(k-1) ≤ ε := le_of_lt h_error_bound
          linarith

/--
The order relation respects equivalence.
This requires an epsilon-delta argument as direct index synchronization accumulates excessive error.
-/
theorem le_well_defined
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    Pre.le x₁ y₁ ↔ Pre.le x₂ y₂ := by
  constructor
  · intro h; exact le_well_defined_forward hx hy h
  · intro h; exact le_well_defined_backward hx hy h

instance : LE CReal := ⟨Quotient.lift₂ Pre.le (fun _ _ _ _ hx hy => propext (le_well_defined hx hy))⟩

/-! ### Proving the Partial Order Axioms -/

theorem le_refl (x : CReal) : x ≤ x := by
  induction x using Quotient.inductionOn
  intro n; simp

theorem le_trans (x y z : CReal) : x ≤ y → y ≤ z → x ≤ z := by
  refine Quot.induction_on₃ x y z (fun x y z => ?_)
  intro hxy hyz n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hm_bound⟩ := find_index_for_bound (by norm_num : 0 < (2 : ℚ)) hε
  let k := max (n + 1) (m + 1)
  have h_n_le_k : n + 1 ≤ k := le_max_left _ _
  have h_m_le_k : m + 1 ≤ k := le_max_right _ _
  have h_k_sub_1_ge_m : m ≤ k - 1 := Nat.le_sub_of_add_le h_m_le_k
  have h_error_bound : 2 / 2 ^ (k - 1) < ε := by
    have h_pow_bound : (2 : ℚ) ^ m ≤ 2 ^ (k - 1) :=
      (pow_le_pow_iff_right₀ rfl).mpr h_k_sub_1_ge_m
    have h_div_le : (2 : ℚ) / 2 ^ (k - 1) ≤ 2 / 2 ^ m := by
      have hc : 0 < (2 : ℚ) ^ m := pow_pos (by norm_num) m
      exact div_le_div_of_le_left (by norm_num) hc h_pow_bound
    linarith [hm_bound]
  have h_xy_hyp : x.approx k ≤ y.approx k + 1 / 2 ^ (k - 1) := by
    have h_k_ge_1 : 1 ≤ k := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
    simpa [Nat.sub_add_cancel h_k_ge_1] using hxy (k - 1)
  have h_yz_hyp : y.approx k ≤ z.approx k + 1 / 2 ^ (k - 1) := by
    have h_k_ge_1 : 1 ≤ k := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_n_le_k
    simpa [Nat.sub_add_cancel h_k_ge_1] using hyz (k - 1)
  have hx_reg : |x.approx (n + 1) - x.approx k| ≤ 1 / 2 ^ (n + 1) :=
    x.is_regular (n + 1) k h_n_le_k
  have hz_reg : |z.approx (n + 1) - z.approx k| ≤ 1 / 2 ^ (n + 1) :=
    z.is_regular (n + 1) k h_n_le_k
  have h1 : x.approx (n + 1) ≤ x.approx k + 1 / 2 ^ (n + 1) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h4 : z.approx k ≤ z.approx (n + 1) + 1 / 2 ^ (n + 1) := by
    have h := (abs_sub_le_iff).1 hz_reg
    linarith [h.right]
  have h_chain :
      x.approx (n + 1) ≤ z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := by
    calc
      x.approx (n + 1)
        ≤ x.approx k + 1 / 2 ^ (n + 1) := h1
      _ ≤ (y.approx k + 1 / 2 ^ (k - 1)) + 1 / 2 ^ (n + 1) := by gcongr
      _ ≤ (z.approx k + 1 / 2 ^ (k - 1) + 1 / 2 ^ (k - 1)) + 1 / 2 ^ (n + 1) := by gcongr
      _ = z.approx k + 2 / 2 ^ (k - 1) + 1 / 2 ^ (n + 1) := by ring_nf
      _ ≤ (z.approx (n + 1) + 1 / 2 ^ (n + 1)) + 2 / 2 ^ (k - 1) + 1 / 2 ^ (n + 1) := by gcongr
      _ = z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := by ring_nf
  have h_two : (2 : ℚ) / 2 ^ (n + 1) = (1 : ℚ) / 2 ^ n := by
    field_simp [pow_succ]; ring
  calc
    x.approx (n + 1)
        ≤ z.approx (n + 1) + 2 / 2 ^ (n + 1) + 2 / 2 ^ (k - 1) := h_chain
    _ = z.approx (n + 1) + 1 / 2 ^ n + 2 / 2 ^ (k - 1) := by simp [h_two]
    _ ≤ z.approx (n + 1) + 1 / 2 ^ n + ε := by
          have : 2 / 2 ^ (k - 1) ≤ ε := le_of_lt h_error_bound
          linarith

theorem le_antisymm (x y : CReal) : x ≤ y → y ≤ x → x = y := by
  refine Quot.induction_on₂ x y (fun x y => ?_)
  intro hxy hyx
  apply Quot.sound
  intro n
  have h_upper : x.approx (n + 1) - y.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n := by
    have hx' : x.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n + y.approx (n + 1) := by
      simpa [add_comm] using (hxy n)
    exact (sub_le_iff_le_add).mpr hx'
  have h_lower : -(1 / 2 ^ n : ℚ) ≤ x.approx (n + 1) - y.approx (n + 1) := by
    have hy' : y.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n + x.approx (n + 1) := by
      simpa [add_comm] using (hyx n)
    have hy_sub : y.approx (n + 1) - x.approx (n + 1) ≤ (1 : ℚ) / 2 ^ n := by simp_all
    have := neg_le_neg hy_sub
    simpa [sub_eq_add_neg] using this
  exact (abs_le.mpr ⟨h_lower, h_upper⟩)

instance : PartialOrder CReal where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

/-! ### Lattice Structure (Max/Min) -/

/-- Maximum of two CReal.Pre. The pointwise definition preserves regularity. -/
protected def Pre.max (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ max (x.approx n) (y.approx n)
  is_regular := by
    intro n m h_le
    have h_max_diff :
        |max (x.approx n) (y.approx n) - max (x.approx m) (y.approx m)|
        ≤ max |x.approx n - x.approx m| |y.approx n - y.approx m| :=
      abs_max_sub_max_le_max (x.approx n) (y.approx n) (x.approx m) (y.approx m)
    have hx := x.is_regular n m h_le
    have hy := y.is_regular n m h_le
    have h_max_to_target :
        max |x.approx n - x.approx m| |y.approx n - y.approx m| ≤ (1 : ℚ) / 2 ^ n :=
      (max_le_iff).2 ⟨hx, hy⟩
    exact _root_.le_trans h_max_diff h_max_to_target

/-- Max respects the equivalence relation. -/
theorem Pre.max_respects_equiv
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.max x₁ y₁) (CReal.Pre.max x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have h_max_diff :
      |max (x₁.approx (n+1)) (y₁.approx (n+1)) -
        max (x₂.approx (n+1)) (y₂.approx (n+1))|
      ≤ max |x₁.approx (n+1) - x₂.approx (n+1)|
            |y₁.approx (n+1) - y₂.approx (n+1)| :=
    abs_max_sub_max_le_max _ _ _ _
  have h_to_target :
      max |x₁.approx (n+1) - x₂.approx (n+1)|
          |y₁.approx (n+1) - y₂.approx (n+1)|
      ≤ (1 : ℚ) / 2 ^ n :=
    (max_le_iff).2 ⟨hx n, hy n⟩
  exact _root_.le_trans h_max_diff h_to_target

/-- Minimum of two CReal.Pre. -/
protected def Pre.min (x y : CReal.Pre) : CReal.Pre where
  approx := fun n ↦ min (x.approx n) (y.approx n)
  is_regular := by
    intro n m h_le
    have h_min_diff :
        |min (x.approx n) (y.approx n) - min (x.approx m) (y.approx m)|
        ≤ max |x.approx n - x.approx m| |y.approx n - y.approx m| :=
      abs_min_sub_min_le_max (x.approx n) (y.approx n) (x.approx m) (y.approx m)
    have hx := x.is_regular n m h_le
    have hy := y.is_regular n m h_le
    have h_max_to_target :
        max |x.approx n - x.approx m| |y.approx n - y.approx m| ≤ (1 : ℚ) / 2 ^ n :=
      (max_le_iff).2 ⟨hx, hy⟩
    exact _root_.le_trans h_min_diff h_max_to_target

/-- Min respects the equivalence relation. -/
theorem Pre.min_respects_equiv
    {x₁ x₂ y₁ y₂ : CReal.Pre}
    (hx : CReal.Pre.Equiv x₁ x₂) (hy : CReal.Pre.Equiv y₁ y₂) :
    CReal.Pre.Equiv (CReal.Pre.min x₁ y₁) (CReal.Pre.min x₂ y₂) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have h_min_diff :
      |min (x₁.approx (n+1)) (y₁.approx (n+1)) -
        min (x₂.approx (n+1)) (y₂.approx (n+1))|
      ≤ max |x₁.approx (n+1) - x₂.approx (n+1)|
            |y₁.approx (n+1) - y₂.approx (n+1)| :=
    abs_min_sub_min_le_max _ _ _ _
  have h_to_target :
      max |x₁.approx (n+1) - x₂.approx (n+1)|
          |y₁.approx (n+1) - y₂.approx (n+1)|
      ≤ (1 : ℚ) / 2 ^ n :=
    (max_le_iff).2 ⟨hx n, hy n⟩
  exact _root_.le_trans h_min_diff h_to_target

-- Lattice axioms at the Pre level (proved pointwise via Equiv).
theorem Pre.sup_inf_self_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max x (CReal.Pre.min x y)) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp

theorem Pre.inf_sup_self_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min x (CReal.Pre.max x y)) x := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp

theorem Pre.sup_comm_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max x y) (CReal.Pre.max y x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [max_comm]

theorem Pre.inf_comm_pre (x y : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min x y) (CReal.Pre.min y x) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [min_comm]

theorem Pre.sup_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.max (CReal.Pre.max x y) z)
                    (CReal.Pre.max x (CReal.Pre.max y z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.max]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [max_assoc]

theorem Pre.inf_assoc_pre (x y z : CReal.Pre) :
    CReal.Pre.Equiv (CReal.Pre.min (CReal.Pre.min x y) z)
                    (CReal.Pre.min x (CReal.Pre.min y z)) := by
  intro n
  dsimp [CReal.Pre.Equiv, CReal.Pre.min]
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have hnn : (0 : ℚ) ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [min_assoc]

/-! ### Constructive Positivity -/

/-- Definition of strict positivity (0 < x) on CReal.Pre (Constructive Definition). -/
protected def Pre.Pos (x : CReal.Pre) : Prop := ∃ N, 1/2^N < x.approx (N+1)

/-- Positivity respects equivalence. -/
theorem Pre.pos_well_defined (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) :
  Pre.Pos x ↔ Pre.Pos y := by
  constructor
  · intro h_pos
    obtain ⟨N, hN⟩ := h_pos
    let M := N + 2
    let K := M + 1
    have hN1_le_K : N + 1 ≤ K := by
      dsimp [K, M]; exact add_le_add_left (by decide : 1 ≤ 3) N
    have h_reg := x.is_regular (N + 1) K hN1_le_K
    have hx := (abs_sub_le_iff).1 h_reg
    have h_xK_ge : x.approx K ≥ x.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      have h := hx.left
      linarith
    have h_sum_N : (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) = 2 / 2 ^ (N + 1) :=
      sum_two_halves N
    have h_two_over_pow : (2 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ N := by
      field_simp [pow_succ]; ring
    have h_two_halves_to_pred :
        (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) := by
      simp; ring_nf
    have h_eq_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 1) := by
      linarith [h_two_halves_to_pred]
    have h_lt' : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < x.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      linarith [hN]
    have h_xK_gt_aux : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < x.approx K :=
      lt_of_lt_of_le h_lt' h_xK_ge
    have h_xK : x.approx K > 1 / 2 ^ (N + 1) := by
      rwa [← h_eq_half]
    have h_equiv_M := hxy M
    have h_equiv := (abs_sub_le_iff).1 h_equiv_M
    have h_y_ge : x.approx K - 1 / 2 ^ M ≤ y.approx K := by
      have hxmy : x.approx (M + 1) - y.approx (M + 1) ≤ 1 / 2 ^ M := h_equiv.left
      have hxmyK : x.approx K - y.approx K ≤ 1 / 2 ^ M := by
        simpa [K] using hxmy
      linarith [hxmyK]
    have step : 1 / 2 ^ (N + 1) - 1 / 2 ^ M < x.approx K - 1 / 2 ^ M := by
      have : 1 / 2 ^ (N + 1) < x.approx K := h_xK
      linarith
    have h_sum_N1 : (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) = 2 / 2 ^ (N + 2) :=
      sum_two_halves (N + 1)
    have h_two_over_pow' : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
      field_simp [pow_succ]; ring
    have h_eq_add : (1 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) := by
      simp; ring_nf
    have h_sub_eq : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ M = 1 / 2 ^ M := by
      dsimp [M] at *
      linarith [h_eq_add]
    have h_yK : y.approx K > 1 / 2 ^ M := by
      have : 1 / 2 ^ M < y.approx K := by
        have := lt_of_lt_of_le step h_y_ge
        rwa [h_sub_eq] at this
      simpa using this
    refine ⟨M, ?_⟩
    simpa [K] using h_yK
  · intro h_pos
    obtain ⟨N, hN⟩ := h_pos
    let M := N + 2
    let K := M + 1
    have hN1_le_K : N + 1 ≤ K := by
      dsimp [K, M]; exact add_le_add_left (by decide : 1 ≤ 3) N
    have h_reg := y.is_regular (N + 1) K hN1_le_K
    have hy := (abs_sub_le_iff).1 h_reg
    have h_yK_ge : y.approx K ≥ y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      have h := hy.left
      linarith
    have h_sum_N : (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) = 2 / 2 ^ (N + 1) :=
      sum_two_halves N
    have h_two_over_pow : (2 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ N := by
      field_simp [pow_succ]; ring
    have h_two_halves_to_pred :
        (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + 1 / 2 ^ (N + 1) := by
      simp; ring_nf
    have h_eq_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 1) := by
      linarith [h_two_halves_to_pred]
    have h_lt' : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
      linarith [hN]
    have h_yK_gt_aux : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) < y.approx K :=
      lt_of_lt_of_le h_lt' h_yK_ge
    have h_yK : y.approx K > 1 / 2 ^ (N + 1) := by
      rwa [h_eq_half] at h_yK_gt_aux
    have h_equiv_M := (CReal.Pre.equiv_symm hxy) M
    have h_equiv := (abs_sub_le_iff).1 h_equiv_M
    have h_x_ge : y.approx K - 1 / 2 ^ M ≤ x.approx K := by
      have hyxm : y.approx (M + 1) - x.approx (M + 1) ≤ 1 / 2 ^ M := h_equiv.left
      have hyxmK : y.approx K - x.approx K ≤ 1 / 2 ^ M := by
        simpa [K] using hyxm
      linarith [hyxmK]
    have h_eq_add : (1 : ℚ) / 2 ^ (N + 1) = (1 : ℚ) / 2 ^ (N + 2) + 1 / 2 ^ (N + 2) := by
      field_simp [pow_succ]; ring
    have h_sub_eq : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ M = 1 / 2 ^ M := by
      dsimp [M] at *
      linarith [h_eq_add]
    have step : 1 / 2 ^ (N + 1) - 1 / 2 ^ M < y.approx K - 1 / 2 ^ M := by
      have : 1 / 2 ^ (N + 1) < y.approx K := h_yK
      linarith
    have h_xK : x.approx K > 1 / 2 ^ M := by
      have t := lt_of_lt_of_le step h_x_ge
      rwa [h_sub_eq] at t
    refine ⟨M, ?_⟩
    simpa [K] using h_xK

/-! ### Lattice Structure and Absolute Value -/

/-- Supremum on CReal, lifted from Pre.max. -/
def sup (x y : CReal) : CReal :=
  Quotient.map₂ Pre.max
    (fun {a₁ a₂} (hx : Pre.Equiv a₁ a₂) {b₁ b₂} (hy : Pre.Equiv b₁ b₂) =>
      Pre.max_respects_equiv hx hy)
    x y

/-- Infimum on CReal, lifted from Pre.min. -/
def inf (x y : CReal) : CReal :=
  Quotient.map₂ Pre.min
    (fun {a₁ a₂} (hx : Pre.Equiv a₁ a₂) {b₁ b₂} (hy : Pre.Equiv b₁ b₂) =>
      Pre.min_respects_equiv hx hy)
    x y

/-- Absolute value on CReal: |x| = sup x (-x). -/
def abs (x : CReal) : CReal := sup x (-x)

instance : Lattice CReal where
  sup := sup
  inf := inf
  le_sup_left := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have h : x.approx (n+1) ≤ max (x.approx (n+1)) (y.approx (n+1)) := le_max_left _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  le_sup_right := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have h : y.approx (n+1) ≤ max (x.approx (n+1)) (y.approx (n+1)) := le_max_right _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  sup_le := by
    intro a b c hab hac
    refine Quot.induction_on₃ a b c (fun x y z hab hac => ?_) hab hac
    intro n
    dsimp [CReal.Pre.le, sup, CReal.Pre.max]
    have hx := hab n
    have hy := hac n
    have h : max (x.approx (n+1)) (y.approx (n+1)) ≤ z.approx (n+1) + 1/2^n := by
      exact max_le hx hy
    exact h
  inf_le_left := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have h : min (x.approx (n+1)) (y.approx (n+1)) ≤ x.approx (n+1) := min_le_left _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  inf_le_right := by
    intro a b
    refine Quot.induction_on₂ a b (fun x y => ?_)
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have h : min (x.approx (n+1)) (y.approx (n+1)) ≤ y.approx (n+1) := min_le_right _ _
    have h_pos : 0 ≤ (1 : ℚ) / 2 ^ n := by positivity
    linarith
  le_inf := by
    intro a b c hab hac
    refine Quot.induction_on₃ a b c (fun x y z hab hac => ?_) hab hac
    intro n
    dsimp [CReal.Pre.le, inf, CReal.Pre.min]
    have hx := hab n
    have hy := hac n
    have h_min_le : min (y.approx (n+1)) (z.approx (n+1)) ≤ y.approx (n+1) := min_le_left _ _
    have h_min_le' : min (y.approx (n+1)) (z.approx (n+1)) ≤ z.approx (n+1) := min_le_right _ _
    have : x.approx (n+1) ≤ y.approx (n+1) + 1/2^n := hx
    have : x.approx (n+1) ≤ z.approx (n+1) + 1/2^n := hy
    have h_min_bound : x.approx (n+1) ≤ min (y.approx (n+1) + 1/2^n) (z.approx (n+1) + 1/2^n) := by
      exact le_min hx hy
    have h_distrib : min (y.approx (n+1) + 1/2^n) (z.approx (n+1) + 1/2^n) =
                     min (y.approx (n+1)) (z.approx (n+1)) + 1/2^n := by
      exact min_add_add_right (y.approx (n+1)) (z.approx (n+1)) (1/2^n)
    rw [h_distrib] at h_min_bound
    exact h_min_bound

/-! ### Ordered Ring Properties -/

/-- Addition preserves order. -/
theorem add_le_add_left (a b : CReal) (h : a ≤ b) (c : CReal) : c + a ≤ c + b := by
  refine Quot.induction_on₃ a b c (fun a b c h => ?_) h
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.add]
  calc
    c.approx (n+2) + a.approx (n+2)
      ≤ c.approx (n+2) + (b.approx (n+2) + (1 : ℚ) / 2^(n+1)) := by
        gcongr
        exact h (n+1)
    _ = (c.approx (n+2) + b.approx (n+2)) + (1 : ℚ) / 2^(n+1) := by
        ring
    _ ≤ (c.approx (n+2) + b.approx (n+2)) + (1 : ℚ) / 2^n := by
        gcongr
        · simp_all only [Nat.one_le_ofNat]
        · simp_all only [le_add_iff_nonneg_right, zero_le]

theorem zero_le_one : (0 : CReal) ≤ 1 := by
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.zero, CReal.Pre.one]
  positivity

/-- Multiplication of non-negative numbers is non-negative. -/
theorem mul_nonneg (a b : CReal) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  refine' Quot.induction_on₂ a b (fun a b ha hb => _) ha hb
  intro n
  dsimp [CReal.Pre.le, CReal.Pre.zero, CReal.Pre.mul]
  let S := CReal.Pre.mulShift a b
  let K := n + 1 + S
  have hK_pos : 0 < K := by positivity
  have haK_nonneg : 0 ≤ a.approx K + 1 / 2 ^ (K - 1) := by
    simp at ha
    simpa [Nat.sub_add_cancel hK_pos] using ha (K - 1)
  have hbK_nonneg : 0 ≤ b.approx K + 1 / 2 ^ (K - 1) := by
    simp at hb
    simpa [Nat.sub_add_cancel hK_pos] using hb (K - 1)
  have haK : -(1 : ℚ) / 2 ^ (K - 1) ≤ a.approx K := by
    have h' : 0 ≤ a.approx K + (1 : ℚ) / 2 ^ (K - 1) := by
      simpa [add_comm] using haK_nonneg
    have hneg := (neg_le_iff_add_nonneg).2 h'
    simp; ring_nf; simp_all only [add_pos_iff, zero_lt_one, or_true, true_or, Nat.succ_add_sub_one, one_div, inv_pow, K,
      S]
  have hbK : -(1 : ℚ) / 2 ^ (K - 1) ≤ b.approx K := by
    have h' : 0 ≤ b.approx K + (1 : ℚ) / 2 ^ (K - 1) := by
      simpa [add_comm] using hbK_nonneg
    have hneg := (neg_le_iff_add_nonneg).2 h'
    simp; ring_nf; simp_all only [add_pos_iff, zero_lt_one, or_true, true_or, Nat.succ_add_sub_one, one_div, inv_pow, K,
      S]
  let Ba : ℚ := a.cBound
  let Bb : ℚ := b.cBound
  have hS_sum : (a.cBound + b.cBound : ℚ) ≤ 2 ^ S :=
    CReal.Pre.sum_cBound_le_pow_mulShift a b
  have hBa_le_S : Ba ≤ 2 ^ S := by
    have hBb_nonneg : (0 : ℚ) ≤ Bb := natCast_nonneg
    have : Ba ≤ Ba + Bb := by linarith
    exact this.trans hS_sum
  have hBb_le_S : Bb ≤ 2 ^ S := by
    have hBa_nonneg : (0 : ℚ) ≤ Ba := natCast_nonneg
    have : Bb ≤ Ba + Bb := by linarith
    exact this.trans hS_sum
  have hK_sub_1 : K - 1 = n + S := by simp [K]
  have h_target_bound (B : ℚ) (hB_le_S : B ≤ 2 ^ S) : B / 2 ^ (n + S) ≤ 1 / 2 ^ n := by
    have h_inv_nonneg : (0 : ℚ) ≤ (1 / 2 ^ (n + S)) := by positivity
    have step := mul_le_mul_of_nonneg_right hB_le_S h_inv_nonneg
    have hstep : B / 2 ^ (n + S) ≤ (2 : ℚ) ^ S / 2 ^ (n + S) := by
      simpa [div_eq_mul_inv] using step
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    have hne1 : (2 : ℚ) ^ S ≠ 0 := pow_ne_zero _ h2
    have hne2 : (2 : ℚ) ^ (n + S) ≠ 0 := pow_ne_zero _ h2
    have h_cancel : (2 : ℚ) ^ S / 2 ^ (n + S) = 1 / 2 ^ n := by
      field_simp [pow_add, hne1, hne2, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    simpa [h_cancel] using hstep
  rcases le_or_gt 0 (a.approx K) with ha_pos | ha_neg
  rcases le_or_gt 0 (b.approx K) with hb_pos | hb_neg
  · have h_prod_nonneg : 0 ≤ a.approx K * b.approx K := _root_.mul_nonneg ha_pos hb_pos
    have h_half_pow_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := by
      positivity
    exact add_nonneg h_prod_nonneg h_half_pow_nonneg
  · have h_abs_b : |b.approx K| ≤ 1 / 2 ^ (K - 1) := by
      have : -b.approx K ≤ 1 / 2 ^ (K - 1) := by linarith [hbK]
      simpa [abs_of_neg hb_neg] using this
    have h_abs_a : |a.approx K| ≤ Ba := by
      simpa using a.abs_approx_le_cBound K
    have h_bound : |a.approx K * b.approx K| ≤ Ba / 2 ^ (K - 1) := by
      have hBa_nonneg : (0 : ℚ) ≤ Ba := natCast_nonneg
      have h_abs_b_nonneg : (0 : ℚ) ≤ |b.approx K| := abs_nonneg _
      have := mul_le_mul h_abs_a h_abs_b h_abs_b_nonneg hBa_nonneg
      simpa [abs_mul, div_eq_mul_inv] using this
    have h_target := h_target_bound Ba hBa_le_S
    have h_left : -(1 / 2 ^ n : ℚ) ≤ -(Ba / 2 ^ (K - 1)) := by
      have := neg_le_neg h_target
      simpa [hK_sub_1] using this
    have h_prod_nonpos : a.approx K * b.approx K ≤ 0 :=
      _root_.mul_nonpos_of_nonneg_of_nonpos ha_pos (le_of_lt hb_neg)
    have h_abs_eq_neg : |a.approx K * b.approx K| = -(a.approx K * b.approx K) :=
      abs_of_nonpos h_prod_nonpos
    have h_right : -(Ba / 2 ^ (K - 1)) ≤ a.approx K * b.approx K := by
      have := neg_le_neg h_bound
      simpa [h_abs_eq_neg] using this
    have h_prod_ge : -(1 / 2 ^ n : ℚ) ≤ a.approx K * b.approx K := h_left.trans h_right
    have h_final : 0 ≤ a.approx K * b.approx K + 1 / 2 ^ n := by
      linarith [h_prod_ge]
    exact h_final
  · have h_abs_a : |a.approx K| ≤ 1 / 2 ^ (K - 1) := by
      have : -a.approx K ≤ 1 / 2 ^ (K - 1) := by linarith [haK]
      simpa [abs_of_neg ha_neg] using this
    have h_abs_b : |b.approx K| ≤ Bb := by
      simpa using b.abs_approx_le_cBound K
    have h_bound : |a.approx K * b.approx K| ≤ Bb / 2 ^ (K - 1) := by
      have hBb_nonneg : (0 : ℚ) ≤ Bb := natCast_nonneg
      have h_div_nonneg : (0 : ℚ) ≤ 1 / 2 ^ (K - 1) := by
        have hpow : 0 < (2 : ℚ) ^ (K - 1) := pow_pos (by norm_num) _
        exact le_of_lt (div_pos (by norm_num) hpow)
      have := mul_le_mul h_abs_a h_abs_b (by exact abs_nonneg _) h_div_nonneg
      simpa [abs_mul, div_eq_mul_inv, mul_comm] using this
    have h_target := h_target_bound Bb hBb_le_S
    have h_left : -(1 / 2 ^ n : ℚ) ≤ -(Bb / 2 ^ (K - 1)) := by
      have := neg_le_neg h_target
      simpa [hK_sub_1] using this
    have h_right : -(Bb / 2 ^ (K - 1)) ≤ a.approx K * b.approx K :=
      (abs_le.mp h_bound).1
    have h_prod_ge : -(1 / 2 ^ n : ℚ) ≤ a.approx K * b.approx K := h_left.trans h_right
    have h_final : 0 ≤ a.approx K * b.approx K + 1 / 2 ^ n := by
      linarith [h_prod_ge]
    exact h_final

/-! ### Strict Positivity and Final Instance -/

/-- Strict positivity (0 < x) on CReal. Lifted from CReal.Pre.Pos. -/
def Pos (x : CReal) : Prop := Quotient.lift Pre.Pos (fun _ _ h => propext (CReal.Pre.pos_well_defined _ _ h)) x

/-- Pre-level: from Pos (y − x) derive x ≤ y. -/
private lemma pre_pos_sub_implies_le
  (x y : CReal.Pre) (hpos : CReal.Pre.Pos (CReal.Pre.add y (CReal.Pre.neg x))) :
  CReal.Pre.le x y := by
  intro n
  rcases hpos with ⟨N, hN⟩
  let K := max (n + 1) (N + 2)
  have hK_ge_n1 : n + 1 ≤ K := le_max_left _ _
  have hK_ge_N2 : N + 2 ≤ K := le_max_right _ _
  have hy_reg' : |y.approx (N + 2) - y.approx K| ≤ (1 : ℚ) / 2 ^ (N + 2) :=
    y.is_regular (N + 2) K hK_ge_N2
  have hy_reg : |y.approx K - y.approx (N + 2)| ≤ (1 : ℚ) / 2 ^ (N + 2) := by
    simpa [abs_sub_comm] using hy_reg'
  have hx_reg' : |x.approx (N + 2) - x.approx K| ≤ (1 : ℚ) / 2 ^ (N + 2) :=
    x.is_regular (N + 2) K hK_ge_N2
  have hx_reg : |x.approx K - x.approx (N + 2)| ≤ (1 : ℚ) / 2 ^ (N + 2) := by
    simpa [abs_sub_comm] using hx_reg'
  have yK_ge : y.approx K ≥ y.approx (N + 2) - 1 / 2 ^ (N + 2) := by
    have h := (abs_sub_le_iff).1 hy_reg
    linarith [h.right]
  have xK_le : x.approx K ≤ x.approx (N + 2) + 1 / 2 ^ (N + 2) := by
    have h := (abs_sub_le_iff).1 hx_reg
    linarith [h.left]
  have h_gap_at_N2 : (1 : ℚ) / 2 ^ N < y.approx (N + 2) - x.approx (N + 2) := by
    simpa [CReal.Pre.add, CReal.Pre.neg, sub_eq_add_neg,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hN
  have h_half_eq : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = 1 / 2 ^ (N + 1) := by
    field_simp [pow_succ]; ring
  have h_yxK : (1 : ℚ) / 2 ^ (N + 1) < y.approx K - x.approx K := by
    have h_lower_bound :
        y.approx K - x.approx K
          ≥ y.approx (N + 2) - x.approx (N + 2) - (2 : ℚ) / 2 ^ (N + 2) := by
      have h_neg_x : -x.approx K ≥ -(x.approx (N + 2) + 1 / 2 ^ (N + 2)) := by
        exact neg_le_neg xK_le
      have := add_le_add yK_ge h_neg_x
      have h_rhs_rewrite : (y.approx (N + 2) - 1 / 2 ^ (N + 2)) + -(x.approx (N + 2) + 1 / 2 ^ (N + 2)) =
                           (y.approx (N + 2) - x.approx (N + 2)) - (2 / 2 ^ (N + 2)) := by ring
      rw [h_rhs_rewrite] at this
      linarith [this]
    have h_two_over : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
      field_simp [pow_succ]; ring
    have h_target : (y.approx (N + 2) - x.approx (N + 2)) - (2 : ℚ) / 2 ^ (N + 2)
                      > 1 / 2 ^ (N + 1) := by
      have : (y.approx (N + 2) - x.approx (N + 2)) - 1 / 2 ^ (N + 1)
               > 1 / 2 ^ N - 1 / 2 ^ (N + 1) := by
        linarith [h_gap_at_N2]
      simp_all only [one_div, Nat.add_max_add_right, add_le_add_iff_right, le_sup_left, Nat.reduceLeDiff, le_sup_right,
        ge_iff_le, tsub_le_iff_right, gt_iff_lt, K]
    exact lt_of_lt_of_le h_target h_lower_bound
  have hx_tail : x.approx (n + 1) ≤ x.approx K + 1 / 2 ^ (n + 1) := by
    have h := x.is_regular (n + 1) K hK_ge_n1
    have h' := (abs_sub_le_iff).1 h
    linarith [h'.left]
  have hy_tail : y.approx K ≤ y.approx (n + 1) + 1 / 2 ^ (n + 1) := by
    have h := y.is_regular (n + 1) K hK_ge_n1
    have h' := (abs_sub_le_iff).1 h
    linarith [h'.right]
  let a : ℚ := 1 / 2 ^ (n + 1)
  let b : ℚ := 1 / 2 ^ (N + 1)
  have hxK_le : x.approx K ≤ y.approx K - b := by
    have : b < y.approx K - x.approx K := h_yxK
    linarith
  have hx_step : x.approx (n + 1) ≤ (y.approx K - b) + a := by
    calc x.approx (n + 1)
      ≤ x.approx K + a := hx_tail
      _ ≤ (y.approx K - b) + a := by linarith [hxK_le]
  have hy_sub1 : y.approx K - b ≤ (y.approx (n + 1) + a) - b := by
    linarith [hy_tail]
  have hy_sub2 : (y.approx K - b) + a ≤ ((y.approx (n + 1) + a) - b) + a := by
    linarith [hy_sub1]
  have hx_step' : x.approx (n + 1) ≤ ((y.approx (n + 1) + a) - b) + a :=
    _root_.le_trans hx_step hy_sub2
  have hb_nonneg : (0 : ℚ) ≤ b := by
    have : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
    exact le_of_lt (div_pos (by norm_num) this)
  have drop_sub :
      ((y.approx (n + 1) + a) - b) + a ≤ y.approx (n + 1) + (a + a) := by
    linarith [hb_nonneg]
  have hx_final_sum : x.approx (n + 1) ≤ y.approx (n + 1) + (a + a) :=
    _root_.le_trans hx_step' drop_sub
  have h_two : a + a = (1 : ℚ) / 2 ^ n := by
    dsimp [a]
    field_simp [pow_succ]; ring
  have : x.approx (n + 1) ≤ y.approx (n + 1) + (1 : ℚ) / 2 ^ n := by
    rwa [← h_two]
  exact this

/-- Quotient level: from Pos (y − x) derive x ≤ y. -/
lemma pos_sub_implies_le (x y : CReal) (h : Pos (y - x)) : x ≤ y := by
  refine Quot.induction_on₂ x y (fun x_pre y_pre h_pre => ?_) h
  simpa using pre_pos_sub_implies_le x_pre y_pre h_pre

/-- Pos (y − x) implies x ≠ y. -/
lemma pos_sub_implies_ne (x y : CReal) (h : Pos (y - x)) : x ≠ y := by
  intro hxy
  have : Pos (0 : CReal) := by simpa [hxy, sub_self] using h
  rcases this with this
  dsimp [Pos] at this
  rcases this with ⟨N, hN⟩
  dsimp [CReal.Pre.zero] at hN
  have : 0 < (1 : ℚ) / 2 ^ N := by
    exact div_pos (by norm_num) (pow_pos (by norm_num) _)
  exact (not_lt_of_ge (le_of_lt this)).elim hN

theorem lt_iff_pos (x y : CReal) : x < y ↔ Pos (y - x) := by
  constructor
  · refine Quot.induction_on₂ x y (fun x_pre y_pre => ?_)
    intro hlt
    
    have h_le : CReal.Pre.le x_pre y_pre := by
      simpa using hlt.1
    have h_not_le : ¬ CReal.Pre.le y_pre x_pre := by
      intro h
      have hyx : (⟦y_pre⟧ : CReal) ≤ ⟦x_pre⟧ := by simpa using h
      exact hlt.2 hyx
    obtain ⟨n, hn⟩ :
        ∃ n : ℕ, ¬ y_pre.approx (n + 1) ≤ x_pre.approx (n + 1) + (1 : ℚ) / 2 ^ n :=
      not_forall.mp h_not_le
    have hn_strict :
        y_pre.approx (n + 1) > x_pre.approx (n + 1) + (1 : ℚ) / 2 ^ n :=
      not_le.mp hn
    let δ : ℚ := (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - (1 : ℚ) / 2 ^ n
    have h_gap_pos : 0 < δ := by
      have : (1 : ℚ) / 2 ^ n < y_pre.approx (n + 1) - x_pre.approx (n + 1) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hn_strict
      exact sub_pos.mpr this
    obtain ⟨M0, hM0⟩ := find_index_for_bound (by norm_num : 0 < (1 : ℚ)) h_gap_pos
    let M := Nat.max M0 n
    have hM_ge_M0 : M0 ≤ M := le_max_left _ _
    have hM_ge_n  : n ≤ M  := le_max_right _ _
    have h_pow_monotone : (1 : ℚ) / 2 ^ M ≤ 1 / 2 ^ M0 := by
      apply one_div_le_one_div_of_le
      · exact pow_pos (by norm_num) _
      · exact (pow_le_pow_iff_right₀ rfl).mpr hM_ge_M0
    have h_small : (1 : ℚ) / 2 ^ M < δ := lt_of_le_of_lt h_pow_monotone hM0
    have h_n1_le_M2 : n + 1 ≤ M + 2 := by
      have : n + 1 ≤ M + 1 := Nat.succ_le_succ hM_ge_n
      exact this.trans (Nat.le_succ (M + 1))
    have hy_reg := y_pre.is_regular (n + 1) (M + 2) h_n1_le_M2
    have hy_pair := (abs_sub_le_iff).1 hy_reg
    have hy_ge : y_pre.approx (M + 2) ≥ y_pre.approx (n + 1) - 1 / 2 ^ (n + 1) := by
      have h := hy_pair.left
      linarith [h]
    have hx_reg := x_pre.is_regular (n + 1) (M + 2) h_n1_le_M2
    have hx_pair := (abs_sub_le_iff).1 hx_reg
    have hx_le : x_pre.approx (M + 2) ≤ x_pre.approx (n + 1) + 1 / 2 ^ (n + 1) := by
      have h := hx_pair.right
      linarith [h]
    have h_diff_lower_aux :
        (y_pre.approx (n + 1) - 1 / 2 ^ (n + 1)) -
            (x_pre.approx (n + 1) + 1 / 2 ^ (n + 1))
          ≤ y_pre.approx (M + 2) - x_pre.approx (M + 2) :=
      sub_le_sub hy_ge hx_le
    have h_rewrite :
        (y_pre.approx (n + 1) - 1 / 2 ^ (n + 1)) -
            (x_pre.approx (n + 1) + 1 / 2 ^ (n + 1))
        = (y_pre.approx (n + 1) - x_pre.approx (n + 1)) -
            (2 : ℚ) / 2 ^ (n + 1) := by
      ring
    have h_two : (2 : ℚ) / 2 ^ (n + 1) = (1 : ℚ) / 2 ^ n := by
      field_simp [pow_succ]; ring
    have h_diff_lower :
        (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - (1 : ℚ) / 2 ^ n
          ≤ y_pre.approx (M + 2) - x_pre.approx (M + 2) := by
      have htmp := h_diff_lower_aux
      rw [h_rewrite, h_two] at htmp
      exact htmp
    dsimp [Pos]
    refine ⟨M, ?_⟩
    dsimp [CReal.Pre.add, CReal.Pre.neg]
    have h_small' :
        (1 : ℚ) / 2 ^ M
          < (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - 1 / 2 ^ n := h_small
    have h_diff_lower' :
        (y_pre.approx (n + 1) - x_pre.approx (n + 1)) - 1 / 2 ^ n
          ≤ y_pre.approx (M + 2) + (-x_pre.approx (M + 2)) := by
      simpa [sub_eq_add_neg] using h_diff_lower
    exact lt_of_lt_of_le h_small' h_diff_lower'
  · intro h
    have h_le : x ≤ y := pos_sub_implies_le x y h
    have h_ne : x ≠ y := pos_sub_implies_ne x y h
    exact lt_of_le_of_ne h_le h_ne

/-- Multiplication of strictly positive numbers is strictly positive. (Constructive Proof) -/
theorem mul_pos (a b : CReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  refine Quot.induction_on₂ a b (fun xa xb ha hb => ?_) ha hb
  have ha_pos_pre : CReal.Pre.Pos xa := by
    have ha' : (0 : CReal) < ⟦xa⟧ := ha
    have : Pos (⟦xa⟧ - 0 : CReal) := (lt_iff_pos 0 ⟦xa⟧).mp ha
    have : Pos (⟦xa⟧ : CReal) := by simpa using this
    dsimp [Pos] at this
    simpa using this
  have hb_pos_pre : CReal.Pre.Pos xb := by
    have hb' : (0 : CReal) < ⟦xb⟧ := hb
    have : Pos (⟦xb⟧ - 0 : CReal) := (lt_iff_pos 0 ⟦xb⟧).mp hb
    have : Pos (⟦xb⟧ : CReal) := by simpa using this
    dsimp [Pos] at this
    simpa using this
  rcases ha_pos_pre with ⟨Na, hNa⟩
  rcases hb_pos_pre with ⟨Nb, hNb⟩
  let M := Na + Nb + 2
  let S := CReal.Pre.mulShift xa xb
  let K := M + 1 + S
  have hK_ge_a : K ≥ Na + 1 := by dsimp [K, M]; linarith
  have hK_ge_b : K ≥ Nb + 1 := by dsimp [K, M]; linarith
  have h_a_stable : xa.approx K > 1 / 2 ^ (Na + 1) := by
    have h_reg := xa.is_regular (Na + 1) K hK_ge_a
    have h_reg' : |xa.approx K - xa.approx (Na + 1)| ≤ 1 / 2 ^ (Na + 1) := by
      simpa [abs_sub_comm] using h_reg
    have h_ge : xa.approx K ≥ xa.approx (Na + 1) - 1 / 2 ^ (Na + 1) := by
      have hpair := (abs_sub_le_iff).1 h_reg'
      linarith [hpair.left]
    have h_eq : (1 : ℚ) / 2 ^ Na - 1 / 2 ^ (Na + 1) = 1 / 2 ^ (Na + 1) := by
      field_simp [pow_succ]; ring
    have : (1 : ℚ) / 2 ^ Na - 1 / 2 ^ (Na + 1) < xa.approx K := by
      have : (1 : ℚ) / 2 ^ Na < xa.approx (Na + 1) := hNa
      exact lt_of_lt_of_le (by linarith) h_ge
    simp_all only [one_div, ge_iff_le, tsub_le_iff_right, gt_iff_lt, K, M, S]
  have h_b_stable : xb.approx K > 1 / 2 ^ (Nb + 1) := by
    have h_reg := xb.is_regular (Nb + 1) K hK_ge_b
    have h_reg' : |xb.approx K - xb.approx (Nb + 1)| ≤ 1 / 2 ^ (Nb + 1) := by
      simpa [abs_sub_comm] using h_reg
    have h_ge : xb.approx K ≥ xb.approx (Nb + 1) - 1 / 2 ^ (Nb + 1) := by
      have hpair := (abs_sub_le_iff).1 h_reg'
      linarith [hpair.left]
    have h_eq : (1 : ℚ) / 2 ^ Nb - 1 / 2 ^ (Nb + 1) = 1 / 2 ^ (Nb + 1) := by
      field_simp [pow_succ]; ring
    have : (1 : ℚ) / 2 ^ Nb - 1 / 2 ^ (Nb + 1) < xb.approx K := by
      have : (1 : ℚ) / 2 ^ Nb < xb.approx (Nb + 1) := hNb
      exact lt_of_lt_of_le (by linarith) h_ge
    simp_all only [one_div, ge_iff_le, gt_iff_lt, tsub_le_iff_right, K, M, S]
  have h_prod : xa.approx K * xb.approx K > 1 / 2 ^ M := by
    have h_pos_a : (0 : ℚ) < 1 / 2 ^ (Na + 1) := by
      exact div_pos (by norm_num) (pow_pos (by norm_num) _)
    have h_pos_b : (0 : ℚ) < 1 / 2 ^ (Nb + 1) := by
      exact div_pos (by norm_num) (pow_pos (by norm_num) _)
    have h_nonneg_b : (0 : ℚ) ≤ 1 / 2 ^ (Nb + 1) := le_of_lt h_pos_b
    have h_pos_xa_K : (0 : ℚ) < xa.approx K := lt_trans h_pos_a h_a_stable
    calc
      xa.approx K * xb.approx K
          > (1 / 2 ^ (Na + 1)) * (1 / 2 ^ (Nb + 1)) := by
              exact mul_lt_mul' (le_of_lt h_a_stable) h_b_stable h_nonneg_b h_pos_xa_K
      _ = 1 / 2 ^ (Na + Nb + 2) := by
              have : (1 : ℚ) / 2 ^ (Na + 1) * (1 / 2 ^ (Nb + 1)) = 1 / (2 ^ (Na + 1) * 2 ^ (Nb + 1)) := by
                field_simp
              rw [this]
              congr 1
              rw [← pow_add]
              congr 1
              ring
      _ = 1 / 2 ^ M := by rfl
  have h_pre_pos_prod : CReal.Pre.Pos (CReal.Pre.mul xa xb) := by
    refine ⟨M, ?_⟩
    dsimp [CReal.Pre.mul]
    simpa [K] using h_prod
  have hpos_prod_C : Pos (((⟦xa⟧ : CReal) * ⟦xb⟧) - 0) := by
    have : Pos (⟦CReal.Pre.mul xa xb⟧ : CReal) := by
      dsimp [Pos]; exact h_pre_pos_prod
    simpa [mul_def, sub_zero] using this
  exact (lt_iff_pos (0 : CReal) ((⟦xa⟧ : CReal) * ⟦xb⟧)).2 hpos_prod_C

theorem zero_lt_one : (0 : CReal) < (1 : CReal) := by
  have h : Pos (1 : CReal) := by
    change Pos ⟦CReal.Pre.one⟧
    dsimp [Pos, CReal.Pre.Pos, CReal.Pre.one]
    use 1
    simp
    norm_num
  simpa [sub_zero] using (lt_iff_pos (0 : CReal) (1 : CReal)).2 (by simpa using h)

instance : ZeroLEOneClass CReal where
  zero_le_one := le_of_lt zero_lt_one

instance : Nontrivial CReal :=
  ⟨⟨0, 1, by exact ne_of_lt zero_lt_one⟩⟩


/-- CReal has AddRightMono property. -/
instance : AddRightMono CReal where
  elim a b c h := by
    have h' : a + b ≤ a + c := add_le_add_left b c h a
    rwa [add_comm a b, add_comm a c] at h'


/-
Ordered structure for CReal using the modern mixin style.
We rely on the existing CommRing and PartialOrder instances and provide the
axioms required by IsOrderedRing.
-/
/-- Left multiplication by nonnegative elements preserves order. -/
theorem mul_le_mul_of_nonneg_left' (a b c : CReal) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  have h_sub_nonneg : 0 ≤ b - a := by
    exact sub_nonneg_of_le h
  have h_prod_nonneg : 0 ≤ c * (b - a) := mul_nonneg c (b - a) hc h_sub_nonneg
  have h_expand : c * (b - a) = c * b - c * a := by ring
  rw [h_expand] at h_prod_nonneg
  exact le_of_sub_nonneg h_prod_nonneg

/-- Right multiplication by nonnegative elements preserves order. -/
theorem mul_le_mul_of_nonneg_right' (a b c : CReal) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]
  exact mul_le_mul_of_nonneg_left' a b c h hc

instance : IsOrderedRing CReal where
  add_le_add_left := add_le_add_left
  zero_le_one := zero_le_one
  mul_le_mul_of_nonneg_left := mul_le_mul_of_nonneg_left'
  mul_le_mul_of_nonneg_right := mul_le_mul_of_nonneg_right'

/-! ### Archimedean Property -/

/-- Embedding of natural numbers into CReal.Pre. -/
def Pre.ofNat (n : ℕ) : CReal.Pre where
  approx := fun _ => (n : ℚ)
  is_regular := by intro k m _; simp

instance : NatCast CReal where
  natCast n := ⟦Pre.ofNat n⟧

/-- Pre-level n-fold addition of a pre-real (compatible with `CReal`'s `nsmul`). -/
def Pre.nsmul (n : ℕ) (y : CReal.Pre) : CReal.Pre :=
  Nat.rec CReal.Pre.zero (fun _ acc => CReal.Pre.add acc y) n

@[simp] lemma nsmul_zero (y : CReal.Pre) : nsmul 0 y = CReal.Pre.zero := rfl
@[simp] lemma nsmul_succ (n : ℕ) (y : CReal.Pre) : nsmul (n+1) y = (nsmul n y).add y := rfl

/-- nsmul respects equivalence at the Pre level. -/
lemma nsmul_respects_equiv {y₁ y₂ : CReal.Pre} (h : CReal.Pre.Equiv y₁ y₂) (n : ℕ) :
    CReal.Pre.Equiv (nsmul n y₁) (nsmul n y₂) := by
  induction n with
  | zero =>
      intro k
      dsimp [CReal.Pre.Equiv, nsmul, CReal.Pre.zero]
      simp
  | succ n ih =>
      intro k
      dsimp [nsmul, CReal.Pre.add, CReal.Pre.Equiv]
      exact add_respects_equiv ih h k

/-- If on a block of length `n` starting at `m+1` we have a pointwise lower bound
    `δ ≤ y.approx (m+t)` for `t = 1..n`, then `(n • y).approx m ≥ (n:ℚ) * δ`. -/
lemma nsmul_approx_lower_bound
    (y : CReal.Pre) (δ : ℚ) (m n : ℕ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ n → δ ≤ y.approx (m + t)) :
    (CReal.Pre.nsmul n y).approx m ≥ (n : ℚ) * δ := by
  induction n generalizing m with
  | zero =>
      simp [CReal.Pre.nsmul, CReal.Pre.zero]
  | succ n ih =>
      have h0 : δ ≤ y.approx (m + 1) := by
        have h1 : 1 ≤ 1 := le_rfl
        have h2 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        simpa using h 1 h1 h2
      have hstep : ∀ t, 1 ≤ t → t ≤ n → δ ≤ y.approx ((m + 1) + t) := by
        intro t ht₁ ht₂
        have h1' : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
        have h2' : t + 1 ≤ n + 1 := Nat.succ_le_succ ht₂
        have := h (t + 1) h1' h2'
        simpa [Nat.add_assoc, add_comm, add_left_comm] using this
      have ih' := ih (m := m + 1) hstep
      dsimp [CReal.Pre.nsmul, CReal.Pre.add] at ih' ⊢
      have h_sum_eq : (n : ℚ) * δ + δ = ((n+1 : ℕ) : ℚ) * δ := by
        have : ((n+1 : ℕ) : ℚ) * δ = (n : ℚ) * δ + δ := by
          simp [Nat.cast_succ, add_mul, one_mul]
        simpa [eq_comm] using this
      calc
        (CReal.Pre.nsmul n y).approx (m + 1) + y.approx (m + 1)
            ≥ (n : ℚ) * δ + δ := add_le_add ih' h0
        _ = ((n+1 : ℕ) : ℚ) * δ := h_sum_eq

/-- From `Pos y` we extract a uniform positive rational lower bound valid for all
    sufficiently large indices. -/
lemma pos_uniform_lower_bound (y : CReal.Pre) (hy : CReal.Pre.Pos y) :
    ∃ K : ℕ, ∃ δ : ℚ, 0 < δ ∧ ∀ m : ℕ, K ≤ m → δ ≤ y.approx m := by
  rcases hy with ⟨N, hN⟩
  let K := N + 2
  let δ : ℚ := 1 / 2 ^ (N + 2)
  have hδ_pos : 0 < δ := by exact div_pos (by norm_num) (pow_pos (by norm_num) _)
  have hN1_le_K : N + 1 ≤ K := by dsimp [K]; exact Nat.le_succ (N + 1)
  have h_reg := y.is_regular (N + 1) K hN1_le_K
  have yK_ge : y.approx K ≥ y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
    have hpair := (abs_sub_le_iff).1 h_reg
    have h1 : y.approx (N + 1) ≤ y.approx K + 1 / 2 ^ (N + 1) := by
      have h := hpair.right
      linarith
    linarith [h1]
  have h_sub_half : (1 : ℚ) / 2 ^ N - 1 / 2 ^ (N + 1) = 1 / 2 ^ (N + 1) := by
    field_simp [pow_succ]; ring
  have h_half_lt : (1 : ℚ) / 2 ^ (N + 1) < y.approx (N + 1) - 1 / 2 ^ (N + 1) := by
    rw [← h_sub_half]; linarith [hN]
  have yK_gt_half_succ : y.approx K > 1 / 2 ^ (N + 1) :=
    lt_of_lt_of_le h_half_lt yK_ge
  have h_sub_id : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ K = 1 / 2 ^ (N + 2) := by
    dsimp [K]; field_simp [pow_succ]; ring
  refine ⟨K, δ, hδ_pos, ?_⟩
  intro m hm
  have hreg2 := y.is_regular K m hm
  have hpair2 := (abs_sub_le_iff).1 hreg2
  have ym_ge : y.approx m ≥ y.approx K - 1 / 2 ^ K := by
    have h1 : y.approx K - y.approx m ≤ 1 / 2 ^ K := hpair2.left
    have h2 : - y.approx m ≤ 1 / 2 ^ K - y.approx K := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_le_sub_right h1 (y.approx K)
    have h3 := neg_le_neg h2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3
  have h_delta_lt : δ < y.approx K - 1 / 2 ^ K := by
    have haux : (1 / 2 ^ (N + 1) - 1 / 2 ^ K) < (y.approx K - 1 / 2 ^ K) :=
      sub_lt_sub_right yK_gt_half_succ (1 / 2 ^ K)
    simp_all only [one_div, inv_pos, Nat.ofNat_pos, pow_succ_pos, add_le_add_iff_left, Nat.one_le_ofNat, ge_iff_le,
      tsub_le_iff_right, gt_iff_lt, δ, K]
  have hK_sub_le : y.approx K - 1 / 2 ^ K ≤ y.approx m := by
    linarith [ym_ge]
  exact (le_of_lt (lt_of_lt_of_le h_delta_lt hK_sub_le))

/-- Bridge: the quotient value of `n • ⟦y⟧` is represented by `Pre.nsmul n y`. -/
@[simp] lemma nsmul_def (y : CReal.Pre) (n : ℕ) :
    (n : ℕ) • (⟦y⟧ : CReal) = ⟦CReal.Pre.nsmul n y⟧ := by
  induction n with
  | zero =>
      simp [CReal.Pre.nsmul]
      rfl
  | succ n ih =>
      rw [add_nsmul, one_nsmul, ih]
      simp [CReal.Pre.nsmul]
      rfl

/-- A small arithmetic helper: with δ > 0, we have
    B ≤ ⌈B/δ⌉ * δ, and with one more step,
    B ≤ (⌈B/δ⌉ + 1) * δ as well. -/
lemma nat_ceil_mul_lower {B δ : ℚ} (hδ : 0 < δ) :
    B ≤ (Nat.ceil (B / δ) : ℚ) * δ := by
  have h1 : B / δ ≤ (Nat.ceil (B / δ) : ℚ) := by
    exact_mod_cast Nat.le_ceil (B / δ)
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
  have h3 : B / δ * δ = B := div_mul_cancel₀ B (ne_of_gt hδ)
  rwa [h3] at h2

lemma nat_ceil_succ_mul_lower {B δ : ℚ} (hδ : 0 < δ) :
    B ≤ ((Nat.ceil (B / δ) + 1 : ℕ) : ℚ) * δ := by
  have base := nat_ceil_mul_lower (B := B) (δ := δ) hδ
  have add_step : (Nat.ceil (B / δ) : ℚ) * δ ≤ ((Nat.ceil (B / δ) : ℕ) + 1 : ℕ) * δ := by
    have : (Nat.ceil (B / δ) : ℚ) ≤ ((Nat.ceil (B / δ) : ℕ) + 1 : ℕ) := by norm_cast; exact Nat.le_succ _
    exact mul_le_mul_of_nonneg_right this (le_of_lt hδ)
  exact base.trans add_step

instance : Archimedean CReal := by
  constructor
  intro x y hy
  refine Quot.induction_on₂ x y (fun x_pre y_pre hy => ?_) hy
  have hy_pos_pre : CReal.Pre.Pos y_pre := by
    have : Pos (⟦y_pre⟧ - 0 : CReal) := (lt_iff_pos (0 : CReal) ⟦y_pre⟧).mp hy
    dsimp [Pos] at this
    simpa using this
  obtain ⟨K0, δ, hδ_pos, h_uniform⟩ := pos_uniform_lower_bound y_pre hy_pos_pre
  obtain ⟨K1, hK1⟩ := find_index_for_bound (by norm_num : 0 < (1 : ℚ)) hδ_pos
  let K := Nat.max K0 K1
  have hK0_le_K : K0 ≤ K := le_max_left _ _
  have hK1_le_K : K1 ≤ K := le_max_right _ _
  have h_pow_mono : (1 : ℚ) / 2 ^ K ≤ 1 / 2 ^ K1 := by
    apply one_div_le_one_div_of_le
    · exact pow_pos (by norm_num) _
    · exact (pow_le_pow_iff_right₀ rfl).mpr hK1_le_K
  have h_small_half : (1 : ℚ) / 2 ^ K < δ := lt_of_le_of_lt h_pow_mono hK1
  have h_uniform' : ∀ m : ℕ, K ≤ m → δ ≤ y_pre.approx m := by
    intro m hm
    simp_all only [one_div, le_sup_left, le_sup_right, sup_le_iff, K]
  let Bx : ℕ := x_pre.cBound
  let n := Nat.ceil ((Bx : ℚ) / δ) + 1
  have hBx_base : (Bx : ℚ) ≤ (Nat.ceil ((Bx : ℚ) / δ) : ℚ) * δ :=
    nat_ceil_mul_lower (B := (Bx : ℚ)) (δ := δ) hδ_pos
  have hBx_plus : (Bx : ℚ) + δ ≤ (n : ℚ) * δ := by
    have h_sum : (Nat.ceil ((Bx : ℚ) / δ) : ℚ) * δ + δ
        = ((Nat.ceil ((Bx : ℚ) / δ) + 1 : ℕ) : ℚ) * δ := by
      have : ((Nat.ceil ((Bx : ℚ) / δ) : ℚ) + 1) * δ
          = ((Nat.ceil ((Bx : ℚ) / δ) + 1 : ℕ) : ℚ) * δ := by
        simp [Nat.cast_add, add_mul, one_mul]
      simp [add_mul, one_mul]
    have := add_le_add_right hBx_base δ
    simpa [n, h_sum, Nat.cast_add, Nat.cast_ofNat] using this
  have h_nsmul_lower :
      (n : ℚ) * δ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 1) := by
    apply nsmul_approx_lower_bound (y := y_pre) (δ := δ) (m := K + 1) (n := n)
    intro t ht₁ _ht₂
    have hK_le : K ≤ (K + 1) + t := by
      exact Nat.le_trans (Nat.le_succ K) (Nat.le_add_right (K + 1) t)
    exact h_uniform' ((K + 1) + t) hK_le
  have h_lt : ⟦x_pre⟧ < (n : ℕ) • (⟦y_pre⟧ : CReal) := by
    rw [nsmul_def]
    apply (lt_iff_pos ⟦x_pre⟧ ⟦CReal.Pre.nsmul n y_pre⟧).mpr
    dsimp [Pos]
    refine ⟨K, ?_⟩
    have hx_abs : |x_pre.approx (K + 2)| ≤ (Bx : ℚ) := by
      simpa using x_pre.abs_approx_le_cBound (K + 2)
    have hx_le : x_pre.approx (K + 2) ≤ (Bx : ℚ) := (abs_le.mp hx_abs).2
    have h_nsmul_lower' : (n : ℚ) * δ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) := by
      apply nsmul_approx_lower_bound (y := y_pre) (δ := δ) (m := K + 2) (n := n)
      intro t ht₁ _ht₂
      have hK_le : K ≤ (K + 2) + t := by
        exact Nat.le_trans (Nat.le_add_right K 2) (Nat.le_add_right (K + 2) t)
      exact h_uniform' ((K + 2) + t) hK_le
    have h_delta_le_sub : δ ≤ (n : ℚ) * δ - (Bx : ℚ) := by
      linarith [hBx_plus]
    have h_delta_le_diff : δ ≤ (n : ℚ) * δ - x_pre.approx (K + 2) := by
      have hstep : (n : ℚ) * δ - (Bx : ℚ) ≤ (n : ℚ) * δ - x_pre.approx (K + 2) :=
        sub_le_sub_left hx_le _
      exact _root_.le_trans h_delta_le_sub hstep
    have h_sub_mono :
        (n : ℚ) * δ - x_pre.approx (K + 2)
          ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) - x_pre.approx (K + 2) :=
      sub_le_sub_right h_nsmul_lower' _
    calc
      (1 : ℚ) / 2 ^ K
          < δ := h_small_half
      _ ≤ (n : ℚ) * δ - x_pre.approx (K + 2) := h_delta_le_diff
      _ ≤ (CReal.Pre.nsmul n y_pre).approx (K + 2) - x_pre.approx (K + 2) := h_sub_mono
      _ = (CReal.Pre.add (CReal.Pre.nsmul n y_pre) (CReal.Pre.neg x_pre)).approx (K + 1) := by
          dsimp [CReal.Pre.add, CReal.Pre.neg]; ring_nf
  use n
  exact le_of_lt h_lt

namespace Pre

/-! ### Inversion (1/x) -/

/--
A pre-real x is separated from zero if we can constructively find a dyadic bound 1/2^N < |x|.
-/
def Separated (x : CReal.Pre) : Prop := ∃ N : ℕ, 1/2^N < |x.approx (N+1)|

/-- Structure to hold the witness data for separation. -/
structure InvWitness (x : CReal.Pre) where
  N : ℕ
  h_bound : 1/2^N < |x.approx (N+1)|

/--
Stability Lemma: The lower bound persists further out in the sequence.
If |x_{N+1}| > 1/2^N, then for K ≥ N+1, |x_K| > 1/2^{N+1}.
-/
lemma inv_witness_stability (x : CReal.Pre) (W : InvWitness x) (K : ℕ) (hK : W.N + 1 ≤ K) :
    1/2^(W.N+1) < |x.approx K| := by
  have h_reg := x.is_regular (W.N+1) K hK
  have h_tri : |x.approx K| ≥ |x.approx (W.N+1)| - |x.approx K - x.approx (W.N+1)| := by
    have h_triangle :
        |x.approx (W.N+1)| ≤ |x.approx (W.N+1) - x.approx K| + |x.approx K| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (abs_add_le (x.approx (W.N+1) - x.approx K) (x.approx K))
    have h_rewrite : |x.approx (W.N+1) - x.approx K| = |x.approx K - x.approx (W.N+1)| := by
      rw [abs_sub_comm]
    have h_triangle' :
        |x.approx (W.N+1)| ≤ |x.approx K - x.approx (W.N+1)| + |x.approx K| := by
      simpa [h_rewrite]
        using h_triangle
    linarith [h_triangle']
  have h_diff_le : |x.approx K - x.approx (W.N+1)| ≤ 1/2^(W.N+1) := by
    simpa [abs_sub_comm] using h_reg
  calc
    |x.approx K|
        ≥ |x.approx (W.N+1)| - |x.approx K - x.approx (W.N+1)| := h_tri
    _ ≥ |x.approx (W.N+1)| - 1/2^(W.N+1) := by
      exact (sub_le_sub_left h_diff_le _)
    _ > 1/2^W.N - 1/2^(W.N+1) := by
      linarith [W.h_bound]
    _ = 1/2^(W.N+1) := by
      field_simp [pow_succ]; ring

/--
The inverse (reciprocal) of a CReal.Pre, given a witness.
Shift S = 2N+2. (x⁻¹)ₙ := 1 / x_{n + S}.
-/
def inv (x : CReal.Pre) (W : InvWitness x) : CReal.Pre where
  approx := fun n =>
    let N := W.N
    let S := 2*N + 2
    (x.approx (n + S))⁻¹
  is_regular := by
    intro n m hnm
    let N := W.N; let S := 2*N + 2
    let Kn := n + S; let Km := m + S
    have hKnm : Kn ≤ Km := add_le_add_right hnm S
    have hKn_ge_N1 : N+1 ≤ Kn := by dsimp [Kn, S]; linarith
    have hKm_ge_N1 : N+1 ≤ Km := _root_.le_trans hKn_ge_N1 hKnm
    have h_bound_Kn := x.inv_witness_stability W Kn hKn_ge_N1
    have h_bound_Km := x.inv_witness_stability W Km hKm_ge_N1
    have h_denom : 1/2^S < |x.approx Kn * x.approx Km| := by
      have h_eq : (1 : ℚ) / 2 ^ S = (1 / 2 ^ (N + 1)) * (1 / 2 ^ (N + 1)) := by
        dsimp [S]
        simp [pow_add, one_div, mul_comm, mul_left_comm]
        ring_nf
      set d : ℚ := 1 / 2 ^ (N + 1) with hd
      have hd_pos : 0 < d := by
        have : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
        simp [d, one_div, this]
      have h_bound_Kn' : d < |x.approx Kn| := by simpa [d, hd] using h_bound_Kn
      have h_bound_Km' : d < |x.approx Km| := by simpa [d, hd] using h_bound_Km
      have h_bound_Kn_pos : 0 < |x.approx Kn| := lt_trans hd_pos h_bound_Kn'
      have h_bound_Km_pos : 0 < |x.approx Km| := lt_trans hd_pos h_bound_Km'
      have h_step1 : d * d < d * |x.approx Km| := by
        exact (mul_lt_mul_iff_right₀ hd_pos).mpr h_bound_Km'
      have h_step2 : d * |x.approx Km| < |x.approx Kn| * |x.approx Km| := by
        exact (Rat.mul_lt_mul_right h_bound_Km_pos).mpr h_bound_Kn
      have h_trans : d * d < |x.approx Kn| * |x.approx Km| := lt_trans h_step1 h_step2
      have : (1 : ℚ) / 2 ^ S = d * d := by
        simp [h_eq, d, one_div]
      simpa [this, abs_mul, mul_comm, mul_left_comm, mul_assoc]
    have h_num := x.is_regular Kn Km hKnm
    have h_ne_zero_Kn : x.approx Kn ≠ 0 := by
      intro h_eq_zero
      rw [h_eq_zero, abs_zero] at h_bound_Kn
      have h_pos : (0 : ℚ) < 1 / 2 ^ (W.N + 1) := by positivity
      have h_contra := h_pos.trans h_bound_Kn
      exact lt_irrefl 0 h_contra
    have h_ne_zero_Km : x.approx Km ≠ 0 := by
      intro h_eq_zero
      rw [h_eq_zero, abs_zero] at h_bound_Km
      have h_pos : (0 : ℚ) < 1 / 2 ^ (W.N + 1) := by positivity
      have h_contra := h_pos.trans h_bound_Km
      exact lt_irrefl 0 h_contra
    calc |(x.approx Kn)⁻¹ - (x.approx Km)⁻¹|
      = |x.approx Km - x.approx Kn| / |x.approx Kn * x.approx Km| := by
          rw [inv_sub_inv h_ne_zero_Kn h_ne_zero_Km, abs_div, abs_mul, mul_comm]
      _ ≤ (1/2^Kn) / (1/2^S) := by
        have h_num' : |x.approx Km - x.approx Kn| ≤ (1 : ℚ) / 2 ^ Kn := by
          simpa [abs_sub_comm] using h_num
        have h_den_pos : 0 < |x.approx Kn * x.approx Km| := by
          have : 0 < (1 : ℚ) / 2 ^ S := by
            have hpow : 0 < (2 : ℚ) ^ S := pow_pos (by norm_num) _
            exact div_pos (by norm_num) hpow
          exact lt_trans this h_denom
        have step1 :
            |x.approx Km - x.approx Kn| / |x.approx Kn * x.approx Km|
              ≤ (1 : ℚ) / 2 ^ Kn / |x.approx Kn * x.approx Km| :=
          div_le_div_of_le_right h_den_pos h_num'
        have step2 :
            (1 : ℚ) / 2 ^ Kn / |x.approx Kn * x.approx Km|
              ≤ (1 : ℚ) / 2 ^ Kn / ((1 : ℚ) / 2 ^ S) := by
          have ha_nonneg : 0 ≤ (1 : ℚ) / 2 ^ Kn := by
            have hpow : 0 < (2 : ℚ) ^ Kn := pow_pos (by norm_num) _
            exact le_of_lt (div_pos (by norm_num) hpow)
          have hc_pos : 0 < (1 : ℚ) / 2 ^ S := by
            have hpow : 0 < (2 : ℚ) ^ S := pow_pos (by norm_num) _
            exact div_pos (by norm_num) hpow
          exact div_le_div_of_le_left ha_nonneg hc_pos (le_of_lt h_denom)
        exact step1.trans step2
      _ = 1/2^n := by
        dsimp [Kn]; rw [pow_add]; field_simp [pow_ne_zero]

/-- Helper lemma for stability using the maximum witness. -/
lemma stability_at_max_witness (x : CReal.Pre) (W1 W2 : InvWitness x) (Nmax : ℕ) (hNmax : Nmax = max W1.N W2.N) (K : ℕ) (hK : Nmax+1 ≤ K) :
    1/2^(Nmax+1) < |x.approx K| := by
  cases le_total W1.N W2.N with
  | inl h_le => rw [hNmax, max_eq_right h_le] at hK ⊢; exact x.inv_witness_stability W2 K hK
  | inr h_le => rw [hNmax, max_eq_left h_le] at hK ⊢; exact x.inv_witness_stability W1 K hK

/--
The definition of the inverse is independent of the chosen witness.
-/
theorem inv_witness_irrelevant (x : CReal.Pre) (W1 W2 : InvWitness x) :
    CReal.Pre.Equiv (CReal.Pre.inv x W1) (CReal.Pre.inv x W2) := by
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  let I1 := CReal.Pre.inv x W1; let I2 := CReal.Pre.inv x W2
  let N1 := W1.N; let N2 := W2.N
  let Nmax := max N1 N2; let Nmin := min N1 N2
  let D := 2 * (Nmax - Nmin)
  have hε3 : 0 < ε / 3 := by exact div_pos hε (by norm_num)
  obtain ⟨K_D, hK_D_bound⟩ : ∃ K, (2^D:ℚ) / 2^K < ε/3 := by
    have one_lt_two : (1 : ℚ) < 2 := by norm_num
    rcases pow_unbounded_of_one_lt ((2^D:ℚ) / (ε/3)) one_lt_two with ⟨K, hK⟩
    use K
    apply (div_lt_iff (pow_pos (by norm_num) _)).mpr
    have hh : (2^D:ℚ) / (ε/3) < 2^K := hK
    have hstep := (div_lt_iff hε3).1 hh
    simpa [mul_comm] using hstep
  let K := max (n+1) K_D
  have h_n1_le_K : n+1 ≤ K := le_max_left _ _
  have h_KD_le_K : K_D ≤ K := le_max_right _ _
  let K1' := K + 2*N1 + 2; let K2' := K + 2*N2 + 2
  have hK1'_ge : N1 + 1 ≤ K1' := by dsimp [K1']; linarith
  have hK2'_ge : N2 + 1 ≤ K2' := by dsimp [K2']; linarith
  have h_bound_K1' := x.inv_witness_stability W1 K1' hK1'_ge
  have h_bound_K2' := x.inv_witness_stability W2 K2' hK2'_ge
  have h_denom' : 1 / 2 ^ (2 * Nmax + 2) < |x.approx K1' * x.approx K2'| := by
    have h_mul_lt :
        (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
          < |x.approx K1'| * |x.approx K2'| := by
      have hposK1 : 0 < |x.approx K1'| := lt_trans (by positivity) h_bound_K1'
      have hposK2 : 0 < |x.approx K2'| := lt_trans (by positivity) h_bound_K2'
      have step1 :
          (1 : ℚ) / 2 ^ (N1 + 1) * (1 / 2 ^ (N2 + 1))
            < |x.approx K1'| * (1 / 2 ^ (N2 + 1)) :=
        mul_lt_mul_of_pos_right h_bound_K1' (by positivity)
      have step2 :
          |x.approx K1'| * (1 / 2 ^ (N2 + 1))
            < |x.approx K1'| * |x.approx K2'| :=
        mul_lt_mul_of_pos_left h_bound_K2' hposK1
      exact step1.trans step2
    have h_eq : (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
                = (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by
      have hden :
          (2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1) = 2 ^ (N1 + N2 + 2) := by
        calc
          (2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1)
              = (2 : ℚ) ^ ((N1 + 1) + (N2 + 1)) := by
                  simpa using (pow_add (2 : ℚ) (N1 + 1) (N2 + 1)).symm
          _ = 2 ^ (N1 + N2 + 2) := by
                  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      calc
        (1 : ℚ) / 2 ^ (N1 + 1) * ((1 : ℚ) / 2 ^ (N2 + 1))
            = (1 : ℚ) / ((2 : ℚ) ^ (N1 + 1) * 2 ^ (N2 + 1)) := by
                field_simp
        _ = (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by simp [hden]
    have h_exp_le : N1 + N2 + 2 ≤ 2 * Nmax + 2 := by
      have h1 : N1 ≤ Nmax := le_max_left _ _
      have h2 : N2 ≤ Nmax := le_max_right _ _
      have hsum : N1 + N2 ≤ Nmax + Nmax := add_le_add h1 h2
      simpa [two_mul] using add_le_add_right hsum 2
    have h_pow_mono :
        (1 : ℚ) / 2 ^ (2 * Nmax + 2) ≤ (1 : ℚ) / 2 ^ (N1 + N2 + 2) := by
      exact one_div_pow_le_one_div_pow_of_le rfl h_exp_le
    have h_right_aux : (1 : ℚ) / 2 ^ (N1 + N2 + 2) < |x.approx K1'| * |x.approx K2'| := by
      simp_all only [div_pos_iff_of_pos_left, Nat.ofNat_pos, le_sup_left, le_sup_right, add_le_add_iff_right, one_div,
        D, Nmax, N1, N2, Nmin, K, K1', K2']
    have h_right : (1 : ℚ) / 2 ^ (N1 + N2 + 2) < |x.approx K1' * x.approx K2'| := by
      simpa [abs_mul] using h_right_aux
    exact lt_of_le_of_lt h_pow_mono h_right
  have h_num' := CReal.abs_approx_diff_le x K1' K2'
  have h_diff_K : |I1.approx K - I2.approx K| < ε/3 := by
    have h_ne_zero_K1' : x.approx K1' ≠ 0 := by
      intro h0
      have : 0 < |x.approx K1'| := lt_trans (by positivity) h_bound_K1'
      have : |x.approx K1'| ≠ 0 := ne_of_gt this
      simp [h0, abs_zero] at this
    have h_ne_zero_K2' : x.approx K2' ≠ 0 := by
      intro h0
      have : 0 < |x.approx K2'| := lt_trans (by positivity) h_bound_K2'
      have : |x.approx K2'| ≠ 0 := ne_of_gt this
      simp [h0, abs_zero] at this
    have h_calc := calc
      |I1.approx K - I2.approx K|
        = |x.approx K2' - x.approx K1'| / |x.approx K1' * x.approx K2'| := by
          dsimp [I1, I2, CReal.Pre.inv]
          change |(x.approx K1')⁻¹ - (x.approx K2')⁻¹|
                = |x.approx K2' - x.approx K1'| / |x.approx K1' * x.approx K2'|
          rw [inv_sub_inv h_ne_zero_K1' h_ne_zero_K2', abs_div]
      _ ≤ (1 / 2 ^ (min K1' K2')) / |x.approx K1' * x.approx K2'| := by
        have h_den_pos : 0 < |x.approx K1' * x.approx K2'| := lt_trans (by positivity) h_denom'
        have h_num'' : |x.approx K2' - x.approx K1'| ≤ 1 / 2 ^ (min K1' K2') := by
          simpa [abs_sub_comm] using h_num'
        exact CReal.div_le_div_of_le (hc := h_den_pos) h_num''
      _ ≤ (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2)) := by
        have ha : 0 ≤ (1 : ℚ) / 2 ^ (min K1' K2') := by positivity
        have hc : 0 < (1 : ℚ) / 2 ^ (2 * Nmax + 2) := by positivity
        have h_le : (1 : ℚ) / 2 ^ (2 * Nmax + 2) ≤ |x.approx K1' * x.approx K2'| := le_of_lt h_denom'
        exact CReal.div_le_div_of_le_left (a := (1 : ℚ) / 2 ^ (min K1' K2')) ha hc h_le
    have h_bound_simplified :
        (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2)) = (2 ^ D : ℚ) / 2 ^ K := by
      have h_min_K' : min K1' K2' = K + 2 * Nmin + 2 := by
        dsimp [K1', K2', Nmin]
        cases le_total N1 N2 with
        | inl hle =>
            have hmin : min N1 N2 = N1 := by
              exact min_eq_left hle
            have horder : 2 * N1 + 2 ≤ 2 * N2 + 2 := by
              exact add_le_add_right (Nat.mul_le_mul_left 2 hle) 2
            have hmin' : min (K + (2 * N1 + 2)) (K + (2 * N2 + 2)) = K + (2 * N1 + 2) :=
              min_eq_left (Nat.add_le_add_left horder K)
            simpa [hmin, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmin'
        | inr hle =>
            have hmin : min N1 N2 = N2 := by
              exact min_eq_right hle
            have horder : 2 * N2 + 2 ≤ 2 * N1 + 2 := by
              exact add_le_add_right (Nat.mul_le_mul_left 2 hle) 2
            have hmin' : min (K + (2 * N1 + 2)) (K + (2 * N2 + 2)) = K + (2 * N2 + 2) :=
              min_eq_right (Nat.add_le_add_left horder K)
            simpa [hmin, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmin'
      have h_exp_diff : 2 * Nmax + 2 = D + (2 * Nmin + 2) := by
        dsimp [D]
        have hminle : Nmin ≤ Nmax := by
          dsimp [Nmin, Nmax]
          cases le_total N1 N2 with
          | inl h => simpa [min_eq_left h, max_eq_right h]
          | inr h => simpa [min_eq_right h, max_eq_left h]
        have hsplit : Nmax = (Nmax - Nmin) + Nmin := by
          simpa using (Nat.sub_add_cancel hminle).symm
        have h := congrArg (fun t => 2 * t + 2) hsplit
        calc
          2 * Nmax + 2 = 2 * ((Nmax - Nmin) + Nmin) + 2 := by
            simpa using h
          _ = (2 * (Nmax - Nmin) + 2 * Nmin) + 2 := by
            simp [Nat.mul_add]
          _ = 2 * (Nmax - Nmin) + (2 * Nmin + 2) := by
            ac_rfl
      calc
        (1 / 2 ^ (min K1' K2')) / (1 / 2 ^ (2 * Nmax + 2))
            = (1 / 2 ^ (K + 2 * Nmin + 2)) / (1 / 2 ^ (D + (2 * Nmin + 2))) := by
                simp [h_min_K', h_exp_diff]
        _ = (2 : ℚ) ^ (D + (2 * Nmin + 2)) / (2 : ℚ) ^ (K + 2 * Nmin + 2) := by
              simp [div_eq_mul_inv, mul_comm]
        _ = ((2 : ℚ) ^ D * (2 : ℚ) ^ (2 * Nmin + 2)) /
            ((2 : ℚ) ^ K * (2 : ℚ) ^ (2 * Nmin + 2)) := by
              simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
        _ = (2 : ℚ) ^ D / (2 : ℚ) ^ K := by
              have hpow_ne : (2 : ℚ) ^ (2 * Nmin + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
              field_simp [hpow_ne]
    rw [h_bound_simplified] at h_calc
    have h_K_bound : (2^D:ℚ) / 2^K ≤ (2^D:ℚ) / 2^K_D := by
      have ha : 0 ≤ (2 ^ D : ℚ) := by positivity
      have hc : 0 < (2 : ℚ) ^ K_D := by positivity
      have h_le_pow : (2 : ℚ) ^ K_D ≤ 2 ^ K :=
        (pow_le_pow_iff_right₀ rfl).mpr h_KD_le_K
      exact CReal.div_le_div_of_le_left (a := (2 ^ D : ℚ)) ha hc h_le_pow
    linarith [h_calc, h_K_bound, hK_D_bound]
  have h_reg1 := I1.is_regular (n+1) K h_n1_le_K
  have h_reg2 := I2.is_regular (n+1) K h_n1_le_K
  have h_diff_K_le : |I1.approx K - I2.approx K| ≤ ε/3 := le_of_lt h_diff_K
  have h_step1 :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ |I1.approx (n+1) - I1.approx K| + |I1.approx K - I2.approx (n+1)| :=
    abs_sub_le _ _ _
  have h_step2 :
      |I1.approx K - I2.approx (n+1)|
        ≤ |I1.approx K - I2.approx K| + |I2.approx K - I2.approx (n+1)| := by
    simpa using abs_sub_le (I1.approx K) (I2.approx K) (I2.approx (n+1))
  have h_tri :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ |I1.approx (n+1) - I1.approx K|
          + (|I1.approx K - I2.approx K| + |I2.approx K - I2.approx (n+1)|) := by
    exact _root_.le_trans h_step1 (_root_.add_le_add_left h_step2 _)
  have h_reg2' : |I2.approx K - I2.approx (n+1)| ≤ 1 / 2 ^ (n+1) := by
    simpa [abs_sub_comm] using h_reg2
  have h_final_bound :
      |I1.approx (n+1) - I2.approx (n+1)|
        ≤ 1/2^(n+1) + (ε/3 + 1/2^(n+1)) := by
    apply _root_.le_trans h_tri
    gcongr
  calc
    |I1.approx (n+1) - I2.approx (n+1)|
      ≤ 1/2^(n+1) + (ε/3 + 1/2^(n+1)) := h_final_bound
    _ = 1/2^n + ε/3 := by field_simp [pow_succ]; ring
    _ ≤ 1/2^n + ε := by gcongr; linarith

lemma abs_lower_of_abs_sub_le {a b t : ℚ} (h : |a - b| ≤ t) :
    |b| ≥ |a| - t := by
  have h' : -|b - a| ≤ |b| - |a| :=
    (abs_le.mp (abs_abs_sub_abs_le_abs_sub b a)).1
  have h0 : |a| - |b - a| ≤ |b| := by
    have := _root_.add_le_add_right h' |a|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hba : |b - a| ≤ t := by simpa [abs_sub_comm] using h
  have hmono' : |a| - t ≤ |a| - |b - a| := by
    have := neg_le_neg hba
    have := _root_.add_le_add_left this |a|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact (_root_.le_trans hmono' h0)

lemma abs_lower_via_equiv_pos
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) {K : ℕ} (hK : 0 < K) :
    |y.approx K| ≥ |x.approx K| - 1 / 2 ^ (K - 1) := by
  have hx : |x.approx K - y.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hK)] using hxy (K - 1)
  exact abs_lower_of_abs_sub_le hx

lemma separated_of_equiv_left
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) (hx : Separated x) : Separated y := by
  rcases hx with ⟨N, hN⟩
  let Wx : InvWitness x := ⟨N, hN⟩
  let K := N + 3
  have hK : 0 < K := by exact Nat.succ_pos _
  have hxK : (1 : ℚ) / 2 ^ (N + 1) < |x.approx K| := by
    have hK_ge : Wx.N + 1 ≤ K := by
      dsimp [K]
      have : N + 1 ≤ N + 3 := Nat.add_le_add_left (by decide : 1 ≤ 3) N
      simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, add_le_add_iff_left, Nat.one_le_ofNat, K,
        Wx]
    exact inv_witness_stability x Wx K hK_ge
  have hyK_lower : |y.approx K| ≥ |x.approx K| - (1 : ℚ) / 2 ^ (K - 1) :=
    abs_lower_via_equiv_pos hxy hK
  have hdiff : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ (N + 2) = 1 / 2 ^ (N + 2) := by
    simpa using CReal.two_halves_to_succ_sub N
  have hKpred : K - 1 = N + 2 := by
    simp [K]
  have : (1 : ℚ) / 2 ^ (N + 2) < |x.approx K| - 1 / 2 ^ (N + 2) := by
    have hstep := sub_lt_sub_right hxK ((1 : ℚ) / 2 ^ (N + 2))
    simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, one_div, Nat.add_one_sub_one, ge_iff_le,
      tsub_le_iff_right, K]
  have hyK : (1 : ℚ) / 2 ^ (N + 2) < |y.approx K| := by
    have hyK' : |x.approx K| - (1 : ℚ) / 2 ^ (N + 2) ≤ |y.approx K| := by
      simpa [hKpred] using hyK_lower
    exact lt_of_lt_of_le this hyK'
  refine ⟨N + 2, ?_⟩
  simpa [K, Nat.add_assoc] using hyK

-- The reverse direction follows by symmetry of Equiv.
lemma separated_of_equiv_right
    {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) (hy : Separated y) : Separated x :=
  separated_of_equiv_left (CReal.Pre.equiv_symm hxy) hy

-- Now the main equivalence is just two lines:
theorem separated_well_defined (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) :
  CReal.Pre.Separated x ↔ CReal.Pre.Separated y := by
  constructor
  · exact CReal.Pre.separated_of_equiv_left hxy
  · exact CReal.Pre.separated_of_equiv_right hxy

/-- Helper to construct a witness for y based on a witness for x, assuming x ≈ y. -/
def transfer_witness (x y : CReal.Pre) (hxy : CReal.Pre.Equiv x y) (Wx : InvWitness x) : InvWitness y :=
  let N := Wx.N
  let M := N + 2
  let K := N + 3
  have hK_ge : Wx.N + 1 ≤ K := by
    dsimp [K]
    exact Nat.add_le_add_left (by decide : 1 ≤ 3) N
  have h_xK : (1 : ℚ) / 2 ^ (N + 1) < |x.approx K| :=
    inv_witness_stability x Wx K hK_ge
  have hK_pos : 0 < K := Nat.succ_pos _
  have hyK_lower : |y.approx K| ≥ |x.approx K| - (1 : ℚ) / 2 ^ (K - 1) :=
    abs_lower_via_equiv_pos hxy hK_pos
  have hKpred : K - 1 = N + 2 := by simp [K]
  have hdiff : (1 : ℚ) / 2 ^ (N + 1) - 1 / 2 ^ (N + 2) = 1 / 2 ^ (N + 2) := by
    simpa using CReal.two_halves_to_succ_sub N
  have h_strict : (1 : ℚ) / 2 ^ (N + 2) < |x.approx K| - 1 / 2 ^ (N + 2) := by
    have := sub_lt_sub_right h_xK ((1 : ℚ) / 2 ^ (N + 2))
    simp_all only [add_le_add_iff_left, Nat.one_le_ofNat, one_div, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos,
      or_true, Nat.add_one_sub_one, ge_iff_le, tsub_le_iff_right, K, N]
  have h_mono : |x.approx K| - (1 : ℚ) / 2 ^ (N + 2) ≤ |y.approx K| := by
    simpa [hKpred] using hyK_lower
  have hyK : (1 : ℚ) / 2 ^ (N + 2) < |y.approx K| := lt_of_lt_of_le h_strict h_mono
  ⟨M, by
    simpa [M, K, Nat.add_assoc] using hyK⟩

namespace CReal.Pre

-- A convenient algebraic identity for inverse differences, with absolute values.
lemma inv_abs_diff_formula (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) :
  |r⁻¹ - s⁻¹| = |s - r| / |r*s| := by
  rw [inv_sub_inv hr hs, abs_div, abs_mul, mul_comm]

-- If |r - s| ≤ α and we have positive lower bounds Lr ≤ |r|, Ls ≤ |s|,
-- then the inverse difference is controlled by α / (Lr*Ls).
lemma inv_sub_inv_bound_of_bounds {r s Lr Ls α : ℚ}
  (hα : |r - s| ≤ α)
  (hLr_pos : 0 < Lr) (hLs_pos : 0 < Ls)
  (hLr : Lr ≤ |r|) (hLs : Ls ≤ |s|) :
  |r⁻¹ - s⁻¹| ≤ α / (Lr * Ls) := by
  have hr_ne : r ≠ 0 := by
    have : 0 < |r| := lt_of_lt_of_le hLr_pos hLr
    exact (abs_ne_zero.mp (ne_of_gt this))
  have hs_ne : s ≠ 0 := by
    have : 0 < |s| := lt_of_lt_of_le hLs_pos hLs
    exact (abs_ne_zero.mp (ne_of_gt this))
  have hα_nn : 0 ≤ α := (abs_nonneg _).trans hα
  have hden_pos : 0 < |r * s| := by
    have hr : 0 < |r| := lt_of_lt_of_le hLr_pos hLr
    have hs : 0 < |s| := lt_of_lt_of_le hLs_pos hLs
    simpa [abs_mul] using (_root_.mul_pos hr hs)
  have hden_ge : (Lr * Ls) ≤ |r * s| := by
    have hLs_nn : 0 ≤ Ls := le_of_lt hLs_pos
    have h1 : Lr * Ls ≤ |r| * Ls := by
      exact mul_le_mul_of_nonneg_right hLr hLs_nn
    have h2 : |r| * Ls ≤ |r| * |s| := by
      exact mul_le_mul_of_nonneg_left hLs (abs_nonneg _)
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h1.trans h2
  have hα' : |s - r| ≤ α := by simpa [abs_sub_comm] using hα
  calc
    |r⁻¹ - s⁻¹|
        = |s - r| / |r * s| := inv_abs_diff_formula r s hr_ne hs_ne
    _ ≤ α / |r * s| := by
      exact div_le_div_of_le_right hden_pos hα'
    _ ≤ α / (Lr * Ls) := by
      exact div_le_div_of_le_left hα_nn (_root_.mul_pos hLr_pos hLs_pos) hden_ge

-- Extract a non-strict lower bound from stability (witness)
lemma abs_lower_from_witness (x : CReal.Pre) (W : InvWitness x) {K : ℕ} (hK : W.N + 1 ≤ K) :
  (1 : ℚ) / 2 ^ (W.N + 1) ≤ |x.approx K| :=
  le_of_lt (inv_witness_stability x W K hK)

-- Equivalence bound at a single index K (needs K > 0 to rewrite K = (K-1)+1)
lemma equiv_at_index_bound {x y : CReal.Pre}
  (hxy : CReal.Pre.Equiv x y) {K : ℕ} (hKpos : 0 < K) :
  |x.approx K - y.approx K| ≤ (1 : ℚ) / 2 ^ (K - 1) := by
  have h : K - 1 + 1 = K := Nat.sub_add_cancel (Nat.succ_le_of_lt hKpos)
  simpa [h] using hxy (K - 1)

-- “Same-index” inverse bound from Equiv + denominator lower bounds.
lemma inv_same_index_bound_of_equiv
  {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y)
  {K : ℕ} {Lx Ly : ℚ}
  (hKpos : 0 < K)
  (hLx_pos : 0 < Lx) (hLy_pos : 0 < Ly)
  (hLx : Lx ≤ |x.approx K|) (hLy : Ly ≤ |y.approx K|) :
  |(x.approx K)⁻¹ - (y.approx K)⁻¹| ≤ ((1 : ℚ) / 2 ^ (K - 1)) / (Lx * Ly) := by
  have hα := equiv_at_index_bound (x := x) (y := y) hxy hKpos
  exact inv_sub_inv_bound_of_bounds (r := x.approx K) (s := y.approx K)
    (Lr := Lx) (Ls := Ly) (α := (1 : ℚ) / 2 ^ (K - 1))
    hα hLx_pos hLy_pos hLx hLy

-- “Two-index” inverse bound for a single pre-real using regularity + lower bounds.
lemma inv_two_index_bound_of_regular_and_bounds
  (x : CReal.Pre) (K K' : ℕ)
  {L : ℚ} (hL_pos : 0 < L)
  (hL_K  : L ≤ |x.approx K|)
  (hL_K' : L ≤ |x.approx K'|)
  (h_reg : |x.approx K - x.approx K'| ≤ (1 : ℚ) / 2 ^ (min K K')) :
  |(x.approx K)⁻¹ - (x.approx K')⁻¹| ≤ ((1 : ℚ) / 2 ^ (min K K')) / (L * L) := by
  exact inv_sub_inv_bound_of_bounds (r := x.approx K) (s := x.approx K')
    (Lr := L) (Ls := L) (α := (1 : ℚ) / 2 ^ (min K K'))
    h_reg hL_pos hL_pos hL_K hL_K'

-- algebra helpers for dyadic powers
lemma one_div_pow_mul_one_div_pow (a b : ℕ) :
  (1 : ℚ) / 2 ^ a * (1 / 2 ^ b) = (1 : ℚ) / 2 ^ (a + b) := by
  field_simp [div_eq_mul_inv, pow_add, mul_comm, mul_left_comm, mul_assoc]; exact pow_add 2 a b

lemma div_one_div_pow_simp (a b : ℕ) :
  ((1 : ℚ) / 2 ^ (a + b)) / ((1 : ℚ) / 2 ^ b) = (1 : ℚ) / 2 ^ a := by
  field_simp [div_eq_mul_inv, pow_add, mul_comm, mul_left_comm, mul_assoc]; ring_nf

theorem inv_respects_equiv
    (x y : CReal.Pre)
    (hxy : CReal.Pre.Equiv x y)
    (Wx : CReal.Pre.InvWitness x) (Wy : CReal.Pre.InvWitness y) :
    CReal.Pre.Equiv (CReal.Pre.inv x Wx) (CReal.Pre.inv y Wy) := by
  let W'y := CReal.Pre.transfer_witness x y hxy Wx
  have h_irrel_y : CReal.Pre.Equiv (CReal.Pre.inv y Wy) (CReal.Pre.inv y W'y) :=
    CReal.Pre.inv_witness_irrelevant y Wy W'y
  have h_core : CReal.Pre.Equiv (CReal.Pre.inv x Wx) (CReal.Pre.inv y W'y) := by
    intro n
    let Nx := Wx.N
    let L  : ℚ := (1 : ℚ) / 2 ^ (Nx + 1)
    let k  := n + 1
    let Sx := 2 * Nx + 2
    let Sy := 2 * (Nx + 2) + 2
    let Kx := k + Sx
    let Ky := k + Sy
    have hKx_le_Ky : Kx ≤ Ky := by
      dsimp [Kx, Ky, Sx, Sy, k]
      have : 2 * Nx + 2 ≤ 2 * Nx + 6 := by
        simp [Nat.add_assoc, two_mul]
      exact Nat.add_le_add_left this (n + 1)
    have hL_Kx : L ≤ |x.approx Kx| := by
      have : Nx + 1 ≤ Kx := by
        dsimp [Kx, Sx, k]
        have hNx_le_2Nx : Nx ≤ 2 * Nx := by
          simpa [Nat.mul_comm, one_mul] using
            Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
        have hNx1_le_2Nx1 : Nx + 1 ≤ 2 * Nx + 1 :=
          add_le_add_right hNx_le_2Nx 1
        have hNx1_le_2Nx2 : Nx + 1 ≤ 2 * Nx + 2 :=
          _root_.le_trans hNx1_le_2Nx1 (Nat.le_succ (2 * Nx + 1))
        exact _root_.le_trans hNx1_le_2Nx2 (Nat.le_add_left _ _)
      simpa [L] using CReal.Pre.abs_lower_from_witness x Wx this
    have hL_Ky_x : L ≤ |x.approx Ky| := by
      have : Nx + 1 ≤ Ky := by
        dsimp [Ky, Sy, k]
        have h1 : Nx + 1 ≤ Nx + 5 :=
          Nat.add_le_add_left (by decide : 1 ≤ 5) Nx
        have h2 : Nx + 5 ≤ 2 * Nx + 6 := by
          have hNx_le_2Nx : Nx ≤ 2 * Nx := by
            simpa [one_mul, Nat.mul_comm] using
              Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
          have h2' : Nx + 5 ≤ 2 * Nx + 5 := add_le_add_right hNx_le_2Nx 5
          exact _root_.le_trans h2' (Nat.le_succ _)
        have hNxSy : Nx + 1 ≤ Sy := by
          dsimp [Sy]; exact _root_.le_trans h1 h2
        have hSy_le : Sy ≤ k + Sy := Nat.le_add_left _ _
        exact _root_.le_trans hNxSy hSy_le
      simpa [L] using CReal.Pre.abs_lower_from_witness x Wx this
    let Ly : ℚ := (1 : ℚ) / 2 ^ (Nx + 3)
    have hLy_Ky : Ly ≤ |y.approx Ky| := by
      have hWyN : W'y.N = Nx + 2 := by
        dsimp [W'y, CReal.Pre.transfer_witness]
      have hWyN_le : W'y.N + 1 ≤ Ky := by
        have h1 : Nx + 3 ≤ 2 * Nx + 6 := by
          have hNx_le_2Nx : Nx ≤ 2 * Nx := by
            have h := Nat.mul_le_mul_left Nx (by decide : 1 ≤ 2)
            simpa [Nat.mul_comm, Nat.one_mul] using h
          have h3_le_6 : 3 ≤ 6 := by decide
          exact add_le_add hNx_le_2Nx h3_le_6
        have h2 : 2 * Nx + 6 ≤ k + (2 * Nx + 6) := Nat.le_add_left _ _
        have hKy : Ky = k + (2 * Nx + 6) := by
          dsimp [Ky, Sy, k]; simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        have : Nx + 3 ≤ Ky := by simpa [hKy] using (Nat.le_add_left_of_le h1)
        simpa [hWyN] using this
      have := CReal.Pre.abs_lower_from_witness y W'y (K := Ky) (hK := hWyN_le)
      simpa [Ly, hWyN] using this
    have h_reg_x : |x.approx Kx - x.approx Ky| ≤ (1 : ℚ) / 2 ^ (min Kx Ky) := by
      simpa [abs_sub_comm] using CReal.abs_approx_diff_le x Kx Ky
    have h_term1 :=
      CReal.Pre.inv_two_index_bound_of_regular_and_bounds x Kx Ky
        (hL_pos := by positivity) hL_Kx hL_Ky_x h_reg_x
    have h_term1' : |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ k := by
      have hmin : min Kx Ky = Kx := min_eq_left hKx_le_Ky
      have hLL : L * L = (1 : ℚ) / 2 ^ (2 * Nx + 2) := by
        simpa [L, two_mul, pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, div_eq_mul_inv] using
          CReal.Pre.one_div_pow_mul_one_div_pow (Nx + 1) (Nx + 1)
      have hcore :
          |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹|
            ≤ ((1 : ℚ) / 2 ^ Kx) / ((1 : ℚ) / 2 ^ (2 * Nx + 2)) := by
        simpa [hmin, hLL] using h_term1
      have hKx : Kx = k + (2 * Nx + 2) := by
        dsimp [Kx, Sx, k]
      have hsimps :
          ((1 : ℚ) / 2 ^ Kx) / ((1 : ℚ) / 2 ^ (2 * Nx + 2)) = (1 : ℚ) / 2 ^ k := by
        simpa [hKx] using CReal.Pre.div_one_div_pow_simp k (2 * Nx + 2)
      simp_all only [add_le_add_iff_left, add_le_add_iff_right, Nat.ofNat_pos, mul_le_mul_iff_right₀,
        le_add_iff_nonneg_right, zero_le, one_div, inf_of_le_left, div_inv_eq_mul, ge_iff_le,
        W'y, Kx, k, Sx, Nx, Ky, Sy, L, Ly]
    have hKpos : 0 < Ky := by dsimp [Ky]; exact Nat.succ_pos _
    have h_term2 :=
      CReal.Pre.inv_same_index_bound_of_equiv (x := x) (y := y) hxy
        (K := Ky) (Lx := L) (Ly := Ly)
        (hKpos := by exact Nat.succ_pos _) (hLx_pos := by positivity) (hLy_pos := by positivity)
        (hLx := hL_Ky_x) (hLy := hLy_Ky)
    have h_term2' : |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
      have hden : L * Ly = (1 : ℚ) / 2 ^ (2 * Nx + 4) := by
        simpa [L, Ly, two_mul, pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, div_eq_mul_inv] using
          CReal.Pre.one_div_pow_mul_one_div_pow (Nx + 1) (Nx + 3)
      have hKy_eq : Ky = k + (2 * Nx + 6) := by
        dsimp [Ky, Sy, k]; simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hKy_pred : Ky - 1 = k + (2 * Nx + 5) := by
        have : Ky = (k + (2 * Nx + 5)) + 1 := by
          rfl
        simp [this]
      have hdiv :
          (1 : ℚ) / 2 ^ (Ky - 1) / (L * Ly) = (1 : ℚ) / 2 ^ (k + 1) := by
        have : (Ky - 1) = (k + 1) + (2 * Nx + 4) := by
          simp +arith [*]
        simpa [this, hden] using CReal.Pre.div_one_div_pow_simp (k + 1) (2 * Nx + 4)
      have hk : k + 1 = n + 2 := by simp [k]
      have : |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| ≤ (1 : ℚ) / 2 ^ (k + 1) := by
        simp_all only [add_le_add_iff_left, add_le_add_iff_right, Nat.ofNat_pos, mul_le_mul_iff_right₀,
          le_add_iff_nonneg_right, zero_le, one_div, inf_of_le_left, add_pos_iff, _root_.zero_lt_one, or_true,
          mul_pos_iff_of_pos_left, or_self, Nat.add_succ_sub_one, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
          div_inv_eq_mul, W'y, Kx, k, Sx, Nx, Ky, Sy, L, Ly]
      simpa [hk] using this
    have := calc
      |(x.approx Kx)⁻¹ - (y.approx Ky)⁻¹|
          ≤ |(x.approx Kx)⁻¹ - (x.approx Ky)⁻¹| +
            |(x.approx Ky)⁻¹ - (y.approx Ky)⁻¹| := by
              simpa using abs_sub_le ((x.approx Kx)⁻¹) ((x.approx Ky)⁻¹) ((y.approx Ky)⁻¹)
      _ ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (n + 2) := add_le_add h_term1' h_term2'
      _ ≤ (1 : ℚ) / 2 ^ n := by
            have hk : k = n + 1 := rfl
            have hmono : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
              simpa using inv_pow_antitone_succ (n + 1)
            calc
              (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ (n + 2)
                  = (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) := by simp [hk]
              _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by gcongr
              _ = (1 : ℚ) / 2 ^ n := two_halves_to_pred n
    simpa [CReal.Pre.inv, CReal.Pre.mul, k, Kx, Ky] using this
  exact CReal.Pre.equiv_trans h_core (CReal.Pre.equiv_symm h_irrel_y)

/-- The cancellation property: x * (1/x) ≈ 1. -/
theorem mul_inv_cancel (x : CReal.Pre) (W : CReal.Pre.InvWitness x) :
  CReal.Pre.Equiv (x.mul (CReal.Pre.inv x W)) CReal.Pre.one := by
  intro n
  let inv_x := CReal.Pre.inv x W
  let prod := x.mul inv_x
  let N := W.N
  let L : ℚ := (1:ℚ) / 2^(N+1)
  let M := N + n + 2
  have h_M_pos : 0 < M := by positivity
  have h_diff_M : |prod.approx M - 1| ≤ 1/2^(n+1) := by
    dsimp [CReal.Pre.mul, CReal.Pre.inv, CReal.Pre.one]
    let S_inv := 2*N + 2
    let S_mul := x.mulShift inv_x
    let K := M + S_mul
    let K_final := K + S_inv
    have h_K_final_ge : N + 1 ≤ K_final := by
      dsimp [K_final, K, S_inv, M]; linarith
    have h_bound_K_final := inv_witness_stability x W K_final h_K_final_ge
    have h_den_pos : 0 < |x.approx K_final| := lt_trans (by positivity) h_bound_K_final
    have hx_ne : x.approx K_final ≠ 0 := by
      exact abs_pos.mp h_den_pos
    have h_num_reg : |x.approx K - x.approx K_final| ≤ (1 : ℚ) / 2 ^ K := by
      simpa [abs_sub_comm] using x.is_regular K K_final (Nat.le_add_right _ _)
    have h_eq_div :
        |x.approx K * (x.approx K_final)⁻¹ - 1|
          = |x.approx K - x.approx K_final| * |x.approx K_final|⁻¹ := by
      have h1 :
          x.approx K / x.approx K_final - 1
            = (x.approx K - x.approx K_final) / x.approx K_final := by
        calc
          x.approx K / x.approx K_final - 1
              = x.approx K / x.approx K_final - x.approx K_final / x.approx K_final := by
                  simp [div_self hx_ne]
          _ = (x.approx K - x.approx K_final) / x.approx K_final := by
                  simpa using (sub_div (x.approx K) (x.approx K_final) (x.approx K_final)).symm
      calc
        |x.approx K * (x.approx K_final)⁻¹ - 1|
            = |x.approx K / x.approx K_final - 1| := by
                simp [div_eq_mul_inv, sub_eq_add_neg, add_comm]
        _ = |(x.approx K - x.approx K_final) / x.approx K_final| := by
                simp [h1]
        _ = |x.approx K - x.approx K_final| / |x.approx K_final| := by
                simp [abs_div]
        _ = |x.approx K - x.approx K_final| * |x.approx K_final|⁻¹ := by
                simp [div_eq_mul_inv]
    have h_num_step :
        |(x.approx K - x.approx K_final) / x.approx K_final|
          ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
      have := div_le_div_of_le_right h_den_pos h_num_reg
      simpa [abs_div] using this
    have h_den_step :
        ((1 : ℚ) / 2 ^ K) / |x.approx K_final| ≤ ((1 : ℚ) / 2 ^ K) / L := by
      have ha : 0 ≤ (1 : ℚ) / 2 ^ K := by
        have hp : 0 < (2 : ℚ) ^ K := pow_pos (by norm_num) _
        exact div_nonneg (by norm_num) (le_of_lt hp)
      have h1 : |x.approx K * (x.approx K_final)⁻¹ - 1|
                ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
        simpa [h_eq_div, div_eq_mul_inv] using h_num_step
      have hLpos : 0 < L := by
        have hpow : 0 < (2 : ℚ) ^ (N + 1) := pow_pos (by norm_num) _
        exact div_pos (by norm_num) hpow
      have h_le : L ≤ |x.approx K_final| := by
        exact le_of_lt (by simpa [L] using h_bound_K_final)
      have h_inv : (1 : ℚ) / |x.approx K_final| ≤ 1 / L :=
        one_div_le_one_div_of_le hLpos h_le
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h_inv ha
    have h_main :
        |x.approx K * (x.approx K_final)⁻¹ - 1|
          ≤ ((1 : ℚ) / 2 ^ K) / L := by
      have h1 : |x.approx K * (x.approx K_final)⁻¹ - 1|
                ≤ ((1 : ℚ) / 2 ^ K) / |x.approx K_final| := by
        rw [h_eq_div]
        have h_nonneg : 0 ≤ |x.approx K_final|⁻¹ := by
          exact inv_nonneg.mpr (abs_nonneg _)
        have h_mul := mul_le_mul_of_nonneg_right h_num_reg h_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          using h_mul
      exact _root_.le_trans h1 h_den_step
    have h_prod_eq : prod.approx M = x.approx K * (x.approx K_final)⁻¹ := by
      dsimp [prod, CReal.Pre.mul, inv_x, CReal.Pre.inv, K, K_final, S_inv]
      rfl
    have h_simp :
        ((1 : ℚ) / 2 ^ K) / L = (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
      dsimp [L]
      have hK' : K = (N + 1) + (n + 1 + S_mul) := by
        have : N + n + 2 + S_mul = (N + 1) + (n + 1 + S_mul) := by
          calc
            N + n + 2 + S_mul
                = N + (n + 1) + (1 + S_mul) := by simp [Nat.add_assoc]; simp +arith
            _ = (N + 1) + (n + 1 + S_mul) := by
                simp [Nat.add_assoc, Nat.add_left_comm]
        simpa [K, M] using this
      have : ((1 : ℚ) / 2 ^ ((N + 1) + (n + 1 + S_mul))) / ((1 : ℚ) / 2 ^ (N + 1))
                = (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
        simpa [Nat.add_comm] using
          CReal.Pre.div_one_div_pow_simp (a := n + 1 + S_mul) (b := N + 1)
      simpa [hK'] using this
    have h_mono :
        (1 : ℚ) / 2 ^ (n + 1 + S_mul) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
      exact one_div_pow_le_one_div_pow_of_le rfl (Nat.le_add_right _ _)
    have h_main' : |prod.approx M - 1| ≤ (1 : ℚ) / 2 ^ (n + 1 + S_mul) := by
      simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, one_div, abs_pos, ne_eq,
        not_false_eq_true, div_inv_eq_mul, M, N, K_final, K, S_mul, inv_x, S_inv, L, prod]
    exact h_main'.trans h_mono
  dsimp [CReal.Pre.Equiv, CReal.Pre.one]
  have h_reg : |prod.approx (n+1) - prod.approx M| ≤ 1 / 2 ^ (n+1) := by
    apply prod.is_regular
    have : n + 1 ≤ (n + 1) + (N + 1) := Nat.le_add_right _ _
    simp [M, Nat.add_assoc, Nat.add_left_comm]
  calc
    |prod.approx (n+1) - 1|
      ≤ |prod.approx (n+1) - prod.approx M| + |prod.approx M - 1| := by
          apply abs_sub_le
    _ ≤ 1/2^(n+1) + 1/2^(n+1) := by
          have h1 : |prod.approx (n+1) - prod.approx M| ≤ 1 / 2 ^ (n+1) := by
            simpa [abs_sub_comm] using h_reg
          exact add_le_add h1 h_diff_M
    _ = 1/2^n := by
          field_simp [pow_succ]; ring

end CReal.Pre

namespace CReal
open CReal.Pre

/-- Embed a rational as a constant pre-real. -/
def Pre.ofRat (q : ℚ) : CReal.Pre where
  approx := fun _ => q
  is_regular := by
    intro n m _hm
    simp

/-- Rational coercion into `CReal` via constant pre-real. -/
instance : RatCast CReal where
  ratCast q := ⟦Pre.ofRat q⟧

/-- A Cauchy sequence of computable real numbers with dyadic modulus. -/
structure RCauSeq' where
  seq : ℕ → CReal
  is_cauchy :
    ∀ n m, n ≤ m →
      seq n ≤ seq m + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal) ∧
      seq m ≤ seq n + (((1 : ℚ) / ((2 : ℚ) ^ n)) : CReal)

/-- A Cauchy sequence of computable real numbers with dyadic modulus, together with explicit representatives. -/
structure RCauSeq where
  seq : ℕ → CReal
  pre : ℕ → CReal.Pre
  seq_spec : ∀ n, seq n = ⟦pre n⟧
  is_cauchy :
    ∀ n m, n ≤ m →
      |(pre (n + 2)).approx (n + 2) - (pre (m + 2)).approx (n + 2)| ≤
        (1 : ℚ) / 2 ^ (n + 1)

@[simp] lemma RCauSeq.seq_spec' (s : RCauSeq) (n : ℕ) :
    s.seq n = ⟦s.pre n⟧ := s.seq_spec n

/-! ### Properties of Separation -/

-- We rely on the decidability of order on ℚ for constructive choice (Nat.find) later.
instance decidable_separated_prop (x : CReal.Pre) (N : ℕ) : Decidable (1/2^N < |x.approx (N+1)|) :=
  inferInstance

/-- Pos x ∨ Pos (-x) implies Separated x. (Constructive) -/
lemma pos_or_neg_pos_implies_separated (x : CReal.Pre) :
  (CReal.Pre.Pos x ∨ CReal.Pre.Pos (CReal.Pre.neg x)) → CReal.Pre.Separated x := by
  intro h
  rcases h with h_pos | h_neg
  · rcases h_pos with ⟨N, hN⟩
    have h_pos_approx : 0 < x.approx (N+1) := lt_trans (by positivity) hN
    have h_abs : |x.approx (N+1)| = x.approx (N+1) := abs_of_pos h_pos_approx
    exact ⟨N, by rwa [h_abs]⟩
  · rcases h_neg with ⟨N, hN⟩
    dsimp [CReal.Pre.neg] at hN
    have h_neg_approx : x.approx (N+1) < 0 := by
      have : 0 < -x.approx (N+1) := lt_trans (by positivity) hN
      exact neg_pos.mp this
    have h_abs : |x.approx (N+1)| = -x.approx (N+1) := abs_of_neg h_neg_approx
    exact ⟨N, by rwa [h_abs]⟩

/-- Separated x implies Pos x ∨ Pos (-x). (Constructive, relies on decidability of ℚ order) -/
lemma separated_implies_pos_or_neg_pos (x : CReal.Pre) (h : CReal.Pre.Separated x) :
  (CReal.Pre.Pos x ∨ CReal.Pre.Pos (CReal.Pre.neg x)) := by
  rcases h with ⟨N, hN⟩
  let approx_val := x.approx (N+1)
  rcases lt_trichotomy approx_val 0 with h_lt | h_eq | h_gt
  · right
    dsimp [CReal.Pre.Pos, CReal.Pre.neg]
    have h_abs : |approx_val| = -approx_val := abs_of_neg h_lt
    exact ⟨N, by rwa [h_abs] at hN⟩
  · have h_rewrite : x.approx (N + 1) = 0 := h_eq
    rw [h_rewrite, abs_zero] at hN
    have h_pos : 0 < (1:ℚ)/2^N := by positivity
    exfalso
    exact lt_irrefl 0 (lt_trans h_pos hN)
  · left
    dsimp [CReal.Pre.Pos]
    have h_abs : |approx_val| = approx_val := abs_of_pos h_gt
    exact ⟨N, by rwa [h_abs] at hN⟩

/-! ### Heyting Field Structure (Constructive Field) -/

/--
Apartness relation: x # y if |x - y| > 0 (constructively).
-/
def Apart (x y : CReal) : Prop :=
  Quotient.lift₂
    (fun x y => Pre.Pos (Pre.add x (Pre.neg y)) ∨ Pre.Pos (Pre.add y (Pre.neg x)))
    (fun x₁ y₁ x₂ y₂ hx hy => propext (by
      constructor
      · intro h
        cases h with
        | inl h =>
          left
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hx (neg_respects_equiv _ _ hy))).mp h
        | inr h =>
          right
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hy (neg_respects_equiv _ _ hx))).mp h
      · intro h
        cases h with
        | inl h =>
          left
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hx (neg_respects_equiv _ _ hy))).mpr h
        | inr h =>
          right
          exact (Pre.pos_well_defined _ _ (add_respects_equiv hy (neg_respects_equiv _ _ hx))).mpr h))
    x y

-- Fixed lim_pre definition
/-- The representative sequence for the limit of an RCauSeq. -/
def lim_pre (s : RCauSeq) : CReal.Pre :=
  let pre_seq (n : ℕ) := (s.pre (n + 2)).approx (n + 2)
  {
    approx := pre_seq
    is_regular := by
      intro n m hnm
      let intermediate := (s.pre (m + 2)).approx (n + 2)
      have h_term₁ : |pre_seq n - intermediate| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
        dsimp [pre_seq]
        exact s.is_cauchy n m hnm
      have h_term₂ : |intermediate - pre_seq m| ≤ (1 : ℚ) / 2 ^ (n + 2) := by
        dsimp [pre_seq]
        have h_le : n + 2 ≤ m + 2 := add_le_add_right hnm 2
        simpa [abs_sub_comm] using
          (s.pre (m + 2)).is_regular (n + 2) (m + 2) h_le
      have h_sum : (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ n := by
        have h_mono : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) :=
          inv_pow_antitone_succ (n + 1)
        calc
          (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2)
              ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
                exact add_le_add le_rfl h_mono
          _ = (1 : ℚ) / 2 ^ n := two_halves_to_pred n
      calc
        |pre_seq n - pre_seq m|
          ≤ |pre_seq n - intermediate| + |intermediate - pre_seq m| := abs_sub_le _ _ _
        _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 2) := add_le_add h_term₁ h_term₂
        _ ≤ (1 : ℚ) / 2 ^ n := h_sum
  }

/-- The limit of a Cauchy sequence of `CReal`s. -/
def lim (s : RCauSeq) : CReal := ⟦lim_pre s⟧

/-- Helper: `(-0) ≈ 0` at the Pre level. -/
lemma neg_zero_equiv_pre : CReal.Pre.Equiv (CReal.Pre.neg CReal.Pre.zero) CReal.Pre.zero := by
  intro n
  have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
  simp [CReal.Pre.neg, CReal.Pre.zero, sub_self, abs_zero]

/-- x is apart from 0 if and only if its underlying representation is Separated. -/
theorem apart_zero_iff_separated (x : CReal) :
  Apart x 0 ↔ Quotient.lift Pre.Separated (fun _ _ h => propext (Pre.separated_well_defined _ _ h)) x := by
  refine Quot.induction_on x (fun x_pre => ?_)
  dsimp [Apart, Quotient.lift]
  constructor
  · intro h
    have hx_or : Pre.Pos x_pre ∨ Pre.Pos (CReal.Pre.neg x_pre) := by
      cases h with
      | inl hpos =>
        have h_eq1 : CReal.Pre.Equiv (x_pre.add (CReal.Pre.neg CReal.Pre.zero)) x_pre :=
          CReal.Pre.equiv_trans
            (add_respects_equiv
              (by
                intro n
                have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
                have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
                simp)
              neg_zero_equiv_pre)
            (add_zero_pre x_pre)
        left
        exact (Pre.pos_well_defined _ _ h_eq1).mp hpos
      | inr hpos =>
        have h_eq2 : CReal.Pre.Equiv (CReal.Pre.zero.add (CReal.Pre.neg x_pre)) (CReal.Pre.neg x_pre) :=
          zero_add_pre (CReal.Pre.neg x_pre)
        right
        exact (Pre.pos_well_defined _ _ h_eq2).mp hpos
    exact pos_or_neg_pos_implies_separated x_pre hx_or
  · intro h
    have hx_or : Pre.Pos x_pre ∨ Pre.Pos (CReal.Pre.neg x_pre) :=
      separated_implies_pos_or_neg_pos x_pre h
    cases hx_or with
    | inl hx =>
      have h_eq1 : CReal.Pre.Equiv (x_pre.add (CReal.Pre.neg CReal.Pre.zero)) x_pre :=
        CReal.Pre.equiv_trans
          (add_respects_equiv
            (by
              intro n
              have hpow : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
              have h_nonneg : 0 ≤ (1 : ℚ) / 2 ^ n := div_nonneg (by norm_num) (le_of_lt hpow)
              simp)
            neg_zero_equiv_pre)
          (add_zero_pre x_pre)
      exact Or.inl ((Pre.pos_well_defined _ _ h_eq1).mpr hx)
    | inr hnx =>
      have h_eq2 : CReal.Pre.Equiv (CReal.Pre.zero.add (CReal.Pre.neg x_pre)) (CReal.Pre.neg x_pre) :=
        zero_add_pre (CReal.Pre.neg x_pre)
      exact Or.inr ((Pre.pos_well_defined _ _ h_eq2).mpr hnx)

/-! ### Pseudo-Order Structure -/

/--
CReal forms a pseudo-order. This is the constructive analogue of a linear order
for structures where equality is not decidable: if x < y, then for any z, either x < z or z < y.
-/
theorem pseudo_order_property (x y z : CReal) (hxy : x < y) : x < z ∨ z < y := by
  have h_pos := (lt_iff_pos x y).mp hxy
  refine Quot.induction_on₃ x y z (fun x_pre y_pre z_pre h_pos => ?_) h_pos
  dsimp [Pos, CReal.Pre.Pos] at h_pos
  rcases h_pos with ⟨N, hN⟩
  dsimp [CReal.Pre.add, CReal.Pre.neg] at hN
  let M := N + 3
  let K := M + 1
  have h_reg_diff := (y_pre.add (x_pre.neg)).is_regular (N+1) K (by simp [K,M])
  dsimp [CReal.Pre.add, CReal.Pre.neg] at h_reg_diff
  have h_diff_K_ge :
      (y_pre.approx (N+2) - x_pre.approx (N+2)) - 1/2^(N+1)
        ≤ y_pre.approx (K+1) - x_pre.approx (K+1) := by
    have h_pair := (abs_sub_le_iff).1 h_reg_diff
    have h_aux :
        (y_pre.approx (N+2) - x_pre.approx (N+2)) -
          (y_pre.approx (K+1) - x_pre.approx (K+1))
          ≤ 1 / 2 ^ (N + 1) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_pair.left
    linarith
  have h_gap_stable : 1/2^(N+1) < y_pre.approx (K+1) - x_pre.approx (K+1) := by
    have h_sub : (1:ℚ)/2^N - 1/2^(N+1) = 1/2^(N+1) := by
      field_simp [pow_succ]; ring
    calc
      1/2^(N+1) = 1/2^N - 1/2^(N+1) := h_sub.symm
      _ < (y_pre.approx (N+2) + -x_pre.approx (N+2)) - 1/2^(N+1) :=
            sub_lt_sub_right hN _
      _ = (y_pre.approx (N+2) - x_pre.approx (N+2)) - 1/2^(N+1) := by simp [sub_eq_add_neg]
      _ ≤ y_pre.approx (K+1) - x_pre.approx (K+1) := h_diff_K_ge
  let m_K := (x_pre.approx K + y_pre.approx K) / 2
  cases le_or_gt (z_pre.approx K) m_K with
  | inl h_le =>
    -- z < y branch
    right
    apply (lt_iff_pos ⟦z_pre⟧ ⟦y_pre⟧).mpr
    dsimp [Pos, CReal.Pre.Pos]
    have h_diff_ge_half : (y_pre.approx K - x_pre.approx K)/2 ≤
        y_pre.approx K - z_pre.approx K := by
      calc
        (y_pre.approx K - x_pre.approx K)/2
            = y_pre.approx K - (x_pre.approx K + y_pre.approx K)/2 := by ring
        _ ≤ y_pre.approx K - z_pre.approx K := sub_le_sub_left h_le _
    -- one–step regularity triples
    have hy_pair :=
      (abs_sub_le_iff).1 (by simpa using y_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_pair :=
      (abs_sub_le_iff).1 (by simpa using z_pre.is_regular K (K+1) (Nat.le_succ _))
    have hx_pair :=
      (abs_sub_le_iff).1 (by simpa using x_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_up : z_pre.approx (K+1) ≤ z_pre.approx K + 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hz_pair.right
      simpa [add_comm, one_div] using h
    have hx_ge : x_pre.approx (K+1) ≥ x_pre.approx K - 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hx_pair.left
      have : x_pre.approx K - (2^K)⁻¹ ≤ x_pre.approx (K+1) :=
        (sub_le_iff_le_add).2 (by simpa [add_comm] using h)
      simpa [one_div] using this
    have hy_ge : y_pre.approx (K+1) ≥ y_pre.approx K - 1 / 2 ^ K := by
      have h := (sub_le_iff_le_add).mp hy_pair.left
      have : y_pre.approx K - (2^K)⁻¹ ≤ y_pre.approx (K+1) :=
        (sub_le_iff_le_add).2 (by simpa [add_comm] using h)
      simpa [one_div] using this
    have hm_ge :
        (x_pre.approx (K+1) + y_pre.approx (K+1))/2 ≥
          (x_pre.approx K + y_pre.approx K)/2 - 1/2^K := by
      linarith [hx_ge, hy_ge]
    have hz_up' :
        z_pre.approx (K+1) ≤
          (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 2/2^K := by
      have hz_to_mK :
          z_pre.approx (K+1) ≤ (x_pre.approx K + y_pre.approx K)/2 + 1/2^K :=
        (hz_up.trans (add_le_add_right h_le _))
      have : (x_pre.approx K + y_pre.approx K)/2
              ≤ (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 1/2^K := by
        linarith [hm_ge]
      have step' := add_le_add_right this (1/2^K)
      have htwo : (1/2^K : ℚ) + 1/2^K = 2/2^K := by ring
      have h_lift :
          (x_pre.approx K + y_pre.approx K)/2 + 1/2^K
            ≤ (x_pre.approx (K+1) + y_pre.approx (K+1))/2 + 2/2^K := by
        calc
          (x_pre.approx K + y_pre.approx K)/2 + 1/2^K
              ≤ (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + 1/2^K + 1/2^K := step'
          _ = (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (1/2^K + 1/2^K) := by ring
          _ = (x_pre.approx (K+1)+y_pre.approx (K+1))/2 + 2/2^K := by simp; ring_nf
      exact hz_to_mK.trans h_lift
    have hK_expr : K = N + 4 := by
      simp [K,M, Nat.add_comm, Nat.add_left_comm]
    have h_two_over : (2:ℚ)/2^K = (1:ℚ)/2^(N+3) := by
      have : (2:ℚ)/2^(N+4) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      simpa [hK_expr]
    have h_gap_half_K1 :
        (1:ℚ)/2^(N+2) < (y_pre.approx (K+1) - x_pre.approx (K+1))/2 := by
      have h_mul := (mul_lt_mul_of_pos_right h_gap_stable (by norm_num : 0 < (1:ℚ)/2))
      simpa [one_div, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_mul
    have h_core_margin :
        (1:ℚ)/2^(N+3)
          < y_pre.approx (K+1)
              - ( (x_pre.approx (K+1)+y_pre.approx (K+1))/2 )
              - (1:ℚ)/2^(N+3) := by
      have hrewrite :
          y_pre.approx (K+1) - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2)
            = (y_pre.approx (K+1) - x_pre.approx (K+1))/2 := by
        field_simp; ring
      have h_sub : (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      have h := sub_lt_sub_right h_gap_half_K1 ((1:ℚ)/2^(N+3))
      calc
        (1:ℚ)/2^(N+3)
            = (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) := h_sub.symm
        _ < (y_pre.approx (K+1) - x_pre.approx (K+1))/2 - (1:ℚ)/2^(N+3) := h
        _ = y_pre.approx (K+1)
              - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2)
              - (1:ℚ)/2^(N+3) := by
              simp [sub_eq_add_neg, add_comm]
              ring_nf
    have h_margin :
        (1:ℚ)/2^M < y_pre.approx (K+1) - z_pre.approx (K+1) := by
      have h_comp :
          y_pre.approx (K+1)
            - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (2:ℚ)/2^K)
              ≤ y_pre.approx (K+1) - z_pre.approx (K+1) :=
        sub_le_sub_left hz_up' _
      have h_base :
          (1:ℚ)/2^(N+3) <
            y_pre.approx (K+1)
              - ((x_pre.approx (K+1)+y_pre.approx (K+1))/2 + (2:ℚ)/2^K) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, h_two_over]
          using h_core_margin
      have h_trans := lt_of_lt_of_le h_base h_comp
      simpa [M] using h_trans
    -- Provide witness M
    refine ⟨M, ?_⟩
    -- Expand and apply h_margin directly
    have h_expand :
      (y_pre.add z_pre.neg).approx (M+1) =
        y_pre.approx (K+1) - z_pre.approx (K+1) := by
      have hK1 : K + 1 = M + 2 := by simp [K,M]
      dsimp [CReal.Pre.add, CReal.Pre.neg]
      simp [hK1, sub_eq_add_neg, add_comm]
      ring_nf
    have h_witness :
      (1 : ℚ)/2^M < (y_pre.add z_pre.neg).approx (M+1) := by
      simpa [h_expand]
        using h_margin
    exact h_witness
  | inr h_gt =>
    -- FIXED second branch
    left
    apply (lt_iff_pos ⟦x_pre⟧ ⟦z_pre⟧).mpr
    dsimp [Pos, CReal.Pre.Pos]
    -- Midpoint inequality gives half-gap at index K
    have h_diff_gt_half :
        (y_pre.approx K - x_pre.approx K)/2 < z_pre.approx K - x_pre.approx K := by
      calc
        (y_pre.approx K - x_pre.approx K)/2
            = (x_pre.approx K + y_pre.approx K)/2 - x_pre.approx K := by ring
        _ < z_pre.approx K - x_pre.approx K := sub_lt_sub_right h_gt _
    -- Regularity from N+2 to K
    have hN2_le_K : N + 2 ≤ K := by simp [K,M]
    have hy_reg := (abs_sub_le_iff).1 (by simpa using y_pre.is_regular (N+2) K hN2_le_K)
    have hx_reg := (abs_sub_le_iff).1 (by simpa using x_pre.is_regular (N+2) K hN2_le_K)
    -- Upper / lower shifts
    have hy_ge : y_pre.approx K ≥ y_pre.approx (N+2) - 1/2^(N+2) := by
      have : y_pre.approx (N+2) - y_pre.approx K ≤ 1/2^(N+2) := by
        simpa [one_div] using hy_reg.left
      linarith
    have hx_le : x_pre.approx K ≤ x_pre.approx (N+2) + 1/2^(N+2) := by
      have : x_pre.approx K - x_pre.approx (N+2) ≤ 1/2^(N+2) := by
        simpa [one_div] using hx_reg.right
      linarith
    -- Lower bound on gap at K in terms of gap at N+2
    have h_yx :
        y_pre.approx K - x_pre.approx K ≥
          (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2 / 2 ^ (N+2) := by
      calc
        y_pre.approx K - x_pre.approx K
            ≥ (y_pre.approx (N+2) - 1/2^(N+2)) - (x_pre.approx (N+2) + 1/2^(N+2)) :=
              sub_le_sub hy_ge hx_le
        _ = (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2/2^(N+2) := by ring
    -- Core gap lower bound from original witness hN
    have h_core :
        (y_pre.approx (N+2) - x_pre.approx (N+2)) - 2 / 2 ^ (N + 2)
          > 1 / 2 ^ (N + 1) := by
      -- Base inequality from the hypothesis hN (index shift already expanded).
      have hyx : 1 / 2 ^ N < y_pre.approx (N+2) - x_pre.approx (N+2) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hN
      -- Express 1 / 2^N directly as the sum of two copies of 1 / 2^(N+1).
      have h_split : (1 : ℚ) / 2 ^ N = (1 : ℚ) / 2 ^ (N + 1) + (1 : ℚ) / 2 ^ (N + 1) := by
        -- 1/2^N = 2/2^(N+1) and 2/2^(N+1) = (1/2^(N+1))+(1/2^(N+1))
        field_simp [pow_succ]; ring
      -- Rewrite the left side of hyx via h_split to get a “double–half” gap.
      have h_big :
          (1 : ℚ) / 2 ^ (N + 1) + (1 : ℚ) / 2 ^ (N + 1)
            < y_pre.approx (N+2) - x_pre.approx (N+2) := by
        simpa [h_split]
          using hyx
      -- Subtract one 1/2^(N+1) from both sides.
      have h_goal :
          (y_pre.approx (N+2) - x_pre.approx (N+2)) - (1 : ℚ) / 2 ^ (N + 1)
            > (1 : ℚ) / 2 ^ (N + 1) := by
        linarith
      -- 2 / 2^(N+2) = 1 / 2^(N+1).
      have h_two : (2 : ℚ) / 2 ^ (N + 2) = (1 : ℚ) / 2 ^ (N + 1) := by
        -- 2^(N+2) = 2^(N+1)*2
        simp [pow_succ, mul_comm]; ring_nf
      -- Replace 2/2^(N+2) with 1/2^(N+1).
      simpa [h_two] using h_goal
      
    have h_yx_strong :
        1 / 2 ^ (N + 1) < y_pre.approx K - x_pre.approx K :=
      lt_of_lt_of_le h_core h_yx
    -- Half-gap lower bound
    have h_gap_half :
        1 / 2 ^ (N + 2) < (y_pre.approx K - x_pre.approx K)/2 := by
      have hpos : (0:ℚ) < (1:ℚ)/2 := by norm_num
      have := mul_lt_mul_of_pos_right h_yx_strong hpos
      simpa [one_div, pow_succ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    -- Pass half-gap through midpoint inequality
    have h_final_at_K :
        1 / 2 ^ (N + 2) < z_pre.approx K - x_pre.approx K :=
      lt_trans h_gap_half h_diff_gt_half
    -- Shift to index K+1
    have hz_pair :=
      (abs_sub_le_iff).1 (by simpa using z_pre.is_regular K (K+1) (Nat.le_succ _))
    have hx_pair :=
      (abs_sub_le_iff).1 (by simpa using x_pre.is_regular K (K+1) (Nat.le_succ _))
    have hz_lower : z_pre.approx (K+1) ≥ z_pre.approx K - 1/2^K := by
      have : z_pre.approx K - z_pre.approx (K+1) ≤ 1/2^K := by
        simpa [one_div] using hz_pair.left
      linarith
    have hx_upper : x_pre.approx (K+1) ≤ x_pre.approx K + 1/2^K := by
      have : x_pre.approx (K+1) - x_pre.approx K ≤ 1/2^K := by
        simpa [one_div] using hx_pair.right
      linarith
    have h_lower_shift :
        z_pre.approx (K+1) - x_pre.approx (K+1)
          ≥ z_pre.approx K - x_pre.approx K - 2/2^K := by
      calc
        z_pre.approx (K+1) - x_pre.approx (K+1)
            ≥ (z_pre.approx K - 1/2^K) - (x_pre.approx K + 1/2^K) :=
              sub_le_sub hz_lower hx_upper
        _ = z_pre.approx K - x_pre.approx K - 2/2^K := by ring
    -- Express 2/2^K as 1/2^(N+3)
    have hK_expr : K = N + 4 := by simp [K,M]
    have h_two_over : (2:ℚ)/2^K = (1:ℚ)/2^(N+3) := by
      have : (2:ℚ)/2^(N+4) = (1:ℚ)/2^(N+3) := by
        field_simp [pow_succ]; ring
      simpa [hK_expr]
    -- Subtract (2/2^K) from inequality at K
    have base_shift :
      1 / 2 ^ (N + 2) - 2 / 2 ^ K < z_pre.approx K - x_pre.approx K - 2 / 2 ^ K := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (sub_lt_sub_right h_final_at_K ((2:ℚ)/2^K))
    -- Rewrite LHS to 1/2^(N+3) using the previously obtained h_two_over (ensure all literals are ℚ).
    have h_left_rewrite :
        (1 : ℚ) / 2 ^ (N + 2) - (2 : ℚ) / 2 ^ K = (1 : ℚ) / 2 ^ (N + 3) := by
      -- coerce all numerals to ℚ
      have h2 : (2 : ℚ) / (2 : ℚ) ^ K = (1 : ℚ) / (2 : ℚ) ^ (N + 3) := h_two_over
      -- (1/2^(N+2) - 1/2^(N+3)) = 1/2^(N+3)
      have h_sub : (1:ℚ)/2^(N+2) - (1:ℚ)/2^(N+3) = (1:ℚ)/2^(N+3) := by
        field_simp [one_div, pow_succ]; ring
      calc
        (1 : ℚ) / 2 ^ (N + 2) - (2 : ℚ) / 2 ^ K
            = (1 : ℚ) / 2 ^ (N + 2) - (1 : ℚ) / 2 ^ (N + 3) := by rw [h2]
        _ = (1 : ℚ) / 2 ^ (N + 3) := h_sub
    -- Derive the needed shifted inequality directly from h_final_at_K (avoids fragile rewrites).
    have h_at_K1 :
        1 / 2 ^ (N + 3) < z_pre.approx K - x_pre.approx K - 2 / 2 ^ K := by
      -- We want: 1/2^(N+3) < (gap) - 2/2^K; with 2/2^K = 1/2^(N+3),
      -- it's equivalent to: 2*(1/2^(N+3)) < gap, i.e. 1/2^(N+2) < gap, which is h_final_at_K.
      have h_sum_halves :
          (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) = 1 / 2 ^ (N + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using two_halves_to_succ (N + 1)
      -- Rewrite the gap inequality into a + a < gap
      have h_gap' : (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K := by
        -- We have: h_sum_halves : 1/2^(N+3) + 1/2^(N+3) = 1/2^(N+2)
        -- and this : 1/2^(N+2) < z_pre.approx K - x_pre.approx K
        rw [h_sum_halves]
        simp_all only [one_div, lt_add_neg_iff_add_lt, tsub_le_iff_right, add_le_add_iff_right, le_add_iff_nonneg_right,
          zero_le, ge_iff_le, gt_iff_lt, sub_lt_sub_iff_right, K, M, m_K]
      -- From a + a < G deduce a < G - a
      have h_goal :
          (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K - 1/2^(N+3) := by
        have : (1:ℚ)/2^(N+3) + (1:ℚ)/2^(N+3) < z_pre.approx K - x_pre.approx K := h_gap'
        linarith
      -- Replace 2/2^K with 1/2^(N+3) (h_two_over) in the target.
      simpa [h_two_over] using h_goal
    -- Lift to K+1 using h_lower_shift
    have h_step :
        1 / 2 ^ (N + 3) < z_pre.approx (K+1) - x_pre.approx (K+1) :=
      lt_of_lt_of_le h_at_K1 h_lower_shift
    -- Strengthen exponent to M (M = N+3 here)
    have h_step_stronger :
        1 / 2 ^ M < z_pre.approx (K+1) - x_pre.approx (K+1) := by
      have hM : M = N + 3 := rfl
      simpa [hM] using h_step
    refine ⟨M, ?_⟩
    -- Expand (z - x) at index M+1
    have h_expand :
      (z_pre.add x_pre.neg).approx (M+1) =
        z_pre.approx (K+1) - x_pre.approx (K+1) := by
      have hK1 : K + 1 = M + 2 := by simp [K,M]
      dsimp [CReal.Pre.add, CReal.Pre.neg]
      simp [hK1, sub_eq_add_neg]
    simpa [h_expand] using h_step_stronger

-- A simp lemma to rewrite the limit representative at any index
@[simp] 
lemma lim_pre_approx_simp (s : RCauSeq) (t : ℕ) :
  (lim_pre s).approx t = (s.pre (t + 2)).approx (t + 2) := rfl

-- Collapse 1/2^n + 1/2^(n-1) + 1/2^n to 1/2^(n-2) (for n ≥ 2)
private lemma three_terms_collapse_aux (m : ℕ) :
    (1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 2) = 1 / 2 ^ m := by
  calc
    (1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 2)
        = ((1 : ℚ) / 2 ^ (m + 2) + 1 / 2 ^ (m + 2)) + 1 / 2 ^ (m + 1) := by
          simp [add_comm, add_left_comm]
    _ = 1 / 2 ^ (m + 1) + 1 / 2 ^ (m + 1) := by
          simp [add_comm]; ring_nf
    _ = 1 / 2 ^ m := two_halves_to_pred m

lemma three_terms_collapse (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℚ) / 2 ^ n + 1 / 2 ^ (n - 1) + 1 / 2 ^ n = 1 / 2 ^ (n - 2) := by
  let m := n - 2
  have hm_add : m + 2 = n := Nat.sub_add_cancel hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hm1 : m + 1 = n - 1 := by
    apply Nat.succ_injective
    have h_left : Nat.succ (m + 1) = n := by
      simp [m, Nat.add_comm]; simp +arith [*]
    have h_right : Nat.succ (n - 1) = n := Nat.succ_pred_eq_of_pos hn_pos
    simp_all only [Nat.sub_add_cancel, Nat.succ_eq_add_one, m]
  have hm0 : m = n - 2 := rfl
  simpa [m, hm0, hm_add, hm1, add_comm, add_left_comm, add_assoc] using
    three_terms_collapse_aux m

-- Synchronous (single-index) bound at index n+2:
-- |(s.pre n)_(n+2) - (lim_pre s)_(n+2)| ≤ 1/2^(n-2)
lemma diff_at_sync_bound (s : RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |(s.pre n).approx (n + 2) - (lim_pre s).approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  -- A := (s.pre n).approx (n+2)
  -- B := (s.pre n).approx n
  -- C := (s.pre (n+4)).approx n  (since K = n+2 ⇒ K+2 = n+4)
  -- L := (lim_pre s).approx (n+2) = (s.pre (n+4)).approx (n+4)
  set A := (s.pre n).approx (n + 2) with hA
  set B := (s.pre n).approx n with hB
  set C := (s.pre (n + 4)).approx n with hC
  set L := (lim_pre s).approx (n + 2) with hL
  have h1 : |A - B| ≤ (1 : ℚ) / 2 ^ n := by
    simpa [A, B, abs_sub_comm] using (s.pre n).is_regular n (n + 2) (Nat.le_add_right _ _)
  have h2 : |B - C| ≤ (1 : ℚ) / 2 ^ (n - 1) := by
    have hnm : n - 2 ≤ n + 2 := by
      have : n - 2 ≤ n := Nat.sub_le _ _
      exact this.trans (Nat.le_add_right _ _)
    have one_lt_n : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
    have hpos : 0 < n - 1 := Nat.sub_pos_of_lt one_lt_n
    have h_succ : Nat.succ (n - 2) = n - 1 := by
      simpa using Nat.succ_pred_eq_of_pos hpos
    have h := s.is_cauchy (n - 2) (n + 2) hnm
    dsimp [B, C, Nat.sub_add_cancel hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
           h_succ, Nat.succ_eq_add_one, Nat.one_add]
    simp_all only [lim_pre_approx_simp, one_div, tsub_le_iff_right, tsub_pos_iff_lt, Nat.succ_eq_add_one,
      Nat.sub_add_cancel, A, B, C, L]
  have h3 : |C - L| ≤ (1 : ℚ) / 2 ^ n := by
    simpa [C, L, lim_pre_approx_simp, abs_sub_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (s.pre (n + 4)).is_regular n (n + 4) (Nat.le_add_right _ _)
  have h_bound : |A - L| ≤ 1/2^n + 1/2^(n-1) + 1/2^n := by
    calc
      |A - L| ≤ |A - B| + |B - C| + |C - L| := by
        have := abs_add_three (A - B) (B - C) (C - L)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      _ ≤ (1/2^n) + (1/2^(n-1)) + (1/2^n) := by
        have := add_le_add (add_le_add h1 h2) h3
        simpa [add_comm, add_left_comm, add_assoc]
  have h_three := three_terms_collapse n hn
  have h_value :
      (1 : ℚ) / 2 ^ n + ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1)) =
        (1 : ℚ) / 2 ^ (n - 2) := by
    calc
      (1 : ℚ) / 2 ^ n + ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1))
          = ((1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ (n - 1)) + (1 : ℚ) / 2 ^ n := by
            simp [add_comm]
      _ = (1 : ℚ) / 2 ^ (n - 2) := by
            simpa [add_comm, add_left_comm, add_assoc] using h_three
  have : |A - L| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
    simp; simp_all
  exact this

lemma lift_sync_bound_to_all_indices
  (d : CReal.Pre) {K : ℕ} {r : ℚ} (hK : |d.approx K| ≤ r) :
  ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ (min j K) := by
  intro j
  have h_tri : |d.approx (j + 1)| ≤ |d.approx (j + 1) - d.approx K| + |d.approx K| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_add_le (d.approx (j + 1) - d.approx K) (d.approx K))
  have hreg : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min (j + 1) K) :=
    CReal.abs_approx_diff_le d (j + 1) K
  have hmin : min j K ≤ min (j + 1) K := by
    exact min_le_min (Nat.le_succ j) le_rfl
  have hpow_mono :
      (2 : ℚ) ^ (min j K) ≤ (2 : ℚ) ^ (min (j + 1) K) :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).2 hmin
  have h_one_div :
      (1 : ℚ) / 2 ^ (min (j + 1) K) ≤ (1 : ℚ) / 2 ^ (min j K) :=
    one_div_le_one_div_of_le (pow_pos (by norm_num) _) hpow_mono
  have hreg' : |d.approx (j + 1) - d.approx K| ≤ (1 : ℚ) / 2 ^ (min j K) :=
    hreg.trans h_one_div
  have h_sum : |d.approx (j + 1) - d.approx K| + |d.approx K|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| :=
    add_le_add_right hreg' _
  have h_step : |d.approx (j + 1)|
      ≤ (1 : ℚ) / 2 ^ (min j K) + |d.approx K| :=
    _root_.le_trans h_tri h_sum
  have h_step' : |d.approx (j + 1)|
      ≤ |d.approx K| + (1 : ℚ) / 2 ^ (min j K) := by
    simpa [add_comm] using h_step
  have hK_add :
      |d.approx K| + (1 : ℚ) / 2 ^ (min j K) ≤ r + (1 : ℚ) / 2 ^ (min j K) :=
    add_le_add_right hK _
  exact _root_.le_trans h_step' hK_add

-- From absolute pre-bounds at all indices to a CReal absolute-value bound
lemma abs_le_of_pre_abs_bound (d : CReal.Pre) {r : ℚ}
  (hall : ∀ j : ℕ, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j) :
  |(⟦d⟧ : CReal)| ≤ (r : CReal) := by
  have h1 : (⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le d (CReal.Pre.ofRat r)
    intro j
    exact (abs_le.mp (hall j)).2
  have h2 : -(⟦d⟧ : CReal) ≤ (r : CReal) := by
    change CReal.Pre.le (CReal.Pre.neg d) (CReal.Pre.ofRat r)
    intro j
    have h := hall j
    have : -(d.approx (j + 1)) ≤ |d.approx (j + 1)| := by
      simpa using (neg_le_abs (d.approx (j + 1)))
    exact (this.trans h)
  change sup ⟦d⟧ (-⟦d⟧) ≤ (r : CReal)
  exact sup_le h1 h2

lemma min_tail_split (j n : ℕ) :
  (1 : ℚ) / 2 ^ (min j (n + 1)) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  cases le_total j (n + 1) with
  | inl h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ (n + 1) := by positivity
      have this : (1 : ℚ) / 2 ^ j ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_right hnn
      simp [min_eq_left h]
  | inr h =>
      have hnn : 0 ≤ (1 : ℚ) / 2 ^ j := by positivity
      have this : (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
        exact le_add_of_nonneg_left hnn
      simp [min_eq_right h]

lemma lift_sync_bound_with_uniform_tail
  (d : CReal.Pre) (n : ℕ) {r : ℚ}
  (h_sync : |d.approx (n + 1)| ≤ r) :
  ∀ j, |d.approx (j + 1)| ≤ r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_base :=
    CReal.lift_sync_bound_to_all_indices (d := d) (K := n + 1) (r := r) (by simpa using h_sync) j
  have h_tail := min_tail_split j n
  have h_mono := add_le_add_right h_tail r
  calc |d.approx (j + 1)|
    ≤ r + (1 : ℚ) / 2 ^ (min j (n + 1)) := h_base
    _ ≤ r + ((1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)) := by gcongr
    _ = r + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by ring

lemma diff_sync_bound_for_d (s : CReal.RCauSeq) (n : ℕ) (hn : 2 ≤ n) :
  |((CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))).approx (n + 1))| ≤ (1 : ℚ) / 2 ^ (n - 2) := by
  let d := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hJ :
    d.approx (n + 1)
      = (s.pre n).approx (n + 2) - (CReal.lim_pre s).approx (n + 2) := by
    dsimp [d, CReal.Pre.add, CReal.Pre.neg]; ring
  have hlim : (CReal.lim_pre s).approx (n + 2) = (s.pre (n + 4)).approx (n + 4) := by
    simp [lim_pre_approx_simp]
  rw [hJ, hlim]
  exact CReal.diff_at_sync_bound s n hn

lemma all_indices_bound_from_sync
  (d : CReal.Pre) (n k : ℕ)
  (_ : 2 ≤ n)
  (h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2))
  (hk : k ≤ n - 2) :
  ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
  intro j
  have h_all_sync :
      |d.approx (j + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) :=
    lift_sync_bound_with_uniform_tail d n (r := (1 : ℚ) / 2 ^ (n - 2)) (by simpa using h_sync) j
  have hmono :
      (1 : ℚ) / 2 ^ (n - 2) ≤ (1 : ℚ) / 2 ^ k :=
    one_div_pow_le_one_div_pow_of_le rfl hk
  have h_stronger :
      (1 : ℚ) / 2 ^ (n - 2) + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1)
        ≤ (1 : ℚ) / 2 ^ k + (1 : ℚ) / 2 ^ j + (1 : ℚ) / 2 ^ (n + 1) := by
    have := add_le_add_right (add_le_add_right hmono ((1 : ℚ) / 2 ^ j)) ((1 : ℚ) / 2 ^ (n + 1))
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact h_all_sync.trans h_stronger

theorem converges_to_lim (s : CReal.RCauSeq) (k : ℕ) :
    ∀ n ≥ k+2, |s.seq n - CReal.lim s| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) := by
  intro n hn
  have hseq : s.seq n = ⟦s.pre n⟧ := s.seq_spec' n
  have hlim : CReal.lim s = ⟦CReal.lim_pre s⟧ := rfl
  let d : CReal.Pre := CReal.Pre.add (s.pre n) (CReal.Pre.neg (CReal.lim_pre s))
  have hn2 : 2 ≤ n := Nat.le_of_add_left_le hn
  have h_sync : |d.approx (n + 1)| ≤ (1 : ℚ) / 2 ^ (n - 2) :=
    diff_sync_bound_for_d s n hn2
  have hk_le : k ≤ n - 2 := Nat.le_sub_of_add_le hn
  have hall_with_tail :
    ∀ j, |d.approx (j + 1)| ≤ (1 : ℚ) / (2 : ℚ) ^ k + 1 / (2 : ℚ) ^ j + 1 / 2 ^ (n + 1) :=
    all_indices_bound_from_sync d n k hn2 h_sync hk_le
  have hall' :
    ∀ j, |d.approx (j + 1)| ≤ ((1 : ℚ) / (2 : ℚ) ^ k + (1 : ℚ) / (2 : ℚ) ^ (n + 1)) + 1 / (2 : ℚ) ^ j := by
    intro j
    simpa [add_comm, add_left_comm, add_assoc] using (hall_with_tail j)
  have h_abs : |(⟦d⟧ : CReal)| ≤ ((((1 : ℚ) / (2 : ℚ) ^ k) + ((1 : ℚ) / (2 : ℚ) ^ (n + 1))) : CReal) :=
    by simpa using (CReal.abs_le_of_pre_abs_bound d hall')
  simpa [hseq, hlim, d, CReal.Pre.add, CReal.Pre.neg, sub_eq_add_neg] using h_abs

end CReal
