/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2.PreBasics

open Nat

namespace Computable
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
    have hknm : kₙ ≤ kₘ := Nat.add_le_add_right hnm S
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
  have h_le' : ks ≤ kbS := Nat.add_le_add_right h_le S
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

set_option maxHeartbeats 400000 in
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


end CReal
end Computable
