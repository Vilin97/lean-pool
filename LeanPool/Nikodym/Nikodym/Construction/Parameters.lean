/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Integer parameters of the construction

Blueprint nodes Q01 and Q02 of `docs/nikodym_construction_lean_blueprint.md`.

For `n ≥ 1` and `q ≥ 1` we set `M = ⌊q^{1/n}⌋₊`, `Qᵢ = ⌊q^{1/(n 2ⁱ)}⌋₊` and
`Dᵢ = ∏_{1 ≤ j < i} Qⱼ` (so `D₁ = 1` and `D_{i+1} = Dᵢ Qᵢ`). Q01 records the exact
natural-number power inequalities that follow from the floor definition. Q02 records the
threshold `q ≥ 2^{n 2^{h-1}}`, which forces `M, Qᵢ ≥ 2` and the matching real lower bounds.
-/

noncomputable section

open Finset Real

namespace Nikodym
namespace Params

variable (n q : ℕ)

/-- Blueprint Q01: `M = ⌊q^{1/n}⌋₊`. -/
def M : ℕ := ⌊(q : ℝ) ^ (1 / (n : ℝ))⌋₊

/-- Blueprint Q01: `Qᵢ = ⌊q^{1/(n 2ⁱ)}⌋₊`. Used for `1 ≤ i ≤ h - 1`. -/
def Q (i : ℕ) : ℕ := ⌊(q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i))⌋₊

/-- Blueprint Q01: mixed-radix products `Dᵢ = ∏_{j ∈ Ico 1 i} Qⱼ`.

This makes `D 0 = D 1 = 1` (empty products) and `D (i + 1) = D i * Q i` whenever `1 ≤ i`,
which is the recurrence `D₁ = 1`, `D_{i+1} = Dᵢ Qᵢ` of the blueprint. -/
def D (i : ℕ) : ℕ := ∏ j ∈ Ico 1 i, Q n q j

variable {n q}

/-! ### Auxiliary identities -/

/-- `1 ≤ n` is `n ≠ 0`. -/
theorem ne_zero_of_one_le {m : ℕ} (hm : 1 ≤ m) : m ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp hm

/-- The exponent in `Q` agrees with the reciprocal of the natural number `n * 2^i`. -/
theorem Q_exp_inv (n i : ℕ) :
    1 / ((n : ℝ) * 2 ^ i) = ((n * 2 ^ i : ℕ) : ℝ)⁻¹ := by
  rw [one_div]
  norm_cast

/-- Blueprint Q01: `⌊q^{1/k}⌋₊ ^ k ≤ q`. -/
theorem floor_root_pow_le {k : ℕ} (hk : k ≠ 0) :
    ⌊(q : ℝ) ^ (k : ℝ)⁻¹⌋₊ ^ k ≤ q := by
  have hy : 0 ≤ (q : ℝ) ^ (k : ℝ)⁻¹ := rpow_nonneg (Nat.cast_nonneg _) _
  have hfl : (⌊(q : ℝ) ^ (k : ℝ)⁻¹⌋₊ : ℝ) ≤ (q : ℝ) ^ (k : ℝ)⁻¹ :=
    Nat.floor_le hy
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hpow : (⌊(q : ℝ) ^ (k : ℝ)⁻¹⌋₊ : ℝ) ^ (k : ℝ) ≤
      ((q : ℝ) ^ (k : ℝ)⁻¹) ^ (k : ℝ) :=
    rpow_le_rpow (Nat.cast_nonneg _) hfl hkpos.le
  rw [rpow_inv_rpow (Nat.cast_nonneg q) (Nat.cast_ne_zero.2 hk)] at hpow
  exact mod_cast hpow

/-- Blueprint Q01: an integer `a` with `a ^ n ≤ q` satisfies `a ≤ M n q`. -/
theorem le_M_of_pow_le {a : ℕ} (hn : 1 ≤ n) (h : a ^ n ≤ q) : a ≤ M n q := by
  refine Nat.le_floor ?_
  have hn0 : n ≠ 0 := ne_zero_of_one_le hn
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hy : 0 ≤ (q : ℝ) ^ (1 / (n : ℝ)) := rpow_nonneg (Nat.cast_nonneg _) _
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  rw [← rpow_le_rpow_iff ha hy hnpos, one_div, rpow_inv_rpow (Nat.cast_nonneg q)
    (Nat.cast_ne_zero.2 hn0)]
  exact mod_cast h

/-- Geometric sum of successive powers of two: `∑_{1 ≤ j < i} 2^{i-1-j} = 2^{i-1} - 1`. -/
theorem sum_two_pow_pred {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ Ico 1 i, 2 ^ (i - 1 - j) = 2 ^ (i - 1) - 1 := by
  have h : i ≤ (i - 1) + 1 := by omega
  rw [sum_Ico_reflect (fun k ↦ 2 ^ k) 1 h]
  have h0 : i - 1 + 1 - i = 0 := by omega
  have h1 : i - 1 + 1 - 1 = i - 1 := by omega
  rw [h0, h1, Nat.Ico_zero_eq_range, Nat.geomSum_eq (le_rfl : 2 ≤ 2), Nat.div_one]

/-- Geometric sum of successive powers of two: `∑_{1 ≤ j < i} 2^{i-j} = 2^i - 2`. -/
theorem sum_two_pow_gap {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ Ico 1 i, 2 ^ (i - j) = 2 ^ i - 2 := by
  have hterm : ∀ j ∈ Ico 1 i, 2 ^ (i - j) = 2 * 2 ^ (i - 1 - j) := by
    intro j hj
    have : i - j = (i - 1 - j) + 1 := by
      have := (mem_Ico.1 hj).2
      omega
    rw [this, pow_succ, mul_comm]
  rw [sum_congr rfl hterm]
  rw [← mul_sum, sum_two_pow_pred hi, Nat.mul_sub, mul_one]
  congr 1
  rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hi]

/-- If `y ≥ 2` then `y / 2 ≤ ⌊y⌋₊`. -/
theorem half_le_floor {y : ℝ} (hy : 2 ≤ y) : y / 2 ≤ ⌊y⌋₊ := by
  have hy0 : 0 ≤ y := zero_le_two.trans hy
  have : (⌊y⌋₊ : ℝ) > y - 1 := by
    have := Nat.lt_floor_add_one y
    linarith
  have : y - 1 ≥ y / 2 := by linarith
  linarith

/-! ### Q01: exact natural-number inequalities -/

/-- Blueprint Q01: `M ^ n ≤ q`. -/
theorem M_pow_le (hn : 1 ≤ n) (hq : 1 ≤ q) : M n q ^ n ≤ q := by
  have := hq
  simpa [M, one_div] using floor_root_pow_le (q := q) (ne_zero_of_one_le hn)

/-- Blueprint Q01: `Q i ^ (n * 2 ^ i) ≤ q`. -/
theorem Q_pow_le (hn : 1 ≤ n) (hq : 1 ≤ q) (i : ℕ) : Q n q i ^ (n * 2 ^ i) ≤ q := by
  have := hq
  have hk : n * 2 ^ i ≠ 0 :=
    Nat.mul_ne_zero (ne_zero_of_one_le hn) (pow_ne_zero _ two_ne_zero)
  simpa [Q, Q_exp_inv] using floor_root_pow_le (q := q) hk

/-- Blueprint Q01: `Q i ≥ 1` for `q ≥ 1`. -/
theorem Q_pos (hq : 1 ≤ q) (i : ℕ) : 1 ≤ Q n q i := by
  rw [Q, Nat.one_le_floor_iff]
  exact one_le_rpow (Nat.one_le_cast.2 hq) (div_nonneg zero_le_one (by positivity))

/-- Blueprint Q01: `D 0 = 1`. -/
@[simp] theorem D_zero : D n q 0 = 1 := by simp [D]

/-- Blueprint Q01: `D 1 = 1`. -/
@[simp] theorem D_one : D n q 1 = 1 := by simp [D]

/-- Blueprint Q01: `D (i + 1) = D i * Q i` for `1 ≤ i`. -/
theorem D_succ {i : ℕ} (hi : 1 ≤ i) : D n q (i + 1) = D n q i * Q n q i :=
  prod_Ico_succ_top hi _

/-- Blueprint Q01: `D i ≥ 1` for `q ≥ 1`. -/
theorem D_pos (hq : 1 ≤ q) (i : ℕ) : 1 ≤ D n q i :=
  one_le_prod' fun j _ ↦ Q_pos hq j

/-- Blueprint Q01: `D` is monotone in the index. -/
theorem D_mono (hq : 1 ≤ q) {j i : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) : D n q j ≤ D n q i := by
  have hunion := prod_Ico_consecutive (Q n q) hj hji
  rw [D, D, ← hunion]
  exact Nat.le_mul_of_pos_right _ (one_le_prod' fun k _ ↦ Q_pos hq k)

/-- Blueprint Q01: `Q j` divides `D i` for `1 ≤ j < i`. -/
theorem Q_dvd_D {j i : ℕ} (hj : 1 ≤ j) (hji : j < i) : Q n q j ∣ D n q i :=
  dvd_prod_of_mem _ (mem_Ico.2 ⟨hj, hji⟩)

/-- Rewrite `Q j ^ (n * 2 ^ i)` by splitting the exponent. -/
theorem Q_pow_mul_exp {i j : ℕ} (hji : j ≤ i) :
    Q n q j ^ (n * 2 ^ i) = (Q n q j ^ (n * 2 ^ j)) ^ (2 ^ (i - j)) := by
  rw [← pow_mul]
  congr 1
  calc
    n * 2 ^ i = n * 2 ^ (j + (i - j)) := by rw [Nat.add_sub_of_le hji]
    _ = n * (2 ^ j * 2 ^ (i - j)) := by rw [pow_add]
    _ = n * 2 ^ j * 2 ^ (i - j) := by ring

/-- Blueprint Q01: raising `(D i * Q i ^ 2) ^ n ≤ q` to the `2^i`-th power. -/
theorem D_mul_Q_sq_pow_two_pow (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    (D n q i * Q n q i ^ 2) ^ (n * 2 ^ i) ≤ q ^ (2 ^ i) := by
  have hsplit :
      (D n q i * Q n q i ^ 2) ^ (n * 2 ^ i) =
        (∏ j ∈ Ico 1 i, (Q n q j ^ (n * 2 ^ j)) ^ (2 ^ (i - j))) *
          (Q n q i ^ (n * 2 ^ i)) ^ 2 := by
    rw [mul_pow, D, ← prod_pow]
    congr 1
    · refine prod_congr rfl fun j hj ↦ ?_
      have hji : j ≤ i := (mem_Ico.1 hj).2.le
      exact Q_pow_mul_exp hji
    · rw [← pow_mul, mul_comm 2, pow_mul]
  have hprod :
      (∏ j ∈ Ico 1 i, (Q n q j ^ (n * 2 ^ j)) ^ (2 ^ (i - j))) ≤
        ∏ j ∈ Ico 1 i, q ^ (2 ^ (i - j)) :=
    prod_le_prod' fun j _ ↦ pow_le_pow_left' (Q_pow_le hn hq j) _
  have hQi : (Q n q i ^ (n * 2 ^ i)) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left' (Q_pow_le hn hq i) _
  have hsum : (∏ j ∈ Ico 1 i, q ^ (2 ^ (i - j))) * q ^ 2 = q ^ (2 ^ i) := by
    rw [prod_pow_eq_pow_sum, ← pow_add, sum_two_pow_gap hi, Nat.sub_add_cancel]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hi
  calc
    (D n q i * Q n q i ^ 2) ^ (n * 2 ^ i) = _ := hsplit
    _ ≤ (∏ j ∈ Ico 1 i, q ^ (2 ^ (i - j))) * q ^ 2 := Nat.mul_le_mul hprod hQi
    _ = q ^ (2 ^ i) := hsum

/-- Blueprint Q01: `(D i * Q i ^ 2) ^ n ≤ q`. -/
theorem D_mul_Q_sq_pow_le (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    (D n q i * Q n q i ^ 2) ^ n ≤ q := by
  have hpow := D_mul_Q_sq_pow_two_pow hn hq hi
  have : ((D n q i * Q n q i ^ 2) ^ n) ^ (2 ^ i) ≤ q ^ (2 ^ i) := by
    rwa [← pow_mul]
  exact (Nat.pow_le_pow_iff_left (pow_ne_zero _ two_ne_zero)).1 this

/-- Blueprint Q01: `(D i) ^ (n * 2^{i-1}) ≤ q^{2^{i-1} - 1}`. -/
theorem D_pow_le (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    D n q i ^ (n * 2 ^ (i - 1)) ≤ q ^ (2 ^ (i - 1) - 1) := by
  have hsplit : D n q i ^ (n * 2 ^ (i - 1)) =
      ∏ j ∈ Ico 1 i, (Q n q j ^ (n * 2 ^ j)) ^ (2 ^ (i - 1 - j)) := by
    rw [D, ← prod_pow]
    refine prod_congr rfl fun j hj ↦ ?_
    have hji : j ≤ i - 1 := Nat.le_sub_one_of_lt (mem_Ico.1 hj).2
    have : n * 2 ^ (i - 1) = n * 2 ^ j * 2 ^ (i - 1 - j) := by
      calc
        n * 2 ^ (i - 1) = n * 2 ^ (j + (i - 1 - j)) := by rw [Nat.add_sub_of_le hji]
        _ = n * (2 ^ j * 2 ^ (i - 1 - j)) := by rw [pow_add]
        _ = n * 2 ^ j * 2 ^ (i - 1 - j) := by ring
    rw [this, pow_mul]
  have hprod :
      (∏ j ∈ Ico 1 i, (Q n q j ^ (n * 2 ^ j)) ^ (2 ^ (i - 1 - j))) ≤
        ∏ j ∈ Ico 1 i, q ^ (2 ^ (i - 1 - j)) :=
    prod_le_prod' fun j _ ↦ pow_le_pow_left' (Q_pow_le hn hq j) _
  calc
    D n q i ^ (n * 2 ^ (i - 1)) = _ := hsplit
    _ ≤ ∏ j ∈ Ico 1 i, q ^ (2 ^ (i - 1 - j)) := hprod
    _ = q ^ (2 ^ (i - 1) - 1) := by rw [prod_pow_eq_pow_sum, sum_two_pow_pred hi]

/-- Blueprint Q01: `(D i) ^ n ≤ q`. -/
theorem D_pow_le' (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) : D n q i ^ n ≤ q := by
  have h := D_pow_le hn hq hi
  have hle : q ^ (2 ^ (i - 1) - 1) ≤ q ^ (2 ^ (i - 1)) :=
    Nat.pow_le_pow_right (Nat.succ_le_iff.mp hq) (Nat.sub_le _ _)
  have : (D n q i ^ n) ^ (2 ^ (i - 1)) ≤ q ^ (2 ^ (i - 1)) := by
    rw [← pow_mul]
    exact h.trans hle
  exact (Nat.pow_le_pow_iff_left (pow_ne_zero _ two_ne_zero)).1 this

/-- Blueprint Q01: `D i * Q i ^ 2 ≤ M`. -/
theorem D_mul_Q_sq_le_M (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    D n q i * Q n q i ^ 2 ≤ M n q :=
  le_M_of_pow_le hn (D_mul_Q_sq_pow_le hn hq hi)

/-- Blueprint Q01: `D i ≤ M`. -/
theorem D_le_M (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) : D n q i ≤ M n q :=
  le_M_of_pow_le hn (D_pow_le' hn hq hi)

/-- Exponent identity for the real form of `D_pow_le`. -/
theorem D_sq_exp {i : ℕ} (hn : 1 ≤ n) :
    ((2 ^ i - 1 : ℕ) : ℝ) * 2 / ((n : ℝ) * 2 ^ i) =
      2 * (1 - (2 : ℝ)⁻¹ ^ i) / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_zero_of_one_le hn)
  have h2 : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ two_ne_zero
  have hsub : ((2 ^ i - 1 : ℕ) : ℝ) = (2 : ℝ) ^ i - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_one]
    norm_cast
  rw [hsub]
  have hcast : ((n : ℝ) * 2 ^ i) = (n : ℝ) * (2 : ℝ) ^ i := by norm_cast
  rw [hcast]
  calc
    ((2 : ℝ) ^ i - 1) * 2 / ((n : ℝ) * (2 : ℝ) ^ i)
      = 2 * ((2 : ℝ) ^ i - 1) / ((n : ℝ) * (2 : ℝ) ^ i) := by ring
    _ = 2 * (1 - ((2 : ℝ) ^ i)⁻¹) / n := by
        field [hn0, h2]
    _ = 2 * (1 - (2 : ℝ)⁻¹ ^ i) / n := by rw [inv_pow]

/-- Blueprint Q01: `(D (i+1) : ℝ) ^ 2 ≤ q^{2(1 - 2^{-i})/n}`. -/
theorem D_sq_le_rpow (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    ((D n q (i + 1) : ℝ)) ^ 2 ≤ (q : ℝ) ^ (2 * (1 - (2 : ℝ)⁻¹ ^ i) / n) := by
  have hi1 : 1 ≤ i + 1 := hi.trans (Nat.le_succ i)
  have hnat : D n q (i + 1) ^ (n * 2 ^ i) ≤ q ^ (2 ^ i - 1) := by
    simpa [Nat.add_sub_cancel] using D_pow_le hn hq hi1
  have hx : 0 ≤ (D n q (i + 1) : ℝ) := Nat.cast_nonneg _
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_zero_of_one_le hn)
  have hexp : 0 ≤ (2 : ℝ) / ((n : ℝ) * 2 ^ i) := by positivity
  have hL :
      ((D n q (i + 1) : ℝ) ^ (n * 2 ^ i)) ^ ((2 : ℝ) / ((n : ℝ) * 2 ^ i)) =
        (D n q (i + 1) : ℝ) ^ (2 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hx]
    congr 1
    rw [Nat.cast_mul, Nat.cast_pow]
    field [hn0]
  have hR :
      ((q : ℝ) ^ (2 ^ i - 1 : ℕ)) ^ ((2 : ℝ) / ((n : ℝ) * 2 ^ i)) =
        (q : ℝ) ^ (2 * (1 - (2 : ℝ)⁻¹ ^ i) / n) := by
    rw [← rpow_natCast, ← rpow_mul hq0, ← mul_div_assoc, D_sq_exp hn]
  have hpow : 0 ≤ (D n q (i + 1) : ℝ) ^ (n * 2 ^ i) := pow_nonneg hx _
  have hcast : (D n q (i + 1) : ℝ) ^ (n * 2 ^ i) ≤ (q : ℝ) ^ (2 ^ i - 1) := by
    simpa [Nat.cast_pow] using (Nat.cast_le (α := ℝ)).2 hnat
  have hineq := rpow_le_rpow hpow hcast hexp
  rw [hL, hR, rpow_two] at hineq
  exact hineq

/-- Blueprint Q01: the crude bound `(D (i+1) : ℝ) ^ 2 ≤ q^{2/n}`. -/
theorem D_sq_le_rpow' (hn : 1 ≤ n) (hq : 1 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    ((D n q (i + 1) : ℝ)) ^ 2 ≤ (q : ℝ) ^ (2 / (n : ℝ)) := by
  refine (D_sq_le_rpow hn hq hi).trans ?_
  refine rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hq) ?_
  have hinv : 0 ≤ ((2 : ℝ)⁻¹) ^ i := by positivity
  have : 1 - ((2 : ℝ)⁻¹) ^ i ≤ 1 := sub_le_self _ hinv
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  have : 2 * (1 - (2 : ℝ)⁻¹ ^ i) ≤ 2 * 1 := mul_le_mul_of_nonneg_left this zero_le_two
  exact (div_le_div_iff_of_pos_right hn0).2 (by linarith)

/-! ### Q02: thresholds and root lower bounds -/

/-- Blueprint Q02: the geometric sum `∑_{i=1}^{h-1} 2^{-i} = 1 - 2^{1-h}`. -/
theorem sum_inv_two_pow {h : ℕ} (hh : 1 ≤ h) :
    ∑ i ∈ Ico 1 h, ((2 : ℝ)⁻¹) ^ i = 1 - (2⁻¹) ^ (h - 1) := by
  have hx : (2 : ℝ)⁻¹ ≠ 1 := by norm_num
  rw [geom_sum_Ico' hx hh]
  have hden : (1 : ℝ) - (2 : ℝ)⁻¹ = 2⁻¹ := by norm_num
  rw [pow_one, hden]
  have : ((2 : ℝ)⁻¹ - (2 : ℝ)⁻¹ ^ h) / (2 : ℝ)⁻¹ =
      1 - 2 * ((2 : ℝ)⁻¹) ^ h := by
    field
  rw [this]
  have : 2 * ((2 : ℝ)⁻¹) ^ h = ((2 : ℝ)⁻¹) ^ (h - 1) := by
    nth_rw 1 [show h = h - 1 + 1 from (Nat.sub_add_cancel hh).symm]
    rw [pow_succ]
    ring
  rw [this]

/-- The threshold forces `1 ≤ q`. -/
theorem one_le_q_of_threshold {h : ℕ} (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) : 1 ≤ q :=
  (Nat.one_le_two_pow).trans hq

/-- Exponent identity used in the threshold comparison. -/
theorem threshold_exp {h i : ℕ} (hn : 1 ≤ n) (hih : i ≤ h - 1) :
    ((n * 2 ^ (h - 1) : ℕ) : ℝ) / ((n * 2 ^ i : ℕ) : ℝ) = (2 ^ (h - 1 - i) : ℕ) := by
  have hfactor : n * 2 ^ (h - 1) = n * 2 ^ i * 2 ^ (h - 1 - i) := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hih]
  have hnz : ((n * 2 ^ i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (ne_zero_of_one_le hn) (pow_ne_zero _ two_ne_zero)
  rw [hfactor, Nat.cast_mul, mul_div_cancel_left₀ _ hnz]

/-- Blueprint Q02: `2 ≤ q^{1/(n 2^i)}` for `1 ≤ i ≤ h-1`. -/
theorem two_le_rpow_Q {h i : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) (hi : 1 ≤ i) (hih : i ≤ h - 1) :
    (2 : ℝ) ≤ (q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) := by
  have := hh
  have := hi
  have hbase : (2 : ℝ) ^ (n * 2 ^ (h - 1)) ≤ (q : ℝ) := by exact_mod_cast hq
  have hnonneg : 0 ≤ (2 : ℝ) ^ (n * 2 ^ (h - 1)) := by positivity
  have hexp : 0 ≤ 1 / ((n : ℝ) * 2 ^ i) := by positivity
  have h1 : 1 ≤ 2 ^ (h - 1 - i) := Nat.one_le_two_pow
  calc
    (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (2 : ℝ) ^ (2 ^ (h - 1 - i)) := pow_le_pow_right₀ one_le_two h1
    _ = (2 : ℝ) ^ (((n * 2 ^ (h - 1) : ℕ) : ℝ) / ((n * 2 ^ i : ℕ) : ℝ)) := by
        rw [threshold_exp hn hih, rpow_natCast]
    _ = ((2 : ℝ) ^ ((n * 2 ^ (h - 1) : ℕ) : ℝ)) ^
          (((n * 2 ^ i : ℕ) : ℝ)⁻¹) := by
        rw [div_eq_mul_inv, rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    _ = ((2 : ℝ) ^ (n * 2 ^ (h - 1))) ^ (1 / ((n : ℝ) * 2 ^ i)) := by
        rw [rpow_natCast, Q_exp_inv]
    _ ≤ (q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) := rpow_le_rpow hnonneg hbase hexp

/-- Blueprint Q02: `2 ≤ q^{1/n}`. -/
theorem two_le_rpow_M {h : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) :
    (2 : ℝ) ≤ (q : ℝ) ^ (1 / (n : ℝ)) := by
  have hhi : 1 ≤ h - 1 := by omega
  have h1 : 1 ≤ 2 ^ (h - 1) :=
    le_trans (by decide : 1 ≤ 2) (Nat.pow_le_pow_right Nat.zero_lt_two hhi)
  have hbase : (2 : ℝ) ^ (n * 2 ^ (h - 1)) ≤ (q : ℝ) := by exact_mod_cast hq
  have hnonneg : 0 ≤ (2 : ℝ) ^ (n * 2 ^ (h - 1)) := by positivity
  have hexp : 0 ≤ 1 / (n : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_zero_of_one_le hn)
  calc
    (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (2 : ℝ) ^ (2 ^ (h - 1)) := pow_le_pow_right₀ one_le_two h1
    _ = (2 : ℝ) ^ (((n * 2 ^ (h - 1) : ℕ) : ℝ) / (n : ℝ)) := by
        rw [Nat.cast_mul, mul_div_cancel_left₀ _ hn0]
        norm_cast
    _ = ((2 : ℝ) ^ ((n * 2 ^ (h - 1) : ℕ) : ℝ)) ^ (n : ℝ)⁻¹ := by
        rw [div_eq_mul_inv, rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    _ = ((2 : ℝ) ^ (n * 2 ^ (h - 1))) ^ (1 / (n : ℝ)) := by
        rw [rpow_natCast, one_div]
    _ ≤ (q : ℝ) ^ (1 / (n : ℝ)) := rpow_le_rpow hnonneg hbase hexp

/-- Blueprint Q02: `2 ≤ Q i` for `1 ≤ i ≤ h-1`. -/
theorem two_le_Q {h i : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) (hi : 1 ≤ i) (hih : i ≤ h - 1) :
    2 ≤ Q n q i :=
  (Nat.le_floor_iff' two_ne_zero).2 (two_le_rpow_Q hn hh hq hi hih)

/-- Blueprint Q02: `2 ≤ M`. -/
theorem two_le_M {h : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) : 2 ≤ M n q :=
  (Nat.le_floor_iff' two_ne_zero).2 (two_le_rpow_M hn hh hq)

/-- Blueprint Q02: `q^{1/(n 2^i)} / 2 ≤ Q i`. -/
theorem Q_ge_half_rpow {h i : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) (hi : 1 ≤ i) (hih : i ≤ h - 1) :
    (q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) / 2 ≤ (Q n q i : ℝ) :=
  half_le_floor (two_le_rpow_Q hn hh hq hi hih)

/-- Blueprint Q02: `q^{1/n} / 2 ≤ M`. -/
theorem M_ge_half_rpow {h : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) :
    (q : ℝ) ^ (1 / (n : ℝ)) / 2 ≤ (M n q : ℝ) :=
  half_le_floor (two_le_rpow_M hn hh hq)

/-- Blueprint Q02: `M ≤ q^{1/n}`. Does not need the threshold. -/
theorem M_le_rpow : (M n q : ℝ) ≤ (q : ℝ) ^ (1 / (n : ℝ)) :=
  Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)

/-- Blueprint Q02: product lower bound on the `Q i`. -/
theorem prod_Q_pow_ge {h : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) :
    (∏ i ∈ Ico 1 h, ((Q n q i : ℝ)) ^ n) ≥
      2 ^ (-(n : ℝ) * (h - 1)) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ (h - 1)) := by
  have hh1 : 1 ≤ h := one_le_two.trans hh
  have hq1 : 1 ≤ q := one_le_q_of_threshold hq
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_zero_of_one_le hn)
  have hhalf : ∀ i ∈ Ico 1 h,
      (q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) / 2 ≤ (Q n q i : ℝ) := by
    intro i hi
    have ⟨hi1, hih⟩ := mem_Ico.1 hi
    exact Q_ge_half_rpow hn hh hq hi1 (Nat.le_sub_one_of_lt hih)
  have hterm : ∀ i ∈ Ico 1 h,
      ((q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) / 2) ^ n ≤ (Q n q i : ℝ) ^ n := by
    intro i hi
    exact pow_le_pow_left₀ (by positivity) (hhalf i hi) _
  have hprod := prod_le_prod (fun i _hi ↦ by positivity) hterm
  have hdiv :
      ∏ i ∈ Ico 1 h, ((q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) / 2) ^ n =
        (∏ i ∈ Ico 1 h, ((q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i))) ^ n) /
          ∏ i ∈ Ico 1 h, (2 : ℝ) ^ n := by
    simp_rw [div_pow]
    rw [prod_div_distrib]
  have hpows : ∀ i ∈ Ico 1 h,
      ((q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i))) ^ n = (q : ℝ) ^ ((2 : ℝ)⁻¹ ^ i) := by
    intro i _hi
    rw [← rpow_natCast, ← rpow_mul (Nat.cast_nonneg q)]
    congr 1
    calc
      1 / ((n : ℝ) * 2 ^ i) * n = (n : ℝ) / ((n : ℝ) * 2 ^ i) := by ring
      _ = 1 / (2 : ℝ) ^ i := by field
      _ = ((2 : ℝ)⁻¹) ^ i := by rw [one_div, inv_pow]
  have hsum := rpow_sum_of_pos (Nat.cast_pos.2 (Nat.succ_le_iff.mp hq1))
    (fun i : ℕ ↦ ((2 : ℝ)⁻¹) ^ i) (Ico 1 h)
  have hcard : #(Ico 1 h) = h - 1 := Nat.card_Ico _ _
  have hden : ∏ i ∈ Ico 1 h, (2 : ℝ) ^ n = (2 : ℝ) ^ (n * (h - 1)) := by
    rw [prod_const, hcard, ← pow_mul]
  calc
    ∏ i ∈ Ico 1 h, ((Q n q i : ℝ) ^ n) ≥
        ∏ i ∈ Ico 1 h, ((q : ℝ) ^ (1 / ((n : ℝ) * 2 ^ i)) / 2) ^ n := hprod
    _ = (∏ i ∈ Ico 1 h, (q : ℝ) ^ ((2 : ℝ)⁻¹ ^ i)) / (2 : ℝ) ^ (n * (h - 1)) := by
        rw [hdiv, prod_congr rfl hpows, hden]
    _ = (q : ℝ) ^ (∑ i ∈ Ico 1 h, ((2 : ℝ)⁻¹) ^ i) / (2 : ℝ) ^ (n * (h - 1)) := by
        rw [hsum]
    _ = (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ (h - 1)) / (2 : ℝ) ^ (n * (h - 1)) := by
        rw [sum_inv_two_pow hh1]
    _ = 2 ^ (-(n : ℝ) * (h - 1)) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ (h - 1)) := by
        have h2 : 0 ≤ (2 : ℝ) := zero_le_two
        rw [div_eq_inv_mul, ← rpow_natCast (2 : ℝ), ← rpow_neg h2]
        congr 2
        rw [Nat.cast_mul, Nat.cast_sub hh1, Nat.cast_one]
        ring

/-- Blueprint Q02: product upper bound on the `D_{i+1}`. -/
theorem prod_D_sq_le {h : ℕ} (hn : 1 ≤ n) (hh : 2 ≤ h)
    (hq : 2 ^ (n * 2 ^ (h - 1)) ≤ q) :
    ∏ i ∈ Ico 1 h, ((D n q (i + 1) : ℝ)) ^ 2 ≤ (q : ℝ) ^ (2 * (h - 1) / (n : ℝ)) := by
  have hq1 : 1 ≤ q := one_le_q_of_threshold hq
  have hh1 : 1 ≤ h := one_le_two.trans hh
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_zero_of_one_le hn)
  have hterm : ∀ i ∈ Ico 1 h, ((D n q (i + 1) : ℝ)) ^ 2 ≤ (q : ℝ) ^ (2 / (n : ℝ)) := by
    intro i hi
    have ⟨hi1, _⟩ := mem_Ico.1 hi
    exact D_sq_le_rpow' hn hq1 hi1
  have hprod := prod_le_prod (fun _ _ ↦ by positivity) hterm
  have hcard : #(Ico 1 h) = h - 1 := Nat.card_Ico _ _
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  calc
    ∏ i ∈ Ico 1 h, ((D n q (i + 1) : ℝ)) ^ 2 ≤
        ∏ i ∈ Ico 1 h, (q : ℝ) ^ (2 / (n : ℝ)) := hprod
    _ = ((q : ℝ) ^ (2 / (n : ℝ))) ^ (h - 1) := by rw [prod_const, hcard]
    _ = (q : ℝ) ^ (2 / (n : ℝ) * (h - 1 : ℕ)) := by
        rw [← rpow_natCast, rpow_mul hq0]
    _ = (q : ℝ) ^ (2 * (h - 1) / (n : ℝ)) := by
        congr 1
        rw [Nat.cast_sub hh1, Nat.cast_one]
        field [hn0]

end Params
end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
