/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
meta import Lean.Meta.Tactic.NormCast
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
Explicit numerical estimates for the factorial majorants used in the proposed
Euler construction. These lemmas prove combinatorial implications; they do not
assert the analytic estimates needed to apply the implications to Euler.
-/

@[expose] public section

noncomputable section

namespace EulerGevrey

open Finset

/-- Every interior entry of the `n`th binomial row is at least `n`. -/
theorem le_choose_of_interior (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hk1 : k = 1
      · simp [hk1]
      by_cases hkn' : k = n
      · subst k
        simp
      have hklt : k < n := by omega
      have hkp : 0 < k - 1 := by omega
      have hp := ih (k - 1) hkp (by omega)
      have hq := ih k hk hklt
      rw [Nat.choose_succ_left n k hk]
      omega

/-- The reciprocal binomial row has uniformly bounded sum, including order zero. -/
theorem sum_inv_choose_le_three (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) ≤ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hsum : ∑ k ∈ range n, (1 : ℝ) / ((n + 1).choose (k + 1) : ℝ)
          ≤ n * (1 / (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ _k ∈ range n, (1 / (n + 1) : ℝ) := by
            apply sum_le_sum
            intro k hk
            apply one_div_le_one_div_of_le hn
            exact_mod_cast le_choose_of_interior (n + 1) (k + 1)
              (by omega) (by have := mem_range.mp hk; omega)
          _ = _ := by simp
      have hquot : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn]
        linarith
      rw [sum_range_succ', sum_range_succ]
      norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]
      linarith

/-- Adding nonnegative shifts to both lower factorial indices enlarges the binomial coefficient. -/
theorem choose_le_shifted (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    n.choose k ≤ (n + d₁ + d₂).choose (k + d₁) := by
  calc
    n.choose k = n.choose (n - k) := (Nat.choose_symm hkn).symm
    _ ≤ (n + d₁).choose (n - k) := Nat.choose_le_add n d₁ (n - k)
    _ = (n + d₁).choose (k + d₁) := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ ≤ (n + d₁ + d₂).choose (k + d₁) :=
      Nat.choose_le_add (n + d₁) d₂ (k + d₁)

/-- The exact reciprocal-binomial comparison used in the shifted product estimate. -/
theorem choose_ratio_le_inv (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2
      ≤ 1 / (n.choose k : ℝ) := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hle : (n.choose k : ℝ) ≤ (n + d₁ + d₂).choose (k + d₁) := by
    exact_mod_cast choose_le_shifted n k d₁ d₂ hkn
  apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hc hle)) hc).2
  nlinarith

/-- A term of the shifted factorial convolution gains the reciprocal binomial coefficient. -/
theorem shifted_factorial_kernel_le (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
        ((n - k + d₂).factorial : ℝ) ^ 2
      ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 / (n.choose k : ℝ) := by
  have hlarge : k + d₁ ≤ n + d₁ + d₂ := by omega
  have hsub : n + d₁ + d₂ - (k + d₁) = n - k + d₂ := by omega
  have hfac : ((n + d₁ + d₂).choose (k + d₁) : ℝ) *
      ((k + d₁).factorial : ℝ) * ((n - k + d₂).factorial : ℝ) =
      ((n + d₁ + d₂).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hlarge
    rw [hsub] at h
    exact_mod_cast h
  have hC : ((n + d₁ + d₂).choose (k + d₁) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlarge
  calc
    _ = ((n + d₁ + d₂).factorial : ℝ) ^ 2 *
        ((n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2) := by
      rw [← hfac]
      field_simp
    _ ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 * (1 / (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left (choose_ratio_le_inv n k d₁ d₂ hkn) (sq_nonneg _)
    _ = _ := by ring

/-- The Gevrey-two factorial majorant with a nonnegative integer shift. -/
def majorant (R : ℝ) (d n : ℕ) : ℝ :=
  R ^ (n + d) * ((n + d).factorial : ℝ) ^ 2

theorem majorant_nonneg (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    0 ≤ majorant R d n := by
  unfold majorant
  positivity

/-- A single Leibniz term obeys the uniform shifted estimate. -/
theorem majorant_product_term (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
  have hexp : k + d₁ + (n - k + d₂) = n + d₁ + d₂ := by omega
  have hpow : R ^ (k + d₁) * R ^ (n - k + d₂) = R ^ (n + d₁ + d₂) := by
    rw [← pow_add, hexp]
  have h := mul_le_mul_of_nonneg_left (shifted_factorial_kernel_le n k d₁ d₂ hkn)
    (pow_nonneg hR (n + d₁ + d₂))
  unfold majorant
  simp only [← Nat.add_assoc]
  calc
    _ = (R ^ (k + d₁) * R ^ (n - k + d₂)) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by ring
    _ = R ^ (n + d₁ + d₂) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by rw [hpow]
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using h

/-- The product constant is exactly `3`, independently of order and both shifts. -/
theorem majorant_convolution (R : ℝ) (hR : 0 ≤ R) (n d₁ d₂ : ℕ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ 3 * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact majorant_product_term R hR n k d₁ d₂ (by have := mem_range.mp hk; omega)
    _ = majorant R (d₁ + d₂) n *
        ∑ k ∈ range (n + 1), (1 / (n.choose k : ℝ)) := by rw [mul_sum]
    _ ≤ majorant R (d₁ + d₂) n * 3 :=
      mul_le_mul_of_nonneg_left (sum_inv_choose_le_three n) (majorant_nonneg R hR _ _)
    _ = _ := by ring

/-- Discarding the reciprocal binomial gain is valid for each admissible split. -/
theorem majorant_product_term_le (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n := by
  have hc : (1 : ℝ) ≤ n.choose k := by
    exact_mod_cast Nat.choose_pos hkn
  have hi : (1 : ℝ) / (n.choose k : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc
  exact (majorant_product_term R hR n k d₁ d₂ hkn).trans
    (mul_le_of_le_one_right (majorant_nonneg R hR _ _) hi)

/-- One spare factorial shift supplies a factor of at least `R`. -/
theorem majorant_shift_le (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    R * majorant R d n ≤ majorant R (d + 1) n := by
  have hf : (((n + d).factorial : ℕ) : ℝ) ≤ ((n + (d + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show n + d ≤ n + (d + 1) by omega)
  have hs : ((n + d).factorial : ℝ) ^ 2 ≤ ((n + (d + 1)).factorial : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n + d).factorial by positivity]
  unfold majorant
  calc
    _ = R ^ (n + (d + 1)) * ((n + d).factorial : ℝ) ^ 2 := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (pow_nonneg hR _)

/-- The geometric tail is bounded uniformly in the truncation length. -/
theorem geometric_tail_le_two_mul (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (n : ℕ) : ∑ k ∈ range n, q ^ (k + 1) ≤ 2 * q := by
  have hgeom : ∀ m : ℕ, ∑ k ∈ range m, q ^ k ≤ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_range_succ']
        simp_rw [pow_succ]
        rw [← sum_mul]
        simp only [pow_zero]
        have hm := mul_le_mul_of_nonneg_right ih hq
        linarith
  simpa only [pow_succ, ← sum_mul] using mul_le_mul_of_nonneg_right (hgeom n) hq

/-- A coefficient of radius `Rc ≤ q R` has the geometric gain `q^k`. -/
theorem majorant_coefficient_term (R Rc q : ℝ)
    (hR : 0 ≤ R) (hRc : 0 ≤ Rc) (hq : 0 ≤ q) (hscale : Rc ≤ q * R)
    (n k d : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * Rc ^ k * (k.factorial : ℝ) ^ 2 * majorant R d (n - k)
      ≤ q ^ k * majorant R d n := by
  have hp : Rc ^ k ≤ (q * R) ^ k := pow_le_pow_left₀ hRc hscale k
  have hterm := majorant_product_term_le R hR n k 0 d hkn
  simp only [zero_add] at hterm
  have hscaled := mul_le_mul_of_nonneg_left hterm (pow_nonneg hq k)
  calc
    _ ≤ (n.choose k : ℝ) * (q * R) ^ k * (k.factorial : ℝ) ^ 2 *
        majorant R d (n - k) := by
      gcongr
      exact majorant_nonneg R hR d (n - k)
    _ = q ^ k * ((n.choose k : ℝ) * majorant R 0 k * majorant R d (n - k)) := by
      simp only [majorant, Nat.add_zero, mul_pow]
      ring
    _ ≤ _ := hscaled

/--
The triangular inverse rule with an explicit sufficient radius, uniform in the
derivative order and in the input shift. The recurrence sums the indices `1,…,n`
as `k + 1` for `k ∈ range n`. No sign assumption on `F` or `Z` is needed.
-/
theorem triangular_inverse_majorant (A Rc R : ℝ)
    (hA : 1 ≤ A) (hRc : 0 ≤ Rc) (hlarge : 2 * A * (Rc + 1) ≤ R)
    (d : ℕ) (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant R d n)
    (hZ : ∀ n, Z n ≤ A * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant R (d + 1) n := by
  have hA0 : 0 ≤ A := by linarith
  have hARc : 0 ≤ A * Rc := mul_nonneg hA0 hRc
  have hR : 0 < R := by nlinarith
  have hq0 : 0 ≤ Rc / R := div_nonneg hRc hR.le
  have hqhalf : Rc / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR).2
    nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hRc]
  have hscale : Rc ≤ (Rc / R) * R := by rw [div_mul_cancel₀ _ hR.ne']
  have hbudget : A / R + 2 * A * (Rc / R) ≤ 1 := by
    calc
      _ = (A + 2 * A * Rc) / R := by ring
      _ ≤ 1 := (div_le_one hR).2 (by nlinarith)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw : 0 ≤ majorant R (d + 1) n := majorant_nonneg R hR.le _ _
      have hshift : majorant R d n ≤ majorant R (d + 1) n / R := by
        apply (le_div_iff₀ hR).2
        simpa only [mul_comm] using majorant_shift_le R hR.le d n
      have hs : (∑ k ∈ range n,
          (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
            Z (n - (k + 1)))
          ≤ (2 * (Rc / R)) * majorant R (d + 1) n := by
        calc
          _ ≤ ∑ k ∈ range n, (Rc / R) ^ (k + 1) * majorant R (d + 1) n := by
            apply sum_le_sum
            intro k hk
            have hklt : k < n := mem_range.mp hk
            have hlow : n - (k + 1) < n := by omega
            have hc : 0 ≤ (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) *
                ((k + 1).factorial : ℝ) ^ 2 := by positivity
            exact (mul_le_mul_of_nonneg_left (ih _ hlow) hc).trans
              (majorant_coefficient_term R Rc (Rc / R) hR.le hRc hq0 hscale
                n (k + 1) (d + 1) (by omega))
          _ = (∑ k ∈ range n, (Rc / R) ^ (k + 1)) * majorant R (d + 1) n :=
            (sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (geometric_tail_le_two_mul (Rc / R) hq0 hqhalf n) hw
      calc
        Z n ≤ A * (F n + ∑ k ∈ range n,
            (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
              Z (n - (k + 1))) := hZ n
        _ ≤ A * (majorant R (d + 1) n / R +
            (2 * (Rc / R)) * majorant R (d + 1) n) :=
          mul_le_mul_of_nonneg_left (add_le_add ((hF n).trans hshift) hs) hA0
        _ = (A / R + 2 * A * (Rc / R)) * majorant R (d + 1) n := by ring
        _ ≤ majorant R (d + 1) n := mul_le_of_le_one_left hw hbudget

/-- For coefficient and inverse size `P^c`, the single polynomial radius `P^(2c+2)` suffices. -/
theorem triangular_inverse_polynomial_radius (P : ℝ) (hP : 2 ≤ P) (c d : ℕ)
    (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant (P ^ (2 * c + 2)) d n)
    (hZ : ∀ n, Z n ≤ P ^ c * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * (P ^ c) ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant (P ^ (2 * c + 2)) (d + 1) n := by
  have hPc : 1 ≤ P ^ c := one_le_pow₀ (by linarith)
  have hPc0 : 0 ≤ P ^ c := by linarith
  have hP2 : 4 ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 2)]
  have heq : P ^ (2 * c + 2) = (P ^ c) ^ 2 * P ^ 2 := by
    rw [show 2 * c + 2 = c * 2 + 2 by omega, pow_add, pow_mul]
  have hlarge : 2 * P ^ c * (P ^ c + 1) ≤ P ^ (2 * c + 2) := by
    calc
      _ ≤ (P ^ c) ^ 2 * 4 := by nlinarith
      _ ≤ (P ^ c) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
      _ = _ := heq.symm
  exact triangular_inverse_majorant (P ^ c) (P ^ c) (P ^ (2 * c + 2))
    hPc hPc0 hlarge d F Z hF hZ

/-- The shifted product rule applies directly to arbitrary real sequences bounded in absolute value.
-/
theorem sequence_product_majorant (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (d₁ d₂ : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ A * majorant R d₁ n)
    (hg : ∀ n, |g n| ≤ B * majorant R d₂ n) (n : ℕ) :
    |∑ k ∈ range (n + 1), (n.choose k : ℝ) * f k * g (n - k)|
      ≤ 3 * A * B * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1), |(n.choose k : ℝ) * f k * g (n - k)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), A * B *
        ((n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by
      apply sum_le_sum
      intro k _hk
      have hfg : |f k| * |g (n - k)| ≤
          (A * majorant R d₁ k) * (B * majorant R d₂ (n - k)) :=
        mul_le_mul (hf k) (hg (n - k)) (abs_nonneg _)
          (mul_nonneg hA (majorant_nonneg R hR d₁ k))
      have hc : (0 : ℝ) ≤ n.choose k := by positivity
      have h := mul_le_mul_of_nonneg_left hfg hc
      simpa only [abs_mul, abs_of_nonneg hc, mul_assoc, mul_left_comm, mul_comm] using h
    _ = A * B * (∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by rw [mul_sum]
    _ ≤ A * B * (3 * majorant R (d₁ + d₂) n) :=
      mul_le_mul_of_nonneg_left (majorant_convolution R hR n d₁ d₂) (mul_nonneg hA hB)
    _ = _ := by ring

end EulerGevrey
